// SPDX-License-Identifier: MIT
/*
$info$
category: glue ~ Logic that binds various parts together
meta: glue|driver ~ Emulation mainloop related glue logic
tags: glue|driver
desc: Glues Frontend, OpDispatcher and IR Opts & Compilation, LookupCache, Dispatcher and provides the Execution loop entrypoint
$end_info$
*/

#include <cstdint>
#ifdef ZYDIS_DISASSEMBLER
#include <Zydis/Zydis.h>
#endif
#include "Interface/Core/ArchHelpers/Arm64Emitter.h"
#include "Interface/Core/LookupCache.h"
#include "Interface/Core/CPUBackend.h"
#include "Interface/Core/CPUID.h"
#include "Interface/Core/Frontend.h"
#include "Interface/Core/OpcodeDispatcher.h"
#include "Interface/Core/JIT/JITClass.h"
#include "Interface/Core/Dispatcher/Dispatcher.h"
#include "Interface/Core/WineAppleHost.h"
#include "Interface/Core/X86Tables/X86Tables.h"
#include <Interface/GDBJIT/GDBJIT.h>
#include "Interface/IR/IR.h"
#include "Interface/IR/IREmitter.h"
#include "Interface/IR/Passes/RegisterAllocationPass.h"
#include "Interface/IR/Passes.h"
#include "Interface/IR/PassManager.h"
#include "Interface/IR/RegisterAllocationData.h"
#include "Utils/Allocator.h"
#include "Utils/Allocator/HostAllocator.h"
#include <FEXCore/Utils/SpinWaitLock.h>
#include "Utils/variable_length_integer.h"

#include <FEXCore/Config/Config.h>
#include <FEXCore/Core/Context.h>
#include <FEXCore/Core/CoreState.h>
#include <FEXCore/Core/SignalDelegator.h>
#include <FEXCore/Core/Thunks.h>
#include <FEXCore/Core/X86Enums.h>
#include <FEXCore/Debug/InternalThreadState.h>
#include <FEXCore/HLE/SyscallHandler.h>
#include <FEXCore/HLE/SourcecodeResolver.h>
#include <FEXCore/Utils/Allocator.h>
#include <FEXCore/Utils/Event.h>
#include <FEXCore/Utils/File.h>
#include <FEXCore/Utils/LogManager.h>
#include "FEXCore/Utils/SignalScopeGuards.h"
#include <FEXCore/Utils/Threads.h>
#include <FEXCore/Utils/Profiler.h>
#include <FEXCore/Utils/SHMStats.h>
#include <FEXCore/fextl/fmt.h>
#include <FEXCore/fextl/memory.h>
#include <FEXCore/fextl/set.h>
#include <FEXCore/fextl/sstream.h>
#include <FEXCore/fextl/vector.h>
#include <FEXHeaderUtils/Syscalls.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <fcntl.h>
#include <functional>
#include <mutex>
#include <queue>
#include <shared_mutex>
#include <signal.h>
#include <stdio.h>
#include <string_view>
#include <sys/stat.h>
#include <type_traits>
#include <unistd.h>
#include <unordered_map>
#include <utility>
#include <xxhash.h>

namespace FEXCore::Context {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
namespace {
void FEXCtorLog(const char* Msg) {
  size_t Len = 0;
  while (Msg[Len]) {
    ++Len;
  }
  uintptr_t SavedTeb {}, SavedX18 {};
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(SavedTeb) :: "memory");
  __asm__ volatile("mov %0, x18" : "=r"(SavedX18));
  register uint64_t x0 __asm__("x0") = 2;
  register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
  register uint64_t x2 __asm__("x2") = static_cast<uint64_t>(Len);
  register uint64_t x16 __asm__("x16") = 4;
  __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
  uintptr_t Restore = SavedTeb;
  if (Restore < 0x10000ull || (Restore & 0xFull)) {
    Restore = SavedX18;
  }
  if (Restore >= 0x10000ull && !(Restore & 0xFull)) {
    __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Restore) : "x18", "memory");
  }
}
static void WineAppleLogHex64(const char* Prefix, uint64_t V) {
  char Line[48];
  size_t I = 0;
  while (Prefix[I] && I < 24) {
    Line[I] = Prefix[I];
    ++I;
  }
  for (int B = 15; B >= 0; --B) {
    const unsigned N = static_cast<unsigned>((V >> (B * 4)) & 0xf);
    Line[I++] = N < 10 ? static_cast<char>('0' + N) : static_cast<char>('a' + (N - 10));
  }
  Line[I++] = '\n';
  Line[I] = 0;
  FEXCore::Allocator::CtorLog(Line);
}

// s73: ARM SP vs guest RSP vs CALL-return slot. C++ only — no extra JIT stp.
static bool WineAppleS73RIP(uint64_t RIP) {
  return RIP == 0x14000101aull || (RIP >= 0x14000138cull && RIP <= 0x1400013bbull);
}

// s82: RET pops [RSP], not callret (s46 is StoreJit only). SP-sync (s80/s81)
// did not unsmash TOS. If both TOS and stash look like guest RIPs and they
// disagree, restore the stash. Skip when TOS is a stack pointer (101a [rsp]).
// s92: global TOS=0 poke smashed CRT (never 13bb). Reverted.
// s93: TOS=0 poke only at 13bb (second chkstk RET).
static void WineAppleFixCallRetSlot(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  const uint64_t Crt = Frame->State.WineAppleCallRet;
  if (Crt < 0x140000000ull || Crt >= 0x140100000ull) {
    return;
  }
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  if (Grsp < 0x10000ull || (Grsp & 7ull) != 0) {
    return;
  }
  auto* Slot = reinterpret_cast<volatile uint64_t*>(Grsp);
  const uint64_t Tos = *Slot;
  if (Tos == Crt) {
    return;
  }
  if (Tos == 0) {
    if (GuestRIP != 0x1400013bbull) {
      return;
    }
  } else if (Tos < 0x140000000ull || Tos >= 0x140100000ull) {
    return;
  }
  // s115: after s113 skip, do not poke callret onto [RSP] when GuestRIP is
  // 147e/1601, or TOS is 1600/1601/147e. Leave the real return so 1600
  // `66 0F 7F` JITs aligned, not mid-insn 1601; RSP stays live.
  if (GuestRIP == 0x14000147eull || GuestRIP == 0x140001601ull ||
      Tos == 0x140001600ull || Tos == 0x140001601ull || Tos == 0x14000147eull) {
    return;
  }
  WineAppleLogHex64("s82 poke=", Tos);
  *Slot = Crt;
}

// s87: wine hostname argc=1. Frame rcx is CRT RIP junk (s86: 400013ed / 13f4).
// Fill after this CompileBlock loads Frame into SRA for 1022 cmp/jl.
static void WineAppleFixArgc(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001022ull) {
    return;
  }
  const uint64_t Rcx = Frame->State.gregs[X86State::REG_RCX];
  const bool Image = Rcx >= 0x140000000ull && Rcx < 0x140100000ull;
  const bool Trunc = (Rcx >> 32) == 0 && (Rcx & 0x40000000ull) != 0;
  if (!Image && !Trunc) {
    return;
  }
  WineAppleLogHex64("s87 poke=", Rcx);
  Frame->State.gregs[X86State::REG_RCX] = 1;
}

// s98: 119e sub rsp,rax. chkstk pop rax smashed (s97: rax=stack ffc0).
// 1194 mov eax,4038 is the alloc size.
static void WineAppleFixChkstkRax(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x14000119eull) {
    return;
  }
  const uint64_t Rax = Frame->State.gregs[X86State::REG_RAX];
  const bool Stack = Rax >= 0x10000ull && (Rax & 7ull) == 0 && (Rax >> 40) == 0 &&
                     (Rax < 0x140000000ull || Rax >= 0x140100000ull);
  if (!Stack) {
    return;
  }
  WineAppleLogHex64("s98 poke=", Rax);
  Frame->State.gregs[X86State::REG_RAX] = 0x4038ull;
}

static void WineAppleLogSlot(char Phase, FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  uint64_t ArmSP = 0;
  __asm__ volatile("mov %0, sp" : "=r"(ArmSP));
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  WineAppleLogHex64(Phase == 'e' ? "s73 e rip=" : "s73 d rip=", GuestRIP);
  WineAppleLogHex64("s73 asp=", ArmSP);
  WineAppleLogHex64("s73 rsp=", Grsp);
  if (Grsp >= 0x10000ull && (Grsp & 7ull) == 0) {
    WineAppleLogHex64("s73 [rsp]=", *reinterpret_cast<volatile uint64_t*>(Grsp));
  }
  // s94: same x23/Frame/[rsp] dump at 13bb (second chkstk RET). s78 was 101a/138c only.
  if (GuestRIP == 0x14000101aull || GuestRIP == 0x14000138cull || GuestRIP == 0x1400013bbull) {
    WineAppleLogHex64("s77 crt=", Frame->State.WineAppleCallRet);
    uint64_t X23 = 0;
    __asm__ volatile("mov %0, x23" : "=r"(X23));
    WineAppleLogHex64("s78 x23=", X23);
    if (Grsp >= 0x10000ull && (Grsp & 7ull) == 0) {
      const volatile uint64_t* S = reinterpret_cast<const volatile uint64_t*>(Grsp);
      WineAppleLogHex64("s78 +0=", S[0]);
      WineAppleLogHex64("s78 +8=", S[1]);
      WineAppleLogHex64("s78 +10=", S[2]);
      WineAppleLogHex64("s78 +18=", S[3]);
      WineAppleLogHex64("s78 +20=", S[4]);
    }
  }
  const uint64_t Slot = 0x10cffff98ull;
  if ((Slot & ~0x3fffull) == (Grsp & ~0x3fffull)) {
    WineAppleLogHex64("s73 [98]=", *reinterpret_cast<volatile uint64_t*>(Slot));
  }
}

// s85/s86: argc/argv at 101a (pre-chkstk) and 1022/1025. Frame after NoBlock Spill.
// s152: same helper, also 1307 HeapAlloc FF15 (rcx=heap rdx=flags; no new function).
static void WineAppleLogS85(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x14000101aull && GuestRIP != 0x140001022ull && GuestRIP != 0x140001025ull &&
      GuestRIP != 0x140001307ull) {
    return;
  }
  WineAppleLogHex64("s85 rip=", GuestRIP);
  WineAppleLogHex64("s85 rax=", Frame->State.gregs[X86State::REG_RAX]);
  WineAppleLogHex64("s85 rcx=", Frame->State.gregs[X86State::REG_RCX]);
  WineAppleLogHex64("s85 rdx=", Frame->State.gregs[X86State::REG_RDX]);
  // s153: HeapAlloc size is r8 (edi from WideCharToMultiByte). Same helper.
  WineAppleLogHex64("s85 r8=", Frame->State.gregs[X86State::REG_R8]);
}

// s99: CRT 147e nop/add rsp,38h/ret after FF15. Frame after NoBlock Spill.
static void WineAppleLogS99(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x14000147eull) {
    return;
  }
  WineAppleLogHex64("s99 rip=", GuestRIP);
  WineAppleLogHex64("s99 rax=", Frame->State.gregs[X86State::REG_RAX]);
  WineAppleLogHex64("s99 rsp=", Frame->State.gregs[X86State::REG_RSP]);
}

// s100: CRT 1476 FF15 IAT (native crash; s99: 147e never CB). Frame after Spill.
static void WineAppleLogS100(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001476ull) {
    return;
  }
  WineAppleLogHex64("s100 rip=", GuestRIP);
  WineAppleLogHex64("s100 rax=", Frame->State.gregs[X86State::REG_RAX]);
  WineAppleLogHex64("s100 rsp=", Frame->State.gregs[X86State::REG_RSP]);
  WineAppleLogHex64("s100 crt=", Frame->State.WineAppleCallRet);
}

// s102: 1478 FF15 kernel32!ResolveDelayLoadedAPI (s101 last callret).
// rcx ParentBase, rdx descriptor, r8 hook, r9 syshook, [rsp+20] thunk, [rsp+28] flags.
static void WineAppleLogS102(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001478ull) {
    return;
  }
  WineAppleLogHex64("s102 rip=", GuestRIP);
  WineAppleLogHex64("s102 rcx=", Frame->State.gregs[X86State::REG_RCX]);
  WineAppleLogHex64("s102 rdx=", Frame->State.gregs[X86State::REG_RDX]);
  WineAppleLogHex64("s102 r8=", Frame->State.gregs[X86State::REG_R8]);
  WineAppleLogHex64("s102 r9=", Frame->State.gregs[X86State::REG_R9]);
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  WineAppleLogHex64("s102 rsp=", Grsp);
  if (Grsp >= 0x10000ull && (Grsp & 7ull) == 0) {
    const volatile uint64_t* S = reinterpret_cast<const volatile uint64_t*>(Grsp);
    WineAppleLogHex64("s102 +20=", S[4]);
    WineAppleLogHex64("s102 +28=", S[5]);
  }
}

// s103: 1478 5th/6th args junk (s102: [rsp+20]=3, [rsp+28]=1475).
// ThunkAddress is LoadStringW IAT 0x140004008; Flags=0. Do not poke rcx/rdx/r8/r9.
static void WineAppleFixDelayThunk(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001478ull) {
    return;
  }
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  if (Grsp < 0x10000ull || (Grsp & 7ull) != 0) {
    return;
  }
  volatile uint64_t* S = reinterpret_cast<volatile uint64_t*>(Grsp);
  const uint64_t Thunk = S[4];
  if (Thunk >= 0x140000000ull && Thunk < 0x140100000ull) {
    return;
  }
  WineAppleLogHex64("s103 poke=", Thunk);
  S[4] = 0x140004008ull;
  S[5] = 0;
}

// s113: 1478 is hostname x64 FF15 kernel32!ResolveDelayLoadedAPI (LoadStringW
// delay-load) AND wineboot/start ARM64EC .text (stp/adrp) at the same VA.
// Discriminator: guest bytes FF 15. Skip Ldr. s117: emulate 147e add rsp,38h; ret
// in C++ (RIP/callret = helper caller) instead of re-JITing 147e. s120 rax=1483.
// s121: after s117/s118/s120, emulate TailMerge add rsp,68h; ret (skip jmp rax).
// Do not compile/run the helper. Not FF15: no-op. Fallback RIP=147e if stack
// not WineAppleStackLike.
// s114: stash live Frame RSP at skip (file-static, not CPUState, not a hardcoded
// 0x10cffbea0). s113: 147e JIT ran with rsp=10cffbea0 then cliff 1601 RSP=0
// (movdqa [rsp+30h],xmm1). 147e is nop; add rsp,38h; ret — 1601 is the caller
// (s82 TOS=1601). Restore stash+0x38+8 at 1601 if RSP is 0 / not stack-like.
// s116: once, store 0x140001483 (helper lone c3 ret) into delay IAT 0x140004008
// so LoadStringW does not re-enter thunk 0x1400015d6 → helper 1450 → 1478.
// 147e is nop; add rsp,38h; ret — smash if used as LoadStringW target.
static uint64_t WineAppleSkipRsp = 0;
static bool WineAppleS116IatDone = false;
// s126: persist last CALL fallthrough outside Frame (AfterNative/Fill zeros
// Frame.rip and WineAppleCallRet). File-static like s114, not a CPUState field.
// s127: FEXWineAppleLastCallRetPeek (after namespace) reads this at LoopTop.
static uint64_t WineAppleLastCallRet = 0;

static bool WineAppleStackLike(uint64_t V) {
  return V >= 0x10000ull && (V & 7ull) == 0 && (V >> 40) == 0 &&
         (V < 0x140000000ull || V >= 0x140100000ull);
}

static bool WineAppleSkipDelayLoad(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001478ull) {
    return false;
  }
  const auto* P = reinterpret_cast<const volatile uint8_t*>(GuestRIP);
  const uint8_t B0 = P[0];
  const uint8_t B1 = P[1];
  if (B0 != 0xff || B1 != 0x15) {
    return false;
  }
  WineAppleLogHex64("s113 skip=", GuestRIP);
  if (!WineAppleS116IatDone) {
    volatile uint64_t* Iat = reinterpret_cast<volatile uint64_t*>(0x140004008ull);
    const uint64_t Old = *Iat;
    WineAppleLogHex64("s116 iat=", Old);
    *Iat = 0x140001483ull;
    WineAppleS116IatDone = true;
  }
  WineAppleSkipRsp = Frame->State.gregs[X86State::REG_RSP];
  WineAppleLogHex64("s114 stash=", WineAppleSkipRsp);
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  uint64_t NewSp = Grsp + 0x38ull;
  uint64_t Ret = 0;
  bool Emulated = false;
  if (WineAppleStackLike(Grsp) && WineAppleStackLike(NewSp)) {
    Ret = *reinterpret_cast<volatile uint64_t*>(NewSp);
    WineAppleLogHex64("s117 ret=", Ret);
    if (Ret == 0x140001601ull) {
      Ret = 0x140001621ull;
      WineAppleLogHex64("s118 rip=", Ret);
    }
    Frame->State.gregs[X86State::REG_RSP] = NewSp + 8ull;
    Frame->State.rip = Ret;
    Frame->State.WineAppleCallRet = Ret;
    Frame->State.gregs[X86State::REG_RAX] = 0x140001483ull;
    WineAppleLogHex64("s120 rax=", 0x140001483ull);
    {
      const uint64_t TmSp = Frame->State.gregs[X86State::REG_RSP] + 0x68ull;
      if (WineAppleStackLike(TmSp)) {
        uint64_t Caller = *reinterpret_cast<volatile uint64_t*>(TmSp);
        WineAppleLogHex64("s121 tos=", Caller);
        Frame->State.gregs[X86State::REG_RSP] = TmSp + 8ull;
        if (Caller < 0x140000000ull || Caller >= 0x140100000ull) {
          Caller = 0x1400011dcull;
          WineAppleLogHex64("s121 rip=", Caller);
        }
        Frame->State.rip = Caller;
        Frame->State.WineAppleCallRet = Caller;
        Frame->State.gregs[X86State::REG_RAX] = 0; // LoadStringW fail-closed *return value* now that jmp rax is skipped
      }
    }
    Emulated = true;
  }
  if (!Emulated) {
    Frame->State.rip = 0x14000147eull;
    Frame->State.WineAppleCallRet = 0x14000147eull;
    Frame->State.gregs[X86State::REG_RAX] = 0x140001483ull;
    WineAppleLogHex64("s120 rax=", 0x140001483ull);
  }
  return true;
}

static void WineAppleFix1601Rsp(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001601ull) {
    return;
  }
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  if (WineAppleStackLike(Grsp)) {
    return;
  }
  uint64_t Restore = WineAppleSkipRsp;
  if (!WineAppleStackLike(Restore)) {
    return;
  }
  Restore += 0x38ull + 8ull;
  WineAppleLogHex64("s114 rsp=", Grsp);
  WineAppleLogHex64("s114 set=", Restore);
  Frame->State.gregs[X86State::REG_RSP] = Restore;
}

// s122: 13bb is __chkstk `c3`. AfterNative executed stack TOS (s121:
// [rsp]=0x10cffffc0 crt=124f) as code. s82 correctly refuses to poke a
// stack-pointer TOS. Emulate RET: pop RSP, set RIP=callret. Do not write [RSP].
// Do not TOS=0 poke. Do not s72 ARM SP. Only when TOS is stack-like.
static bool WineAppleSkip13bbStackTos(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x1400013bbull) {
    return false;
  }
  const uint64_t Crt = Frame->State.WineAppleCallRet;
  if (Crt < 0x140000000ull || Crt >= 0x140100000ull) {
    return false;
  }
  const uint64_t Grsp = Frame->State.gregs[X86State::REG_RSP];
  if (!WineAppleStackLike(Grsp)) {
    return false;
  }
  const uint64_t Tos = *reinterpret_cast<volatile uint64_t*>(Grsp);
  if (!WineAppleStackLike(Tos)) {
    return false; // only when TOS is a stack pointer, not 0, not image RIP
  }
  WineAppleLogHex64("s122 tos=", Tos);
  WineAppleLogHex64("s122 rip=", Crt);
  Frame->State.gregs[X86State::REG_RSP] = Grsp + 8ull; // emulate ret pop, do not write [RSP]
  Frame->State.rip = Crt;
  return true;
}

// s124: CompileBlock GuestRIP==0 with WineAppleCallRet in hostname image
// is a RET/callret that landed on 0 (s123 FAR guest_rip=0 after 12be/12e9/1307
// WriteConsoleW). Restore RIP to callret and br DispatcherLoopTop. Do not
// decode addr 0. Do not poke TOS. Do not add WineAppleHost opcodes. Before
// GuestRIP < 0x10000 CompileOneInsn (that ldrb@0 is the s123 cliff).
static bool WineAppleSkipRip0(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0) {
    return false;
  }
  const uint64_t Crt = Frame->State.WineAppleCallRet;
  if (Crt < 0x140000000ull || Crt >= 0x140100000ull) {
    return false;
  }
  WineAppleLogHex64("s124 rip=", Crt);
  Frame->State.rip = Crt;
  return true;
}

// s144: CompileBlock GuestRIP==0x140001387 is mid-instruction: epilogue
// 1386 `41 5e` pop r14; 1388 `c3` ret. Landing on 1387 (`5e`) decodes as
// pop rsi from the second byte. Rewind RIP to 1386 and br DispatcherLoopTop.
// Do not decode 1387. Do not poke TOS. Before GuestRIP < 0x10000 WineAppleHost.
static bool WineAppleSkipRip1387(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001387ull) {
    return false;
  }
  WineAppleLogHex64("s144 rip=", GuestRIP);
  Frame->State.rip = 0x140001386ull;
  return true;
}

// s146: CompileBlock GuestRIP==0x140001376 is hostname `0F 28 B4 24 50 40 00 00`
// movaps xmm6,[rsp+4050h] after 1370 FF15 IAT (s145 FAR). Discriminator: guest
// bytes 0F 28 (wineboot ARM may share ImageBase). Emulate: copy 16 bytes from
// RSP+0x4050 into XMM6 (sse.data[6] overlays avx lane 6 low 128), RIP=137e
// (add rsp,4068h). Guard memcpy: RSP>>28==0x10 (s134 stack) and no wrap.
// Do not poke TOS. Do not decode 1376. Same CompileBlock site as SkipRip0.
static bool WineAppleSkipRip1376(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x140001376ull) {
    return false;
  }
  const auto* P = reinterpret_cast<const volatile uint8_t*>(GuestRIP);
  if (P[0] != 0x0f || P[1] != 0x28) {
    return false;
  }
  const uint64_t Rsp = Frame->State.gregs[X86State::REG_RSP];
  if ((Rsp >> 28) != 0x10ull) {
    return false;
  }
  if (Rsp > (~0ull - 0x4050ull - 16ull)) {
    return false;
  }
  const uint64_t Src = Rsp + 0x4050ull;
  const volatile uint64_t* SrcP = reinterpret_cast<const volatile uint64_t*>(Src);
  Frame->State.xmm.sse.data[6][0] = SrcP[0];
  Frame->State.xmm.sse.data[6][1] = SrcP[1];
  Frame->State.rip = 0x14000137eull;
  WineAppleLogHex64("s146 xmm=", Src);
  return true;
}

// s147: CompileBlock GuestRIP==0x14000137e is hostname `48 81 C4 68 40 00 00`
// add rsp,4068h after s146 emulate of 1376 movaps. Discriminator: guest
// bytes 48 81 (REX.W add). Emulate: RSP += 0x4068, RIP=1385 (137e+7; pop rbx).
// s149: s147 set RIP=1383 (imm32 tail 00 00). Real pop rbx is 1385 `5b`.
// Guard: RSP>>28==0x10 (s134 stack) and add doesn't wrap.
// Do not poke TOS. Do not decode 137e. Same CompileBlock site as SkipRip1376.
static bool WineAppleSkipRip137e(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  if (GuestRIP != 0x14000137eull) {
    return false;
  }
  const auto* P = reinterpret_cast<const volatile uint8_t*>(GuestRIP);
  if (P[0] != 0x48 || P[1] != 0x81) {
    return false;
  }
  const uint64_t Rsp = Frame->State.gregs[X86State::REG_RSP];
  if ((Rsp >> 28) != 0x10ull) {
    return false;
  }
  if (Rsp > (~0ull - 0x4068ull)) {
    return false;
  }
  const uint64_t NewRsp = Rsp + 0x4068ull;
  Frame->State.gregs[X86State::REG_RSP] = NewRsp;
  Frame->State.rip = 0x140001385ull;
  WineAppleLogHex64("s147 rsp=", NewRsp);
  return true;
}

} // namespace

// s123/s128/s142: RIP-local TEB for ExitFunctionEC br x9 at WriteConsoleW
// (12b0/12b6), hostname IAT FF15 at 127e (fallthrough 1284), and hostname
// IAT FF15 at 1370 (movaps restore 1376) after WriteConsoleW.
// Not global s110. WineAppleLogHex64 is file-static in the anon ns above.
extern "C" uintptr_t FEXWineAppleTebIfWriteConsole(FEXCore::Core::CPUState* St) {
  if (!St) {
    return 0;
  }
  const uint64_t Rip = St->rip;
  const uint64_t Crt = St->WineAppleCallRet;
  const bool WC = Rip == 0x1400012b0ull || Rip == 0x1400012b6ull ||
                  Rip == 0x14000127eull || Rip == 0x140001284ull ||
                  Rip == 0x140001370ull || Rip == 0x140001376ull ||
                  Crt == 0x1400012b0ull || Crt == 0x1400012b6ull ||
                  Crt == 0x14000127eull || Crt == 0x140001284ull ||
                  Crt == 0x140001370ull || Crt == 0x140001376ull;
  if (!WC) {
    return 0;
  }
  const uint64_t Teb = St->gs_cached;
  const bool S142 = Rip == 0x140001370ull || Rip == 0x140001376ull ||
                    Crt == 0x140001370ull || Crt == 0x140001376ull;
  const bool S128 = Rip == 0x14000127eull || Rip == 0x140001284ull ||
                    Crt == 0x14000127eull || Crt == 0x140001284ull;
  {
    char Line[48];
    const char* Prefix = S142 ? "s142 teb=" : S128 ? "s128 teb=" : "s123 teb=";
    size_t I = 0;
    while (Prefix[I] && I < 24) {
      Line[I] = Prefix[I];
      ++I;
    }
    for (int B = 15; B >= 0; --B) {
      const unsigned N = static_cast<unsigned>((Teb >> (B * 4)) & 0xf);
      Line[I++] = N < 10 ? static_cast<char>('0' + N) : static_cast<char>('a' + (N - 10));
    }
    Line[I++] = '\n';
    Line[I] = 0;
    FEXCore::Allocator::CtorLog(Line);
  }
  if (Teb < (1ull << 40) || Teb >= 0x800000000000ull) {
    return 0;
  }
  return Teb;
}

// s126: AfterNative, before FillSRA. Area+0x30 is EmulatorData[0] StateFrame
// (Module.S ldr x16,[x17,#0x30]; StateFrame == &Frame->State). Restore RIP
// from Frame callret, else file-static LastCallRet, when Frame.rip is 0.
extern "C" void FEXWineAppleFixRip0FromArea(void* Area) {
  if (!Area) {
    return;
  }
  auto* St = *reinterpret_cast<FEXCore::Core::CPUState**>(reinterpret_cast<char*>(Area) + 0x30);
  if (!St || St->rip) {
    return;
  }
  uint64_t R = St->WineAppleCallRet;
  if (R < 0x140000000ull || R >= 0x140100000ull) {
    R = WineAppleLastCallRet;
  }
  if (R < 0x140000000ull || R >= 0x140100000ull) {
    return;
  }
  WineAppleLogHex64("s126 rip=", R);
  St->rip = R;
}

// s127: LoopTop peek of s126 file-static LastCallRet when RIP and Frame
// callret are both 0. AfterNative helper never logged; Frame slot unused.
extern "C" uint64_t FEXWineAppleLastCallRetPeek() {
  const uint64_t V = WineAppleLastCallRet;
  if (V >= 0x140000000ull && V < 0x140100000ull) {
    WineAppleLogHex64("s127 rip=", V);
  }
  return V;
}
#endif

ContextImpl::ContextImpl(const FEXCore::HostFeatures& Features)
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  // Assign HostFeatures after bases construct (copy of Features was suspect).
  : HostFeatures {}
#else
  : HostFeatures {Features}
#endif
  , CPUID {this}
  , CodeCache {*this} {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("ContextImpl: after CPUID+CodeCache\n");
  // Scalar copy only — operator= on HostFeatures copies CPUMIDRs via
  // fextl::vector (libc #memmove exit-thunk before JIT → c000001d).
  HostFeatures.DCacheLineSize = Features.DCacheLineSize;
  HostFeatures.ICacheLineSize = Features.ICacheLineSize;
  HostFeatures.SupportsCacheMaintenanceOps = Features.SupportsCacheMaintenanceOps;
  HostFeatures.SupportsAES = Features.SupportsAES;
  HostFeatures.SupportsCRC = Features.SupportsCRC;
  HostFeatures.SupportsCLZERO = Features.SupportsCLZERO;
  HostFeatures.SupportsAtomics = Features.SupportsAtomics;
  HostFeatures.SupportsRCPC = Features.SupportsRCPC;
  HostFeatures.SupportsTSOImm9 = Features.SupportsTSOImm9;
  HostFeatures.SupportsRAND = Features.SupportsRAND;
  HostFeatures.SupportsAVX = Features.SupportsAVX;
  HostFeatures.SupportsSVE128 = Features.SupportsSVE128;
  HostFeatures.SupportsSVE256 = Features.SupportsSVE256;
  HostFeatures.SupportsSHA = Features.SupportsSHA;
  HostFeatures.SupportsPMULL_128Bit = Features.SupportsPMULL_128Bit;
  HostFeatures.SupportsCSSC = Features.SupportsCSSC;
  HostFeatures.SupportsFCMA = Features.SupportsFCMA;
  HostFeatures.SupportsFlagM = Features.SupportsFlagM;
  HostFeatures.SupportsFlagM2 = Features.SupportsFlagM2;
  HostFeatures.SupportsRPRES = Features.SupportsRPRES;
  HostFeatures.SupportsPreserveAllABI = Features.SupportsPreserveAllABI;
  HostFeatures.SupportsAES256 = Features.SupportsAES256;
  HostFeatures.SupportsSVEBitPerm = Features.SupportsSVEBitPerm;
  HostFeatures.SupportsCPUIndexInTPIDRRO = Features.SupportsCPUIndexInTPIDRRO;
  HostFeatures.SupportsFRINTTS = Features.SupportsFRINTTS;
  HostFeatures.SupportsECV = Features.SupportsECV;
  HostFeatures.SupportsWFXT = Features.SupportsWFXT;
  HostFeatures.Supports3DNow = Features.Supports3DNow;
  HostFeatures.SupportsSSE4a = Features.SupportsSSE4a;
  HostFeatures.SupportsMOPS = Features.SupportsMOPS;
  HostFeatures.SupportsAFP = Features.SupportsAFP;
  HostFeatures.SupportsFloatExceptions = Features.SupportsFloatExceptions;
  HostFeatures.IsInstCountCI = Features.IsInstCountCI;
  // CPUMIDRs left empty (never push during ProcessInit).
  FEXCtorLog("ContextImpl: after HostFeatures assign\n");
#endif
  if (!Config.Is64BitMode()) {
    // When operating in 32-bit mode, the virtual memory we care about is only the lower 32-bits.
    Config.VirtualMemSize = 1ULL << 32;
  }

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("ContextImpl: skip Symbols/TSC for now\n");
#else
  if (Config.BlockJITNaming() || Config.GlobalJITNaming() || Config.LibraryJITNaming()) {
    // Only initialize symbols file if enabled. Ensures we don't pollute /tmp with empty files.
    Symbols.InitFile();
  }

  uint64_t FrequencyCounter = FEXCore::GetCycleCounterFrequency();
  if (FrequencyCounter && FrequencyCounter < FEXCore::Context::TSC_SCALE_MAXIMUM && Config.SmallTSCScale()) {
    // Scale TSC until it is at the minimum required.
    while (FrequencyCounter < FEXCore::Context::TSC_SCALE_MAXIMUM) {
      FrequencyCounter <<= 1;
      ++Config.TSCScale;
    }
  }
#endif

  // Track atomic TSO emulation configuration.
  UpdateAtomicTSOEmulationConfig();
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("ContextImpl: ctor done\n");
#endif
}

struct GetFrameBlockInfoResult {
  const CPU::CPUBackend::JITCodeHeader* InlineHeader;
  const CPU::CPUBackend::JITCodeTail* InlineTail;
};
static GetFrameBlockInfoResult GetFrameBlockInfo(FEXCore::Core::CpuStateFrame* Frame) {
  const uint64_t BlockBegin = Frame->State.InlineJITBlockHeader;
  auto InlineHeader = reinterpret_cast<const CPU::CPUBackend::JITCodeHeader*>(BlockBegin);

  if (InlineHeader) {
    auto InlineTail = reinterpret_cast<const CPU::CPUBackend::JITCodeTail*>(Frame->State.InlineJITBlockHeader + InlineHeader->OffsetToBlockTail);
    return {InlineHeader, InlineTail};
  }

  return {InlineHeader, nullptr};
}

bool ContextImpl::IsAddressInCurrentBlock(FEXCore::Core::InternalThreadState* Thread, uint64_t Address, uint64_t Size) {
  auto [_, InlineTail] = GetFrameBlockInfo(Thread->CurrentFrame);
  return InlineTail && (Address + Size > InlineTail->RIP && Address < InlineTail->RIP + InlineTail->GuestSize);
}

bool ContextImpl::IsCurrentBlockSingleInst(FEXCore::Core::InternalThreadState* Thread) {
  auto [_, InlineTail] = GetFrameBlockInfo(Thread->CurrentFrame);
  return InlineTail && InlineTail->SingleInst;
}

uint64_t ContextImpl::GetGuestBlockEntry(FEXCore::Core::InternalThreadState* Thread) {
  auto [_, InlineTail] = GetFrameBlockInfo(Thread->CurrentFrame);
  return InlineTail ? InlineTail->RIP : 0;
}

uint64_t ContextImpl::RestoreRIPFromHostPC(FEXCore::Core::InternalThreadState* Thread, uint64_t HostPC) {
  const auto Frame = Thread->CurrentFrame;
  const uint64_t BlockBegin = Frame->State.InlineJITBlockHeader;
  auto [InlineHeader, InlineTail] = GetFrameBlockInfo(Thread->CurrentFrame);

  if (InlineHeader) {
    // Check if the host PC is currently within a code block.
    // If it is then RIP can be reconstructed from the beginning of the code block.
    // This is currently as close as FEX can get RIP reconstructions.
    if (HostPC >= reinterpret_cast<uint64_t>(BlockBegin) && HostPC < reinterpret_cast<uint64_t>(BlockBegin + InlineTail->Size)) {

      auto RIPEntry =
        reinterpret_cast<const uint8_t*>(Frame->State.InlineJITBlockHeader + InlineHeader->OffsetToBlockTail + InlineTail->OffsetToRIPEntries);

      // Reconstruct RIP from JIT entries for this block.
      uint64_t StartingHostPC = BlockBegin;
      uint64_t StartingGuestRIP = InlineTail->RIP;

      for (uint32_t i = 0; i < InlineTail->NumberOfRIPEntries; ++i) {
        auto Offset = FEXCore::Utils::vl64pair::Decode(RIPEntry);
        RIPEntry += Offset.Size;
        if (HostPC >= (StartingHostPC + Offset.IntegerARMPC)) {
          // We are beyond this entry, keep going forward.
          StartingHostPC += Offset.IntegerARMPC;
          StartingGuestRIP += Offset.IntegerX86RIP;
        } else {
          // Passed where the Host PC is at. Break now.
          break;
        }
      }
      return StartingGuestRIP;
    }
  }

  // Fallback to what is stored in the RIP currently.
  return Frame->State.rip;
}

uint32_t ContextImpl::ReconstructCompactedEFLAGS(FEXCore::Core::InternalThreadState* Thread, bool WasInJIT, const uint64_t* HostGPRs,
                                                 uint64_t PSTATE) {
  const auto Frame = Thread->CurrentFrame;
  uint32_t EFLAGS {};

  // Currently these flags just map 1:1 inside of the resulting value.
  for (size_t i = 0; i < FEXCore::Core::CPUState::NUM_EFLAG_BITS; ++i) {
    switch (i) {
    case X86State::RFLAG_CF_RAW_LOC:
    case X86State::RFLAG_PF_RAW_LOC:
    case X86State::RFLAG_AF_RAW_LOC:
    case X86State::RFLAG_TF_RAW_LOC:
    case X86State::RFLAG_ZF_RAW_LOC:
    case X86State::RFLAG_SF_RAW_LOC:
    case X86State::RFLAG_OF_RAW_LOC:
    case X86State::RFLAG_DF_RAW_LOC:
      // Intentionally do nothing.
      // These contain multiple bits which can corrupt other members when compacted.
      break;
    default: EFLAGS |= uint32_t {Frame->State.flags[i]} << i; break;
    }
  }

  uint32_t Packed_NZCV {};
  if (WasInJIT) {
    // If we were in the JIT then NZCV is in the CPU's PSTATE object.
    // Packed in to the same bit locations as RFLAG_NZCV_LOC.
    Packed_NZCV = PSTATE;

    // If we were in the JIT then PF and AF are in registers.
    // Move them to the CPUState frame now.
    Frame->State.pf_raw = HostGPRs[CPU::REG_PF.Idx()];
    Frame->State.af_raw = HostGPRs[CPU::REG_AF.Idx()];
  } else {
    // If we were not in the JIT then the NZCV state is stored in the CPUState RFLAG_NZCV_LOC.
    // SF/ZF/CF/OF are packed in a 32-bit value in RFLAG_NZCV_LOC.
    memcpy(&Packed_NZCV, &Frame->State.flags[X86State::RFLAG_NZCV_LOC], sizeof(Packed_NZCV));
  }

  uint32_t OF = (Packed_NZCV >> IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_OF_RAW_LOC)) & 1;
  uint32_t CF = (Packed_NZCV >> IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_CF_RAW_LOC)) & 1;
  uint32_t ZF = (Packed_NZCV >> IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_ZF_RAW_LOC)) & 1;
  uint32_t SF = (Packed_NZCV >> IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_SF_RAW_LOC)) & 1;

  // CF is inverted in our representation, undo the invert here.
  CF ^= 1;

  // Pack in to EFLAGS
  EFLAGS |= OF << X86State::RFLAG_OF_RAW_LOC;
  EFLAGS |= CF << X86State::RFLAG_CF_RAW_LOC;
  EFLAGS |= ZF << X86State::RFLAG_ZF_RAW_LOC;
  EFLAGS |= SF << X86State::RFLAG_SF_RAW_LOC;

  // PF calculation is deferred, calculate it now.
  // Popcount the 8-bit flag and then extract the lower bit.
  uint32_t PFByte = Frame->State.pf_raw & 0xff;
  uint32_t PF = std::popcount(PFByte ^ 1) & 1;
  EFLAGS |= PF << X86State::RFLAG_PF_RAW_LOC;

  // AF calculation is deferred, calculate it now.
  // XOR with PF byte and extract bit 4.
  uint32_t AF = ((Frame->State.af_raw ^ PFByte) & (1 << 4)) ? 1 : 0;
  EFLAGS |= AF << X86State::RFLAG_AF_RAW_LOC;

  uint8_t TFByte = Frame->State.flags[X86State::RFLAG_TF_RAW_LOC];
  EFLAGS |= (TFByte & 1) << X86State::RFLAG_TF_RAW_LOC;

  // DF is pretransformed, undo the transform from 1/-1 back to 0/1
  uint8_t DFByte = Frame->State.flags[X86State::RFLAG_DF_RAW_LOC];
  if (DFByte & 0x80) {
    EFLAGS |= 1 << X86State::RFLAG_DF_RAW_LOC;
  }

  return EFLAGS;
}

void ContextImpl::ReconstructXMMRegisters(const FEXCore::Core::InternalThreadState* Thread, __uint128_t* XMM_Low, __uint128_t* YMM_High) {
  const size_t MaximumRegisters = Config.Is64BitMode ? FEXCore::Core::CPUState::NUM_XMMS : 8;

  if (YMM_High != nullptr && HostFeatures.SupportsAVX) {
    const bool SupportsConvergedRegisters = HostFeatures.SupportsSVE256;

    if (SupportsConvergedRegisters) {
      ///< Output wants to de-interleave
      for (size_t i = 0; i < MaximumRegisters; ++i) {
        memcpy(&XMM_Low[i], &Thread->CurrentFrame->State.xmm.avx.data[i][0], sizeof(__uint128_t));
        memcpy(&YMM_High[i], &Thread->CurrentFrame->State.xmm.avx.data[i][2], sizeof(__uint128_t));
      }
    } else {
      ///< Matches what FEX wants with non-converged registers
      for (size_t i = 0; i < MaximumRegisters; ++i) {
        memcpy(&XMM_Low[i], &Thread->CurrentFrame->State.xmm.sse.data[i][0], sizeof(__uint128_t));
        memcpy(&YMM_High[i], &Thread->CurrentFrame->State.avx_high[i][0], sizeof(__uint128_t));
      }
    }
  } else {
    // Only support SSE, no AVX here, even if requested.
    memcpy(XMM_Low, Thread->CurrentFrame->State.xmm.sse.data, MaximumRegisters * sizeof(__uint128_t));
  }
}

void ContextImpl::SetXMMRegistersFromState(FEXCore::Core::InternalThreadState* Thread, const __uint128_t* XMM_Low, const __uint128_t* YMM_High) {
  const size_t MaximumRegisters = Config.Is64BitMode ? FEXCore::Core::CPUState::NUM_XMMS : 8;
  if (YMM_High != nullptr && HostFeatures.SupportsAVX) {
    const bool SupportsConvergedRegisters = HostFeatures.SupportsSVE256;

    if (SupportsConvergedRegisters) {
      ///< Output wants to de-interleave
      for (size_t i = 0; i < MaximumRegisters; ++i) {
        memcpy(&Thread->CurrentFrame->State.xmm.avx.data[i][0], &XMM_Low[i], sizeof(__uint128_t));
        memcpy(&Thread->CurrentFrame->State.xmm.avx.data[i][2], &YMM_High[i], sizeof(__uint128_t));
      }
    } else {
      ///< Matches what FEX wants with non-converged registers
      for (size_t i = 0; i < MaximumRegisters; ++i) {
        memcpy(&Thread->CurrentFrame->State.xmm.sse.data[i][0], &XMM_Low[i], sizeof(__uint128_t));
        memcpy(&Thread->CurrentFrame->State.avx_high[i][0], &YMM_High[i], sizeof(__uint128_t));
      }
    }
  } else {
    // Only support SSE, no AVX here, even if requested.
    memcpy(Thread->CurrentFrame->State.xmm.sse.data, XMM_Low, MaximumRegisters * sizeof(__uint128_t));
  }
}

void ContextImpl::SetFlagsFromCompactedEFLAGS(FEXCore::Core::InternalThreadState* Thread, uint32_t EFLAGS) {
  const auto Frame = Thread->CurrentFrame;
  for (size_t i = 0; i < FEXCore::Core::CPUState::NUM_EFLAG_BITS; ++i) {
    switch (i) {
    case X86State::RFLAG_OF_RAW_LOC:
    case X86State::RFLAG_CF_RAW_LOC:
    case X86State::RFLAG_ZF_RAW_LOC:
    case X86State::RFLAG_SF_RAW_LOC:
      // Intentionally do nothing.
      break;
    case X86State::RFLAG_AF_RAW_LOC:
      // AF stored in bit 4 in our internal representation. It is also
      // XORed with byte 4 of the PF byte, but we write that as zero here so
      // we don't need any special handling for that.
      Frame->State.af_raw = (EFLAGS & (1U << i)) ? (1 << 4) : 0;
      break;
    case X86State::RFLAG_PF_RAW_LOC:
      // PF is inverted in our internal representation.
      Frame->State.pf_raw = (EFLAGS & (1U << i)) ? 0 : 1;
      break;
    case X86State::RFLAG_DF_RAW_LOC:
      // DF is encoded as 1/-1
      Frame->State.flags[i] = (EFLAGS & (1U << i)) ? 0xff : 1;
      break;
    default: Frame->State.flags[i] = (EFLAGS & (1U << i)) ? 1 : 0; break;
    }
  }

  // Calculate packed NZCV. Note CF is inverted.
  uint32_t Packed_NZCV {};
  Packed_NZCV |= (EFLAGS & (1U << X86State::RFLAG_OF_RAW_LOC)) ? 1U << IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_OF_RAW_LOC) : 0;
  Packed_NZCV |= (EFLAGS & (1U << X86State::RFLAG_CF_RAW_LOC)) ? 0 : 1U << IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_CF_RAW_LOC);
  Packed_NZCV |= (EFLAGS & (1U << X86State::RFLAG_ZF_RAW_LOC)) ? 1U << IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_ZF_RAW_LOC) : 0;
  Packed_NZCV |= (EFLAGS & (1U << X86State::RFLAG_SF_RAW_LOC)) ? 1U << IR::OpDispatchBuilder::IndexNZCV(X86State::RFLAG_SF_RAW_LOC) : 0;
  memcpy(&Frame->State.flags[X86State::RFLAG_NZCV_LOC], &Packed_NZCV, sizeof(Packed_NZCV));

  // Reserved, Read-As-1, Write-as-1
  Frame->State.flags[X86State::RFLAG_RESERVED_LOC] = 1;
  // Interrupt Flag. Can't be written by CPL-3 userland.
  Frame->State.flags[X86State::RFLAG_IF_LOC] = 1;
}

bool ContextImpl::InitCore() {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("InitCore: enter\n");
#endif
  // Initialize the CPU core signal handlers & DispatcherConfig
  Dispatcher = FEXCore::CPU::Dispatcher::Create(this);
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("InitCore: after Dispatcher::Create\n");
#endif

  // Set up the SignalDelegator config since core is initialized.
  SignalDelegation->SetConfig(Dispatcher->MakeSignalDelegatorConfig());
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("InitCore: after SetConfig\n");
#endif

#if defined(_WIN32) && !defined(ARCHITECTURE_arm64ec)
  // WOW64 always needs the interrupt fault check to be enabled.
  Config.NeedsPendingInterruptFaultCheck = true;
#endif

  if (Config.GdbServer) {
    // If gdbserver is enabled then this needs to be enabled.
    Config.NeedsPendingInterruptFaultCheck = true;
  }

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("InitCore: done\n");
#endif
  return true;
}

void ContextImpl::HandleCallback(FEXCore::Core::InternalThreadState* Thread, uint64_t RIP) {
  static_cast<ContextImpl*>(Thread->CTX)->Dispatcher->ExecuteJITCallback(Thread->CurrentFrame, RIP);
}

void ContextImpl::ExecuteThread(FEXCore::Core::InternalThreadState* Thread) {
  // Update the thread pointer for Thunk return to the latest.
  Thread->CurrentFrame->Pointers.ThunkCallbackRet = SignalDelegation->GetThunkCallbackRET();

  Dispatcher->ExecuteDispatch(Thread->CurrentFrame);

  // If it is the parent thread that died then just leave
  // TODO: This doesn't make sense when the parent thread doesn't outlive its children
}

void ContextImpl::InitializeCompiler(FEXCore::Core::InternalThreadState* Thread) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  auto WineAppleL1Only = [&]() {
    FEXCtorLog("InitializeCompiler: L1 host alloc\n");
    constexpr size_t L1Entries = 8 * 1024;
    constexpr size_t EntrySize = 16;
    constexpr size_t L1Bytes = L1Entries * EntrySize;
    void* L1 = FEXCore::Allocator::VirtualAlloc(L1Bytes, false, true);
    if (L1) {
      volatile unsigned char* B = static_cast<volatile unsigned char*>(L1);
      for (size_t I = 0; I < L1Bytes; ++I) {
        B[I] = 0;
      }
      Thread->CurrentFrame->State.L1Pointer = reinterpret_cast<uint64_t>(L1);
      Thread->CurrentFrame->State.L1Mask = static_cast<uint64_t>(L1Entries - 1) * EntrySize;
      FEXCtorLog("InitializeCompiler: L1 OK\n");
    } else {
      FEXCtorLog("InitializeCompiler: L1 alloc FAILED\n");
    }
    if (Dispatcher) {
      Dispatcher->InitThreadPointers(Thread);
    }
  };

  FEXCtorLog("InitializeCompiler: Hangover begin\n");
  Thread->OpDispatcher = fextl::make_unique<FEXCore::IR::OpDispatchBuilder>(this);
  FEXCtorLog("InitializeCompiler: OpDispatcher\n");
  // Single-insn blocks: LoopTop NULL-map peek must see every RIP (no ARM64 in a block).
  Thread->OpDispatcher->SetMultiblock(false);

  Thread->LookupCache = fextl::make_unique<FEXCore::LookupCache>(this);
  FEXCtorLog("InitializeCompiler: LookupCache\n");
  if (!Thread->LookupCache || !Thread->LookupCache->GetL1Pointer()) {
    FEXCtorLog("InitializeCompiler: LookupCache FAIL, L1 fallback\n");
    WineAppleL1Only();
    return;
  }

  Thread->FrontendDecoder = fextl::make_unique<FEXCore::Frontend::Decoder>(Thread);
  FEXCtorLog("InitializeCompiler: Decoder\n");
  Thread->PassManager = fextl::make_unique<FEXCore::IR::PassManager>();
  FEXCtorLog("InitializeCompiler: PassManager\n");

  Thread->CurrentFrame->State.L1Pointer = Thread->LookupCache->GetL1Pointer();
  Thread->CurrentFrame->State.L1Mask = Thread->LookupCache->GetScaledL1PointerMask();
  Thread->CurrentFrame->Pointers.L2Pointer = Thread->LookupCache->GetPagePointer();

  if (Dispatcher) {
    Dispatcher->InitThreadPointers(Thread);
  }

  Thread->PassManager->AddDefaultPasses(this);
  Thread->PassManager->AddDefaultValidationPasses();
  Thread->PassManager->RegisterSyscallHandler(SyscallHandler);
  Thread->PassManager->InsertRegisterAllocationPass(this);
  FEXCtorLog("InitializeCompiler: before Arm64JITCore\n");
  Thread->CPUBackend = FEXCore::CPU::CreateArm64JITCore(this, Thread);
  if (!Thread->CPUBackend) {
    FEXCtorLog("InitializeCompiler: Arm64JITCore FAIL, L1 fallback\n");
    WineAppleL1Only();
    return;
  }
  Thread->PassManager->Finalize();
  FEXCtorLog("InitializeCompiler: Arm64JITCore\n");
  return;
#else
  Thread->OpDispatcher = fextl::make_unique<FEXCore::IR::OpDispatchBuilder>(this);
  Thread->OpDispatcher->SetMultiblock(Config.Multiblock);
  Thread->LookupCache = fextl::make_unique<FEXCore::LookupCache>(this);
  Thread->FrontendDecoder = fextl::make_unique<FEXCore::Frontend::Decoder>(Thread);
  Thread->PassManager = fextl::make_unique<FEXCore::IR::PassManager>();

  Thread->CurrentFrame->State.L1Pointer = Thread->LookupCache->GetL1Pointer();
  Thread->CurrentFrame->State.L1Mask = Thread->LookupCache->GetScaledL1PointerMask();

  Thread->CurrentFrame->Pointers.L2Pointer = Thread->LookupCache->GetPagePointer();

  Dispatcher->InitThreadPointers(Thread);

  Thread->PassManager->AddDefaultPasses(this);
  Thread->PassManager->AddDefaultValidationPasses();

  Thread->PassManager->RegisterSyscallHandler(SyscallHandler);

  // Create CPU backend
  Thread->PassManager->InsertRegisterAllocationPass(this);
  Thread->CPUBackend = FEXCore::CPU::CreateArm64JITCore(this, Thread);

  Thread->PassManager->Finalize();
#endif
}

FEXCore::Core::InternalThreadState*
ContextImpl::CreateThread(uint64_t InitialRIP, uint64_t StackPointer, const FEXCore::Core::CPUState* NewThreadState) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("CreateThread: enter\n");
  // No C++ ctor: large InternalThreadState construction uses #memset (exit-thunk).
  // Hand-zero host-bump memory and poke const CurrentFrame/CTX fields.
  const size_t Sz = sizeof(FEXCore::Core::InternalThreadState);
  const size_t Al = alignof(FEXCore::Core::InternalThreadState);
  void* Mem = FEXCore::Allocator::aligned_alloc(Al, Sz);
  if (!Mem) {
    FEXCtorLog("CreateThread: alloc FAILED\n");
    return nullptr;
  }
  FEXCtorLog("CreateThread: after alloc\n");
  {
    // volatile: prevent libcall to #memset (ARM64EC exit-thunk before JIT).
    volatile unsigned char* B = static_cast<volatile unsigned char*>(Mem);
    for (size_t I = 0; I < Sz; ++I) {
      B[I] = 0;
    }
  }
  FEXCtorLog("CreateThread: after zero\n");
  auto* Thread = static_cast<FEXCore::Core::InternalThreadState*>(Mem);
  {
    FEXCore::Core::CpuStateFrame* Frame = &Thread->BaseFrameState;
    // Standard-layout: overwrite const pointer members without running ctor.
    *reinterpret_cast<FEXCore::Core::CpuStateFrame**>(reinterpret_cast<char*>(Thread) +
                                                      offsetof(FEXCore::Core::InternalThreadState, CurrentFrame)) = Frame;
    *reinterpret_cast<FEXCore::Context::Context**>(reinterpret_cast<char*>(Thread) +
                                                   offsetof(FEXCore::Core::InternalThreadState, CTX)) = this;
  }
  FEXCtorLog("CreateThread: after field poke\n");
#else
  FEXCore::Core::InternalThreadState* Thread = new FEXCore::Core::InternalThreadState {
    .CTX = this,
  };
#endif
  FEXCore::Allocator::VirtualName("FEXMem_ThreadState", Thread, sizeof(*Thread));

  Thread->CurrentFrame->State.gregs[X86State::REG_RSP] = StackPointer;
  Thread->CurrentFrame->State.rip = InitialRIP;

  // Copy over the new thread state to the new object
  if (NewThreadState) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    auto* D = reinterpret_cast<unsigned char*>(&Thread->CurrentFrame->State);
    const auto* S = reinterpret_cast<const unsigned char*>(NewThreadState);
    for (size_t I = 0; I < sizeof(FEXCore::Core::CPUState); ++I) {
      D[I] = S[I];
    }
#else
    memcpy(&Thread->CurrentFrame->State, NewThreadState, sizeof(FEXCore::Core::CPUState));
#endif
  }

  // Set up the thread manager state
  Thread->CurrentFrame->Thread = Thread;

  InitializeCompiler(Thread);
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("CreateThread: after InitializeCompiler\n");
#endif

  Thread->CurrentFrame->State.DeferredSignalRefCount.Store(0);

#if !(defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE)
  if (Config.BlockJITNaming() || Config.GlobalJITNaming() || Config.LibraryJITNaming()) {
    // Allocate a JIT symbol buffer only if enabled.
    Thread->SymbolBuffer = JITSymbols::AllocateBuffer();
  }
#endif

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCtorLog("CreateThread: done\n");
#endif
  return Thread;
}

void ContextImpl::DestroyThread(FEXCore::Core::InternalThreadState* Thread) {
  FEXCore::Allocator::VirtualProtect(&Thread->InterruptFaultPage, sizeof(Thread->InterruptFaultPage),
                                     Allocator::ProtectOptions::Read | Allocator::ProtectOptions::Write);
  delete Thread;
}

#ifndef _WIN32
void ContextImpl::UnlockAfterFork(FEXCore::Core::InternalThreadState* LiveThread, bool Child) {
  Allocator::UnlockAfterFork(LiveThread, Child);

  Profiler::PostForkAction(Child);
  if (Child) {
    if (CodeMapWriter) {
      CodeMapWriter->ResetAfterFork();
    }

    CodeInvalidationMutex.StealAndDropActiveLocks();
    if (Config.StrictInProcessSplitLocks) {
      StrictSplitLockMutex = 0;
    }
  } else {
    CodeInvalidationMutex.unlock();
    if (Config.StrictInProcessSplitLocks) {
      FEXCore::Utils::SpinWaitLock::unlock(&StrictSplitLockMutex);
    }
    return;
  }
}

void ContextImpl::LockBeforeFork(FEXCore::Core::InternalThreadState* Thread) {
  CodeInvalidationMutex.lock();
  Allocator::LockBeforeFork(Thread);
  if (Config.StrictInProcessSplitLocks) {
    FEXCore::Utils::SpinWaitLock::lock(&StrictSplitLockMutex);
  }
}
#endif

void ContextImpl::OnCodeBufferAllocated(const fextl::shared_ptr<CPU::CodeBuffer>& Buffer) {
  if (Config.GlobalJITNaming()) {
    Symbols.RegisterJITSpace(Buffer->Ptr, Buffer->AllocatedSize);
  }

  {
    std::scoped_lock lk {CodeBufferListLock};
    CodeBufferList.emplace_back(Buffer);
  }
}

void ContextImpl::ClearCodeCache(FEXCore::Core::InternalThreadState* Thread, bool NewCodeBuffer) {
  FEXCORE_PROFILE_INSTANT("ClearCodeCache");

  if (NewCodeBuffer) {
    // Allocate new CodeBuffer + L3 LookupCache and clear L1+L2 caches
    Thread->CPUBackend->ClearCache();
  } else {
    // Clear L1+L2 cache of this thread, and clear L3 cache across any threads using it
    auto lk = Thread->LookupCache->AcquireWriteLock();
    Thread->LookupCache->ClearCache(lk);
  }
  Allocator::VirtualDontNeed(Thread->CallRetStackBase, FEXCore::Core::InternalThreadState::CALLRET_STACK_SIZE);
}

static void IRDumper(FEXCore::Core::InternalThreadState* Thread, IR::IREmitter* IREmitter, uint64_t GuestRIP) {
  FEXCore::File::File FD = FEXCore::File::File::GetStdERR();
  fextl::stringstream out;
  auto NewIR = IREmitter->ViewIR();
  FEXCore::IR::Dump(&out, &NewIR);
  fextl::fmt::print(FD, "IR-ShouldDump-{} 0x{:x}:\n{}\n@@@@@\n", NewIR.PostRA() ? "post" : "pre", GuestRIP, out.str());
};

bool ContextImpl::CheckIfBlockIsCacheable(FEXCore::Core::InternalThreadState& Thread, uint64_t GuestRIP, uint64_t MaxInst) {
  return Thread.FrontendDecoder->CheckIfCacheable(Thread, reinterpret_cast<const uint8_t*>(GuestRIP), GuestRIP, MaxInst);
}

ContextImpl::GenerateIRResult
ContextImpl::GenerateIR(FEXCore::Core::InternalThreadState* Thread, uint64_t GuestRIP, bool ExtendedDebugInfo, uint64_t MaxInst) {
#if !(defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE)
  FEXCORE_PROFILE_SCOPED("GenerateIR");
#endif

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCore::Allocator::CtorLog("IR: ResetWorkingList\n");
#endif
  Thread->OpDispatcher->ResetWorkingList();
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCore::Allocator::CtorLog("IR: after Reset\n");
#endif

  uint64_t TotalInstructions {0};
  uint64_t TotalInstructionsLength {0};

  bool HasCustomIR {};

#if !(defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE)
  if (HasCustomIRHandlers.load(std::memory_order_relaxed)) {
    std::shared_lock lk(CustomIRMutex);
    auto Handler = CustomIRHandlers.find(GuestRIP);
    if (Handler != CustomIRHandlers.end()) {
      TotalInstructions = 1;
      TotalInstructionsLength = 1;
      Handler->second.Handler(GuestRIP, Thread->OpDispatcher.get());
      HasCustomIR = true;
    }
  }
#endif

  if (!HasCustomIR) {
    const uint8_t* GuestCode {};
    GuestCode = reinterpret_cast<const uint8_t*>(GuestRIP);

    bool HadDispatchError {false};
    bool HadInvalidInst {false};

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    FEXCore::Allocator::CtorLog("IR: Decode\n");
#endif
    Thread->FrontendDecoder->DecodeInstructionsAtEntry(Thread, GuestCode, GuestRIP, MaxInst);
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    FEXCore::Allocator::CtorLog("IR: after Decode\n");
#endif

    auto BlockInfo = Thread->FrontendDecoder->GetDecodedBlockInfo();
    auto CodeBlocks = &BlockInfo->Blocks;

    Thread->OpDispatcher->BeginFunction(GuestRIP, CodeBlocks, BlockInfo->TotalInstructionCount, BlockInfo->Is64BitMode,
                                        AreMonoHacksActive() && MonoBackpatcherBlock.load(std::memory_order_relaxed) == GuestRIP);
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    FEXCore::Allocator::CtorLog("IR: after BeginFunction\n");
#endif

    const auto GPRSize = Thread->OpDispatcher->GetGPROpSize();

#ifdef ZYDIS_DISASSEMBLER
    const auto ZydisMachineMode = Config.Is64BitMode ? ZYDIS_MACHINE_MODE_LONG_64 : ZYDIS_MACHINE_MODE_LEGACY_32;
    if (FEXCore::Config::Get_X86DISASSEMBLE()) {
      const uint64_t DecodedMin = Thread->FrontendDecoder->DecodedMinAddress;
      const uint64_t DecodedMax = Thread->FrontendDecoder->DecodedMaxAddress;
      LogMan::Msg::IFmt("Guest x86 Begin (RIP={:#x}, {:#x}-{:#x})", GuestRIP, DecodedMin, DecodedMax);
    }
#endif

    for (size_t j = 0; j < CodeBlocks->size(); ++j) {
      const FEXCore::Frontend::Decoder::DecodedBlocks& Block = CodeBlocks->at(j);

#ifdef ZYDIS_DISASSEMBLER
      if (FEXCore::Config::Get_X86DISASSEMBLE() && CodeBlocks->size() > 1) {
        LogMan::Msg::IFmt("  Block {} Entry={:#x} NumInsts={}", j, Block.Entry, Block.NumInstructions);
      }
#endif

      bool BlockInForceTSOValidRange = false;
      auto InstForceTSOIt = ForceTSOInstructions.end();
#if !(defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE)
      if (ForceTSOValidRanges.Contains({Block.Entry, Block.Entry + Block.Size})) {
        if (auto It = ForceTSOInstructions.lower_bound(Block.Entry); *It < Block.Entry + Block.Size) {
          InstForceTSOIt = It;
          BlockInForceTSOValidRange = true;
        }
      }
#endif

      // Set the block entry point
      Thread->OpDispatcher->SetNewBlockIfChanged(Block.Entry);

      uint64_t BlockInstructionsLength {};

      // Reset any block-specific state
      Thread->OpDispatcher->StartNewBlock();

      uint64_t InstsInBlock = Block.NumInstructions;

      if (InstsInBlock == 0) {
        // Special case for an empty instruction block.
        Thread->OpDispatcher->ExitFunction(Thread->OpDispatcher->_InlineEntrypointOffset(GPRSize, Block.Entry - GuestRIP));
      }

      for (size_t i = 0; i < InstsInBlock; ++i) {
        uint64_t InstAddress = Block.Entry + BlockInstructionsLength;
        const FEXCore::X86Tables::X86InstInfo* TableInfo {nullptr};
        const FEXCore::X86Tables::DecodedInst* DecodedInfo {nullptr};

        TableInfo = Block.DecodedInstructions[i].TableInfo;
        DecodedInfo = &Block.DecodedInstructions[i];

#ifdef ZYDIS_DISASSEMBLER
        if (FEXCore::Config::Get_X86DISASSEMBLE()) {
          const uint8_t* InstBytes = reinterpret_cast<const uint8_t*>(InstAddress);
          ZydisDisassembledInstruction ZydisInst;
          if (ZYAN_SUCCESS(ZydisDisassembleIntel(ZydisMachineMode, InstAddress, InstBytes, DecodedInfo->InstSize, &ZydisInst))) {
            LogMan::Msg::IFmt("    {:#x}: {}", InstAddress, ZydisInst.text);
          } else {
            LogMan::Msg::IFmt("    {:#x}: (decode failed, {} bytes)", InstAddress, DecodedInfo->InstSize);
          }
        }
#endif

        bool IsLocked = DecodedInfo->Flags & FEXCore::X86Tables::DecodeFlags::FLAG_LOCK;

        // Do a partial register cache flush before every instruction. This
        // prevents cross-instruction static register caching, while allowing
        // context load/stores to be optimized within a block. Theoretically,
        // this flush is not required for correctness, all mandatory flushes are
        // included in instruction-specific handlers. Instead, this is a blunt
        // heuristic to make the register cache less aggressive, as the current
        // RA generates bad code in common cases with tied registers otherwise.
        //
        // However, it makes our exception handling behaviour more predictable.
        // It is potentially correctness bearing in that sense, but that is a
        // side effect here and (if that behaviour is required) we should handle
        // that more explicitly later.
        Thread->OpDispatcher->FlushRegisterCache(true);

#if !(defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE)
        if (ExtendedDebugInfo || Thread->OpDispatcher->CanHaveSideEffects(TableInfo, DecodedInfo)) {
          Thread->OpDispatcher->_GuestOpcode(InstAddress - GuestRIP);
        }

        if (Config.SMCChecks == FEXCore::Config::CONFIG_SMC_FULL || Block.ForceFullSMCDetection) {
          auto ExistingCodePtr = reinterpret_cast<uint8_t*>(Block.Entry + BlockInstructionsLength);
          auto InstAddressReg = Thread->OpDispatcher->_EntrypointOffset(GPRSize, InstAddress - GuestRIP);
          std::array<uint8_t, 0x10> CodeOriginal;
          memcpy(CodeOriginal.data(), ExistingCodePtr, DecodedInfo->InstSize);
          auto CodeChanged = Thread->OpDispatcher->_ValidateCode(CodeOriginal, InstAddressReg, DecodedInfo->InstSize);

          auto InvalidateCodeCond = Thread->OpDispatcher->CondJump(CodeChanged);

          auto CurrentBlock = Thread->OpDispatcher->GetCurrentBlock();
          auto CodeWasChangedBlock = Thread->OpDispatcher->CreateNewCodeBlockAtEnd();
          Thread->OpDispatcher->SetTrueJumpTarget(InvalidateCodeCond, CodeWasChangedBlock);

          Thread->OpDispatcher->SetCurrentCodeBlock(CodeWasChangedBlock);
          Thread->OpDispatcher->_ThreadRemoveCodeEntry();
          Thread->OpDispatcher->ExitFunction(Thread->OpDispatcher->_InlineEntrypointOffset(GPRSize, InstAddress - GuestRIP));

          auto NextOpBlock = Thread->OpDispatcher->CreateNewCodeBlockAfter(CurrentBlock);

          Thread->OpDispatcher->SetFalseJumpTarget(InvalidateCodeCond, NextOpBlock);
          Thread->OpDispatcher->SetCurrentCodeBlock(NextOpBlock);
        }
#endif

        if (TableInfo && TableInfo->OpcodeDispatcher.OpDispatch) {
          auto Fn = TableInfo->OpcodeDispatcher.OpDispatch;
          Thread->OpDispatcher->ResetHandledLock();
          Thread->OpDispatcher->ResetDecodeFailure();
          IR::ForceTSOMode ForceTSO = IR::ForceTSOMode::NoOverride;
          if (BlockInForceTSOValidRange) {
            if (InstForceTSOIt != ForceTSOInstructions.end() && *InstForceTSOIt == InstAddress) {
              ForceTSO = IR::ForceTSOMode::ForceEnabled;
            } else {
              ForceTSO = IR::ForceTSOMode::ForceDisabled;
            }
          } else if (DecodedInfo->Flags & X86Tables::DecodeFlags::FLAG_FORCE_TSO) {
            ForceTSO = IR::ForceTSOMode::ForceEnabled;
          }

          Thread->OpDispatcher->SetForceTSO(ForceTSO);
          std::invoke(Fn, Thread->OpDispatcher, DecodedInfo);
          if (Thread->OpDispatcher->HadDecodeFailure()) {
            HadDispatchError = true;
          } else {
            if (Thread->OpDispatcher->HasHandledLock() != IsLocked) {
              HadDispatchError = true;
              LogMan::Msg::EFmt("Missing LOCK HANDLER at 0x{:x}{{'{}'}}", InstAddress, TableInfo->Name ?: "UND");
            }
            BlockInstructionsLength += DecodedInfo->InstSize;
            TotalInstructionsLength += DecodedInfo->InstSize;
            ++TotalInstructions;

            // Walk InstForceTSOIt forward past the handled instruction
            InstForceTSOIt =
              std::find_if(InstForceTSOIt, ForceTSOInstructions.end(), [&](auto Val) { return Val >= Block.Entry + BlockInstructionsLength; });
          }
        } else {
          // Invalid instruction
          if (!BlockInstructionsLength) {
            // SMC can modify block contents and patch invalid instructions to valid ones inline.
            // End blocks upon encountering them and only emit an invalid opcode exception if there are no prior instructions in the block (that could have modified it to be valid).

            if (TableInfo) {
              LogMan::Msg::EFmt("Invalid or Unknown instruction: {} 0x{:x}", TableInfo->Name ?: "UND", Block.Entry - GuestRIP);
            }

            if (Block.BlockStatus == Frontend::Decoder::DecodedBlockStatus::INVALID_INST ||
                Block.BlockStatus == Frontend::Decoder::DecodedBlockStatus::BAD_RELOCATION) {
              Thread->OpDispatcher->InvalidOp(DecodedInfo);
            } else {
              Thread->OpDispatcher->NoExecOp(DecodedInfo);
            }
          }

          HadInvalidInst = true;
        }

        const bool NeedsBlockEnd = (HadDispatchError && TotalInstructions > 0) ||
                                   (Thread->OpDispatcher->NeedsBlockEnder() && i + 1 == InstsInBlock) || HadInvalidInst;

        // If we had a dispatch error then leave early
        if (HadDispatchError && TotalInstructions == 0) {
          // Couldn't handle any instruction in op dispatcher
          Thread->OpDispatcher->DelayedDisownBuffer();
          return {std::nullopt, 0, 0, 0, 0};
        }

        if (NeedsBlockEnd) {
          // We had some instructions. Early exit
          Thread->OpDispatcher->ExitFunction(
            Thread->OpDispatcher->_InlineEntrypointOffset(GPRSize, Block.Entry + BlockInstructionsLength - GuestRIP));
          break;
        }


        if (Thread->OpDispatcher->FinishOp(DecodedInfo->PC + DecodedInfo->InstSize, i + 1 == InstsInBlock)) {
          break;
        }
      }
    }

#ifdef ZYDIS_DISASSEMBLER
    if (FEXCore::Config::Get_X86DISASSEMBLE()) {
      LogMan::Msg::IFmt("Guest x86 End");
    }
#endif

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    FEXCore::Allocator::CtorLog("IR: Finalize\n");
#endif
    Thread->OpDispatcher->Finalize();
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    FEXCore::Allocator::CtorLog("IR: after Finalize\n");
#endif

    Thread->FrontendDecoder->DelayedDisownBuffer();
  }

  IR::IREmitter* IREmitter = Thread->OpDispatcher.get();

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  FEXCore::Allocator::CtorLog("IR: RA\n");
  if (auto* RA = Thread->PassManager->GetRAPass()) {
    RA->Run(IREmitter);
  }
  FEXCore::Allocator::CtorLog("IR: after RA\n");
#else
  auto ShouldDump = Thread->OpDispatcher->ShouldDumpIR();
  // Debug
  if (ShouldDump) {
    IRDumper(Thread, IREmitter, GuestRIP);
  }

  // Run the passmanager over the IR from the dispatcher
  Thread->PassManager->Run(IREmitter);

  // Debug
  if (ShouldDump) {
    IRDumper(Thread, IREmitter, GuestRIP);
  }
#endif

  return {
    .IRView = IREmitter->ViewIR(),
    .TotalInstructions = TotalInstructions,
    .TotalInstructionsLength = TotalInstructionsLength,
    .StartAddr = Thread->FrontendDecoder->DecodedMinAddress,
    .Length = Thread->FrontendDecoder->DecodedMaxAddress - Thread->FrontendDecoder->DecodedMinAddress,
    .NeedsAddGuestCodeRanges = !HasCustomIR,
  };
}

ContextImpl::CompileCodeResult ContextImpl::CompileCode(FEXCore::Core::InternalThreadState* Thread, uint64_t GuestRIP, uint64_t MaxInst) {
  if (SourcecodeResolver && Config.GDBSymbols()) {
    auto MappedSection = SyscallHandler->LookupExecutableFileSection(Thread, GuestRIP);
    if (MappedSection) {
      MappedSection->FileInfo.SourcecodeMap =
        SourcecodeResolver->GenerateMap(MappedSection->FileInfo.Filename, CodeMap::GetBaseFilename(MappedSection->FileInfo, false));
    }
  }

  // Generate IR + Meta Info
  auto [IRView, TotalInstructions, TotalInstructionsLength, StartAddr, Length, NeedsAddGuestCodeRanges] =
    GenerateIR(Thread, GuestRIP, Config.GDBSymbols(), MaxInst);
  if (!IRView) {
    // OpDispatcher IR already released in this case.
    return {{}, nullptr, 0, 0, false};
  }

  // Attempt to get the CPU backend to compile this code
  // Re-check if another thread raced us in compiling this block.
  // We could lock CodeBufferWriteMutex earlier to prevent this from happening,
  // but this would increase lock contention. Redundant frontend runs aren't
  // as expensive and are easily reverted.
  if (MaxInst != 1) {
    if (auto Block = Thread->LookupCache->FindBlock(Thread, GuestRIP)) {
      // Raced to compile, release the OpDispatcher IR.
      Thread->OpDispatcher->DelayedDisownBuffer();
      return {.CompiledCode = {.BlockBegin = reinterpret_cast<uint8_t*>(Block), .EntryPoints = {{GuestRIP, reinterpret_cast<uint8_t*>(Block)}}},
              .DebugData = nullptr,
              .StartAddr = 0,
              .Length = 0,
              .NeedsAddGuestCodeRanges = false};
    }
  }

  auto DebugData = fextl::make_unique<FEXCore::Core::DebugData>();

  // If the trap flag is set we generate single instruction blocks that each check to generate a single step exception.
  bool TFSet = Thread->CurrentFrame->State.flags[X86State::RFLAG_TF_RAW_LOC];

  auto CompiledCode = Thread->CPUBackend->CompileCode(GuestRIP, Length, TotalInstructions == 1, &*IRView, DebugData.get(), TFSet);

  // Release the IR
  Thread->OpDispatcher->DelayedDisownBuffer();

  return {
    .CompiledCode = std::move(CompiledCode),
    .DebugData = std::move(DebugData),
    .StartAddr = StartAddr,
    .Length = Length,
    .NeedsAddGuestCodeRanges = NeedsAddGuestCodeRanges,
  };
}

uintptr_t ContextImpl::CompileBlock(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP, uint64_t MaxInst) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  auto RetWA = [Frame](uintptr_t P) -> uintptr_t {
    if (Frame) {
      Frame->WineAppleCodePtr = P;
    }
    return P;
  };
  FEXCore::Allocator::CtorLog("CB: pre\n");
  if (GuestRIP == 0x1400013fcull) {
    FEXCore::Allocator::CtorLog("CB: rip 13fc\n");
  }
  if (GuestRIP == 0x1400013ffull) {
    FEXCore::Allocator::CtorLog("CB: rip 13ff\n");
  }
  if (!Frame) {
    FEXCore::Allocator::CtorLog("CB: no Frame\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  // s124: before low-RIP WineAppleHost fallback (GuestRIP < 0x10000 ldrb@0)
  // and before other CompileOneInsn low-RIP exits.
  if (WineAppleSkipRip0(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s124 skip rip0\n");
      return RetWA(Dlt);
    }
  }
  // s144: same CompileBlock site as SkipRip0 (before WineAppleHost low-RIP)
  if (WineAppleSkipRip1387(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s144 skip 1387\n");
      return RetWA(Dlt);
    }
  }
  // s146: same CompileBlock site as SkipRip0 / SkipRip1387
  if (WineAppleSkipRip1376(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s146 skip 1376\n");
      return RetWA(Dlt);
    }
  }
  // s147: same CompileBlock site as SkipRip0 / SkipRip1387 / SkipRip1376
  if (WineAppleSkipRip137e(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s147 skip 137e\n");
      return RetWA(Dlt);
    }
  }
  if (!Frame->Thread) {
    FEXCore::Allocator::CtorLog("CB: no Thread\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  if (!Frame->Thread->CPUBackend) {
    FEXCore::Allocator::CtorLog("CB: no Backend\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  if (!Frame->Thread->LookupCache) {
    FEXCore::Allocator::CtorLog("CB: no Cache\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  if (GuestRIP < 0x10000ull) {
    FEXCore::Allocator::CtorLog("CB: low RIP\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  {
    const uintptr_t Teb = Frame->State.gs_cached;
    if (Teb >= (1ull << 40) && Teb < 0x800000000000ull) {
      __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Teb) : "x18", "memory");
    } else {
      FEXCore::Allocator::CtorLog("CB: bad TEB\n");
      return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
    }
  }
  // Skip PROFILE/mutex/PreCompile/EntryPoints map — all ARM64EC exit-thunks
  // (exp-jit1s13 c000001d in CompileBlock C++).
  auto* Thread = Frame->Thread;
  WineAppleFixCallRetSlot(Frame, GuestRIP);
  WineAppleFixArgc(Frame, GuestRIP);
  WineAppleFixChkstkRax(Frame, GuestRIP);
  WineAppleFixDelayThunk(Frame, GuestRIP);
  WineAppleFix1601Rsp(Frame, GuestRIP);
  if (WineAppleSkipDelayLoad(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s113 skip Ldr\n");
      return RetWA(Dlt);
    }
  }
  if (WineAppleSkip13bbStackTos(Frame, GuestRIP)) {
    const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
    if (Dlt) {
      FEXCore::Allocator::CtorLog("CB: s122 skip 13bb\n");
      return RetWA(Dlt);
    }
  }
  WineAppleLogS85(Frame, GuestRIP);
  WineAppleLogS99(Frame, GuestRIP);
  WineAppleLogS100(Frame, GuestRIP);
  WineAppleLogS102(Frame, GuestRIP);
  if (WineAppleS73RIP(GuestRIP)) {
    WineAppleLogSlot('e', Frame, GuestRIP);
  }
  FEXCore::Allocator::CtorLog("CB: enter\n");
  FEXCore::Allocator::CtorLog("CB: GenerateIR\n");
  // s145; s144 KEEP 349k skip-spin; 1386 41 5e pop r14; RIP-local MaxInst=2 like s89; do not global MaxInst=2.
  // s89: MaxInst=2 only at 1022 so cmp ecx,2 + jl stay in one block.
  // Global MaxInst=2 (s88) decoded ARM ucrtbase as x64.
  const uint64_t GenMaxInst =
      (GuestRIP == 0x140001022ull || GuestRIP == 0x140001386ull) ? 2ull : 1ull;
  auto IRRes = GenerateIR(Thread, GuestRIP, false, GenMaxInst);
  FEXCore::Allocator::CtorLog("CB: after GenerateIR\n");
  if (!IRRes.IRView) {
    FEXCore::Allocator::CtorLog("CB: no IR, WineApple\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  FEXCore::Allocator::CtorLog("CB: JIT CompileCode\n");
  if (GuestRIP == 0x1400013fcull) {
    if (IRRes.Length == 3) {
      FEXCore::Allocator::CtorLog("CB: 13fc len=3\n");
    } else if (IRRes.Length == 0) {
      FEXCore::Allocator::CtorLog("CB: 13fc len=0\n");
    } else {
      FEXCore::Allocator::CtorLog("CB: 13fc len!=3\n");
    }
    {
      char Line[40];
      size_t I = 0;
      const char* Pfx = "CB: 13fc dlt=";
      while (Pfx[I]) {
        Line[I] = Pfx[I];
        ++I;
      }
      const uint64_t Dlt = Frame->Pointers.DispatcherLoopTop;
      for (int B = 15; B >= 0; --B) {
        const unsigned N = static_cast<unsigned>((Dlt >> (B * 4)) & 0xf);
        Line[I++] = N < 10 ? static_cast<char>('0' + N) : static_cast<char>('a' + (N - 10));
      }
      Line[I++] = '\n';
      Line[I] = 0;
      FEXCore::Allocator::CtorLog(Line);
    }
  }
  auto CC = Thread->CPUBackend->CompileCode(GuestRIP, IRRes.Length, true, &*IRRes.IRView, nullptr, false);
  Thread->OpDispatcher->DelayedDisownBuffer();
  FEXCore::Allocator::CtorLog("CB: after JIT\n");
  auto* CodePtr = CC.BlockBegin;
  if (!CodePtr) {
    FEXCore::Allocator::CtorLog("CB: JIT empty, WineApple\n");
    return RetWA(FEX::WineApple::CompileOneInsn(Frame, GuestRIP));
  }
  if (Frame->State.L1Pointer) {
    const uint64_t Off = GuestRIP & Frame->State.L1Mask;
    auto* E = reinterpret_cast<volatile uint64_t*>(Frame->State.L1Pointer + Off);
    E[0] = reinterpret_cast<uint64_t>(CodePtr);
    E[1] = GuestRIP;
  }
  FEXCore::Allocator::CtorLog("CB: done\n");
  if (WineAppleS73RIP(GuestRIP)) {
    WineAppleLogSlot('d', Frame, GuestRIP);
  }
  // FillStaticRegs after NoBlock blr CompileBlock reloads STATE from tpidr
  // (x28 is not ARM64EC callee-saved). malloc/resize during GenerateIR/RA/
  // JumpTargets can leave Darwin tpidr residue; pin TEB again before return.
  {
    const uintptr_t Teb = Frame->State.gs_cached;
    if (Teb >= (1ull << 40) && Teb < 0x800000000000ull) {
      __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Teb) : "x18", "memory");
    }
  }
  {
    const auto* P = reinterpret_cast<const volatile uint8_t*>(GuestRIP);
    const uint8_t B0 = P[0];
    uint64_t Len = 0;
    if (B0 == 0xe8) {
      Len = 5;
    } else if (B0 == 0xff && P[1] == 0x15) {
      Len = 6;
    } else if ((B0 & 0xf0) == 0x40) {
      if (P[1] == 0xe8) {
        Len = 6;
      } else if (P[1] == 0xff && P[2] == 0x15) {
        Len = 7;
      }
    }
    if (Len) {
      Frame->State.WineAppleCallRet = GuestRIP + Len;
      WineAppleLastCallRet = GuestRIP + Len;
      FEXCore::Allocator::CtorLog("CB: callret\n");
      // s101: every CALL stash RIP (last before CA is the native IAT).
      WineAppleLogHex64("s101 e8=", GuestRIP);
      if (GuestRIP == 0x14000101aull) {
        WineAppleLogHex64("s77 crt1=", Frame->State.WineAppleCallRet);
      }
    }
  }
  // s95: CodePtr NoBlock br's after Fill. First vs second 13bb RET.
  if (GuestRIP == 0x1400013bbull) {
    WineAppleLogHex64("s95 ptr=", reinterpret_cast<uint64_t>(CodePtr));
  }
  return RetWA(reinterpret_cast<uintptr_t>(CodePtr));
#else
  auto Thread = Frame->Thread;
  FEXCORE_PROFILE_SCOPED("CompileBlock");
  FEXCORE_PROFILE_ACCUMULATION(Thread, AccumulatedJITTime);

  static_cast<ContextImpl*>(Thread->CTX)->SyscallHandler->PreCompile();

  // Invalidate might take a unique lock on this, to guarantee that during invalidation no code gets compiled
  auto lk = GuardSignalDeferringSection<std::shared_lock>(CodeInvalidationMutex, Thread);

  // Is the code in the cache?
  // The backends only check L1 and L2, not L3
  if (auto HostCode = Thread->LookupCache->FindBlock(Thread, GuestRIP)) {
    return HostCode;
  }

  // Accumulate a JIT count now, as even if another thread raced us, it should count as a compile.
  FEXCORE_PROFILE_INSTANT_INCREMENT(Thread, AccumulatedJITCount, 1);

  auto [CompiledCode, DebugData, StartAddr, Length, NeedsAddGuestCodeRanges] = CompileCode(Thread, GuestRIP, MaxInst);
  auto CodePtr = CompiledCode.EntryPoints[GuestRIP];
  if (CodePtr == nullptr) {
    return 0;
  } else if (!DebugData) {
    // DebugData wasn't populated, indicating another thread raced us for compiling this block
    return reinterpret_cast<uintptr_t>(CodePtr);
  }

  // The core managed to compile the code.
  if (Config.BlockJITNaming()) {
    auto FragmentBasePtr = CompiledCode.BlockBegin;

    auto GuestRIPLookup = SyscallHandler->LookupExecutableFileSection(Thread, GuestRIP);

    if (DebugData->Subblocks.size()) {
      for (auto& Subblock : DebugData->Subblocks) {
        auto BlockBasePtr = FragmentBasePtr + Subblock.HostCodeOffset;
        if (GuestRIPLookup) {
          Symbols.Register(Thread->SymbolBuffer.get(), BlockBasePtr, CompiledCode.Size, GuestRIPLookup->FileInfo.Filename,
                           GuestRIP - GuestRIPLookup->FileStartVA);
        } else {
          Symbols.Register(Thread->SymbolBuffer.get(), BlockBasePtr, GuestRIP, Subblock.HostCodeSize);
        }
      }
    } else {
      if (GuestRIPLookup) {
        Symbols.Register(Thread->SymbolBuffer.get(), FragmentBasePtr, CompiledCode.Size, GuestRIPLookup->FileInfo.Filename,
                         GuestRIP - GuestRIPLookup->FileStartVA);
      } else {
        Symbols.Register(Thread->SymbolBuffer.get(), FragmentBasePtr, GuestRIP, CompiledCode.Size);
      }
    }
  }

  if (Config.LibraryJITNaming() || Config.GDBSymbols()) {
    auto MappedSection = SyscallHandler->LookupExecutableFileSection(Thread, GuestRIP);
    if (MappedSection) {
      if (Config.LibraryJITNaming()) {
        Symbols.RegisterNamedRegion(Thread->SymbolBuffer.get(), CodePtr, DebugData->HostCodeSize, MappedSection->FileInfo.Filename);
      }

      if (Config.GDBSymbols()) {
        GDBJITRegister(MappedSection->FileInfo, MappedSection->FileStartVA, GuestRIP, (uintptr_t)CodePtr, *DebugData);
      }
    }
  }

  // Clear any relocations that might have been generated
  if (!CodeCache.IsGeneratingCache) {
    Thread->CPUBackend->ClearRelocations();
  }

  fextl::vector<uint64_t> CodePages;

  if (NeedsAddGuestCodeRanges) {
    // Track in the guest to host map all entrypoints for all pages the compiled block touches, if any page didn't previously
    // contain code, inform the frontend so it can setup SMC detection.
    auto BlockInfo = Thread->FrontendDecoder->GetDecodedBlockInfo();
    CodePages.reserve(BlockInfo->CodePages.size());
    CodePages.insert(CodePages.end(), BlockInfo->CodePages.begin(), BlockInfo->CodePages.end());
    for (auto CodePage : BlockInfo->CodePages) {
      if (Thread->LookupCache->AddBlockExecutableRange(Thread, BlockInfo->EntryPoints, CodePage, FEXCore::Utils::FEX_PAGE_SIZE)) {
        SyscallHandler->MarkGuestExecutableRange(Thread, CodePage, FEXCore::Utils::FEX_PAGE_SIZE);
      }
    }
  }

  // Insert to lookup cache

  for (auto [GuestAddr, HostAddr] : CompiledCode.EntryPoints) {
    Thread->LookupCache->AddBlockMapping(Thread, GuestAddr, CodePages, HostAddr);
  }

  if (CodeMapWriter) {
    auto Region = SyscallHandler->LookupExecutableFileSection(Thread, GuestRIP);
    if (Region && Region->FileStartVA != 0) {
      CodeMapWriter->AppendBlock(*Region, GuestRIP);
    }
  }

  return (uintptr_t)CodePtr;
#endif
}

uintptr_t ContextImpl::CompileSingleStep(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  FEXCORE_PROFILE_SCOPED("CompileSingleStep");
  auto Thread = Frame->Thread;

  static_cast<ContextImpl*>(Thread->CTX)->SyscallHandler->PreCompile();

  // Invalidate might take a unique lock on this, to guarantee that during invalidation no code gets compiled
  auto lk = GuardSignalDeferringSection<std::shared_lock>(CodeInvalidationMutex, Thread);

  auto [CompiledCode, DebugData, StartAddr, Length, _] = CompileCode(Thread, GuestRIP, 1);
  auto CodePtr = CompiledCode.EntryPoints[GuestRIP];
  if (CodePtr == nullptr) {
    return 0;
  }

  // Clear any relocations that might have been generated
  Thread->CPUBackend->ClearRelocations();

  return (uintptr_t)CodePtr;
}

void ContextImpl::InvalidateCodeBuffersCodeRange(uint64_t Start, uint64_t Length) {
  FEXCORE_PROFILE_SCOPED("InvalidateCodeBuffersCodeRange");

  LOGMAN_THROW_A_FMT(CodeInvalidationMutex.try_lock() == false, "CodeInvalidationMutex needs to be unique_locked here");
  std::scoped_lock lk {CodeBufferListLock};
  auto it = CodeBufferList.begin();
  while (it != CodeBufferList.end()) {
    if (auto Strong = it->lock()) {
      Strong->LookupCache->InvalidateRange(Start, Length);
      it++;
    } else {
      it = CodeBufferList.erase(it);
    }
  }
}

void ContextImpl::InvalidateThreadCachedCodeRange(FEXCore::Core::InternalThreadState* Thread, uint64_t Start, uint64_t Length) {
  LOGMAN_THROW_A_FMT(CodeInvalidationMutex.try_lock() == false, "CodeInvalidationMutex needs to be unique_locked here");

  // Ensures now-modified mappings aren't cached as being in their previous non-executable state.
  // Accessing FrontendDecoder is safe as the thread's code invalidation mutex must be locked here.
  Thread->FrontendDecoder->ResetExecutableRangeCache();

  if (Thread->LookupCache->InvalidateCacheRange(Start, Length)) {
    FEXCORE_PROFILE_SCOPED("InvalidateCallRet");

    // This may cause access violations in the thread on Windows as zeroing is not atomic, this is handled by the frontend
    Allocator::VirtualDontNeed(Thread->CallRetStackBase, FEXCore::Core::InternalThreadState::CALLRET_STACK_SIZE);
  }
}

void ContextImpl::ThreadRemoveCodeEntryFromJit(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  static_cast<ContextImpl*>(Frame->Thread->CTX)->SyscallHandler->InvalidateGuestCodeRange(Frame->Thread, GuestRIP, 1);
}

std::optional<CustomIRResult>
ContextImpl::AddCustomIREntrypoint(uintptr_t Entrypoint, CustomIREntrypointHandler Handler, void* Creator, void* Data) {
  LOGMAN_THROW_A_FMT(Config.Is64BitMode || !(Entrypoint >> 32), "64-bit Entrypoint in 32-bit mode {:x}", Entrypoint);

  std::unique_lock lk(CustomIRMutex);

  auto InsertedIterator = CustomIRHandlers.emplace(Entrypoint, CustomIRHandlerEntry {Handler, Creator, Data});
  HasCustomIRHandlers = true;

  if (!InsertedIterator.second) {
    const auto& [fn, Creator, Data] = InsertedIterator.first->second;
    return CustomIRResult(Creator, Data);
  }

  return std::nullopt;
}

void ContextImpl::AddThunkTrampolineIRHandler(uintptr_t Entrypoint, uintptr_t GuestThunkEntrypoint) {
  LOGMAN_THROW_A_FMT(Entrypoint, "Tried to link null pointer address to guest function");
  LOGMAN_THROW_A_FMT(GuestThunkEntrypoint, "Tried to link address to null pointer guest function");
  if (!Config.Is64BitMode) {
    LOGMAN_THROW_A_FMT((Entrypoint >> 32) == 0, "Tried to link 64-bit address in 32-bit mode");
    LOGMAN_THROW_A_FMT((GuestThunkEntrypoint >> 32) == 0, "Tried to link 64-bit address in 32-bit mode");
  }

  LogMan::Msg::DFmt("Thunks: Adding guest trampoline from address {:#x} to guest function {:#x}", Entrypoint, GuestThunkEntrypoint);

  auto Result = AddCustomIREntrypoint(
    Entrypoint,
    [this, GuestThunkEntrypoint](uintptr_t Entrypoint, FEXCore::IR::IREmitter* emit) {
      auto IRHeader = emit->_IRHeader(emit->Invalid(), Entrypoint, 0, 0, 0, 0);
      auto Block = emit->CreateCodeNode(true, 0);
      IRHeader.first->Blocks = emit->WrapNode(Block);
      emit->SetCurrentCodeBlock(Block);

      const auto GPRSize = this->Config.Is64BitMode ? IR::OpSize::i64Bit : IR::OpSize::i32Bit;

      // Thunk entry-points don't get cached, don't need to be padded.
      if (GPRSize == IR::OpSize::i64Bit) {
        IR::Ref R = emit->_StoreRegister(emit->Constant(Entrypoint), GPRSize);
        R->Reg = IR::PhysicalRegister(IR::RegClass::GPRFixed, X86State::REG_R11).Raw;
      } else {
        emit->_StoreContextFPR(GPRSize, emit->_VCastFromGPR(IR::OpSize::i64Bit, IR::OpSize::i64Bit, emit->Constant(Entrypoint)),
                               offsetof(Core::CPUState, mm[0][0]));
      }
      emit->_ExitFunction(IR::OpSize::i64Bit, emit->Constant(GuestThunkEntrypoint), IR::BranchHint::None, emit->Invalid(), emit->Invalid());
    },
    ThunkHandler, (void*)GuestThunkEntrypoint);

  if (Result.has_value()) {
    if (Result->Creator != ThunkHandler) {
      ERROR_AND_DIE_FMT("Input address for AddThunkTrampoline is already linked by another module");
    }
    if (Result->Data != (void*)GuestThunkEntrypoint) {
      // NOTE: This may happen in Vulkan thunks if the Vulkan driver resolves two different symbols
      //       to the same function (e.g. vkGetPhysicalDeviceFeatures2/vkGetPhysicalDeviceFeatures2KHR)
      LogMan::Msg::EFmt("Input address for AddThunkTrampoline is already linked elsewhere");
    }
  }
}

void ContextImpl::AddForceTSOInformation(const IntervalList<uint64_t>& ValidRanges, fextl::set<uint64_t>&& Instructions) {
  LogMan::Throw::AFmt(CodeInvalidationMutex.try_lock() == false, "CodeInvalidationMutex needs to be unique_locked here");
  ForceTSOValidRanges.Insert(ValidRanges);
  ForceTSOInstructions.merge(std::move(Instructions));
}

void ContextImpl::RemoveForceTSOInformation(uint64_t Address, uint64_t Size) {
  LogMan::Throw::AFmt(CodeInvalidationMutex.try_lock() == false, "CodeInvalidationMutex needs to be unique_locked here");

  ForceTSOValidRanges.Remove({Address, Address + Size});
  ForceTSOInstructions.erase(ForceTSOInstructions.lower_bound(Address), ForceTSOInstructions.upper_bound(Address + Size));
}

void ContextImpl::MarkMonoBackpatcherBlock(uint64_t BlockEntry) {
  MonoBackpatcherBlock.store(BlockEntry, std::memory_order_relaxed);
}

void ContextImpl::RemoveCustomIREntrypoint(FEXCore::Core::InternalThreadState* Thread, uintptr_t Entrypoint) {
  LOGMAN_THROW_A_FMT(Config.Is64BitMode || !(Entrypoint >> 32), "64-bit Entrypoint in 32-bit mode {:x}", Entrypoint);

  std::scoped_lock lk(CustomIRMutex);

  CustomIRHandlers.erase(Entrypoint);
  HasCustomIRHandlers = !CustomIRHandlers.empty();
  SyscallHandler->InvalidateGuestCodeRange(Thread, Entrypoint, 1);
}

void ContextImpl::MonoBackpatcherWrite(FEXCore::Core::CpuStateFrame* Frame, uint8_t Size, uint64_t Address, uint64_t Value) {
  auto Thread = Frame->Thread;
  auto CTX = static_cast<ContextImpl*>(Thread->CTX);
  {
    auto lk = GuardSignalDeferringSection(CTX->CodeInvalidationMutex, Thread);

    if (Size == 8) {
      *reinterpret_cast<uint64_t*>(Address) = Value;
    } else if (Size == 4) {
      *reinterpret_cast<uint32_t*>(Address) = Value;
    } else {
      ERROR_AND_DIE_FMT("Unexpected write size for backpatcher: {}", Size);
    }
  }

  CTX->SyscallHandler->InvalidateGuestCodeRange(Thread, Address, Size);
}

void ContextImpl::ConfigureAOTGen(FEXCore::Core::InternalThreadState* Thread, fextl::set<uint64_t>* ExternalBranches, uint64_t SectionMaxAddress) {
  Thread->FrontendDecoder->SetExternalBranches(ExternalBranches);
}
} // namespace FEXCore::Context
