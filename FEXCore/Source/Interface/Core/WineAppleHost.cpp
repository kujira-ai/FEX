// SPDX-License-Identifier: MIT
#include "Interface/Core/WineAppleHost.h"

#include <FEXCore/Core/CoreState.h>
#include <FEXCore/Utils/AllocatorHooks.h>

#include <cstdint>

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE

namespace FEX::WineApple {
namespace {

constexpr size_t kPage = 16384;
constexpr uint64_t kMaxCache = 16;

struct CacheEnt {
  uint64_t Guest;
  uint64_t Host;
};

struct Meta {
  uint64_t NCache;
  void* Unhandled;
  CacheEnt Cache[kMaxCache];
};

bool PlausibleMeta(void* P) {
  const auto U = reinterpret_cast<uintptr_t>(P);
  if (U < 0x10000ull || (U & 0xFFFull) != 0) {
    return false;
  }
  if ((U & 0xFFFFFFFFull) == 0 || U >= 0x0001'0000'0000'0000ull) {
    return false;
  }
  return true;
}

Meta* GetMeta() {
  static Meta* P {};
  if (!PlausibleMeta(P)) {
    void* Page = FEXCore::Allocator::VirtualAlloc(kPage, false, true);
    if (!Page) {
      return nullptr;
    }
    auto* M = static_cast<volatile unsigned char*>(Page);
    for (size_t I = 0; I < sizeof(Meta); ++I) {
      M[I] = 0;
    }
    P = static_cast<Meta*>(Page);
  }
  return P;
}

void FlushICache(void* Page, size_t Bytes) {
  uintptr_t P = reinterpret_cast<uintptr_t>(Page) & ~63ull;
  const uintptr_t E = reinterpret_cast<uintptr_t>(Page) + Bytes;
  for (; P < E; P += 64) {
    __asm__ volatile("dc cvau, %0" ::"r"(P) : "memory");
  }
  __asm__ volatile("dsb ish" ::: "memory");
  P = reinterpret_cast<uintptr_t>(Page) & ~63ull;
  for (; P < E; P += 64) {
    __asm__ volatile("ic ivau, %0" ::"r"(P) : "memory");
  }
  __asm__ volatile("dsb ish\n\tisb" ::: "memory");
}

void* EmitRX(const uint32_t* Words, size_t NWords) {
  void* Page = FEXCore::Allocator::VirtualAlloc(kPage, false, true);
  if (!Page) {
    return nullptr;
  }
  auto* W = static_cast<volatile uint32_t*>(Page);
  for (size_t I = 0; I < NWords; ++I) {
    W[I] = Words[I];
  }
  FlushICache(Page, NWords * 4);
  (void)FEXCore::Allocator::VirtualProtect(Page, kPage,
                                           FEXCore::Allocator::ProtectOptions::Read | FEXCore::Allocator::ProtectOptions::Exec);
  return Page;
}

void* UnhandledFAR0() {
  Meta* M = GetMeta();
  if (!M) {
    return nullptr;
  }
  if (M->Unhandled) {
    return M->Unhandled;
  }
  const uint32_t Words[] = {
    0xAA1F03EBu, // mov x11, xzr
    0xF900017Fu, // str xzr, [x11]
  };
  M->Unhandled = EmitRX(Words, 2);
  return M->Unhandled;
}

// ARM64EC x64 SRA: RAX,RCX,RDX,RBX,RSP,RBP,RSI,RDI
int GprXn(uint8_t Rm) {
  switch (Rm) {
  case 0: return 8;
  case 1: return 0;
  case 2: return 1;
  case 3: return 27;
  case 4: return 23;
  case 5: return 29;
  case 6: return 25;
  case 7: return 26;
  default: return -1;
  }
}

uint32_t EncSubImm(unsigned Xn, uint32_t Imm) {
  return 0xD1000000u | (Imm << 10) | (Xn << 5) | Xn;
}
uint32_t EncAddImm(unsigned Xn, uint32_t Imm) {
  return 0x91000000u | (Imm << 10) | (Xn << 5) | Xn;
}

uint32_t EncMovReg(unsigned Rd, unsigned Rm) {
  return 0xAA0003E0u | (Rm << 16) | Rd; // mov Xd, Xm
}
uint32_t EncStrUoff(unsigned Rt, unsigned Rn, uint32_t ByteOff) {
  return 0xF9000000u | ((ByteOff / 8) << 10) | (Rn << 5) | Rt;
}
uint32_t EncMovz(unsigned Rd, uint16_t Imm, unsigned Hw) {
  return 0xD2800000u | (Hw << 21) | (static_cast<uint32_t>(Imm) << 5) | Rd;
}
uint32_t EncMovk(unsigned Rd, uint16_t Imm, unsigned Hw) {
  return 0xF2800000u | (Hw << 21) | (static_cast<uint32_t>(Imm) << 5) | Rd;
}

void EmitMovAbs(uint32_t* Out, size_t& N, unsigned Rd, uint64_t Abs) {
  Out[N++] = EncMovz(Rd, static_cast<uint16_t>(Abs), 0);
  Out[N++] = EncMovk(Rd, static_cast<uint16_t>(Abs >> 16), 1);
  Out[N++] = EncMovk(Rd, static_cast<uint16_t>(Abs >> 32), 2);
  Out[N++] = EncMovk(Rd, static_cast<uint16_t>(Abs >> 48), 3);
}

void EmitBrAbs(uint32_t* Out, size_t& N, unsigned Rd, uint64_t Abs) {
  EmitMovAbs(Out, N, Rd, Abs);
  Out[N++] = 0xD61F0000u | (Rd << 5);
}

void EmitRipAddBr(uint32_t* Out, size_t& N, uint32_t Delta, uint64_t LoopTop) {
  Out[N++] = 0xF9400F8Au; // ldr x10, [x28, #24] RIP
  Out[N++] = 0x91000000u | (Delta << 10) | (10u << 5) | 10u;
  Out[N++] = 0xF9000F8Au;
  if (LoopTop) {
    EmitBrAbs(Out, N, 10, LoopTop);
  } else {
    Out[N++] = 0xAA1F03EBu;
    Out[N++] = 0xF900017Fu;
  }
}

void SeedL1(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP, uint64_t Host) {
  if (!Frame || !Frame->State.L1Pointer || !Host) {
    return;
  }
  const uint64_t Off = GuestRIP & Frame->State.L1Mask;
  auto* E = reinterpret_cast<volatile uint64_t*>(Frame->State.L1Pointer + Off);
  E[0] = Host;
  E[1] = GuestRIP;
}

} // namespace

void Ensure() {
  (void)UnhandledFAR0();
}

uintptr_t CompileOneInsn(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP) {
  const uint64_t LoopTop = Frame ? Frame->Pointers.DispatcherLoopTop : 0;
  if (GuestRIP < 0x10000ull) {
    void* U = UnhandledFAR0();
    return U ? reinterpret_cast<uintptr_t>(U) : 0;
  }
  Meta* M = GetMeta();
  if (!M) {
    return 0;
  }
  for (uint64_t I = 0; I < M->NCache && I < kMaxCache; ++I) {
    if (M->Cache[I].Guest == GuestRIP && M->Cache[I].Host) {
      SeedL1(Frame, GuestRIP, M->Cache[I].Host);
      return M->Cache[I].Host;
    }
  }

  uint8_t B0 = 0, B1 = 0, B2 = 0, B3 = 0, B4 = 0, B5 = 0;
  {
    const auto* P = reinterpret_cast<const volatile uint8_t*>(GuestRIP);
    B0 = P[0];
    B1 = P[1];
    B2 = P[2];
    B3 = P[3];
    B4 = P[4];
    B5 = P[5];
  }

  uint32_t Words[32];
  size_t N = 0;
  if (B0 == 0x90) {
    EmitRipAddBr(Words, N, 1, LoopTop);
  } else if (B0 == 0x66 && B1 == 0x90) {
    EmitRipAddBr(Words, N, 2, LoopTop);
  } else if (int Xn = GprXn(static_cast<uint8_t>(B0 - 0x50)); B0 >= 0x50 && B0 <= 0x57 && Xn >= 0) {
    Words[N++] = EncSubImm(23, 8); // RSP -= 8
    Words[N++] = 0xF90002E0u | static_cast<uint32_t>(Xn);
    EmitRipAddBr(Words, N, 1, LoopTop);
  } else if (B0 == 0x48 && B1 == 0x83 && (B2 & 0xC0) == 0xC0) {
    // REX.W 83 /0 add r64, imm8  or  /5 sub r64, imm8  (mod=11)
    const uint8_t Ext = (B2 >> 3) & 7;
    const int Xn = GprXn(B2 & 7);
    const int8_t Imm8 = static_cast<int8_t>(B3);
    if (Xn >= 0 && (Ext == 0 || Ext == 5)) {
      uint32_t Mag = Imm8 < 0 ? static_cast<uint32_t>(-Imm8) : static_cast<uint32_t>(Imm8);
      const bool Sub = (Ext == 5);
      if (Mag <= 4095) {
        if (Sub == (Imm8 >= 0)) {
          Words[N++] = EncSubImm(static_cast<unsigned>(Xn), Mag);
        } else {
          Words[N++] = EncAddImm(static_cast<unsigned>(Xn), Mag);
        }
        EmitRipAddBr(Words, N, 4, LoopTop);
      }
    }
  } else if (B0 == 0x48 && B1 == 0x8B && (B2 & 0xC0) == 0xC0) {
    // REX.W 8B /r mov r64, r64 (mod=11)
    const int Dst = GprXn((B2 >> 3) & 7);
    const int Src = GprXn(B2 & 7);
    if (Dst >= 0 && Src >= 0) {
      Words[N++] = EncMovReg(static_cast<unsigned>(Dst), static_cast<unsigned>(Src));
      EmitRipAddBr(Words, N, 3, LoopTop);
    }
  } else if (B0 == 0x48 && B1 == 0x89 && (B2 & 7) != 4) {
    // REX.W 89 /r mov r/m64, r64 — mod=01 disp8, no SIB
    const uint8_t Mod = B2 >> 6;
    const int Src = GprXn((B2 >> 3) & 7);
    const int Base = GprXn(B2 & 7);
    if (Mod == 1 && Src >= 0 && Base >= 0) {
      const int8_t Disp = static_cast<int8_t>(B3);
      if (Disp >= 0 && (Disp & 7) == 0) {
        const uint32_t Off = static_cast<uint32_t>(Disp);
        if ((Off / 8) <= 4095) {
          Words[N++] = EncStrUoff(static_cast<unsigned>(Src), static_cast<unsigned>(Base), Off);
          EmitRipAddBr(Words, N, 4, LoopTop);
        }
      }
    }
  } else if (B0 >= 0xB8 && B0 <= 0xBF) {
    // mov r32, imm32 — zero-extends into the 64-bit SRA GPR
    const int Xn = GprXn(static_cast<uint8_t>(B0 - 0xB8));
    if (Xn >= 0) {
      const uint32_t Imm = static_cast<uint32_t>(B1) | (static_cast<uint32_t>(B2) << 8) |
                           (static_cast<uint32_t>(B3) << 16) | (static_cast<uint32_t>(B4) << 24);
      const unsigned Rd = static_cast<unsigned>(Xn);
      Words[N++] = EncMovz(Rd, static_cast<uint16_t>(Imm), 0);
      if (Imm >> 16) {
        Words[N++] = EncMovk(Rd, static_cast<uint16_t>(Imm >> 16), 1);
      }
      EmitRipAddBr(Words, N, 5, LoopTop);
    }
  } else if (B0 == 0xE8) {
    // call rel32: push RIP+5, RIP = RIP+5+disp32, br LoopTop
    const int32_t Disp = static_cast<int32_t>(static_cast<uint32_t>(B1) | (static_cast<uint32_t>(B2) << 8) |
                                              (static_cast<uint32_t>(B3) << 16) | (static_cast<uint32_t>(B4) << 24));
    const uint64_t Ret = GuestRIP + 5;
    const uint64_t Tgt = Ret + static_cast<uint64_t>(static_cast<int64_t>(Disp));
    Words[N++] = EncSubImm(23, 8);       // RSP -= 8
    EmitMovAbs(Words, N, 10, Ret);       // x10 = return RIP
    Words[N++] = 0xF90002EAu;            // str x10, [x23]
    EmitMovAbs(Words, N, 10, Tgt);       // x10 = target
    Words[N++] = 0xF9000F8Au;            // str x10, [x28, #24] RIP
    if (LoopTop) {
      EmitBrAbs(Words, N, 10, LoopTop);
    } else {
      Words[N++] = 0xAA1F03EBu;
      Words[N++] = 0xF900017Fu;
    }
  } else if (B0 == 0xFF && B1 == 0x25 && LoopTop) {
    // jmp qword [rip+disp32]: load IAT, RIP = *slot, br LoopTop
    const int32_t Disp = static_cast<int32_t>(static_cast<uint32_t>(B2) | (static_cast<uint32_t>(B3) << 8) |
                                              (static_cast<uint32_t>(B4) << 16) | (static_cast<uint32_t>(B5) << 24));
    const uint64_t Slot = GuestRIP + 6 + static_cast<uint64_t>(static_cast<int64_t>(Disp));
    if (Slot >= 0x10000ull) {
      EmitMovAbs(Words, N, 10, Slot);
      Words[N++] = 0xF9400149u; // ldr x9, [x10]
      Words[N++] = 0xF9000F89u; // str x9, [x28, #24] RIP
      EmitBrAbs(Words, N, 10, LoopTop);
    }
  }

  if (N == 0) {
    void* U = UnhandledFAR0();
    const uint64_t Host = U ? reinterpret_cast<uint64_t>(U) : 0;
    SeedL1(Frame, GuestRIP, Host);
    return Host;
  }

  void* Page = EmitRX(Words, N);
  if (!Page) {
    void* U = UnhandledFAR0();
    return U ? reinterpret_cast<uintptr_t>(U) : 0;
  }
  const uint64_t Host = reinterpret_cast<uint64_t>(Page);
  if (M->NCache < kMaxCache) {
    M->Cache[M->NCache].Guest = GuestRIP;
    M->Cache[M->NCache].Host = Host;
    ++M->NCache;
  }
  SeedL1(Frame, GuestRIP, Host);
  return Host;
}

} // namespace FEX::WineApple

extern "C" {
void FEXWineAppleEnsure() {
  FEX::WineApple::Ensure();
}
uintptr_t FEXWineAppleCompileOneInsn(void* Frame, uint64_t GuestRIP) {
  return FEX::WineApple::CompileOneInsn(static_cast<FEXCore::Core::CpuStateFrame*>(Frame), GuestRIP);
}
}

#else

namespace FEX::WineApple {
void Ensure() {}
uintptr_t CompileOneInsn(FEXCore::Core::CpuStateFrame*, uint64_t) {
  return 0;
}
} // namespace FEX::WineApple

extern "C" {
void FEXWineAppleEnsure() {}
uintptr_t FEXWineAppleCompileOneInsn(void*, uint64_t) {
  return 0;
}
}

#endif
