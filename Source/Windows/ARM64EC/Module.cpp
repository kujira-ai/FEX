// SPDX-License-Identifier: MIT
/*
$info$
tags: Bin|ARM64EC
desc: Implements the ARM64EC BT module API using FEXCore
$end_info$
*/

#include <FEXCore/fextl/fmt.h>
#include <FEXCore/Core/X86Enums.h>
#include <FEXCore/Core/SignalDelegator.h>
#include <FEXCore/Core/Context.h>
#include <FEXCore/Core/CoreState.h>
#include <FEXCore/Debug/InternalThreadState.h>
#include <FEXCore/HLE/SyscallHandler.h>
#include <FEXCore/Config/Config.h>
#include <FEXCore/Utils/Allocator.h>
#include <FEXCore/Utils/LogManager.h>
#include <FEXCore/Utils/Threads.h>
#include <FEXCore/Utils/Profiler.h>
#include <FEXCore/Utils/SHMStats.h>
#include <FEXCore/Utils/EnumOperators.h>
#include <FEXCore/Utils/EnumUtils.h>
#include <FEXCore/Utils/FPState.h>
#include <FEXCore/Utils/ArchHelpers/Arm64.h>
#include <FEXCore/Utils/MathUtils.h>
#include <FEXCore/Utils/TypeDefines.h>
#include <FEXCore/Utils/SignalScopeGuards.h>

#include "Windows/Common/Allocator.h"
#include "Windows/Common/EnvironmentVariablesHandling.h"
#include "Common/CallRetStack.h"
#include "Common/JITGuardPage.h"
#include "Common/Config.h"
#include "Common/Exception.h"
#include "Common/ImageTracker.h"
#include "Common/InvalidationTracker.h"
#include "Common/OvercommitTracker.h"
#include "Common/TSOHandlerConfig.h"
#include "Common/CPUFeatures.h"
#include "Common/Logging.h"
#include "Common/Module.h"
#include "Common/CRT/CRT.h"
#include "Common/PortabilityInfo.h"
#include "Common/Handle.h"
#include "DummyHandlers.h"
#include "BTInterface.h"
#include "Windows/Common/SHMStats.h"

#include <cstdint>
#include <cstdio>
#include <type_traits>
#include <mutex>
#include <optional>
#include <unordered_map>
#include <utility>
#include <ntstatus.h>
#include <windef.h>
#include <winternl.h>
#include <winnt.h>
#include <wine/debug.h>
#include <rpmalloc/rpmalloc.h>

namespace Exception {
class ECSyscallHandler;
}

extern "C" {
extern IMAGE_DOS_HEADER __ImageBase; // Provided by the linker

extern void* ExitFunctionEC;
extern void* CheckCall;
extern void* ExitFunctionSuspendPoint;
extern void* ExitFunctionSuspendResumePoint;

void* X64ReturnInstr; // See Module.S
uintptr_t NtDllBase;
#if FEX_ON_WINE_APPLE
void* WineFallbackCheckCall;
#endif

// Exports on ARM64EC point to x64 fast forward sequences to allow for redirecting to the JIT if functions are hotpatched. This LUT is from their addresses to the relative addresses of the native code exports.
uint32_t* NtDllRedirectionLUT;
uint32_t NtDllRedirectionLUTSize;

// Wine doesn't support issuing direct system calls with SVC, and unlike Windows it doesn't have a 'stable' syscall number for NtContinue
void* WineSyscallDispatcher;
uint64_t WineNtContinueSyscallId;
uint64_t WineNtAllocateVirtualMemorySyscallId;
uint64_t WineNtProtectVirtualMemorySyscallId;
uint64_t WineNtFreeVirtualMemorySyscallId;

NTSTATUS NtContinueNative(ARM64_NT_CONTEXT* NativeContext, BOOLEAN Alert);
NTSTATUS NtAllocateVirtualMemoryNative(HANDLE, PVOID*, ULONG_PTR, SIZE_T*, ULONG, ULONG);
NTSTATUS NtProtectVirtualMemoryNative(HANDLE, PVOID*, SIZE_T*, ULONG, ULONG*);
NTSTATUS NtFreeVirtualMemoryNative(HANDLE, PVOID*, SIZE_T*, ULONG);

[[noreturn]]
void JumpSetStack(uintptr_t PC, uintptr_t SP);
}

#if FEX_ON_WINE_APPLE
using WineGetCurrentTeb_t = void* (*)();
static WineGetCurrentTeb_t FEXWineGetCurrentTeb {};

static bool FEXIsPlausibleWineTeb(uintptr_t Teb) {
  // Reject Darwin SVC residue (e.g. MAP flags 0x1002) and null/low junk.
  if (Teb < 0x100000000ULL) {
    return false;
  }
  // Wine-on-macOS TEBs observed ~0x7fffffd0000 (below the old 0x7fffff000000 floor).
  // Accept normal 64-bit user VAs; exclude kernel canonical high half.
  if (Teb >= 0x800000000000ULL) {
    return false;
  }
  // Prefer page-aligned (TEB is on a page); still allow if slightly off.
  return true;
}

static void FEXSetLastGoodTeb(uintptr_t Teb) {
  if (!FEXIsPlausibleWineTeb(Teb)) {
    return;
  }
  // Host-mmap slab [24] — never PE .data (RO risk on 16k pages).
  FEXCore::Allocator::SetWineAppleLastGoodTeb(reinterpret_cast<void*>(Teb));
}

__attribute__((noinline)) static uintptr_t FEXResolveWineTeb() {
  // Prefer raw tpidr/x18. wine_get_current_teb is a PE export — calling it
  // during ProcessInit/ThreadInit re-enters arm64x_check_call and can hit
  // exit_thunk → c000001d before hybrid dispatch is stable.
  uintptr_t Teb {};
  uintptr_t X18 {};
  asm volatile("mrs %0, tpidr_el0" : "=r"(Teb) :: "memory");
  if (FEXIsPlausibleWineTeb(Teb)) {
    return Teb;
  }
  asm volatile("mov %0, x18" : "=r"(X18));
  if (FEXIsPlausibleWineTeb(X18)) {
    return X18;
  }
  // BeginSimulation: tpidr/x18 often zero after loader C — ThreadInit host-slab stash.
  const uintptr_t Last = reinterpret_cast<uintptr_t>(FEXCore::Allocator::GetWineAppleLastGoodTeb());
  if (FEXIsPlausibleWineTeb(Last)) {
    return Last;
  }
  // After process_attach hybrid is up — ntdll last_good via wine_get_current_teb.
  if (FEXWineGetCurrentTeb) {
    const uintptr_t FromWine = reinterpret_cast<uintptr_t>(FEXWineGetCurrentTeb());
    if (FEXIsPlausibleWineTeb(FromWine)) {
      return FromWine;
    }
  }
  return 0;
}

__attribute__((noinline)) static void FEXSyncTebX18() {
  const uintptr_t Teb = FEXResolveWineTeb();
  if (!Teb) {
    return;
  }
  asm volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Teb) : "x18", "memory");
}

static inline _TEB* FEXNtCurrentTeb_Wine() {
  return reinterpret_cast<_TEB*>(FEXResolveWineTeb());
}
#undef NtCurrentTeb
#define NtCurrentTeb() FEXNtCurrentTeb_Wine()

// Early ProcessInit must not route through Wine's syscall dispatcher: patched ntdll thunks
// target x64 fast-forward sequences before FEX's JIT is ready. Use host mmap/mprotect instead.
static constexpr size_t FEX_WINE_APPLE_PAGE_SIZE = 16384;

// Darwin SVC may clobber x18; never leave tpidr/x18 as MAP flags (0x1002) or garbage.
static void FEXWineAppleRestoreTeb(uintptr_t SavedTeb) {
  if (FEXIsPlausibleWineTeb(SavedTeb)) {
    asm volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(SavedTeb) : "x18", "memory");
  } else {
    FEXSyncTebX18();
  }
}

static uintptr_t FEXWineAppleSaveTeb() {
  return FEXResolveWineTeb();
}

static void* FEXWineAppleMmap(size_t Size) {
  void* Result {};
  const uintptr_t Len = Size;
  const uintptr_t SavedTeb = FEXWineAppleSaveTeb();
  __asm__ volatile("mov x16, #197\n\t" /* SYS_mmap */
                   "mov x0, #0\n\t"
                   "mov x1, %1\n\t"
                   "mov x2, #3\n\t"       /* PROT_READ | PROT_WRITE */
                   "mov x3, #0x1002\n\t"  /* MAP_PRIVATE | MAP_ANON */
                   "mov x4, #-1\n\t"
                   "mov x5, #0\n\t"
                   "svc #0x80\n\t"
                   "mov %0, x0"
                   : "=r"(Result)
                   : "r"(Len)
                   : "x0", "x1", "x2", "x3", "x4", "x5", "x16", "x18", "memory", "cc");
  FEXWineAppleRestoreTeb(SavedTeb);
  if (reinterpret_cast<intptr_t>(Result) < 0) {
    return nullptr;
  }
  return Result;
}

static void FEXWineAppleMunmap(void* Ptr, size_t Size) {
  const uintptr_t Addr = reinterpret_cast<uintptr_t>(Ptr);
  const uintptr_t Len = Size;
  const uintptr_t SavedTeb = FEXWineAppleSaveTeb();
  __asm__ volatile("mov x16, #73\n\t" /* SYS_munmap */
                   "mov x0, %0\n\t"
                   "mov x1, %1\n\t"
                   "svc #0x80"
                   :
                   : "r"(Addr), "r"(Len)
                   : "x0", "x1", "x16", "x18", "memory", "cc");
  FEXWineAppleRestoreTeb(SavedTeb);
}

static int FEXEarlyStrcmp(const char* A, const char* B) {
  while (*A && *A == *B) {
    A++;
    B++;
  }
  return static_cast<unsigned char>(*A) - static_cast<unsigned char>(*B);
}

static bool FEXWineAppleMprotect(void* Address, size_t Size, int Prot) {
  const uintptr_t Start = reinterpret_cast<uintptr_t>(Address) & ~(FEX_WINE_APPLE_PAGE_SIZE - 1);
  const uintptr_t End = (reinterpret_cast<uintptr_t>(Address) + Size + FEX_WINE_APPLE_PAGE_SIZE - 1) & ~(FEX_WINE_APPLE_PAGE_SIZE - 1);
  long Ret {};
  const uintptr_t Len = End - Start;
  const uintptr_t SavedTeb = FEXWineAppleSaveTeb();
  __asm__ volatile("mov x16, #74\n\t" /* SYS_mprotect */
                   "mov x0, %1\n\t"
                   "mov x1, %2\n\t"
                   "mov x2, %3\n\t"
                   "svc #0x80\n\t"
                   "mov %0, x0"
                   : "=r"(Ret)
                   : "r"(Start), "r"(Len), "r"(Prot)
                   : "x0", "x1", "x2", "x16", "x18", "memory", "cc");
  FEXWineAppleRestoreTeb(SavedTeb);
  return Ret == 0;
}

#else
static inline void FEXSyncTebX18() {}

static int FEXEarlyStrcmp(const char* A, const char* B) {
  return strcmp(A, B);
}
#endif

static IMAGE_NT_HEADERS64* FEXGetNtHeaders(HMODULE Module) {
  const auto* Dos = reinterpret_cast<const IMAGE_DOS_HEADER*>(Module);
  return reinterpret_cast<IMAGE_NT_HEADERS64*>(reinterpret_cast<uintptr_t>(Module) + Dos->e_lfanew);
}

static void* FEXGetImageDirectoryEntry(HMODULE Module, DWORD Directory) {
  const auto* Nt = FEXGetNtHeaders(Module);
  const auto& Entry = Nt->OptionalHeader.DataDirectory[Directory];
  if (!Entry.VirtualAddress || !Entry.Size) {
    return nullptr;
  }
  return reinterpret_cast<void*>(reinterpret_cast<uintptr_t>(Module) + Entry.VirtualAddress);
}

static void* FEXGetExportByName(HMODULE Module, const char* Name) {
  const uintptr_t Base = reinterpret_cast<uintptr_t>(Module);
  const auto* Exports = static_cast<const IMAGE_EXPORT_DIRECTORY*>(FEXGetImageDirectoryEntry(Module, IMAGE_DIRECTORY_ENTRY_EXPORT));
  if (!Exports) {
    return nullptr;
  }

  const auto* NameTable = reinterpret_cast<const uint32_t*>(Base + Exports->AddressOfNames);
  const auto* FunctionTable = reinterpret_cast<const uint32_t*>(Base + Exports->AddressOfFunctions);
  const auto* OrdinalTable = reinterpret_cast<const uint16_t*>(Base + Exports->AddressOfNameOrdinals);
  for (DWORD Idx = 0; Idx < Exports->NumberOfNames; Idx++) {
    const char* ExportName = reinterpret_cast<const char*>(Base + NameTable[Idx]);
    if (FEXEarlyStrcmp(ExportName, Name) == 0) {
      return reinterpret_cast<void*>(Base + FunctionTable[OrdinalTable[Idx]]);
    }
  }
  return nullptr;
}

#if FEX_ON_WINE_APPLE
struct FEXWineChpeProcessInfo {
  ULONG Wow64ExecuteFlags;
  USHORT NativeMachineType;
  USHORT EmulatedMachineType;
  HANDLE SectionHandle;
  void* CrossProcessWorkList;
  void* unknown;
};

__attribute__((noinline)) static HMODULE FEXGetNtDllFromWineProcessInfo() {
  static constexpr uintptr_t WINE_PEB64_SIZE = 0x7c8;
  static constexpr uintptr_t CHPE_UNKNOWN_OFFSET = offsetof(FEXWineChpeProcessInfo, unknown);
  const uintptr_t Teb = FEXResolveWineTeb();
  if (!Teb) {
    return nullptr;
  }
  const uintptr_t Peb = *reinterpret_cast<const uintptr_t*>(Teb + 0x60);
  return reinterpret_cast<HMODULE>(*reinterpret_cast<const uintptr_t*>(Peb + WINE_PEB64_SIZE + CHPE_UNKNOWN_OFFSET));
}

__attribute__((noinline)) static uintptr_t FEXGetImageBaseFromPeb() {
  const uintptr_t Teb = FEXResolveWineTeb();
  if (!Teb) {
    return 0;
  }
  const uintptr_t Peb = *reinterpret_cast<const uintptr_t*>(Teb + 0x60);
  return *reinterpret_cast<const uintptr_t*>(Peb + offsetof(__PEB, ImageBaseAddress));
}
#endif

struct ThreadCPUArea {
  static constexpr size_t TEBCPUAreaOffset = 0x1788;
  CHPE_V2_CPU_AREA_INFO* Area;

  explicit ThreadCPUArea(_TEB* TEB)
    : Area(nullptr) {
    if (!TEB) {
      return;
    }
    Area = *reinterpret_cast<CHPE_V2_CPU_AREA_INFO**>(reinterpret_cast<uintptr_t>(TEB) + TEBCPUAreaOffset);
  }

  bool valid() const {
    return Area != nullptr;
  }

  uint64_t& EmulatorStackLimit() const {
    return Area->EmulatorStackLimit;
  }

  uint64_t& EmulatorStackBase() const {
    return Area->EmulatorStackBase;
  }

  ARM64EC_NT_CONTEXT& ContextAmd64() const {
    return *Area->ContextAmd64;
  }

  FEXCore::Core::CpuStateFrame*& StateFrame() const {
    return reinterpret_cast<FEXCore::Core::CpuStateFrame*&>(Area->EmulatorData[0]);
  }

  FEXCore::Core::InternalThreadState*& ThreadState() const {
    return reinterpret_cast<FEXCore::Core::InternalThreadState*&>(Area->EmulatorData[1]);
  }

  uint64_t& DispatcherLoopTopEnterEC() const {
    return reinterpret_cast<uint64_t&>(Area->EmulatorData[2]);
  }

  uint64_t& DispatcherLoopTopEnterECFillSRA() const {
    return reinterpret_cast<uint64_t&>(Area->EmulatorData[3]);
  }
};

struct FrontendThreadData {
  bool InLockedRWXRead {};
};

namespace {
fextl::unique_ptr<FEXCore::Context::Context> CTX;
fextl::unique_ptr<FEX::DummyHandlers::DummySignalDelegator> SignalDelegator;
fextl::unique_ptr<Exception::ECSyscallHandler> SyscallHandler;
fextl::unique_ptr<FEX::Windows::StatAlloc> StatAllocHandler;
std::optional<FEX::Windows::InvalidationTracker> InvalidationTracker;
std::optional<FEX::Windows::CPUFeatures> CPUFeatures;
std::optional<FEX::Windows::OvercommitTracker> OvercommitTracker;
std::optional<FEX::Windows::ImageTracker> ImageTracker;

std::recursive_mutex ThreadCreationMutex;
// Map of TIDs to their FEX thread state, `ThreadCreationMutex` must be locked when accessing
std::unordered_map<DWORD, FEXCore::Core::InternalThreadState*> Threads;

static uintptr_t GetTebAddress() {
#if FEX_ON_WINE_APPLE
  return FEXResolveWineTeb();
#else
  uintptr_t Teb {};
  asm volatile("mov %0, x18" : "=r"(Teb));
  return Teb;
#endif
}

std::pair<NTSTATUS, ThreadCPUArea> GetThreadCPUArea(HANDLE Thread) {
  THREAD_BASIC_INFORMATION Info;
  const NTSTATUS Err = NtQueryInformationThread(Thread, ThreadBasicInformation, &Info, sizeof(Info), nullptr);
  return {Err, ThreadCPUArea(reinterpret_cast<_TEB*>(Info.TebBaseAddress))};
}

ThreadCPUArea GetCPUArea() {
  const uintptr_t Teb = GetTebAddress();
  FEXSyncTebX18();
  ThreadCPUArea CPUArea {reinterpret_cast<_TEB*>(Teb)};
  return CPUArea;
}

// Wine-apple never assigns file-scope CTX (RO .rdata on 16k pages); context lives
// in Allocator WineApple stash. Using null CTX makes LLVM emit brk in SyncThreadContext.
static FEXCore::Context::Context* GetFEXContext() {
#if FEX_ON_WINE_APPLE
  return static_cast<FEXCore::Context::Context*>(FEXCore::Allocator::GetWineAppleContext());
#else
  return CTX.get();
#endif
}

#if FEX_ON_WINE_APPLE
// Module.S: misaligned-SP path needs x86 `ret` page without writing PE globals.
extern "C" void* FEXGetX64ReturnInstr() {
  return FEXCore::Allocator::GetOrCreateX64ReturnInstr();
}

extern "C" uintptr_t FEXWineAppleCompileOneInsn(void* Frame, uint64_t GuestRIP);
extern "C" void FEXWineAppleEnsure();

// EnterEC miss → one-insn host backend (same as CompileBlock).
extern "C" uint64_t FEXWineAppleCompileStub(uint64_t FrameU, uint64_t GuestRIP) {
  return FEXWineAppleCompileOneInsn(reinterpret_cast<void*>(FrameU), GuestRIP);
}

// FillSRA if EP looks like x64 (not ARM64EC code). Fail closed. Not a basename list.
extern "C" uint64_t WineAppleEpLooksX64(uint64_t Ep) {
  if (Ep < 0x10000ull) {
    return 0;
  }
  const uint8_t B = *reinterpret_cast<const volatile uint8_t*>(Ep);
  if (B == 0x90 || B == 0x66 || B == 0x48 || B == 0xe8 || B == 0xe9) {
    return 1;
  }
  if (B >= 0x40 && B <= 0x4f) {
    return 1; // REX
  }
  if (B >= 0x50 && B <= 0x57) {
    return 1; // PUSH r64
  }
  return 0;
}

// C linkage for Module.S enter_jit — re-bind CHPE EmulatorData every entry.
// jul9e: TEB->ChpeV2CpuAreaInfo->EmulatorData[0..2] were NULL at P8 after ThreadInit.
// Module.S: PE-resident EnterEC (Darwin W^X-safe).
extern "C" void WineAppleEnterEC();
// Gate lb: real FillSRA (LoopTop+CompileBlock). EnterEC dispatcher is ret-only
// on wine-apple (Dispatcher.cpp); FillSRA is the RX-safe JIT entry.
extern "C" uint64_t WineAppleRealFillSRA;
uint64_t WineAppleRealFillSRA = 0;

extern "C" void FEXSyncTebX18ForEnter() {
  // TEB only — no GetCurrentThreadId/Threads (hybrid fault). Prefer Resolve, then slab.
  FEXSyncTebX18();
  uintptr_t X18 {};
  asm volatile("mov %0, x18" : "=r"(X18));
  if (FEXIsPlausibleWineTeb(X18)) {
    return;
  }
  const uintptr_t Last = reinterpret_cast<uintptr_t>(FEXCore::Allocator::GetWineAppleLastGoodTeb());
  if (FEXIsPlausibleWineTeb(Last)) {
    asm volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Last) : "x18", "memory");
  }
}

// BeginSimulation entry: load CHPE area from host slab (no TEB required).
// Returns Area in x0; also restores TEB into x18/tpidr when possible.
extern "C" void* FEXWineAppleBeginSimSetup() {
  {
    const char Msg[] = "BeginSim: enter\n";
    register uint64_t x0 __asm__("x0") = 2;
    register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
    register uint64_t x2 __asm__("x2") = sizeof(Msg) - 1;
    register uint64_t x16 __asm__("x16") = 4;
    __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
  }
  FEXSyncTebX18ForEnter();
  void* Area = FEXCore::Allocator::GetWineAppleCpuArea();
  uintptr_t Teb {};
  asm volatile("mov %0, x18" : "=r"(Teb));
  if (!Area && FEXIsPlausibleWineTeb(Teb)) {
    Area = *reinterpret_cast<void**>(Teb + 0x1788);
  }
  // Gate fk: ProcessHeap is valid before NtContinue; Invalid handle 0 still fires
  // during/after NtContinue (null heap *arg*, not null ProcessHeap).
  if (FEXIsPlausibleWineTeb(Teb)) {
    const uintptr_t Peb = *reinterpret_cast<uintptr_t*>(Teb + 0x60);
    const uintptr_t Heap = (Peb ? *reinterpret_cast<uintptr_t*>(Peb + 0x30) : 0);
    char Msg[96];
    size_t I = 0;
    const char* Pfx = "BeginSim: teb/peb/heap=";
    while (Pfx[I]) {
      Msg[I] = Pfx[I];
      ++I;
    }
    static const char Hex[] = "0123456789abcdef";
    auto puthex = [&](uintptr_t V) {
      Msg[I++] = '0';
      Msg[I++] = 'x';
      for (int S = 60; S >= 0; S -= 4) {
        Msg[I++] = Hex[(V >> S) & 0xf];
      }
      Msg[I++] = ' ';
    };
    puthex(Teb);
    puthex(Peb);
    puthex(Heap);
    Msg[I++] = '\n';
    Msg[I] = 0;
    register uint64_t x0 __asm__("x0") = 2;
    register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
    register uint64_t x2 __asm__("x2") = I;
    register uint64_t x16 __asm__("x16") = 4;
    __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
    asm volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Teb) : "x18", "memory");
  }
  return Area;
}

// Called from BeginSimulation after SyncThreadContext with ContextAmd64 in x0.
// Logs Rip/Rcx/Rsp and ensures ProcessHeap; returns Rip in x0 for br (0 = abort).
// Gate fs (diag only): also log tpidr, ProcessParameters, CommandLine Buffer/Length
// so the start.exe wmain addr-0x8 cliff can be classified (argv vs PEB vs TEB).
extern "C" uint64_t FEXWineAppleBeforeNativeEntry(void* ContextAmd64) {
  FEXSyncTebX18ForEnter();
  uintptr_t Teb {};
  uintptr_t Tpidr {};
  asm volatile("mov %0, x18" : "=r"(Teb));
  asm volatile("mrs %0, tpidr_el0" : "=r"(Tpidr));
  uint64_t Rip = 0, Rcx = 0, Rdx = 0, Rsp = 0;
  if (ContextAmd64) {
    const auto* B = reinterpret_cast<const uint64_t*>(ContextAmd64);
    // AMD64 CONTEXT offsets / 8: Rcx=0x10, Rdx=0x11, Rsp=0x13, Rip=0x1f
    Rcx = B[0x80 / 8];
    Rdx = B[0x88 / 8];
    Rsp = B[0x98 / 8];
    Rip = B[0xf8 / 8];
  }
  uintptr_t Heap = 0, Peb = 0, Params = 0, CmdBuf = 0;
  uint32_t CmdLen = 0;
  if (FEXIsPlausibleWineTeb(Teb)) {
    Peb = *reinterpret_cast<uintptr_t*>(Teb + 0x60);
    if (Peb) {
      Heap = *reinterpret_cast<uintptr_t*>(Peb + 0x30);
      // PEB.ProcessParameters @ +0x20; UNICODE_STRING CommandLine @ +0x70
      // (Length @ +0, Buffer @ +8 on 64-bit).
      Params = *reinterpret_cast<uintptr_t*>(Peb + 0x20);
      if (Params) {
        CmdLen = *reinterpret_cast<uint16_t*>(Params + 0x70);
        CmdBuf = *reinterpret_cast<uintptr_t*>(Params + 0x78);
      }
    }
  }
  char Msg[256];
  size_t I = 0;
  auto put = [&](const char* S) {
    while (*S && I + 1 < sizeof(Msg)) {
      Msg[I++] = *S++;
    }
  };
  auto puthex = [&](uint64_t V) {
    static const char Hex[] = "0123456789abcdef";
    put("0x");
    for (int S = 60; S >= 0; S -= 4) {
      if (I + 1 >= sizeof(Msg)) {
        return;
      }
      Msg[I++] = Hex[(V >> S) & 0xf];
    }
    if (I + 1 < sizeof(Msg)) {
      Msg[I++] = ' ';
    }
  };
  put("BeforeNative: rip=");
  puthex(Rip);
  put("rcx=");
  puthex(Rcx);
  put("heap=");
  puthex(Heap);
  put("tpidr=");
  puthex(Tpidr);
  put("x18=");
  puthex(Teb);
  put("params=");
  puthex(Params);
  put("cmdlen=");
  puthex(CmdLen);
  put("cmdbuf=");
  puthex(CmdBuf);
  put("rsp=");
  puthex(Rsp);
  if (I + 1 < sizeof(Msg)) {
    Msg[I++] = '\n';
  }
  Msg[I] = 0;
  {
    register uint64_t x0 __asm__("x0") = 2;
    register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
    register uint64_t x2 __asm__("x2") = I;
    register uint64_t x16 __asm__("x16") = 4;
    __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
  }
  if (FEXIsPlausibleWineTeb(Teb)) {
    asm volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Teb) : "x18", "memory");
  }
  (void)Rdx;
  // Gate lc BeforeNative→FillSRA: pin past c000001d (lc3–lc5 HostRetStub spin)
  // but EiC tip regressed OPENGL-140 (lc5s1/3/4/5). Reverted for tip hold.
  return Rip;
}
#endif

FrontendThreadData* GetFrontendThreadData(FEXCore::Core::InternalThreadState* Thread) {
  return static_cast<FrontendThreadData*>(Thread->FrontendPtr);
}

bool IsEmulatorStackAddress(const ThreadCPUArea CPUArea, uint64_t Address) {
  return Address <= CPUArea.EmulatorStackBase() && Address >= CPUArea.EmulatorStackLimit();
}

bool IsDispatcherAddress(uint64_t Address) {
  if (!SignalDelegator) {
    return false;
  }
  const auto& Config = SignalDelegator->GetConfig();
  return Address >= Config.DispatcherBegin && Address < Config.DispatcherEnd;
}

struct FexLdrData {
  ULONG Length;
  BOOLEAN Initialized;
  PVOID SsHandle;
  LIST_ENTRY InLoadOrderModuleList;
  LIST_ENTRY InMemoryOrderModuleList;
  LIST_ENTRY InInitializationOrderModuleList;
};

struct FexLdrEntry {
  LIST_ENTRY InMemoryOrderLinks;
  LIST_ENTRY InInitializationOrderLinks;
  LIST_ENTRY InLoadOrderLinks;
  PVOID DllBase;
  PVOID EntryPoint;
  ULONG SizeOfImage;
  UNICODE_STRING FullDllName;
  UNICODE_STRING BaseDllName;
};

static HMODULE GetModuleFromPeb(const wchar_t* Name) {
  uintptr_t Teb {};
#if FEX_ON_WINE_APPLE
  asm volatile("mrs %0, tpidr_el0" : "=r"(Teb) :: "memory");
#else
  asm volatile("mov %0, x18" : "=r"(Teb));
#endif
  const uintptr_t Peb = *reinterpret_cast<const uintptr_t*>(Teb + 0x60);
  const uintptr_t Ldr = *reinterpret_cast<const uintptr_t*>(Peb + offsetof(__PEB, LdrData));
  const uintptr_t Head = Ldr + offsetof(FexLdrData, InMemoryOrderModuleList);
  uintptr_t Cur = *reinterpret_cast<const uintptr_t*>(Head);
  while (Cur != Head) {
    const auto* Entry = reinterpret_cast<const FexLdrEntry*>(Cur - offsetof(FexLdrEntry, InMemoryOrderLinks));
    if (Entry->BaseDllName.Buffer && _wcsicmp(Entry->BaseDllName.Buffer, Name) == 0) {
      return reinterpret_cast<HMODULE>(Entry->DllBase);
    }
    Cur = *reinterpret_cast<const uintptr_t*>(Cur);
  }
  return nullptr;
}

bool FillNtDllLUTs(HMODULE NtDll) {
  const auto* LoadConfig =
    reinterpret_cast<_IMAGE_LOAD_CONFIG_DIRECTORY64*>(FEXGetImageDirectoryEntry(NtDll, IMAGE_DIRECTORY_ENTRY_LOAD_CONFIG));
  const auto* CHPEMetadata = reinterpret_cast<IMAGE_ARM64EC_METADATA*>(LoadConfig->CHPEMetadataPointer);
  const auto* RedirectionTableBegin = reinterpret_cast<IMAGE_ARM64EC_REDIRECTION_ENTRY*>(NtDllBase + CHPEMetadata->RedirectionMetadata);
  const auto* RedirectionTableEnd = RedirectionTableBegin + CHPEMetadata->RedirectionMetadataCount;

  NtDllRedirectionLUTSize = std::prev(RedirectionTableEnd)->Source + 1;

  SIZE_T AllocSize = NtDllRedirectionLUTSize * sizeof(uint32_t);
  PVOID LutBase = nullptr;
#if FEX_ON_WINE_APPLE
  LutBase = FEXWineAppleMmap(AllocSize);
  if (!LutBase) {
    NtDllRedirectionLUT = nullptr;
    NtDllRedirectionLUTSize = 0;
    return false;
  }
#else
  const NTSTATUS Status =
    NtAllocateVirtualMemoryNative(NtCurrentProcess(), &LutBase, 0, &AllocSize, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
  if (!NT_SUCCESS(Status) || !LutBase) {
    NtDllRedirectionLUT = nullptr;
    NtDllRedirectionLUTSize = 0;
    return false;
  }
#endif
  NtDllRedirectionLUT = static_cast<uint32_t*>(LutBase);
  for (auto It = RedirectionTableBegin; It != RedirectionTableEnd; It++) {
    NtDllRedirectionLUT[It->Source] = It->Destination;
  }
  return true;
}

template<typename T>
void WriteModuleRVA(HMODULE Module, LONG RVA, T Data) {
  if (!RVA) {
    return;
  }

  void* Address = reinterpret_cast<void*>(reinterpret_cast<uintptr_t>(Module) + RVA);
#if FEX_ON_WINE_APPLE
  FEXWineAppleMprotect(Address, sizeof(T), 3 /* PROT_READ | PROT_WRITE */);
  *reinterpret_cast<T*>(Address) = Data;
#else
  void* ProtAddress = Address;
  SIZE_T ProtSize = sizeof(T);
  ULONG Prot;
  NtProtectVirtualMemoryNative(NtCurrentProcess(), &ProtAddress, &ProtSize, PAGE_READWRITE, &Prot);
  *reinterpret_cast<T*>(Address) = Data;
  NtProtectVirtualMemoryNative(NtCurrentProcess(), &ProtAddress, &ProtSize, Prot, nullptr);
#endif
}

void PatchCallChecker() {
  // See the comment for CheckCall in Module.S for why this is necessary
  const auto Module = reinterpret_cast<HMODULE>(&__ImageBase);
  const auto* LoadConfig =
    reinterpret_cast<_IMAGE_LOAD_CONFIG_DIRECTORY64*>(FEXGetImageDirectoryEntry(Module, IMAGE_DIRECTORY_ENTRY_LOAD_CONFIG));
  const auto* CHPEMetadata = reinterpret_cast<IMAGE_ARM64EC_METADATA*>(LoadConfig->CHPEMetadataPointer);
#if FEX_ON_WINE_APPLE
  if (CHPEMetadata->__os_arm64x_dispatch_call) {
    WineFallbackCheckCall = *reinterpret_cast<void* const*>(
      reinterpret_cast<uintptr_t>(Module) + CHPEMetadata->__os_arm64x_dispatch_call);
  }
#endif
  WriteModuleRVA(Module, CHPEMetadata->__os_arm64x_dispatch_call, &CheckCall);
  WriteModuleRVA(Module, CHPEMetadata->__os_arm64x_dispatch_icall, &CheckCall);
  WriteModuleRVA(Module, CHPEMetadata->__os_arm64x_dispatch_icall_cfg, &CheckCall);
}

// Fills in the syscall numbers necessary to call *Native variants of syscalls from FEX under wine.
void ParseWineSyscallNumbers(HMODULE NtDll) {
  const auto* Exports = reinterpret_cast<IMAGE_EXPORT_DIRECTORY*>(FEXGetImageDirectoryEntry(NtDll, IMAGE_DIRECTORY_ENTRY_EXPORT));
  const auto* NameTable = reinterpret_cast<uint32_t*>(NtDllBase + Exports->AddressOfNames);
  const auto* FunctionTable = reinterpret_cast<uint32_t*>(NtDllBase + Exports->AddressOfFunctions);
  const auto* OrdinalTable = reinterpret_cast<uint16_t*>(NtDllBase + Exports->AddressOfNameOrdinals);
  struct SyscallEntry {
    const char* Name;
    uint32_t RVA;

    bool operator<(const SyscallEntry& Other) const {
      return RVA < Other.RVA;
    }
  };

  // Cannot use any syscalls at this stage, so rely on a stack-allocated array
  std::array<SyscallEntry, 0x200> SyscallTable;
  auto SyscallTableEnd = SyscallTable.begin();

  // Windows/Wine orders syscalls in memory by their ID, take advantage of that to find the syscall indices for those
  // which we need to manually issue. Note that all functions starting with Nt besides NtGetTickCount are syscalls.
  for (uint32_t Idx = 0; Idx < Exports->NumberOfNames; Idx++) {
    const char* Name = reinterpret_cast<const char*>(NtDllBase + NameTable[Idx]);
    if (Name[0] == 'N' && Name[1] == 't' && FEXEarlyStrcmp(Name, "NtGetTickCount") != 0) {
      *SyscallTableEnd++ = {Name, FunctionTable[OrdinalTable[Idx]]};
    }
  }

  // Sort such that index 0 is now syscall 0, etc. Avoid libc++ introspect sort during early init.
  for (auto It = SyscallTable.begin(); It != SyscallTableEnd; It++) {
    for (auto Jt = It + 1; Jt != SyscallTableEnd; Jt++) {
      if (Jt->RVA < It->RVA) {
        const SyscallEntry Tmp = *It;
        *It = *Jt;
        *Jt = Tmp;
      }
    }
  }

  for (auto it = SyscallTable.begin(); it != SyscallTableEnd; it++) {
    uint32_t CurSyscallId = static_cast<uint32_t>(std::distance(SyscallTable.begin(), it));
    if (FEXEarlyStrcmp(it->Name, "NtContinue") == 0) {
      WineNtContinueSyscallId = CurSyscallId;
    } else if (FEXEarlyStrcmp(it->Name, "NtAllocateVirtualMemory") == 0) {
      WineNtAllocateVirtualMemorySyscallId = CurSyscallId;
    } else if (FEXEarlyStrcmp(it->Name, "NtProtectVirtualMemory") == 0) {
      WineNtProtectVirtualMemorySyscallId = CurSyscallId;
    } else if (FEXEarlyStrcmp(it->Name, "NtFreeVirtualMemory") == 0) {
      WineNtFreeVirtualMemorySyscallId = CurSyscallId;
    }
  }
}

#if FEX_ON_WINE_APPLE
// Minimal host-mmap slab for rpmalloc — avoid Wine NtAllocate* this early.
static constexpr size_t FEX_RPMALLOC_SLAB_SIZE = 64ull << 20; // 64 MiB
static void* FEXRPMallocSlab {};
static size_t FEXRPMallocSlabUsed {};

static void* WineRPMallocMap(size_t size, size_t alignment, size_t* offset, size_t* mapped_size) {
  if (!FEXRPMallocSlab) {
    FEXRPMallocSlab = FEXWineAppleMmap(FEX_RPMALLOC_SLAB_SIZE);
    FEXRPMallocSlabUsed = 0;
    if (!FEXRPMallocSlab) {
      return nullptr;
    }
  }
  size_t Align = alignment ? alignment : 16;
  size_t Pad = (Align - (FEXRPMallocSlabUsed % Align)) % Align;
  size_t Need = Pad + size;
  if (FEXRPMallocSlabUsed + Need > FEX_RPMALLOC_SLAB_SIZE) {
    // Fall back to a fresh host mapping for large/overflow spans
    void* Extra = FEXWineAppleMmap(size + Align);
    if (!Extra) {
      return nullptr;
    }
    uintptr_t P = reinterpret_cast<uintptr_t>(Extra);
    size_t Off = (Align - (P % Align)) % Align;
    *offset = Off;
    *mapped_size = size + Align;
    return reinterpret_cast<void*>(P + Off);
  }
  *offset = Pad;
  *mapped_size = Need;
  void* Result = reinterpret_cast<char*>(FEXRPMallocSlab) + FEXRPMallocSlabUsed + Pad;
  FEXRPMallocSlabUsed += Need;
  return Result;
}

static void WineRPMallocUnmap(void* address, size_t offset, size_t mapped_size) {
  // Slab bump allocator: only unmap standalone overflow mappings (outside slab).
  auto* Base = reinterpret_cast<char*>(address) - offset;
  auto* Slab = reinterpret_cast<char*>(FEXRPMallocSlab);
  if (FEXRPMallocSlab && Base >= Slab && Base < Slab + static_cast<ptrdiff_t>(FEX_RPMALLOC_SLAB_SIZE)) {
    return;
  }
  FEXWineAppleMunmap(Base, mapped_size);
}

static void InitWineRPMalloc() {
  static rpmalloc_interface_t Interface {
    .memory_map = WineRPMallocMap,
    .memory_unmap = WineRPMallocUnmap,
  };
  static rpmalloc_config_t Config {
    .page_size = FEX_WINE_APPLE_PAGE_SIZE, // 16K host pages
    .enable_huge_pages = 0,
    .unmap_on_finalize = 0,
  };
  // Pre-create host slab before rpmalloc's first map callback.
  size_t DummyOff = 0, DummyMap = 0;
  (void)WineRPMallocMap(64, 16, &DummyOff, &DummyMap);
  rpmalloc_initialize_config(&Interface, &Config);
}
#endif

// Syscall thunks may have been patched before FEX has loaded, the default call checker installed by ntdll into FEX will
// try to invoke the JIT when calling such patched syscalls but this obviously doesn't work before FEX is initalised.
// This function parses ntdll and sets up a custom call checker to prevent this, as such it must avoid using any syscall
// thunks itself.
__attribute__((noinline)) void InitSyscalls() {
#if FEX_ON_WINE_APPLE
  const auto NtDll = FEXGetNtDllFromWineProcessInfo();
#else
  const auto NtDll = GetModuleFromPeb(L"ntdll.dll");
#endif
  if (!NtDll) {
    return;
  }
  NtDllBase = reinterpret_cast<uintptr_t>(NtDll);
  FEXWineGetCurrentTeb = reinterpret_cast<WineGetCurrentTeb_t>(FEXGetExportByName(NtDll, "wine_get_current_teb"));

  void* SavedWineSyscallDispatcher = nullptr;
  const auto WineSyscallDispatcherPtr = reinterpret_cast<void**>(FEXGetExportByName(NtDll, "__wine_syscall_dispatcher"));
  if (WineSyscallDispatcherPtr) {
    SavedWineSyscallDispatcher = *WineSyscallDispatcherPtr;
    WineSyscallDispatcher = nullptr;
  }

  if (!FillNtDllLUTs(NtDll)) {
    return;
  }
  PatchCallChecker();

  if (WineSyscallDispatcherPtr) {
    ParseWineSyscallNumbers(NtDll);
    WineSyscallDispatcher = SavedWineSyscallDispatcher;
  }
}

void HandleImageMap(uint64_t Address, bool MainImage = false) {
  fextl::string ModulePath = FEX::Windows::GetSectionFilePath(Address);
  fextl::string ModuleName = fextl::string {FEX::Windows::BaseName(ModulePath)};
  InvalidationTracker->HandleImageMap(ModuleName, Address);
  ImageTracker->HandleImageMap(ModulePath, Address, MainImage);
}

void HandleImageUnmap(uint64_t Address, uint64_t Size) {
  ImageTracker->HandleImageUnmap(Address, Size);
}

} // namespace

namespace Exception {
static std::optional<FEX::Windows::TSOHandlerConfig> HandlerConfig;
static uintptr_t KiUserExceptionDispatcher;

struct alignas(16) KiUserExceptionDispatcherStackLayout {
  ARM64_NT_CONTEXT Context;
  uint64_t Pad[4]; // Only present on newer Windows versions, likely for SVE.
  EXCEPTION_RECORD Rec;
  uint64_t Align;
  uint64_t Redzone[2];
};

static bool HandleUnalignedAccess(const ThreadCPUArea CPUArea, ARM64_NT_CONTEXT& Context, bool IsJIT) {
  auto Thread = CPUArea.ThreadState();
  FEXCORE_PROFILE_INSTANT_INCREMENT(Thread, AccumulatedSIGBUSCount, 1);
  const auto Result =
    FEXCore::ArchHelpers::Arm64::HandleUnalignedAccess(Thread, HandlerConfig->GetUnalignedHandlerType(), Context.Pc, &Context.X0, IsJIT);
  Context.Pc += Result.value_or(0);
  return Result.has_value();
}

static void LoadStateFromECContext(FEXCore::Core::InternalThreadState* Thread, CONTEXT& Context) {
  if (!Thread || !Thread->CurrentFrame) {
    return;
  }
  auto* FexCtx = GetFEXContext();
  if (!FexCtx) {
    return;
  }
  auto& State = Thread->CurrentFrame->State;

  if ((Context.ContextFlags & CONTEXT_INTEGER) == CONTEXT_INTEGER) {
    // General register state
    State.gregs[FEXCore::X86State::REG_RAX] = Context.Rax;
    State.gregs[FEXCore::X86State::REG_RCX] = Context.Rcx;
    State.gregs[FEXCore::X86State::REG_RDX] = Context.Rdx;
    State.gregs[FEXCore::X86State::REG_RBX] = Context.Rbx;

    State.gregs[FEXCore::X86State::REG_RSI] = Context.Rsi;
    State.gregs[FEXCore::X86State::REG_RDI] = Context.Rdi;
    State.gregs[FEXCore::X86State::REG_R8] = Context.R8;
    State.gregs[FEXCore::X86State::REG_R9] = Context.R9;
    State.gregs[FEXCore::X86State::REG_R10] = Context.R10;
    State.gregs[FEXCore::X86State::REG_R11] = Context.R11;
    State.gregs[FEXCore::X86State::REG_R12] = Context.R12;
    State.gregs[FEXCore::X86State::REG_R13] = Context.R13;
    State.gregs[FEXCore::X86State::REG_R14] = Context.R14;
    State.gregs[FEXCore::X86State::REG_R15] = Context.R15;
  }

  if ((Context.ContextFlags & CONTEXT_CONTROL) == CONTEXT_CONTROL) {
    State.rip = Context.Rip;
    State.gregs[FEXCore::X86State::REG_RSP] = Context.Rsp;
    State.gregs[FEXCore::X86State::REG_RBP] = Context.Rbp;
    FexCtx->SetFlagsFromCompactedEFLAGS(Thread, Context.EFlags);
  }

  if ((Context.ContextFlags & CONTEXT_SEGMENTS) == CONTEXT_SEGMENTS) {
    State.es_idx = Context.SegEs & 0xffff;
    State.cs_idx = Context.SegCs & 0xffff;
    State.ss_idx = Context.SegSs & 0xffff;
    State.ds_idx = Context.SegDs & 0xffff;
    State.fs_idx = Context.SegFs & 0xffff;
    State.gs_idx = Context.SegGs & 0xffff;

    // The TEB is the only populated GDT entry by default
    const auto TEB = reinterpret_cast<uint64_t>(NtCurrentTeb());
    auto GDT = State.GetSegmentFromIndex(State, (Context.SegGs & 0xffff));
    State.SetGDTBase(GDT, TEB);
    State.SetGDTLimit(GDT, 0xF'FFFFU);
    State.gs_cached = TEB;
    State.fs_cached = 0;
    State.es_cached = 0;
    State.cs_cached = 0;
    State.ss_cached = 0;
    State.ds_cached = 0;
  }

  if ((Context.ContextFlags & CONTEXT_FLOATING_POINT) == CONTEXT_FLOATING_POINT) {
    // Floating-point register state
    if ((Context.ContextFlags & CONTEXT_XSTATE) == CONTEXT_XSTATE) {
      const auto* Ymm = RtlLocateExtendedFeature(reinterpret_cast<CONTEXT_EX*>(&Context + 1), XSTATE_AVX, nullptr);
      FexCtx->SetXMMRegistersFromState(Thread, reinterpret_cast<const __uint128_t*>(Context.FltSave.XmmRegisters),
                                       reinterpret_cast<const __uint128_t*>(Ymm));
    } else {
      FexCtx->SetXMMRegistersFromState(Thread, reinterpret_cast<const __uint128_t*>(Context.FltSave.XmmRegisters), nullptr);
    }
    memcpy(State.mm, Context.FltSave.FloatRegisters, sizeof(State.mm));

    State.FCW = Context.FltSave.ControlWord;
    State.flags[FEXCore::X86State::X87FLAG_IE_LOC] = Context.FltSave.StatusWord & 1;
    State.flags[FEXCore::X86State::X87FLAG_C0_LOC] = (Context.FltSave.StatusWord >> 8) & 1;
    State.flags[FEXCore::X86State::X87FLAG_C1_LOC] = (Context.FltSave.StatusWord >> 9) & 1;
    State.flags[FEXCore::X86State::X87FLAG_C2_LOC] = (Context.FltSave.StatusWord >> 10) & 1;
    State.flags[FEXCore::X86State::X87FLAG_C3_LOC] = (Context.FltSave.StatusWord >> 14) & 1;
    State.flags[FEXCore::X86State::X87FLAG_TOP_LOC] = (Context.FltSave.StatusWord >> 11) & 0b111;
    State.AbridgedFTW = Context.FltSave.TagWord;
  }
}

static void ReconstructThreadState(FEXCore::Core::InternalThreadState* Thread, ARM64_NT_CONTEXT& Context) {
  const auto& Config = SignalDelegator->GetConfig();
  auto& State = Thread->CurrentFrame->State;

  State.rip = CTX->RestoreRIPFromHostPC(Thread, Context.Pc);

  // Spill all SRA GPRs
  for (size_t i = 0; i < Config.SRAGPRCount; i++) {
    State.gregs[i] = Context.X[Config.SRAGPRMapping[i]];
  }

  // Spill all SRA FPRs
  for (size_t i = 0; i < Config.SRAFPRCount; i++) {
    memcpy(State.xmm.sse.data[i], &Context.V[Config.SRAFPRMapping[i]], sizeof(__uint128_t));
  }

  // Spill EFlags
  uint32_t EFlags = CTX->ReconstructCompactedEFLAGS(Thread, true, Context.X, Context.Cpsr);
  CTX->SetFlagsFromCompactedEFLAGS(Thread, EFlags);
}

// Reconstructs an x64 context from the input thread's state, packed into a regular ARM64 context following the ARM64EC register mapping
static ARM64_NT_CONTEXT StoreStateToPackedECContext(FEXCore::Core::InternalThreadState* Thread, uint32_t FPCR, uint32_t FPSR) {
  ARM64_NT_CONTEXT ECContext {};

  ECContext.ContextFlags = CONTEXT_ARM64_FULL;
  if (CPUFeatures->IsFeaturePresent(PF_AVX2_INSTRUCTIONS_AVAILABLE)) {
    // This is a FEX extension and requires corresponding wine-side patches to be of use, however it is harmless to set
    // even if those patches are not used.
    ECContext.ContextFlags |= CONTEXT_ARM64_FEX_YMMSTATE;
  }

  auto& State = Thread->CurrentFrame->State;

  ECContext.X8 = State.gregs[FEXCore::X86State::REG_RAX];
  ECContext.X0 = State.gregs[FEXCore::X86State::REG_RCX];
  ECContext.X1 = State.gregs[FEXCore::X86State::REG_RDX];
  ECContext.X27 = State.gregs[FEXCore::X86State::REG_RBX];
  ECContext.Sp = State.gregs[FEXCore::X86State::REG_RSP];
  ECContext.Fp = State.gregs[FEXCore::X86State::REG_RBP];
  ECContext.X25 = State.gregs[FEXCore::X86State::REG_RSI];
  ECContext.X26 = State.gregs[FEXCore::X86State::REG_RDI];
  ECContext.X2 = State.gregs[FEXCore::X86State::REG_R8];
  ECContext.X3 = State.gregs[FEXCore::X86State::REG_R9];
  ECContext.X4 = State.gregs[FEXCore::X86State::REG_R10];
  ECContext.X5 = State.gregs[FEXCore::X86State::REG_R11];
  ECContext.X19 = State.gregs[FEXCore::X86State::REG_R12];
  ECContext.X20 = State.gregs[FEXCore::X86State::REG_R13];
  ECContext.X21 = State.gregs[FEXCore::X86State::REG_R14];
  ECContext.X22 = State.gregs[FEXCore::X86State::REG_R15];

  ECContext.Pc = State.rip;

  CTX->ReconstructXMMRegisters(Thread, reinterpret_cast<__uint128_t*>(&ECContext.V[0]), reinterpret_cast<__uint128_t*>(&ECContext.V[16]));

  ECContext.Lr = State.mm[0][0];
  ECContext.X6 = State.mm[1][0];
  ECContext.X7 = State.mm[2][0];
  ECContext.X9 = State.mm[3][0];
  ECContext.X16 = (State.mm[3][1] & 0xffff) << 48 | (State.mm[2][1] & 0xffff) << 32 | (State.mm[1][1] & 0xffff) << 16 | (State.mm[0][1] & 0xffff);
  ECContext.X10 = State.mm[4][0];
  ECContext.X11 = State.mm[5][0];
  ECContext.X12 = State.mm[6][0];
  ECContext.X15 = State.mm[7][0];
  ECContext.X17 = (State.mm[7][1] & 0xffff) << 48 | (State.mm[6][1] & 0xffff) << 32 | (State.mm[5][1] & 0xffff) << 16 | (State.mm[4][1] & 0xffff);

  // Zero all disallowed registers
  ECContext.X13 = 0;
  ECContext.X14 = 0;
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(ECContext.X18));
  ECContext.X23 = 0;
  ECContext.X24 = 0;
  ECContext.X28 = 0;

  // NZCV+SS will be converted into EFlags by ntdll, the rest are lost during exception handling.
  // See HandleGuestException
  uint32_t EFlags = CTX->ReconstructCompactedEFLAGS(Thread, false, nullptr, 0);
  ECContext.Cpsr = 0;
  ECContext.Cpsr |= (EFlags & (1U << FEXCore::X86State::RFLAG_TF_RAW_LOC)) ? (1U << 21) : 0;
  ECContext.Cpsr |= (EFlags & (1U << FEXCore::X86State::RFLAG_OF_RAW_LOC)) ? (1U << 28) : 0;
  ECContext.Cpsr |= (EFlags & (1U << FEXCore::X86State::RFLAG_CF_RAW_LOC)) ? (1U << 29) : 0;
  ECContext.Cpsr |= (EFlags & (1U << FEXCore::X86State::RFLAG_ZF_RAW_LOC)) ? (1U << 30) : 0;
  ECContext.Cpsr |= (EFlags & (1U << FEXCore::X86State::RFLAG_SF_RAW_LOC)) ? (1U << 31) : 0;

  ECContext.Fpcr = FPCR;
  ECContext.Fpsr = FPSR;

  return ECContext;
}

static void RethrowGuestException(const EXCEPTION_RECORD& Rec, ARM64_NT_CONTEXT& Context) {
  const auto& Config = SignalDelegator->GetConfig();
  auto* Thread = GetCPUArea().ThreadState();
  auto& Fault = Thread->CurrentFrame->SynchronousFaultData;
  uint64_t GuestSp = Context.X[Config.SRAGPRMapping[static_cast<size_t>(FEXCore::X86State::REG_RSP)]];
  auto* Args = reinterpret_cast<KiUserExceptionDispatcherStackLayout*>(FEXCore::AlignDown(GuestSp, 64)) - 1;

  LogMan::Msg::DFmt("Reconstructing context");
  if (!IsDispatcherAddress(Context.Pc)) {
    ReconstructThreadState(Thread, Context);
  }
  Args->Context = StoreStateToPackedECContext(Thread, Context.Fpcr, Context.Fpsr);
  LogMan::Msg::DFmt("pc: {:X} rip: {:X}", Context.Pc, Args->Context.Pc);

  // X64 Windows always clears TF, DF and AF when handling an exception, restoring after.
  // Current ARM64EC windows can only restore NZCV+SS when returning from an exception and other flags are left untouched from the handler context.
  // TODO: Can extend wine to support this by mapping the remaining EFlags into reserved cpsr members.
  uint32_t EFlags = CTX->ReconstructCompactedEFLAGS(Thread, false, nullptr, 0);
  EFlags &= ~(1 << FEXCore::X86State::RFLAG_TF_RAW_LOC);
  CTX->SetFlagsFromCompactedEFLAGS(Thread, EFlags);

  Args->Rec = FEX::Windows::HandleGuestException(Fault, Rec, Args->Context.Pc, Args->Context.X8);
  if (Args->Rec.ExceptionCode == EXCEPTION_SINGLE_STEP) {
    Args->Context.Cpsr &= ~(1 << 21); // PSTATE.SS
  } else if (Args->Rec.ExceptionCode == EXCEPTION_BREAKPOINT) {
    // INT3 will set RIP to the instruction following it, undo this (any edge cases with multibyte instructions that trigger breakpoints are bugs present in Windows also)
    Args->Context.Pc -= 1;
  }

  Context.Sp = reinterpret_cast<uint64_t>(Args);
  Context.Pc = KiUserExceptionDispatcher;
}

class ECSyscallHandler : public FEXCore::HLE::SyscallHandler, public FEXCore::Allocator::FEXAllocOperators {
public:
  ECSyscallHandler() {
    OSABI = FEXCore::HLE::SyscallOSABI::OS_GENERIC;
  }

  uint64_t HandleSyscall(FEXCore::Core::CpuStateFrame* Frame, FEXCore::HLE::SyscallArguments* Args) override {
    ProcessPendingCrossProcessEmulatorWork();

    // Manually raise an exeption with the current JIT state packed into a native context, ntdll handles this and
    // reenters the JIT (see dlls/ntdll/signal_arm64ec.c in wine).
    uint64_t FPCR, FPSR;
    __asm volatile("mrs %[fpcr], fpcr" : [fpcr] "=r"(FPCR));
    __asm volatile("mrs %[fpsr], fpsr" : [fpsr] "=r"(FPSR));

    auto* Thread = GetCPUArea().ThreadState();
    KiUserExceptionDispatcherStackLayout DispatchArgs {
      .Context = StoreStateToPackedECContext(Thread, static_cast<uint32_t>(FPCR), static_cast<uint32_t>(FPSR)),
      .Rec = {.ExceptionCode = STATUS_EMULATION_SYSCALL}};
    // PC is expected to hold the return address after the thunk, so skip over the INT 2E/SYSCALL instruction.
    DispatchArgs.Context.Pc += 2;
    JumpSetStack(KiUserExceptionDispatcher, reinterpret_cast<uintptr_t>(&DispatchArgs));
  }

  std::optional<FEXCore::ExecutableFileSectionInfo> LookupExecutableFileSection(FEXCore::Core::InternalThreadState*, uint64_t Address) override {
    return ImageTracker->LookupExecutableFileSection(Address);
  }

  void MarkGuestExecutableRange(FEXCore::Core::InternalThreadState* Thread, uint64_t Start, uint64_t Length) override {
    InvalidationTracker->ReprotectRWXIntervals(Start, Length);
  }

  void InvalidateGuestCodeRange(FEXCore::Core::InternalThreadState* Thread, uint64_t Start, uint64_t Length) override {
    InvalidationTracker->InvalidateAlignedInterval(Start, Length, false);
  }

  void MarkOvercommitRange(uint64_t Start, uint64_t Length) override {
    OvercommitTracker->MarkRange(Start, Length);
  }

  void UnmarkOvercommitRange(uint64_t Start, uint64_t Length) override {
    OvercommitTracker->UnmarkRange(Start, Length);
  }

  FEXCore::HLE::ExecutableRangeInfo QueryGuestExecutableRange(FEXCore::Core::InternalThreadState* Thread, uint64_t Address) override {
    return InvalidationTracker->QueryExecutableRange(Address);
  }

  void PreCompile() override {
    ProcessPendingCrossProcessEmulatorWork();
  }
};

void SetKiUserExceptionDispatcher(uintptr_t Addr) {
  KiUserExceptionDispatcher = Addr;
}
} // namespace Exception

#if FEX_ON_WINE_APPLE
static void FinishWineAppleProcessInit() {
  const auto NtDll = reinterpret_cast<HMODULE>(NtDllBase);

  SignalDelegator = fextl::make_unique<FEX::DummyHandlers::DummySignalDelegator>();
  SyscallHandler = fextl::make_unique<Exception::ECSyscallHandler>();
  CTX->SetSignalDelegator(SignalDelegator.get());
  CTX->SetSyscallHandler(SyscallHandler.get());

  Exception::HandlerConfig.emplace(*CTX);
  InvalidationTracker.emplace(*CTX, Threads);
  ImageTracker.emplace(*CTX, false);

  const auto MainModule = reinterpret_cast<uintptr_t>(reinterpret_cast<__TEB*>(NtCurrentTeb())->Peb->ImageBaseAddress);
  HandleImageMap(MainModule, true);
  HandleImageMap(NtDllBase);

  CPUFeatures.emplace(*CTX);

  X64ReturnInstr = FEXWineAppleMmap(FEXCore::Utils::FEX_PAGE_SIZE);
  if (X64ReturnInstr) {
    FEXWineAppleMprotect(X64ReturnInstr, FEXCore::Utils::FEX_PAGE_SIZE, 7);
    InvalidationTracker->HandleMemoryProtectionNotification(reinterpret_cast<uint64_t>(X64ReturnInstr), FEXCore::Utils::FEX_PAGE_SIZE,
                                                            PAGE_EXECUTE_READ);
    *reinterpret_cast<uint8_t*>(X64ReturnInstr) = 0xc3;
  }

  const uintptr_t KiUserExceptionDispatcherFFS = reinterpret_cast<uintptr_t>(FEXGetExportByName(NtDll, "KiUserExceptionDispatcher"));
  if (KiUserExceptionDispatcherFFS && NtDllRedirectionLUT) {
    Exception::SetKiUserExceptionDispatcher(NtDllRedirectionLUT[KiUserExceptionDispatcherFFS - NtDllBase] + NtDllBase);
  }
}
#endif

// Persist the current JIT GPR state into ContextAmd64 before leaving simulation.
extern "C" void StoreJitStateToContextAmd64() {
  FEXSyncTebX18();
#if !FEX_ON_WINE_APPLE
  ProcessPendingCrossProcessEmulatorWork();
#endif
  const auto CPUArea = GetCPUArea();
  auto* Thread = CPUArea.ThreadState();
  FEXCore::Core::CpuStateFrame* Frame = Thread ? Thread->CurrentFrame : CPUArea.StateFrame();
  if (!Frame || !CPUArea.Area || !CPUArea.Area->ContextAmd64) {
    return;
  }

  auto& State = Frame->State;
  auto& Ctx = CPUArea.ContextAmd64().AMD64_Context;
  Ctx.ContextFlags |= CONTEXT_INTEGER | CONTEXT_CONTROL;
  Ctx.Rax = State.gregs[FEXCore::X86State::REG_RAX];
  Ctx.Rcx = State.gregs[FEXCore::X86State::REG_RCX];
  Ctx.Rdx = State.gregs[FEXCore::X86State::REG_RDX];
  Ctx.Rbx = State.gregs[FEXCore::X86State::REG_RBX];
  Ctx.Rsp = State.gregs[FEXCore::X86State::REG_RSP];
  Ctx.Rbp = State.gregs[FEXCore::X86State::REG_RBP];
  Ctx.Rsi = State.gregs[FEXCore::X86State::REG_RSI];
  Ctx.Rdi = State.gregs[FEXCore::X86State::REG_RDI];
  Ctx.R8 = State.gregs[FEXCore::X86State::REG_R8];
  Ctx.R9 = State.gregs[FEXCore::X86State::REG_R9];
  Ctx.R10 = State.gregs[FEXCore::X86State::REG_R10];
  Ctx.R11 = State.gregs[FEXCore::X86State::REG_R11];
  Ctx.R12 = State.gregs[FEXCore::X86State::REG_R12];
  Ctx.R13 = State.gregs[FEXCore::X86State::REG_R13];
  Ctx.R14 = State.gregs[FEXCore::X86State::REG_R14];
  Ctx.R15 = State.gregs[FEXCore::X86State::REG_R15];
  Ctx.Rip = State.rip;
}

// Marshal x64 JIT GPR state into ARM64EC CPU registers before calling an entry thunk.
// x9 must already hold the target function address; x17 holds the entry thunk.
extern "C" void ApplyJitStateToCpuForEcEntry() {
  FEXSyncTebX18();
#if !FEX_ON_WINE_APPLE
  ProcessPendingCrossProcessEmulatorWork();
#endif
  const auto CPUArea = GetCPUArea();
  auto* Thread = CPUArea.ThreadState();
  FEXCore::Core::CpuStateFrame* Frame = Thread ? Thread->CurrentFrame : CPUArea.StateFrame();
  const CONTEXT* Amd64Ctx = (CPUArea.Area && CPUArea.Area->ContextAmd64) ? &CPUArea.ContextAmd64().AMD64_Context : nullptr;

  uint64_t x0 {};
  uint64_t x1 {};
  uint64_t x2 {};
  uint64_t x3 {};
  uint64_t x5 {};
  uint64_t x8 {};
  uint64_t x19 {};
  uint64_t x20 {};
  uint64_t x21 {};
  uint64_t x22 {};
  uint64_t x25 {};
  uint64_t x26 {};
  uint64_t x27 {};
  uint64_t fp {};
  uint64_t sp {};

  if (Frame) {
    auto& State = Frame->State;
    x0 = State.gregs[FEXCore::X86State::REG_RCX];
    x1 = State.gregs[FEXCore::X86State::REG_RDX];
    x2 = State.gregs[FEXCore::X86State::REG_R8];
    x3 = State.gregs[FEXCore::X86State::REG_R9];
    x5 = State.gregs[FEXCore::X86State::REG_R11];
    x8 = State.gregs[FEXCore::X86State::REG_RAX];
    x19 = State.gregs[FEXCore::X86State::REG_R12];
    x20 = State.gregs[FEXCore::X86State::REG_R13];
    x21 = State.gregs[FEXCore::X86State::REG_R14];
    x22 = State.gregs[FEXCore::X86State::REG_R15];
    x25 = State.gregs[FEXCore::X86State::REG_RSI];
    x26 = State.gregs[FEXCore::X86State::REG_RDI];
    x27 = State.gregs[FEXCore::X86State::REG_RBX];
    fp = State.gregs[FEXCore::X86State::REG_RBP];
    sp = State.gregs[FEXCore::X86State::REG_RSP];
  } else if (Amd64Ctx && (Amd64Ctx->ContextFlags & CONTEXT_INTEGER)) {
    x0 = Amd64Ctx->Rcx;
    x1 = Amd64Ctx->Rdx;
    x2 = Amd64Ctx->R8;
    x3 = Amd64Ctx->R9;
    x5 = Amd64Ctx->R11;
    x8 = Amd64Ctx->Rax;
    x19 = Amd64Ctx->R12;
    x20 = Amd64Ctx->R13;
    x21 = Amd64Ctx->R14;
    x22 = Amd64Ctx->R15;
    x25 = Amd64Ctx->Rsi;
    x26 = Amd64Ctx->Rdi;
    x27 = Amd64Ctx->Rbx;
    fp = Amd64Ctx->Rbp;
    if (Amd64Ctx->ContextFlags & CONTEXT_CONTROL) {
      sp = Amd64Ctx->Rsp;
    }
  } else {
    __wine_dbg_output( "ApplyJitStateToCpuForEcEntry: no thread state\n" );
    return;
  }

  if (!sp) {
    __asm__ volatile( "mov %0, sp" : "=r"( sp ) );
  }

#if FEX_ON_WINE_APPLE
  // Do not write x19–x29: those are C callee-saved / FP. Setting x29 here
  // made the epilogue pop [guest RBP] and br to CHPE Area+0x50 (hn4).
  (void)sp;
  (void)fp;
  (void)x5;
  (void)x19;
  (void)x20;
  (void)x21;
  (void)x22;
  (void)x25;
  (void)x26;
  (void)x27;
  __asm__ volatile("mov x0, %0\n\t"
                   "mov x1, %1\n\t"
                   "mov x2, %2\n\t"
                   "mov x3, %3\n\t"
                   "mov x8, %4\n"
                   :
                   : "r"(x0), "r"(x1), "r"(x2), "r"(x3), "r"(x8)
                   : "x0", "x1", "x2", "x3", "x8");
#else
  __asm__ volatile("mov x0, %0\n\t"
                   "mov x1, %1\n\t"
                   "mov x2, %2\n\t"
                   "mov x3, %3\n"
                   : : "r"(x0), "r"(x1), "r"(x2), "r"(x3)
                   : "x0", "x1", "x2", "x3");
  __asm__ volatile("mov x4, %0\n\t"
                   "mov x5, %1\n\t"
                   "mov x8, %2\n\t"
                   "mov x19, %3\n"
                   : : "r"(sp), "r"(x5), "r"(x8), "r"(x19)
                   : "x4", "x5", "x8", "x19");
  __asm__ volatile("mov x20, %0\n\t"
                   "mov x21, %1\n\t"
                   "mov x22, %2\n\t"
                   "mov x25, %3\n"
                   : : "r"(x20), "r"(x21), "r"(x22), "r"(x25)
                   : "x20", "x21", "x22", "x25");
  __asm__ volatile("mov x26, %0\n\t"
                   "mov x27, %1\n\t"
                   "mov x29, %2\n"
                   : : "r"(x26), "r"(x27), "r"(fp)
                   : "x26", "x27", "x29");
#endif
}

extern "C" void SyncThreadContext(CONTEXT* Context) {
  // TEB first: hybrid ProcessPending import can clobber x18; wine-apple needs tpidr/x18.
  FEXSyncTebX18();
#if FEX_ON_WINE_APPLE
  // Full LoadStateFromECContext (XMM/segments/EFlags via CTX vtable) faults under
  // wine-apple (gate el addr 0x100001 in SetXMM). Minimal integer+control only.
  if (!Context) {
    return;
  }
  const auto CPUArea = GetCPUArea();
  if (!CPUArea.valid()) {
    return;
  }
  auto* Thread = CPUArea.ThreadState();
  if (!Thread || !Thread->CurrentFrame) {
    return;
  }
  auto& State = Thread->CurrentFrame->State;
  if ((Context->ContextFlags & CONTEXT_INTEGER) == CONTEXT_INTEGER) {
    State.gregs[FEXCore::X86State::REG_RAX] = Context->Rax;
    State.gregs[FEXCore::X86State::REG_RCX] = Context->Rcx;
    State.gregs[FEXCore::X86State::REG_RDX] = Context->Rdx;
    State.gregs[FEXCore::X86State::REG_RBX] = Context->Rbx;
    State.gregs[FEXCore::X86State::REG_RSI] = Context->Rsi;
    State.gregs[FEXCore::X86State::REG_RDI] = Context->Rdi;
    State.gregs[FEXCore::X86State::REG_R8] = Context->R8;
    State.gregs[FEXCore::X86State::REG_R9] = Context->R9;
    State.gregs[FEXCore::X86State::REG_R10] = Context->R10;
    State.gregs[FEXCore::X86State::REG_R11] = Context->R11;
    State.gregs[FEXCore::X86State::REG_R12] = Context->R12;
    State.gregs[FEXCore::X86State::REG_R13] = Context->R13;
    State.gregs[FEXCore::X86State::REG_R14] = Context->R14;
    State.gregs[FEXCore::X86State::REG_R15] = Context->R15;
  }
  if ((Context->ContextFlags & CONTEXT_CONTROL) == CONTEXT_CONTROL) {
    State.rip = Context->Rip;
    State.gregs[FEXCore::X86State::REG_RSP] = Context->Rsp;
    State.gregs[FEXCore::X86State::REG_RBP] = Context->Rbp;
  }
  // BeginSimulation reloads TEB from x18 after return; Darwin C clobbers x18.
  FEXSyncTebX18();
  return;
#else
  ProcessPendingCrossProcessEmulatorWork();
  const auto CPUArea = GetCPUArea();
  auto* FexCtx = GetFEXContext();
  if (!Context || !FexCtx || !CPUArea.valid()) {
    return;
  }
  auto* Thread = CPUArea.ThreadState();
  if (!Thread || !Thread->CurrentFrame) {
    return;
  }
  // All other EFlags bits are lost when converting to/from an ARM64EC context, so merge them in from the current JIT state.
  // This is advisable over dropping their values as thread suspend/resume uses this function, and that can happen at any point in guest code.
  static constexpr uint32_t ECValidEFlagsMask {(1U << FEXCore::X86State::RFLAG_OF_RAW_LOC) | (1U << FEXCore::X86State::RFLAG_CF_RAW_LOC) |
                                               (1U << FEXCore::X86State::RFLAG_ZF_RAW_LOC) | (1U << FEXCore::X86State::RFLAG_SF_RAW_LOC) |
                                               (1U << FEXCore::X86State::RFLAG_TF_RAW_LOC)};

  uint32_t StateEFlags = FexCtx->ReconstructCompactedEFLAGS(Thread, false, nullptr, 0);
  Context->EFlags = (Context->EFlags & ECValidEFlagsMask) | (StateEFlags & ~ECValidEFlagsMask);
  Exception::LoadStateFromECContext(Thread, *Context);
#endif
}

NTSTATUS ProcessInit() {
  InitSyscalls();
#if FEX_ON_WINE_APPLE && defined(FEX_DEBUG_PROCESSINIT_STAGES)
  // Kept for bisect only — do NOT enable in normal builds (skips ThreadInit).
  return STATUS_SUCCESS;
#endif

#if FEX_ON_WINE_APPLE
  // Capture TEB once before any Darwin SVC. Re-resolving after write(2) can see
  // tpidr residue (0x1002/0x1003) and permanently lose the real TEB.
  const uintptr_t ProcessSavedTeb = FEXWineAppleSaveTeb();
  if (FEXIsPlausibleWineTeb(ProcessSavedTeb)) {
    FEXWineAppleRestoreTeb(ProcessSavedTeb);
  }
  // Host write(2) only — __wine_dbg_output can fault this early (c000001d in ntdll).
  auto FEXPiLog = [ProcessSavedTeb](const char* Msg) {
    const size_t Len = strlen(Msg);
    register uint64_t x0 __asm__("x0") = 2; /* stderr */
    register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
    register uint64_t x2 __asm__("x2") = static_cast<uint64_t>(Len);
    register uint64_t x16 __asm__("x16") = 4; /* SYS_write */
    __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
    FEXWineAppleRestoreTeb(ProcessSavedTeb);
  };
  FEXPiLog("FEX ProcessInit: after InitSyscalls\n");
  // Skip Config::Initialize (MetaLayer/map faults early). GetConv null-checks Meta
  // and Getters use compile-time defaults. Set after context exists if needed.

  FEXPiLog("FEX ProcessInit: before FetchHostFeatures\n");
  const auto HostFeatures = FEX::Windows::CPUFeatures::FetchHostFeaturesWineApple();
  FEXPiLog("FEX ProcessInit: after FetchHostFeatures\n");
  FEXPiLog("FEX ProcessInit: before CreateNewContext\n");
  // Do not assign file-scope CTX (RO .rdata on 16k pages). Stack raw pointer only this gate.
  FEXCore::Context::Context* WineAppleCTX {};
  {
    auto Tmp = FEXCore::Context::Context::CreateNewContext(HostFeatures);
    WineAppleCTX = Tmp.release();
  }
  if (!WineAppleCTX) {
    FEXPiLog("FEX ProcessInit: CreateNewContext FAILED\n");
    return STATUS_NO_MEMORY;
  }
  FEXPiLog("FEX ProcessInit: after CreateNewContext\n");
  // No function-local statics (magic-static __cxa_guard → c000001d). Host-bump + placement-new.
  {
    void* SigMem = FEXCore::Allocator::aligned_alloc(alignof(FEX::DummyHandlers::DummySignalDelegator),
                                                     sizeof(FEX::DummyHandlers::DummySignalDelegator));
    void* SysMem = FEXCore::Allocator::aligned_alloc(alignof(Exception::ECSyscallHandler), sizeof(Exception::ECSyscallHandler));
    if (!SigMem || !SysMem) {
      FEXPiLog("FEX ProcessInit: handler alloc FAILED\n");
      return STATUS_NO_MEMORY;
    }
    auto* BootstrapSignalDelegator = ::new (SigMem) FEX::DummyHandlers::DummySignalDelegator();
    FEXPiLog("FEX ProcessInit: after SignalDelegator ctor\n");
    auto* BootstrapSyscallHandler = ::new (SysMem) Exception::ECSyscallHandler();
    FEXPiLog("FEX ProcessInit: after SyscallHandler ctor\n");
    WineAppleCTX->SetSignalDelegator(BootstrapSignalDelegator);
    WineAppleCTX->SetSyscallHandler(BootstrapSyscallHandler);
  }
  FEXPiLog("FEX ProcessInit: before InitCore\n");
  WineAppleCTX->InitCore();
  FEXPiLog("FEX ProcessInit: after InitCore\n");

  // Stash for ThreadInit (file-scope CTX unique_ptr is RO .rdata — unusable).
  FEXCore::Allocator::SetWineAppleContext(WineAppleCTX);
  FEXPiLog("FEX ProcessInit: after SetWineAppleContext\n");

  // Skip InitCRTProcess / full FinishWineApple (file-scope CTX + make_unique).
  // jul10ai: pre-create slab-backed x86 ret + host ARM64 stub (no PE global writes).
  if (FEXCore::Allocator::GetOrCreateX64ReturnInstr()) {
    FEXPiLog("FEX ProcessInit: X64ReturnInstr slab OK\n");
  } else {
    FEXPiLog("FEX ProcessInit: X64ReturnInstr slab FAIL\n");
  }
  FEXWineAppleEnsure();
  FEXPiLog("FEX ProcessInit: WineAppleHost OK\n");
  FEXPiLog("FEX ProcessInit: before ThreadInit\n");
  const NTSTATUS Ti = ThreadInit();
  FEXPiLog("FEX ProcessInit: after ThreadInit\n");
  return Ti;
#else
  FEX::Windows::InitCRTProcess();
  const auto NtDll = GetModuleHandle("ntdll.dll");
  const bool IsWine = !!GetProcAddress(NtDll, "wine_get_version");

  const auto ExecutableName = FEX::Windows::BaseName(FEX::Windows::GetExecutableFilePath());
  FEX::Config::LoadConfig(fextl::string {ExecutableName}, _environ, FEX::ReadPortabilityInformation());
  FEXCore::Config::ReloadMetaLayer();
  FEX::Windows::Logging::Init();

  FEXCore::Config::Set(FEXCore::Config::CONFIG_IS64BIT_MODE, "1");
  FEXCore::Profiler::Init("", "");

  SignalDelegator = fextl::make_unique<FEX::DummyHandlers::DummySignalDelegator>();
  SyscallHandler = fextl::make_unique<Exception::ECSyscallHandler>();

  OvercommitTracker.emplace(IsWine);
  FEX::Windows::SetupEnvironmentVariableValues(NtDll);
  FEX::Windows::Allocator::SetupHooks(NtDll);

  {
    auto HostFeatures = FEX::Windows::CPUFeatures::FetchHostFeatures(IsWine);
    CTX = FEXCore::Context::Context::CreateNewContext(HostFeatures);
  }

  CTX->SetSignalDelegator(SignalDelegator.get());
  CTX->SetSyscallHandler(SyscallHandler.get());
  CTX->InitCore();

  Exception::HandlerConfig.emplace(*CTX);
  InvalidationTracker.emplace(*CTX, Threads);
  ImageTracker.emplace(*CTX, false);

  const auto MainModule = reinterpret_cast<uintptr_t>(reinterpret_cast<__TEB*>(NtCurrentTeb())->Peb->ImageBaseAddress);
  HandleImageMap(MainModule, true);
  HandleImageMap(NtDllBase);
  CPUFeatures.emplace(*CTX);

  X64ReturnInstr = ::VirtualAlloc(nullptr, FEXCore::Utils::FEX_PAGE_SIZE, MEM_COMMIT, PAGE_EXECUTE_READWRITE);
  InvalidationTracker->HandleMemoryProtectionNotification(reinterpret_cast<uint64_t>(X64ReturnInstr), FEXCore::Utils::FEX_PAGE_SIZE,
                                                          PAGE_EXECUTE_READ);
  *reinterpret_cast<uint8_t*>(X64ReturnInstr) = 0xc3;

  const uintptr_t KiUserExceptionDispatcherFFS = reinterpret_cast<uintptr_t>(GetProcAddress(NtDll, "KiUserExceptionDispatcher"));
  Exception::SetKiUserExceptionDispatcher(NtDllRedirectionLUT[KiUserExceptionDispatcherFFS - NtDllBase] + NtDllBase);

  FEX_CONFIG_OPT(TSOEnabled, TSOENABLED);
  if (TSOEnabled()) {
    BOOL Enable = TRUE;
    NTSTATUS Status = NtSetInformationProcess(NtCurrentProcess(), ProcessFexHardwareTso, &Enable, sizeof(Enable));
    if (Status == STATUS_SUCCESS) {
      CTX->SetHardwareTSOSupport(true);
    }
  }

  FEX_CONFIG_OPT(ProfileStats, PROFILESTATS);
  FEX_CONFIG_OPT(StartupSleep, STARTUPSLEEP);
  FEX_CONFIG_OPT(StartupSleepProcName, STARTUPSLEEPPROCNAME);

  if (IsWine && ProfileStats()) {
    StatAllocHandler = fextl::make_unique<FEX::Windows::StatAlloc>(FEXCore::SHMStats::AppType::WIN_ARM64EC);
  }

  if (StartupSleep() && (StartupSleepProcName().empty() || ExecutableName == StartupSleepProcName())) {
    LogMan::Msg::IFmt("[{}][{}] Sleeping for {} seconds", GetCurrentProcessId(), ExecutableName, StartupSleep());
    std::this_thread::sleep_for(std::chrono::seconds(StartupSleep()));
  }

  return STATUS_SUCCESS;
#endif
}

void ProcessTerm(HANDLE Handle, BOOL After, NTSTATUS Status) {}

class ScopedCallbackDisable {
private:
  bool Prev;

public:
  ScopedCallbackDisable() {
    const auto CPUArea = GetCPUArea();
    if (!CPUArea.valid()) {
      Prev = false;
      return;
    }
    Prev = CPUArea.Area->InSyscallCallback;
    CPUArea.Area->InSyscallCallback = true;
  }

  ~ScopedCallbackDisable() {
    const auto CPUArea = GetCPUArea();
    if (!CPUArea.valid()) {
      return;
    }
    CPUArea.Area->InSyscallCallback = Prev;
  }
};

// Returns true if exception dispatch should be halted and the execution context restored to NativeContext
bool ResetToConsistentStateImpl(const ThreadCPUArea CPUArea, EXCEPTION_RECORD* Exception, CONTEXT* GuestContext, ARM64_NT_CONTEXT* NativeContext) {
  auto Thread = CPUArea.ThreadState();
  FEXCORE_PROFILE_ACCUMULATION(Thread, AccumulatedSignalTime);
  LogMan::Msg::DFmt("Exception: Code: {:X} Address: {:X}", Exception->ExceptionCode, reinterpret_cast<uintptr_t>(Exception->ExceptionAddress));

  if (NativeContext->Pc == reinterpret_cast<uint64_t>(&ExitFunctionSuspendPoint)) {
    // A suspend interrupt can occur in ExitFunctionEC before InSimulation is unset and set SuspendDoorbell. If this
    // occurs then it is still our duty to cooperatively suspend with an appropriate context. To support this, after
    // unsetting InSimulation a brk #0xCAFE instruction will be raised that we can handle here.
    NativeContext->Pc = reinterpret_cast<uintptr_t>(&ExitFunctionSuspendResumePoint); // Jump to the suspend resume point.
    *CPUArea.Area->SuspendDoorbell = 0;
    return true;
  }

  if (Exception->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
    const auto FaultAddress = static_cast<uint64_t>(Exception->ExceptionInformation[1]);

    if (FEX::Windows::CallRetStack::HandleAccessViolation(Thread, FaultAddress, NativeContext->X17)) {
      return true;
    }

    if (FEX::Windows::JITGuardPage::HandleJITGuardPage(Thread, reinterpret_cast<void*>(FaultAddress), NativeContext->X,
                                                       reinterpret_cast<__uint128_t*>(NativeContext->V), &NativeContext->Pc)) {
      return true;
    }

    std::scoped_lock Lock(ThreadCreationMutex);
    if (InvalidationTracker && InvalidationTracker->HandleRWXAccessViolation(Thread, NativeContext->Pc, FaultAddress)) {
      FEXCORE_PROFILE_INSTANT_INCREMENT(Thread, AccumulatedSMCCount, 1);
      if (CTX->IsAddressInCodeBuffer(Thread, NativeContext->Pc) && !CTX->IsCurrentBlockSingleInst(CPUArea.ThreadState()) &&
          CTX->IsAddressInCurrentBlock(Thread, FaultAddress & FEXCore::Utils::FEX_PAGE_MASK, FEXCore::Utils::FEX_PAGE_SIZE)) {
        // If we are not patching ourself (single inst block case) and potentially patching the current block, this is inline SMC. Reconstruct the current context (before the SMC write) then single step the write to reduce it to regular SMC.
        Exception::ReconstructThreadState(Thread, *NativeContext);
        LogMan::Msg::DFmt("Handled inline self-modifying code: pc: {:X} rip: {:X} fault: {:X}", NativeContext->Pc,
                          Thread->CurrentFrame->State.rip, FaultAddress);
        NativeContext->Pc = CPUArea.DispatcherLoopTopEnterECFillSRA();
        NativeContext->Sp = CPUArea.EmulatorStackBase();
        NativeContext->X11 = 1;                                        // Set ENTRY_FILL_SRA_SINGLE_INST_REG to force a single step
        NativeContext->X17 = reinterpret_cast<uint64_t>(CPUArea.Area); // Set EC_ENTRY_CPUAREA_REG
      } else {
        LogMan::Msg::DFmt("Handled self-modifying code: pc: {:X} fault: {:X}", NativeContext->Pc, FaultAddress);
      }

      return true;
    }
  }

  bool IsJIT = CTX->IsAddressInCodeBuffer(Thread, NativeContext->Pc);
  if (Exception->ExceptionCode == EXCEPTION_DATATYPE_MISALIGNMENT && Exception::HandleUnalignedAccess(CPUArea, *NativeContext, IsJIT)) {
    LogMan::Msg::DFmt("Handled unaligned atomic: new pc: {:X}", NativeContext->Pc);
    return true;
  }

  if (!IsJIT && !IsDispatcherAddress(NativeContext->Pc)) {
    LogMan::Msg::DFmt("Passing through exception");
    return false;
  }

  // The JIT (in CompileBlock) emits code to check the suspend doorbell at the start of every block, and run the following instruction if it is set:
  static constexpr uint32_t SuspendTrapMagic {0xD4395FC0}; // brk #0xCAFE
  if (Exception->ExceptionCode == EXCEPTION_ILLEGAL_INSTRUCTION && *reinterpret_cast<uint32_t*>(NativeContext->Pc) == SuspendTrapMagic) {
    Exception::ReconstructThreadState(Thread, *NativeContext);
    *NativeContext = Exception::StoreStateToPackedECContext(Thread, NativeContext->Fpcr, NativeContext->Fpsr);
    LogMan::Msg::DFmt("Suspending: RIP: {:X} SP: {:X}", NativeContext->Pc, NativeContext->Sp);
    CPUArea.Area->InSimulation = 0;
    *CPUArea.Area->SuspendDoorbell = 0;
    return true;
  }

  if (IsEmulatorStackAddress(CPUArea, reinterpret_cast<uint64_t>(__builtin_frame_address(0)))) {
    Exception::RethrowGuestException(*Exception, *NativeContext);
    LogMan::Msg::DFmt("Rethrowing onto guest stack: {:X}", NativeContext->Sp);
    return true;
  } else {
    LogMan::Msg::EFmt("Unexpected exception in JIT code on guest stack");
    return false;
  }
}

NTSTATUS ResetToConsistentState(EXCEPTION_RECORD* Exception, CONTEXT* GuestContext, ARM64_NT_CONTEXT* NativeContext) {
  FEXSyncTebX18();
  bool Cont {};
  if (Exception->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
    const auto FaultAddress = static_cast<uint64_t>(Exception->ExceptionInformation[1]);

    if (OvercommitTracker) {
      {
        ScopedCallbackDisable guard;
        Cont = OvercommitTracker->HandleAccessViolation(FaultAddress);
      }
      if (Cont) {
        NtContinueNative(NativeContext, false);
      }
    }
  }

  const auto CPUArea = GetCPUArea();
  if (!CPUArea.ThreadState()) {
    return STATUS_SUCCESS;
  }

  {
    ScopedCallbackDisable guard;
    Cont = ResetToConsistentStateImpl(CPUArea, Exception, GuestContext, NativeContext);
  }

  if (Cont) {
    NtContinueNative(NativeContext, false);
  }

  CPUArea.Area->InSimulation = false;
  CPUArea.Area->InSyscallCallback = false;
  return STATUS_SUCCESS;
}

void NotifyMemoryAlloc(void* Address, SIZE_T Size, ULONG Type, ULONG Prot, BOOL After, NTSTATUS Status) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  if (!After) {
    ThreadCreationMutex.lock();
  } else {
    // MEM_RESET(_UNDO) ignores the passed permissions
    if (!Status && !(Type & (MEM_RESET | MEM_RESET_UNDO))) {
      InvalidationTracker->HandleMemoryProtectionNotification(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), Prot);
    }
    ThreadCreationMutex.unlock();
  }
}

void NotifyMemoryFree(void* Address, SIZE_T Size, ULONG FreeType, BOOL After, NTSTATUS Status) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  if (!After) {
    ThreadCreationMutex.lock();
  } else {
    if (!Status) {
      InvalidationTracker->InvalidateAlignedInterval(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), true);
    }
    ThreadCreationMutex.unlock();
  }
}

void NotifyMemoryProtect(void* Address, SIZE_T Size, ULONG NewProt, BOOL After, NTSTATUS Status) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

#if FEX_ON_WINE_APPLE
  // Wine ntdll hybrid metadata patching calls NtProtectVirtualMemory synchronously;
  // invalidation here can recurse through arm64x_check_call during bring-up.
  (void)Address;
  (void)Size;
  (void)NewProt;
  (void)After;
  (void)Status;
  return;
#endif

  if (!After) {
    ThreadCreationMutex.lock();
  } else {
    if (!Status) {
      InvalidationTracker->HandleMemoryProtectionNotification(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), NewProt);
    }
    ThreadCreationMutex.unlock();
  }
}

NTSTATUS NotifyMapViewOfSection(void* Unk1, void* Address, void* Unk2, SIZE_T Size, ULONG AllocType, ULONG Prot) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return STATUS_SUCCESS;
  }

#if FEX_ON_WINE_APPLE
  // Defer image tracking until loader_init completes; HandleImageMap during
  // kernel32 bring-up can recurse through hybrid thunks / incomplete IATs.
  (void)Unk1;
  (void)Address;
  (void)Unk2;
  (void)Size;
  (void)AllocType;
  (void)Prot;
  return STATUS_SUCCESS;
#endif

  {
    std::scoped_lock Lock(ThreadCreationMutex);
    HandleImageMap(reinterpret_cast<uint64_t>(Address));
  }


  return STATUS_SUCCESS;
}

void NotifyUnmapViewOfSection(void* Address, BOOL After, NTSTATUS Status) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  if (!After) {
    ThreadCreationMutex.lock();
    auto [Start, Size] = InvalidationTracker->InvalidateContainingSection(reinterpret_cast<uint64_t>(Address), true);
    if (Size) {
      HandleImageUnmap(Start, Size);
    }
  } else {
    ThreadCreationMutex.unlock();
  }
}

void FlushInstructionCacheHeavy(const void* Address, SIZE_T Size) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  std::scoped_lock Lock(ThreadCreationMutex);
  InvalidationTracker->InvalidateAlignedInterval(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), false);
}

void BTCpu64FlushInstructionCache(const void* Address, SIZE_T Size) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  std::scoped_lock Lock(ThreadCreationMutex);
  InvalidationTracker->InvalidateAlignedInterval(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), false);
}

void BTCpu64NotifyMemoryDirty(void* Address, SIZE_T Size) {
  if (!InvalidationTracker || !GetCPUArea().ThreadState()) {
    return;
  }

  std::scoped_lock Lock(ThreadCreationMutex);
  InvalidationTracker->InvalidateAlignedInterval(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size), false);
}

void BTCpu64NotifyReadFile(HANDLE Handle, void* Address, SIZE_T Size, BOOL After, NTSTATUS Status) {
  auto* ThreadState = GetCPUArea().ThreadState();
  if (!InvalidationTracker || !ThreadState) {
    return;
  }

  auto& InLockedRWXRead = GetFrontendThreadData(ThreadState)->InLockedRWXRead;
  if (!After) {
    ThreadCreationMutex.lock();
    CTX->GetCodeInvalidationMutex().lock();
    if (InvalidationTracker->BeginUntrackedWriteLocked(reinterpret_cast<uint64_t>(Address), static_cast<uint64_t>(Size))) {
      InLockedRWXRead = true;
    } else {
      CTX->GetCodeInvalidationMutex().unlock();
      ThreadCreationMutex.unlock();
    }
  } else {
    if (InLockedRWXRead) {
      InLockedRWXRead = false;
      CTX->GetCodeInvalidationMutex().unlock();
      ThreadCreationMutex.unlock();
    }
  }
}

NTSTATUS ThreadInit() {
#if FEX_ON_WINE_APPLE
  // Capture TEB before any Darwin SVC (write/mmap clobber tpidr/x18).
  uintptr_t SavedTeb = FEXWineAppleSaveTeb();
  if (!FEXIsPlausibleWineTeb(SavedTeb)) {
    // Last chance after ProcessInit SVC noise — never deref junk (0x1003+0x1788).
    SavedTeb = FEXResolveWineTeb();
  }
  if (!FEXIsPlausibleWineTeb(SavedTeb)) {
    return STATUS_UNSUCCESSFUL;
  }
  FEXWineAppleRestoreTeb(SavedTeb);
  // Host-mmap slab stash for BeginSimulation when tpidr/x18 are wiped after process_attach.
  FEXSetLastGoodTeb(SavedTeb);
  auto TiLog = [SavedTeb](const char* Msg) {
    size_t Len = 0;
    while (Msg[Len]) {
      ++Len;
    }
    register uint64_t x0 __asm__("x0") = 2;
    register uint64_t x1 __asm__("x1") = reinterpret_cast<uint64_t>(Msg);
    register uint64_t x2 __asm__("x2") = static_cast<uint64_t>(Len);
    register uint64_t x16 __asm__("x16") = 4;
    __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18");
    FEXWineAppleRestoreTeb(SavedTeb);
  };
  TiLog("FEX ThreadInit: enter\n");
  // Skip ThreadCreationMutex / InitCRTThread / Threads map — PE BSS / CRT hazards.
  // Build CPUArea from SavedTeb — do not re-read clobbered tpidr via GetCPUArea().
  ThreadCPUArea CPUArea {reinterpret_cast<_TEB*>(SavedTeb)};
  if (!CPUArea.Area) {
    TiLog("FEX ThreadInit: no CHPE CPU area\n");
    return STATUS_UNSUCCESSFUL;
  }
  FEXCore::Allocator::SetWineAppleCpuArea(CPUArea.Area);
  {
    const bool TebOk = reinterpret_cast<uintptr_t>(FEXCore::Allocator::GetWineAppleLastGoodTeb()) == SavedTeb;
    const bool AreaOk = FEXCore::Allocator::GetWineAppleCpuArea() == CPUArea.Area;
    TiLog(TebOk && AreaOk ? "FEX ThreadInit: slab TEB+CpuArea OK\n" : "FEX ThreadInit: slab TEB+CpuArea FAIL\n");
  }
  TiLog("FEX ThreadInit: after GetCPUArea\n");
#else
  std::scoped_lock Lock(ThreadCreationMutex);
  FEX::Windows::InitCRTThread();
  const auto CPUArea = GetCPUArea();
  if (!CPUArea.Area) {
    return STATUS_UNSUCCESSFUL;
  }
#endif

  static constexpr size_t EmulatorStackSize = 0x40000;
#if FEX_ON_WINE_APPLE
  // Use Allocator VirtualAlloc (HostMmap+TEB restore) — not a separate SVC path.
  const uint64_t EmulatorStack =
    reinterpret_cast<uint64_t>(FEXCore::Allocator::VirtualAlloc(EmulatorStackSize, false, true));
  if (!EmulatorStack) {
    TiLog("FEX ThreadInit: emulator stack mmap failed\n");
    return STATUS_NO_MEMORY;
  }
  TiLog("FEX ThreadInit: after emulator stack\n");
#else
  const uint64_t EmulatorStack = reinterpret_cast<uint64_t>(::VirtualAlloc(nullptr, EmulatorStackSize, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE));
#endif
  CPUArea.EmulatorStackLimit() = EmulatorStack;
  CPUArea.EmulatorStackBase() = EmulatorStack + EmulatorStackSize;

#if FEX_ON_WINE_APPLE
  auto* Ctx = static_cast<FEXCore::Context::Context*>(FEXCore::Allocator::GetWineAppleContext());
  if (!Ctx) {
    TiLog("FEX ThreadInit: no WineAppleCTX\n");
    return STATUS_UNSUCCESSFUL;
  }
  TiLog("FEX ThreadInit: before CreateThread\n");
  auto* Thread = Ctx->CreateThread(0, 0);
  TiLog("FEX ThreadInit: after CreateThread\n");
#else
  auto* Thread = CTX->CreateThread(0, 0);
#endif

  // Default segment setup.
  auto Frame = Thread->CurrentFrame;
#if FEX_ON_WINE_APPLE
  TiLog("FEX ThreadInit: before GDT alloc\n");
  using GdtSeg = FEXCore::Core::CPUState::gdt_segment;
  constexpr size_t GdtBytes = sizeof(GdtSeg) * 32;
  void* GdtMem = FEXCore::Allocator::aligned_alloc(alignof(GdtSeg), GdtBytes);
  if (!GdtMem) {
    TiLog("FEX ThreadInit: GDT alloc FAILED\n");
    return STATUS_NO_MEMORY;
  }
  {
    volatile unsigned char* B = static_cast<volatile unsigned char*>(GdtMem);
    for (size_t I = 0; I < GdtBytes; ++I) {
      B[I] = 0;
    }
  }
  auto* NewSegments = static_cast<GdtSeg*>(GdtMem);
  TiLog("FEX ThreadInit: after GDT alloc\n");
#else
  auto NewSegments = new FEXCore::Core::CPUState::gdt_segment[32];
#endif

  // Setup initial code-segment GDT
  auto& GDT = NewSegments[FEXCore::Core::CPUState::DEFAULT_USER_CS];
  FEXCore::Core::CPUState::SetGDTBase(&GDT, 0);
  FEXCore::Core::CPUState::SetGDTLimit(&GDT, 0xF'FFFFU);
  GDT.L = 1; // L = Long Mode = 64-bit
  GDT.D = 0; // D = Default Operand SIze = Reserved

  Frame->State.segment_arrays[FEXCore::Core::CPUState::SEGMENT_ARRAY_INDEX_GDT] = &NewSegments[0];
  // TODO: LDTs are currently unsupported, mirror them to GDT.
  Frame->State.segment_arrays[FEXCore::Core::CPUState::SEGMENT_ARRAY_INDEX_LDT] = &NewSegments[0];

  Frame->State.cs_idx = FEXCore::Core::CPUState::DEFAULT_USER_CS << 3;
  Frame->State.cs_cached = FEXCore::Core::CPUState::CalculateGDTBase(GDT);

#if FEX_ON_WINE_APPLE
  TiLog("FEX ThreadInit: before callret mmap\n");
  // Host 16K pages; use Allocator VirtualAlloc for TEB-safe Darwin mmap.
  constexpr size_t CRS = FEXCore::Core::InternalThreadState::CALLRET_STACK_SIZE;
  constexpr size_t Guard = FEX_WINE_APPLE_PAGE_SIZE;
  void* CrsAlloc = FEXCore::Allocator::VirtualAlloc(CRS + 2 * Guard, false, true);
  if (!CrsAlloc) {
    TiLog("FEX ThreadInit: callret stack mmap failed\n");
    return STATUS_NO_MEMORY;
  }
  Thread->CallRetStackBase = reinterpret_cast<void*>(reinterpret_cast<uintptr_t>(CrsAlloc) + Guard);
  TiLog("FEX ThreadInit: after callret mmap\n");
#else
  FEX::Windows::CallRetStack::InitializeThread(Thread);
#endif
  Thread->CurrentFrame->Pointers.ExitFunctionEC = reinterpret_cast<uintptr_t>(&ExitFunctionEC);
  CPUArea.StateFrame() = Thread->CurrentFrame;

  uint64_t EnterEC = Thread->CurrentFrame->Pointers.DispatcherLoopTopEnterEC;
  CPUArea.DispatcherLoopTopEnterEC() = EnterEC;

  uint64_t EnterECFillSRA = Thread->CurrentFrame->Pointers.DispatcherLoopTopEnterECFillSRA;
  CPUArea.DispatcherLoopTopEnterECFillSRA() = EnterECFillSRA;

#if FEX_ON_WINE_APPLE
  // Gate lb: AbsoluteLoopTopEnterEC is ret-only on wine-apple; FillSRA still
  // enters LoopTop+CompileBlock (RX dispatcher code). Publish FillSRA for
  // WineAppleEnterEC; keep PE-text EnterEC stub on [2]. BeginSim bare-br unchanged.
  {
    WineAppleRealFillSRA = EnterECFillSRA;
    const uint64_t Stub = reinterpret_cast<uint64_t>(&WineAppleEnterEC);
    CPUArea.DispatcherLoopTopEnterEC() = Stub;
    Thread->CurrentFrame->Pointers.DispatcherLoopTopEnterEC = Stub;
    /* EmulatorData[3] remains real FillSRA (set above). */
    TiLog("FEX ThreadInit: WineAppleEnterEC→FillSRA LoopTop (lb)\n");
  }
  // jul10ah: field-by-field ContextAmd64 + light LoadState (no aggregate brace-init /
  // no float memcpy / no file-scope CTX). Aggregate assign → c000001d previously.
  // callret/gs published with EmulatorData at end (no mid-init hybrid risk).
  Frame->State.callret_sp = reinterpret_cast<uint64_t>(Thread->CallRetStackBase) + CRS / 4;
  Frame->State.gs_cached = SavedTeb;
  Frame->State.gs_idx = 0x2b;
  TiLog("FEX ThreadInit: gs/callret set\n");
#else
  CPUArea.ContextAmd64() = {.ContextFlags = CONTEXT_CONTROL | CONTEXT_SEGMENTS | CONTEXT_INTEGER | CONTEXT_FLOATING_POINT,
                            .AMD64_SegCs = (FEXCore::Core::CPUState::DEFAULT_USER_CS << 3) | 3,
                            .AMD64_SegDs = 0x2b,
                            .AMD64_SegEs = 0x2b,
                            .AMD64_SegFs = 0x53,
                            .AMD64_SegGs = 0x2b,
                            .AMD64_SegSs = 0x2b,
                            .AMD64_EFlags = 0x202,
                            .AMD64_MxCsr = 0x1f80,
                            .AMD64_MxCsr_copy = 0x1f80,
                            .AMD64_ControlWord = 0x27f};
  Exception::LoadStateFromECContext(Thread, CPUArea.ContextAmd64().AMD64_Context);
#endif

#if FEX_ON_WINE_APPLE
  // Host-bump FrontendThreadData — no operator new / memset.
  {
    void* Fp = FEXCore::Allocator::aligned_alloc(alignof(FrontendThreadData), sizeof(FrontendThreadData));
    if (!Fp) {
      TiLog("FEX ThreadInit: FrontendPtr alloc FAILED\n");
      return STATUS_NO_MEMORY;
    }
    volatile unsigned char* B = static_cast<volatile unsigned char*>(Fp);
    for (size_t I = 0; I < sizeof(FrontendThreadData); ++I) {
      B[I] = 0;
    }
    Thread->FrontendPtr = Fp;
  }
  TiLog("FEX ThreadInit: FrontendPtr ok\n");
#else
  Thread->FrontendPtr = new FrontendThreadData();
#endif

#if !FEX_ON_WINE_APPLE
  {
    auto ThreadTID = GetCurrentThreadId();
    Threads.emplace(ThreadTID, Thread);
    if (StatAllocHandler) {
      Thread->ThreadStats = StatAllocHandler->AllocateSlot(ThreadTID);
    }
  }
#endif

  // Publish EmulatorData LAST — once set, Darwin SVC / hybrid return may enter
  // EnterEC. No TiLog (svc) after this point.
  CPUArea.StateFrame() = Frame;
  CPUArea.ThreadState() = Thread;
  CPUArea.Area->SuspendDoorbell = reinterpret_cast<ULONG*>(&Thread->CurrentFrame->SuspendDoorbell);
#if FEX_ON_WINE_APPLE
  FEXWineAppleRestoreTeb(SavedTeb);
#endif
  return STATUS_SUCCESS;
}

NTSTATUS ThreadTerm(HANDLE Thread, LONG ExitCode) {
  if (!FEX::Windows::ValidateHandleAccess(Thread, THREAD_TERMINATE)) {
    return STATUS_ACCESS_DENIED;
  }

  auto ThreadDup = FEX::Windows::DupHandle(Thread, THREAD_QUERY_INFORMATION | THREAD_SUSPEND_RESUME);

  THREAD_BASIC_INFORMATION Info;
  if (auto Err = NtQueryInformationThread(*ThreadDup, ThreadBasicInformation, &Info, sizeof(Info), nullptr); Err) {
    return Err;
  }

  const auto ThreadTID = reinterpret_cast<uint64_t>(Info.ClientId.UniqueThread);
  bool Self = ThreadTID == GetCurrentThreadId();
  if (!Self) {
    CONTEXT TmpContext;
    // If we are suspending a thread that isn't ourselves, try to suspend it first so we know internal JIT locks aren't being held.
    NtSuspendThread(*ThreadDup, NULL);
    // This will wait for the thread to be suspended
    NtGetContextThread(*ThreadDup, &TmpContext);
  }

  const auto [Err, CPUArea] = GetThreadCPUArea(*ThreadDup);
  if (Err) {
    return Err;
  }

  {
    std::scoped_lock Lock(ThreadCreationMutex);
    auto it = Threads.find(ThreadTID);
    if (it == Threads.end()) {
      // Thread already terminated
      return STATUS_SUCCESS;
    }

    Threads.erase(it);
    if (StatAllocHandler) {
      StatAllocHandler->DeallocateSlot(CPUArea.ThreadState()->ThreadStats);
    }
  }
  auto ThreadState = CPUArea.ThreadState();

  delete GetFrontendThreadData(ThreadState);

  // GDT and LDT are mirrored, only free one.
  delete[] ThreadState->CurrentFrame->State.segment_arrays[FEXCore::Core::CPUState::SEGMENT_ARRAY_INDEX_GDT];

#if FEX_ON_WINE_APPLE
  {
    constexpr size_t CRS = FEXCore::Core::InternalThreadState::CALLRET_STACK_SIZE;
    constexpr size_t Guard = FEX_WINE_APPLE_PAGE_SIZE;
    if (ThreadState->CallRetStackBase) {
      void* Base = reinterpret_cast<void*>(reinterpret_cast<uintptr_t>(ThreadState->CallRetStackBase) - Guard);
      FEXWineAppleMunmap(Base, CRS + 2 * Guard);
      ThreadState->CallRetStackBase = nullptr;
    }
  }
#else
  FEX::Windows::CallRetStack::DestroyThread(ThreadState);
#endif
  CTX->DestroyThread(ThreadState);
#if FEX_ON_WINE_APPLE
  FEXWineAppleMunmap(reinterpret_cast<void*>(CPUArea.EmulatorStackLimit()), 0x40000);
#else
  ::VirtualFree(reinterpret_cast<void*>(CPUArea.EmulatorStackLimit()), 0, MEM_RELEASE);
#endif
  if (ThreadTID == GetCurrentThreadId()) {
    FEX::Windows::DeinitCRTThread();
  }

  return STATUS_SUCCESS;
}

BOOLEAN BTCpu64IsProcessorFeaturePresent(UINT Feature) {
  if (!CPUFeatures) {
    return FALSE;
  }
  return CPUFeatures->IsFeaturePresent(Feature) ? TRUE : FALSE;
}

void UpdateProcessorInformation(SYSTEM_CPU_INFORMATION* Info) {
  if (!CPUFeatures) {
    return;
  }
  CPUFeatures->UpdateInformation(Info);
}
