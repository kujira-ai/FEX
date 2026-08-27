// SPDX-License-Identifier: MIT
#ifdef ENABLE_FEX_ALLOCATOR
#include <rpmalloc/rpmalloc.h>
#ifndef _WIN32
#include <sys/prctl.h>
#include <sys/mman.h>
#else
#define NTDDI_VERSION 0x0A000005
#include <memoryapi.h>
#endif
#endif

#include <cstdint>
#include <malloc.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

namespace FEXCore::Allocator {
// Mirror header enum for this TU only (JemallocLibs cannot pull full AllocatorHooks.h/fmt).
enum class ProtectOptions : uint32_t {
  None = 0,
  Read = (1U << 0),
  Write = (1U << 1),
  Exec = (1U << 2),
};
inline ProtectOptions operator|(ProtectOptions A, ProtectOptions B) {
  return static_cast<ProtectOptions>(static_cast<uint32_t>(A) | static_cast<uint32_t>(B));
}
using mmap_hook_type = void* (*)(void* addr, size_t length, int prot, int flags, int fd, off_t offset);
using munmap_hook_type = int (*)(void* addr, size_t length);

#ifdef ENABLE_FEX_ALLOCATOR
typedef void* (*rp_mmap_hook_type)(size_t size, size_t alignment, size_t* offset, size_t* mapped_size);
typedef void (*rp_munmap_hook_type)(void* address, size_t offset, size_t mapped_size);
extern "C" rp_mmap_hook_type rp_mmap_hook;
extern "C" rp_munmap_hook_type rp_munmap_hook;

#ifndef _WIN32
mmap_hook_type fex_mmap_hook = ::mmap;
munmap_hook_type fex_munmap_hook = ::munmap;
#endif

// Assume a 64KB page size until told otherwise.
static rpmalloc_config_t global_config {
  .page_size = 64 * 1024,
  // THP causes crashes for some reason.
  .enable_huge_pages = 0,
  .disable_decommit = 0,
  .page_name = "FEXAllocator",
  .huge_page_name = "FEXAllocator",
  .unmap_on_finalize = 0,
};

#if defined(_WIN32)
// Wine-on-macOS PE: VirtualAlloc IAT → ntdll thunks (illegal this early);
// rpmalloc_initialize also faults. Use Darwin host mmap when FEX_ON_WINE_APPLE.
namespace {
constexpr size_t kWinSlabSize = 128ull << 20;
// On FEX_ON_WINE_APPLE, slab header holds host-writable pointers (PE globals may be RO
// on 16k pages; host mmap slab is always RW).
// [0]=Context* [8]=X64ReturnInstr* [16]=HostMeta* [24]=LastGoodTeb* [32]=CpuArea*
constexpr size_t kWineAppleSlabHeader = 48;
void* gWinSlab {};
size_t gWinUsed {};

#if FEX_ON_WINE_APPLE
// PE BSS may not be zeroed; gWinSlab can hold file-bleed junk (e.g. 0x38….00000000).
static bool PlausibleSlab(void* P) {
  const auto U = reinterpret_cast<uintptr_t>(P);
  if (U < 0x10000ull) {
    return false;
  }
  if ((U & 0xFFFull) != 0) {
    return false; // HostMmap is page-aligned
  }
  if ((U & 0xFFFFFFFFull) == 0) {
    return false; // classic BSS junk: high non-zero, low zero
  }
  if (U >= 0x0001'0000'0000'0000ull) {
    return false;
  }
  return true;
}

// Hand-rolled — never call #memset/#memcpy (ARM64EC exit-thunks to x64 before JIT).
static void HostMemset(void* Dst, int Val, size_t N) {
  auto* P = static_cast<unsigned char*>(Dst);
  const auto B = static_cast<unsigned char>(Val);
  for (size_t I = 0; I < N; ++I) {
    P[I] = B;
  }
}
static void HostMemcpy(void* Dst, const void* Src, size_t N) {
  auto* D = static_cast<unsigned char*>(Dst);
  const auto* S = static_cast<const unsigned char*>(Src);
  for (size_t I = 0; I < N; ++I) {
    D[I] = S[I];
  }
}

// prot: Darwin PROT_* bits (1=R 2=W 4=X).
// flags default: MAP_PRIVATE|MAP_ANON=0x1002; MAP_JIT=0x0800 for executable codegen.
void* HostMmap(size_t Size, uint64_t Prot = 3, uint64_t Flags = 0x1002ull) {
  void* Result {};
  const uintptr_t Len = Size;
  const uintptr_t ProtU = Prot;
  const uintptr_t FlagsU = Flags;
  // Darwin SVC clobbers x18 (TEB); save/restore.
  uintptr_t SavedTeb {};
  uintptr_t SavedX18 {};
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(SavedTeb) :: "memory");
  __asm__ volatile("mov %0, x18" : "=r"(SavedX18));
  __asm__ volatile("mov x16, #197\n\t"
                   "mov x0, #0\n\t"
                   "mov x1, %1\n\t"
                   "mov x2, %2\n\t"
                   "mov x3, %3\n\t"
                   "mov x4, #-1\n\t"
                   "mov x5, #0\n\t"
                   "svc #0x80\n\t"
                   "mov %0, x0"
                   : "=r"(Result)
                   : "r"(Len), "r"(ProtU), "r"(FlagsU)
                   : "x0", "x1", "x2", "x3", "x4", "x5", "x16", "x18", "memory", "cc");
  // Prefer pre-SVC TEB; fall back to pre-SVC x18 if tpidr was already junk.
  uintptr_t Restore = SavedTeb;
  if (Restore < 0x10000ull || (Restore & 0xFull)) {
    Restore = SavedX18;
  }
  if (Restore >= 0x10000ull && !(Restore & 0xFull)) {
    __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Restore) : "x18", "memory");
  }
  if (reinterpret_cast<intptr_t>(Result) < 0) {
    return nullptr;
  }
  return Result;
}

void HostMunmap(void* Ptr, size_t Size) {
  if (!Ptr || !Size) {
    return;
  }
  uintptr_t SavedTeb {}, SavedX18 {};
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(SavedTeb) :: "memory");
  __asm__ volatile("mov %0, x18" : "=r"(SavedX18));
  register uint64_t x0 __asm__("x0") = reinterpret_cast<uint64_t>(Ptr);
  register uint64_t x1 __asm__("x1") = Size;
  register uint64_t x16 __asm__("x16") = 73; // SYS_munmap
  __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x16) : "memory", "x18", "cc");
  uintptr_t Restore = (SavedTeb >= 0x10000ull && !(SavedTeb & 0xFull)) ? SavedTeb : SavedX18;
  if (Restore >= 0x10000ull && !(Restore & 0xFull)) {
    __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Restore) : "x18", "memory");
  }
}

int HostMprotect(void* Ptr, size_t Size, uint64_t Prot) {
  if (!Ptr || !Size) {
    return -1;
  }
  uintptr_t SavedTeb {}, SavedX18 {};
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(SavedTeb) :: "memory");
  __asm__ volatile("mov %0, x18" : "=r"(SavedX18));
  register uint64_t x0 __asm__("x0") = reinterpret_cast<uint64_t>(Ptr);
  register uint64_t x1 __asm__("x1") = Size;
  register uint64_t x2 __asm__("x2") = Prot;
  register uint64_t x16 __asm__("x16") = 74; // SYS_mprotect
  __asm__ volatile("svc #0x80" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x16) : "memory", "x18", "cc");
  uintptr_t Restore = (SavedTeb >= 0x10000ull && !(SavedTeb & 0xFull)) ? SavedTeb : SavedX18;
  if (Restore >= 0x10000ull && !(Restore & 0xFull)) {
    __asm__ volatile("msr tpidr_el0, %0\n\t mov x18, %0" ::"r"(Restore) : "x18", "memory");
  }
  return static_cast<int>(x0);
}
#else
void* HostMmap(size_t Size, uint64_t Prot = 3) {
  (void)Prot;
  return ::VirtualAlloc(nullptr, Size, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
}
#endif

void* WinBump(size_t Size, size_t Align = 16) {
#if FEX_ON_WINE_APPLE
  if (!PlausibleSlab(gWinSlab)) {
    gWinSlab = nullptr;
    gWinUsed = 0;
  }
#endif
  if (!gWinSlab) {
    gWinSlab = HostMmap(kWinSlabSize);
#if FEX_ON_WINE_APPLE
    gWinUsed = kWineAppleSlabHeader;
    if (gWinSlab) {
      auto* H = reinterpret_cast<void**>(gWinSlab);
      for (int I = 0; I < 6; ++I) {
        H[I] = nullptr;
      }
    }
#else
    gWinUsed = 0;
#endif
    if (!gWinSlab) {
      return nullptr;
    }
  }
  if (Align < 16) {
    Align = 16;
  }
  size_t Pad = (Align - (gWinUsed % Align)) % Align;
  if (gWinUsed + Pad + Size > kWinSlabSize) {
    size_t Chunk = (Size + Align + 0xFFFF) & ~size_t(0xFFFF);
    void* Extra = HostMmap(Chunk);
    if (!Extra) {
      return nullptr;
    }
    uintptr_t P = reinterpret_cast<uintptr_t>(Extra);
    P = (P + Align - 1) & ~(Align - 1);
    return reinterpret_cast<void*>(P);
  }
  void* Result = reinterpret_cast<char*>(gWinSlab) + gWinUsed + Pad;
  gWinUsed += Pad + Size;
  return Result;
}
} // namespace

#if FEX_ON_WINE_APPLE
// Exec-capable host maps for Dispatcher/JIT (no VirtualAlloc IAT).
void* VirtualAlloc(void* Base, size_t Size, bool Execute, bool Commit) {
  (void)Commit;
  if (Base) {
    return nullptr; // fixed-base not needed on wine-apple bring-up path
  }
  // Always RW first (EmitDispatcher / WineAppleHost writes). Darwin W^X:
  // VirtualProtect RX after emit. MAP_JIT not required.
  (void)Execute;
  return HostMmap(Size, 3ull /* PROT_READ|PROT_WRITE */, 0x1002ull);
}
void* VirtualAlloc(size_t Size, bool Execute, bool Commit) {
  return VirtualAlloc(nullptr, Size, Execute, Commit);
}
void VirtualFree(void* Ptr, size_t Size) {
  HostMunmap(Ptr, Size);
}
void VirtualDontNeed(void* Ptr, size_t Size, bool Recommit) {
  (void)Recommit;
  // Best-effort: re-zero via hand loop if small; else leave committed.
  if (Ptr && Size && Size <= (1ull << 20)) {
    auto* B = static_cast<unsigned char*>(Ptr);
    for (size_t I = 0; I < Size; ++I) {
      B[I] = 0;
    }
  }
}
bool VirtualProtect(void* Ptr, size_t Size, ProtectOptions options) {
  uint64_t Prot = 0;
  if (options == ProtectOptions::None) {
    Prot = 0;
  } else if (options == ProtectOptions::Read) {
    Prot = 1;
  } else if (options == (ProtectOptions::Read | ProtectOptions::Write)) {
    Prot = 3;
  } else if (options == (ProtectOptions::Read | ProtectOptions::Exec)) {
    Prot = 5;
  } else if (options == (ProtectOptions::Read | ProtectOptions::Write | ProtectOptions::Exec)) {
    Prot = 7;
  } else {
    return false;
  }
  return HostMprotect(Ptr, Size, Prot) == 0;
}
#endif

void* malloc(size_t size) {
  return WinBump(size);
}
void* calloc(size_t n, size_t size) {
  size_t N = n * size;
  void* P = WinBump(N);
  if (P) {
#if FEX_ON_WINE_APPLE
    auto* B = static_cast<unsigned char*>(P);
    for (size_t I = 0; I < N; ++I) {
      B[I] = 0;
    }
#else
    memset(P, 0, N);
#endif
  }
  return P;
}
void* memalign(size_t align, size_t s) {
  return WinBump(s, align ? align : 16);
}
void* valloc(size_t size) {
  return WinBump(size, 0x10000);
}
int posix_memalign(void** r, size_t a, size_t s) {
  *r = WinBump(s, a ? a : 16);
  return *r ? 0 : 12;
}
void* realloc(void* ptr, size_t size) {
  void* P = WinBump(size);
  if (P && ptr) {
#if FEX_ON_WINE_APPLE
    auto* D = static_cast<unsigned char*>(P);
    const auto* S = static_cast<const unsigned char*>(ptr);
    for (size_t I = 0; I < size; ++I) {
      D[I] = S[I];
    }
#else
    memcpy(P, ptr, size);
#endif
  }
  return P;
}
void free(void* ptr) {
  (void)ptr;
}
size_t malloc_usable_size(void* ptr) {
  (void)ptr;
  return 0;
}
void* aligned_alloc(size_t a, size_t s) {
  return WinBump(s, a ? a : 16);
}
void aligned_free(void* ptr) {
  (void)ptr;
}

#if FEX_ON_WINE_APPLE
static void EnsureWineAppleSlab() {
  if (!PlausibleSlab(gWinSlab)) {
    (void)WinBump(0, 16); // establish slab via HostMmap
  }
}

void SetWineAppleContext(void* Ptr) {
  EnsureWineAppleSlab();
  if (PlausibleSlab(gWinSlab)) {
    *reinterpret_cast<void**>(gWinSlab) = Ptr;
  }
}
void* GetWineAppleContext() {
  if (!PlausibleSlab(gWinSlab)) {
    return nullptr;
  }
  return *reinterpret_cast<void**>(gWinSlab);
}

void* GetOrCreateX64ReturnInstr() {
  EnsureWineAppleSlab();
  if (!PlausibleSlab(gWinSlab)) {
    return nullptr;
  }
  auto* Slot = reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 8);
  if (*Slot) {
    return *Slot;
  }
  // x86 RET opcode — Module.S loads this as LR for misaligned SP EC exits.
  constexpr size_t Pg = 16384;
  void* Page = HostMmap(Pg, 3ull); // RW first
  if (!Page) {
    return nullptr;
  }
  *static_cast<volatile uint8_t*>(Page) = 0xc3;
  (void)HostMprotect(Page, Pg, 5ull); // RX best-effort
  *Slot = Page;
  return Page;
}

void SetWineAppleLastGoodTeb(void* Teb) {
  EnsureWineAppleSlab();
  if (!PlausibleSlab(gWinSlab)) {
    return;
  }
  *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 24) = Teb;
}

void* GetWineAppleLastGoodTeb() {
  if (!PlausibleSlab(gWinSlab)) {
    return nullptr;
  }
  return *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 24);
}

void SetWineAppleCpuArea(void* Area) {
  EnsureWineAppleSlab();
  if (!PlausibleSlab(gWinSlab)) {
    return;
  }
  *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 32) = Area;
}

void* GetWineAppleCpuArea() {
  if (!PlausibleSlab(gWinSlab)) {
    return nullptr;
  }
  return *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 32);
}

void SetWineAppleHostMeta(void* Ptr) {
  EnsureWineAppleSlab();
  if (!PlausibleSlab(gWinSlab)) {
    return;
  }
  *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 16) = Ptr;
}

void* GetWineAppleHostMeta() {
  if (!PlausibleSlab(gWinSlab)) {
    return nullptr;
  }
  return *reinterpret_cast<void**>(reinterpret_cast<char*>(gWinSlab) + 16);
}
#endif

void InitializeThread() {}
#else
void* malloc(size_t size) {
  return ::rpmalloc(size);
}
void* calloc(size_t n, size_t size) {
  return ::rpcalloc(n, size);
}
void* memalign(size_t align, size_t s) {
  return ::rpmemalign(align, s);
}
void* valloc(size_t size) {
  return ::rpaligned_alloc(global_config.page_size, size);
}
int posix_memalign(void** r, size_t a, size_t s) {
  void* ptr;
  auto res = ::rpposix_memalign(&ptr, a, s);
  *r = ptr;
  return res;
}
void* realloc(void* ptr, size_t size) {
  return ::rprealloc(ptr, size);
}
void free(void* ptr) {
  return ::rpfree(ptr);
}
size_t malloc_usable_size(void* ptr) {
  return ::rpmalloc_usable_size(ptr);
}
void* aligned_alloc(size_t a, size_t s) {
  return ::rpaligned_alloc(a, s);
}
void aligned_free(void* ptr) {
  return ::rpfree(ptr);
}

void InitializeThread() {
  rpmalloc_thread_initialize();
}
#endif

#ifndef _WIN32
[[nodiscard]]
constexpr uint64_t AlignUp(uint64_t value, uint64_t size) {
  return value + (size - value % size) % size;
}

static void* FEX_rp_mmap(size_t size, size_t alignment, size_t* offset, size_t* mapped_size) {
#define pointer_offset(ptr, ofs) (void*)((char*)(ptr) + (ptrdiff_t)(ofs))
  // If the alignment is less than the operating page size then alignment is guaranteed. Just remove it.
  if (alignment < global_config.page_size) {
    alignment = 0;
  }

  size_t map_size = AlignUp(size + alignment, global_config.page_size);
  auto ptr = fex_mmap_hook(0, map_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);

  if (ptr == MAP_FAILED) {
    ptr = nullptr;
  } else {
#ifndef PR_SET_VMA
#define PR_SET_VMA 0x53564d41
#endif

#ifndef PR_SET_VMA_ANON_NAME
#define PR_SET_VMA_ANON_NAME 0
#endif
    prctl(PR_SET_VMA, PR_SET_VMA_ANON_NAME, ptr, map_size, global_config.page_name);

    // Disable HUGEPAGE on allocation from rpmalloc.
    madvise(ptr, map_size, MADV_NOHUGEPAGE);
  }

  if (ptr == nullptr) {
    fprintf(stderr, "Failed to map VMA region.");
    return nullptr;
  }

  if (alignment) {
    size_t padding = ((uintptr_t)ptr & (uintptr_t)(alignment - 1));
    if (padding) {
      padding = alignment - padding;
    }
    ptr = pointer_offset(ptr, padding);
    *offset = padding;
  }
  *mapped_size = map_size;
  return ptr;
}

static void FEX_rp_memory_commit(void* address, size_t size) {
  // NOP-implementation.
}

static void FEX_rp_memory_decommit(void* address, size_t size) {
  if (global_config.disable_decommit) {
    return;
  }

  if (madvise(address, size, MADV_DONTNEED)) {
    fprintf(stderr, "Failed to decommit VMA region.");
  }
}

static void FEX_rp_memory_unmap(void* address, size_t offset, size_t mapped_size) {
  address = pointer_offset(address, -(int32_t)offset);
  int Result = fex_munmap_hook(address, mapped_size);
  if (Result == -1) {
    fprintf(stderr, "Failed to unmap VMA region.");
  }
#undef pointer_offset
}

void SetupAllocatorHooks(mmap_hook_type MMapHook, munmap_hook_type MunmapHook) {
  fex_mmap_hook = MMapHook;
  fex_munmap_hook = MunmapHook;
}

static rpmalloc_interface_t global_interface {
  .memory_map = FEX_rp_mmap,
  .memory_commit = FEX_rp_memory_commit,
  .memory_decommit = FEX_rp_memory_decommit,
  .memory_unmap = FEX_rp_memory_unmap,
  .map_fail_callback = nullptr,
  .error_callback = nullptr,
};

void InitializeAllocator(size_t PageSize) {
  global_config.page_size = PageSize;
  rpmalloc_initialize_config(&global_interface, &global_config);
  rp_mmap_hook = FEX_rp_mmap;
  rp_munmap_hook = FEX_rp_memory_unmap;
}
#endif

#elif defined(_WIN32)
#error "Tried building _WIN32 without jemalloc"

#else
void InitializeThread() {}

void* malloc(size_t size) {
  return ::malloc(size);
}
void* calloc(size_t n, size_t size) {
  return ::calloc(n, size);
}
void* memalign(size_t align, size_t s) {
  return ::memalign(align, s);
}
void* valloc(size_t size) {
  return ::valloc(size);
}
int posix_memalign(void** r, size_t a, size_t s) {
  return ::posix_memalign(r, a, s);
}
void* realloc(void* ptr, size_t size) {
  return ::realloc(ptr, size);
}
void free(void* ptr) {
  return ::free(ptr);
}
size_t malloc_usable_size(void* ptr) {
  return ::malloc_usable_size(ptr);
}
void* aligned_alloc(size_t a, size_t s) {
  return ::aligned_alloc(a, s);
}
void aligned_free(void* ptr) {
  return ::free(ptr);
}

void SetupAllocatorHooks(mmap_hook_type MMapHook, munmap_hook_type MunmapHook) {}

void InitializeAllocator(size_t PageSize) {}

#endif
} // namespace FEXCore::Allocator

#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
// ARM64EC clang emits #memset/#memcpy (x64 IAT). These are ARM64 loops so
// FEXCore ctors (OpDispatchBuilder) do not exit-thunk before the JIT exists.
extern "C" {
void* FEX_WineApple_memset(void* Dst, int Val, size_t N) {
  auto* P = static_cast<unsigned char*>(Dst);
  const auto B = static_cast<unsigned char>(Val);
  for (size_t I = 0; I < N; ++I) {
    P[I] = B;
  }
  return Dst;
}

void* FEX_WineApple_memcpy(void* Dst, const void* Src, size_t N) {
  auto* D = static_cast<unsigned char*>(Dst);
  const auto* S = static_cast<const unsigned char*>(Src);
  for (size_t I = 0; I < N; ++I) {
    D[I] = S[I];
  }
  return Dst;
}

void* FEX_WineApple_memmove(void* Dst, const void* Src, size_t N) {
  auto* D = static_cast<unsigned char*>(Dst);
  const auto* S = static_cast<const unsigned char*>(Src);
  if (D == S || N == 0) {
    return Dst;
  }
  if (D < S) {
    for (size_t I = 0; I < N; ++I) {
      D[I] = S[I];
    }
  } else {
    for (size_t I = N; I > 0; --I) {
      D[I - 1] = S[I - 1];
    }
  }
  return Dst;
}

int FEX_WineApple_memcmp(const void* A, const void* B, size_t N) {
  const auto* P = static_cast<const unsigned char*>(A);
  const auto* Q = static_cast<const unsigned char*>(B);
  for (size_t I = 0; I < N; ++I) {
    if (P[I] != Q[I]) {
      return static_cast<int>(P[I]) - static_cast<int>(Q[I]);
    }
  }
  return 0;
}
}
#endif
