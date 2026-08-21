// SPDX-License-Identifier: MIT
#ifndef FEX_ON_WINE_APPLE
#define FEX_ON_WINE_APPLE 0
#endif

#define _SECIMP
#define _CRTIMP
#include <cstdint>
#include <cstring>
#include "../Priv.h"

#if FEX_ON_WINE_APPLE
// Host Darwin mmap slab — rpmalloc_initialize faults under Wine-on-macOS PE
// (writes into ntdll). Keep ProcessInit allocations on a private host slab.
namespace {

constexpr size_t kSlabSize = 64ull << 20;
void* gSlab {};
size_t gUsed {};

void* HostMmap(size_t Size) {
  void* Result {};
  const uintptr_t Len = Size;
  __asm__ volatile("mov x16, #197\n\t" /* SYS_mmap */
                   "mov x0, #0\n\t"
                   "mov x1, %1\n\t"
                   "mov x2, #3\n\t"      /* PROT_READ|PROT_WRITE */
                   "mov x3, #0x1002\n\t" /* MAP_PRIVATE|MAP_ANON */
                   "mov x4, #-1\n\t"
                   "mov x5, #0\n\t"
                   "svc #0x80\n\t"
                   "mov %0, x0"
                   : "=r"(Result)
                   : "r"(Len)
                   : "x0", "x1", "x2", "x3", "x4", "x5", "x16", "memory", "cc");
  if (reinterpret_cast<intptr_t>(Result) < 0) {
    return nullptr;
  }
  return Result;
}

void* Bump(size_t Size, size_t Align = 16) {
  if (!gSlab) {
    gSlab = HostMmap(kSlabSize);
    gUsed = 0;
    if (!gSlab) {
      return nullptr;
    }
  }
  if (Align < 16) {
    Align = 16;
  }
  size_t Pad = (Align - (gUsed % Align)) % Align;
  if (gUsed + Pad + Size > kSlabSize) {
    // Overflow: fresh mapping (never freed — ProcessInit lifetime)
    void* Extra = HostMmap(Size + Align);
    if (!Extra) {
      return nullptr;
    }
    uintptr_t P = reinterpret_cast<uintptr_t>(Extra);
    P = (P + Align - 1) & ~(Align - 1);
    return reinterpret_cast<void*>(P);
  }
  void* Result = reinterpret_cast<char*>(gSlab) + gUsed + Pad;
  gUsed += Pad + Size;
  return Result;
}

} // namespace

void* calloc(size_t NumOfElements, size_t SizeOfElements) {
  size_t N = NumOfElements * SizeOfElements;
  void* P = Bump(N);
  if (P) {
    memset(P, 0, N);
  }
  return P;
}

void free(void* Memory) {
  (void)Memory; // bump / slab — no free
}

void* malloc(size_t Size) {
  return Bump(Size);
}

void* realloc(void* Memory, size_t NewSize) {
  if (!Memory) {
    return Bump(NewSize);
  }
  void* P = Bump(NewSize);
  if (P && Memory) {
    // Best-effort copy; old size unknown — copy NewSize (may read past old)
    memcpy(P, Memory, NewSize);
  }
  return P;
}

DLLEXPORT_FUNC(void*, _aligned_malloc, (size_t Size, size_t Alignment)) {
  return Bump(Size, Alignment ? Alignment : 16);
}

DLLEXPORT_FUNC(void, _aligned_free, (void* Memory)) {
  (void)Memory;
}

#else
#include <rpmalloc/rpmalloc.h>

void* calloc(size_t NumOfElements, size_t SizeOfElements) {
  return ::rpcalloc(NumOfElements, SizeOfElements);
}

void free(void* Memory) {
  ::rpfree(Memory);
}

void* malloc(size_t Size) {
  return ::rpmalloc(Size);
}

void* realloc(void* Memory, size_t NewSize) {
  return ::rprealloc(Memory, NewSize);
}

DLLEXPORT_FUNC(void*, _aligned_malloc, (size_t Size, size_t Alignment)) {
  return ::rpaligned_alloc(Alignment, Size);
}

DLLEXPORT_FUNC(void, _aligned_free, (void* Memory)) {
  ::rpfree(Memory);
}
#endif
