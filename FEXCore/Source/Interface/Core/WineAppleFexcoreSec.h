#pragma once
// Put FEXCore code after Module.S .text. ARM64EC default .text$#Name sorts
// before plain .text$0* ('#' < '0') and moved WineAppleEnterEC.
#pragma clang section text=".text$zzFEX"

// ARM64EC clang treats extern C mem* as x64 (#memset IAT → exit-thunk).
// Inline loops in this TU so ctors never leave ARM64EC.
static inline void* FEX_WineApple_memset(void* Dst, int Val, __SIZE_TYPE__ N) {
  auto* P = static_cast<volatile unsigned char*>(Dst);
  const auto B = static_cast<unsigned char>(Val);
  for (__SIZE_TYPE__ I = 0; I < N; ++I) {
    P[I] = B;
  }
  return Dst;
}
static inline void* FEX_WineApple_memcpy(void* Dst, const void* Src, __SIZE_TYPE__ N) {
  auto* D = static_cast<volatile unsigned char*>(Dst);
  const auto* S = static_cast<const unsigned char*>(Src);
  for (__SIZE_TYPE__ I = 0; I < N; ++I) {
    D[I] = S[I];
  }
  return Dst;
}
static inline void* FEX_WineApple_memmove(void* Dst, const void* Src, __SIZE_TYPE__ N) {
  auto* D = static_cast<volatile unsigned char*>(Dst);
  const auto* S = static_cast<const unsigned char*>(Src);
  if (D == S || N == 0) {
    return Dst;
  }
  if (D < S) {
    for (__SIZE_TYPE__ I = 0; I < N; ++I) {
      D[I] = S[I];
    }
  } else {
    for (__SIZE_TYPE__ I = N; I > 0; --I) {
      D[I - 1] = S[I - 1];
    }
  }
  return Dst;
}
static inline int FEX_WineApple_memcmp(const void* A, const void* B, __SIZE_TYPE__ N) {
  const auto* P = static_cast<const unsigned char*>(A);
  const auto* Q = static_cast<const unsigned char*>(B);
  for (__SIZE_TYPE__ I = 0; I < N; ++I) {
    if (P[I] != Q[I]) {
      return static_cast<int>(P[I]) - static_cast<int>(Q[I]);
    }
  }
  return 0;
}
#define memset FEX_WineApple_memset
#define memcpy FEX_WineApple_memcpy
#define memmove FEX_WineApple_memmove
#define memcmp FEX_WineApple_memcmp
