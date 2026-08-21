// SPDX-License-Identifier: MIT
#pragma once
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <type_traits>

namespace ARMEmitter {
class Buffer {
public:
  Buffer() {
    SetBuffer(nullptr, 0);
  }

  Buffer(uint8_t* Base, uint64_t BaseSize) {
    SetBuffer(Base, BaseSize);
  }

  void SetBuffer(uint8_t* Base, uint64_t BaseSize) {
    BufferBase = Base;
    CurrentOffset = BufferBase;
    Size = BaseSize;
  }

  template<typename T>
  requires (std::is_trivially_copyable_v<T>)
  void dcn(const T& Data) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    // No std::memcpy — ARM64EC exit-thunk before JIT (c000001d). Volatile byte copy.
    const auto* S = reinterpret_cast<const volatile unsigned char*>(&Data);
    volatile unsigned char* D = CurrentOffset;
    for (size_t I = 0; I < sizeof(T); ++I) {
      D[I] = S[I];
    }
#else
    std::memcpy(CurrentOffset, &Data, sizeof(Data));
#endif
    CurrentOffset += sizeof(Data);
  }
  void dc8(uint8_t Data) {
    dcn(Data);
  }
  void dc16(uint16_t Data) {
    dcn(Data);
  }
  void dc32(uint32_t Data) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    *reinterpret_cast<volatile uint32_t*>(CurrentOffset) = Data;
    CurrentOffset += 4;
#else
    dcn(Data);
#endif
  }
  void dc64(uint64_t Data) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    *reinterpret_cast<volatile uint64_t*>(CurrentOffset) = Data;
    CurrentOffset += 8;
#else
    dcn(Data);
#endif
  }

  void EmitString(const char* String) {
    const auto StringLength = strlen(String);
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    volatile unsigned char* D = CurrentOffset;
    for (size_t I = 0; I < StringLength; ++I) {
      D[I] = static_cast<unsigned char>(String[I]);
    }
#else
    memcpy(CurrentOffset, String, StringLength);
#endif
    CurrentOffset += StringLength;
  }

  void Align(size_t Size = 4) {
    // Align the buffer to provided size.
    auto CurrentAlignment = reinterpret_cast<uint64_t>(CurrentOffset) & (Size - 1);
    if (!CurrentAlignment) {
      return;
    }
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    volatile unsigned char* D = CurrentOffset;
    for (size_t I = 0; I < Size - CurrentAlignment; ++I) {
      D[I] = 0;
    }
#else
    std::memset(CurrentOffset, 0, Size - CurrentAlignment);
#endif
    CurrentOffset += Size - CurrentAlignment;
  }

  template<typename T>
  T GetCursorAddress() const {
    return reinterpret_cast<T>(CurrentOffset);
  }

  static void ClearICache(void* Begin, std::size_t Length) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
    // Pure asm — no __builtin___clear_cache (may libcall / fault early).
    auto P = reinterpret_cast<uintptr_t>(Begin) & ~63ull;
    const auto E = reinterpret_cast<uintptr_t>(Begin) + Length;
    for (; P < E; P += 64) {
      __asm__ volatile("dc cvau, %0" ::"r"(P) : "memory");
    }
    __asm__ volatile("dsb ish" ::: "memory");
    P = reinterpret_cast<uintptr_t>(Begin) & ~63ull;
    for (; P < E; P += 64) {
      __asm__ volatile("ic ivau, %0" ::"r"(P) : "memory");
    }
    __asm__ volatile("dsb ish\n\tisb" ::: "memory");
#else
    __builtin___clear_cache(static_cast<char*>(Begin), static_cast<char*>(Begin) + Length);
#endif
  }

  size_t GetCursorOffset() const {
    return static_cast<size_t>(CurrentOffset - BufferBase);
  }

  uint8_t* GetBufferBase() const {
    return BufferBase;
  }

  void CursorIncrement(size_t Size) {
    CurrentOffset += Size;
  }

  void SetCursorOffset(size_t Offset) {
    CurrentOffset = BufferBase + Offset;
  }

  uint64_t GetBufferSize() const {
    return Size;
  }

  template<typename T>
  size_t GetCursorOffsetFromAddress(const T* Address) const {
    return static_cast<size_t>(reinterpret_cast<const uint8_t*>(Address) - BufferBase);
  }

protected:

  uint8_t* BufferBase;
  uint8_t* CurrentOffset;
  uint64_t Size;
};
} // namespace ARMEmitter
