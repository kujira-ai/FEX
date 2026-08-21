// SPDX-License-Identifier: MIT
#pragma once

#include <cstdint>

namespace FEXCore::Core {
struct CpuStateFrame;
}

// Darwin host backend under the wine-apple JIT path (mmap/W^X/one-insn emit).
// CompileBlock should look like Hangover: decode → host backend → RX code.
namespace FEX::WineApple {
void Ensure();
uintptr_t CompileOneInsn(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP);
} // namespace FEX::WineApple

extern "C" {
void FEXWineAppleEnsure();
uintptr_t FEXWineAppleCompileOneInsn(void* Frame, uint64_t GuestRIP);
}
