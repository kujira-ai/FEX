// SPDX-License-Identifier: MIT
#pragma once

#include <cstdint>

namespace FEXCore::Core {
struct CpuStateFrame;
}

// Darwin host fallback (mmap/W^X/one-insn emit) if Arm64JITCore is null.
// Product compiler is Hangover Arm64JITCore via ContextImpl::CompileBlock.
namespace FEX::WineApple {
void Ensure();
uintptr_t CompileOneInsn(FEXCore::Core::CpuStateFrame* Frame, uint64_t GuestRIP);
} // namespace FEX::WineApple

extern "C" {
void FEXWineAppleEnsure();
uintptr_t FEXWineAppleCompileOneInsn(void* Frame, uint64_t GuestRIP);
}
