// SPDX-License-Identifier: MIT
#include "Interface/Context/Context.h"
#include "Interface/Core/OpcodeDispatcher.h"
#include "Interface/Core/Dispatcher/Dispatcher.h"
#include "Interface/Core/X86Tables/X86Tables.h"

#include <FEXCore/Core/CoreState.h>
#include <FEXCore/Core/Context.h>
#include <FEXCore/Core/CPUID.h>
#include <FEXCore/Core/HostFeatures.h>
#include <FEXCore/Core/SignalDelegator.h>
#include <FEXCore/HLE/SyscallHandler.h>

#include <FEXCore/Core/Thunks.h>
#include "FEXCore/Debug/InternalThreadState.h"

namespace FEXCore::Context {
fextl::unique_ptr<FEXCore::Context::Context> FEXCore::Context::Context::CreateNewContext(const FEXCore::HostFeatures& Features) {
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
  auto HostWrite = [](const char* Msg) {
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
  };
  HostWrite("CreateNewContext: enter\n");
  const size_t Sz = sizeof(FEXCore::Context::ContextImpl);
  const size_t Al = alignof(FEXCore::Context::ContextImpl);
  HostWrite("CreateNewContext: before aligned_alloc\n");
  void* Mem = FEXCore::Allocator::aligned_alloc(Al, Sz);
  if (!Mem) {
    HostWrite("CreateNewContext: aligned_alloc FAILED\n");
    return nullptr;
  }
  HostWrite("CreateNewContext: aligned_alloc OK\n");
  HostWrite("CreateNewContext: before placement new\n");
  auto* Obj = ::new (Mem) FEXCore::Context::ContextImpl(Features);
  HostWrite("CreateNewContext: after placement new\n");
  return fextl::unique_ptr<FEXCore::Context::Context>(Obj);
#else
  return fextl::make_unique<FEXCore::Context::ContextImpl>(Features);
#endif
}

void FEXCore::Context::ContextImpl::CompileRIP(FEXCore::Core::InternalThreadState* Thread, uint64_t GuestRIP) {
  CompileBlock(Thread->CurrentFrame, GuestRIP);
}

void FEXCore::Context::ContextImpl::CompileRIPCount(FEXCore::Core::InternalThreadState* Thread, uint64_t GuestRIP, uint64_t MaxInst) {
  CompileBlock(Thread->CurrentFrame, GuestRIP, MaxInst);
}

void FEXCore::Context::ContextImpl::SetSignalDelegator(FEXCore::SignalDelegator* _SignalDelegation) {
  SignalDelegation = _SignalDelegation;
}

void FEXCore::Context::ContextImpl::SetSyscallHandler(FEXCore::HLE::SyscallHandler* Handler) {
  SyscallHandler = Handler;
  SourcecodeResolver = Handler->GetSourcecodeResolver();
}

void FEXCore::Context::ContextImpl::SetThunkHandler(FEXCore::ThunkHandler* Handler) {
  ThunkHandler = Handler;
}

FEXCore::CPUID::FunctionResults FEXCore::Context::ContextImpl::RunCPUIDFunction(uint32_t Function, uint32_t Leaf) {
  return CPUID.RunFunction(Function, Leaf);
}

FEXCore::CPUID::XCRResults FEXCore::Context::ContextImpl::RunXCRFunction(uint32_t Function) {
  return CPUID.RunXCRFunction(Function);
}

FEXCore::CPUID::FunctionResults FEXCore::Context::ContextImpl::RunCPUIDFunctionName(uint32_t Function, uint32_t Leaf, uint32_t CPU) {
  return CPUID.RunFunctionName(Function, Leaf, CPU);
}

bool FEXCore::Context::ContextImpl::IsAddressInCodeBuffer(FEXCore::Core::InternalThreadState* Thread, uintptr_t Address) const {
  return Thread->CPUBackend->IsAddressInCodeBuffer(Address);
}
} // namespace FEXCore::Context
