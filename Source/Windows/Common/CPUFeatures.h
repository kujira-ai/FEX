// SPDX-License-Identifier: MIT
#pragma once
#ifndef FEX_ON_WINE_APPLE
#define FEX_ON_WINE_APPLE 0
#endif

#include <windef.h>
#include <winternl.h>

#include <Common/HostFeatures.h>

namespace FEXCore::Context {
class Context;
}

/**
 * @brief Maps CPUID results to Windows CPU info structures
 */
namespace FEX::Windows {
class CPUFeatures {
public:
  static FEXCore::HostFeatures FetchHostFeatures(bool IsWine);
#if FEX_ON_WINE_APPLE
  static FEXCore::HostFeatures FetchHostFeaturesWineApple();
#endif

  CPUFeatures(FEXCore::Context::Context& CTX);

  /**
   * @brief If the given PF_* feature is supported
   */
  bool IsFeaturePresent(uint32_t Feature);

  /**
   * @brief Fills in `Info` according to the detected CPU features
   */
  void UpdateInformation(SYSTEM_CPU_INFORMATION* Info);

private:
  SYSTEM_CPU_INFORMATION CpuInfo {};
};
} // namespace FEX::Windows
