// Dummy FEXCore .text growth to prove WineAppleEnterEC PE RVA is pinned.
// Not emit. Not G3h/G3i/lw. Size via FEX_WINE_APPLE_DUMMY_NOPS (CMake 256).
#if defined(FEX_ON_WINE_APPLE) && FEX_ON_WINE_APPLE
#ifndef FEX_WINE_APPLE_DUMMY_NOPS
#define FEX_WINE_APPLE_DUMMY_NOPS 256
#endif
#define FEX_WA_STR(x) #x
#define FEX_WA_XSTR(x) FEX_WA_STR(x)

extern "C" __attribute__((used, noinline)) void FEXWineAppleDummyFexcoreGrowth() {
  asm volatile(".rept " FEX_WA_XSTR(FEX_WINE_APPLE_DUMMY_NOPS) "\n nop\n .endr");
}
#else
extern "C" void FEXWineAppleDummyFexcoreGrowth() {}
#endif
