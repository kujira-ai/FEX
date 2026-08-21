#pragma once
// Put FEXCore code after Module.S .text. ARM64EC default .text$#Name sorts
// before plain .text$0* ('#' < '0') and moved WineAppleEnterEC.
#pragma clang section text=".text$zzFEX"
