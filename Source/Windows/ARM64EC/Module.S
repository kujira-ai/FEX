.text
.balign 16

  // __os_arm64x_x64_jump in ARM64EC docs
  // Expects target code address in x9
.globl DispatchJump
DispatchJump:
  str lr, [sp, #-8]! // Push return address to stack, this will be popped by the x86 RET instr.
  b check_target_ec

  // __os_arm64x_dispatch_ret in ARM64EC docs
  // Expects target code address in lr
.globl RetToEntryThunk
RetToEntryThunk:
  mov x9, lr

check_target_ec:
  mrs x18, tpidr_el0
  // Check if target is in fact x86 code
  ldr x16, [x18, #0x60] // TEB->PEB
  ldr x16, [x16, #0x368] // PEB->EcCodeBitMap
  lsr x17, x9, #15
  and x17, x17, #0x1fffffffffff8
#ifdef FEX_ON_WINE_APPLE
  // NULL map: no EC bits → treat as x64 (enter_jit). Full map has no OOB.
  cbz x16, enter_jit
#endif
  ldr x16, [x16, x17]
  lsr x17, x9, #12
  lsr x16, x16, x17
  tbnz x16, #0, ExitFunctionEC
  b enter_jit

  // __os_arm64x_dispatch_call_no_redirect in ARM64EC docs
  // Expects target code address in x9, and to be called using a 'blr x16' instruction.
.globl ExitToX64
ExitToX64:
#ifndef FEX_ON_WINE_APPLE
  str lr, [sp, #-8]! // Push return address to stack, this will be popped by the x86 RET instr.
#else
  // WineAppleEnterEC is store-PC+ret (no guest x86 RET). Do not push lr — that
  // left SP permanently wrong and crashed iexit_thunk epilogues (write@0 / ldp).
#endif

enter_jit:
#ifdef FEX_ON_WINE_APPLE
  // No stack use: hybrid check_target_ec can enter with unusable SP (stp → write@0).
  // Prefer tpidr_el0 as TEB; if implausible, try x18 as-is.
  mrs x18, tpidr_el0
  lsr x15, x18, #32
  cbnz x15, 1f
  // tpidr not a high pointer — cannot recover without stack/FEXSync
  b ExitFunctionEC
1:
  ldr x17, [x18, #0x1788] // TEB->ChpeV2CpuAreaInfo
  cbz x17, ExitFunctionEC
  ldr x16, [x17, #0x30] // EmulatorData[0] StateFrame
  cbz x16, ExitFunctionEC
  lsr x15, x16, #32
  cbz x15, ExitFunctionEC
  ldr x15, [x17, #0x38] // EmulatorData[1] ThreadState
  cbz x15, ExitFunctionEC
  // EnterEC is store-PC+ret on wine-apple (no LoopTop yet).
  ldr x16, [x17, #0x40] // EmulatorData[2] EnterEC
  cbz x16, ExitFunctionEC
  br x16
#else
  mrs x18, tpidr_el0
  ldr x17, [x18, #0x1788] // TEB->ChpeV2CpuAreaInfo
  cbz x17, ExitFunctionEC
  ldr x16, [x17, #0x30] // ChpeV2CpuAreaInfo->EmulatorData[0] - StateFrame
  cbz x16, ExitFunctionEC
  lsr x15, x16, #32
  cbz x15, ExitFunctionEC
  ldr x15, [x17, #0x38] // ChpeV2CpuAreaInfo->EmulatorData[1] - ThreadState
  cbz x15, ExitFunctionEC
  mov w16, #1
  strb w16, [x17, #0x0] // ChpeV2CpuAreaInfo->InSimulation
  ldr x16, [x17, #0x40] // ChpeV2CpuAreaInfo->EmulatorData[2] - DispatcherLoopTopEnterEC
  cbz x16, ExitFunctionEC
  br x16 // DispatcherLoopTopEnterEC(RIP:x9, CPUArea:x17)
#endif

#ifdef FEX_ON_WINE_APPLE
// EP looks like x64 → FillSRA. ARM64EC wineboot/start (adrp/stp) ret native.
// No C/svc (BeginSim saves ntdll Rip in x4; C would clobber). x17=CPUArea*, x9=EP.
.globl WineAppleEnterEC
.extern WineAppleRealFillSRA
WineAppleEnterEC:
  ldr x16, [x17, #0x30]          // StateFrame
  cbz x16, 1f
  str x9, [x16, #0x18]           // State.rip
1:
  ldrb w16, [x9]
  cmp w16, #0x90
  b.eq 5f
  cmp w16, #0x66
  b.eq 5f
  cmp w16, #0x48
  b.eq 5f
  cmp w16, #0xe8
  b.eq 5f
  cmp w16, #0xe9
  b.eq 5f
  sub w15, w16, #0x40
  cmp w15, #0x18                 // 0x40–0x57 REX / PUSH r64
  b.hs 8f
5:
  mov w16, #1
  strb w16, [x17]                // InSimulation
  adrp x16, WineAppleRealFillSRA
  ldr x16, [x16, :lo12:WineAppleRealFillSRA]
  cbnz x16, 6f
  ldr x16, [x17, #0x48]
  cbz x16, 8f
6:
  br x16
8:
  ret
  .balign 4
#endif

  // Invoked by KiUserEmulationDispatcher after e.g. an NtContinue to x86 code
.global BeginSimulation
BeginSimulation:
#ifdef FEX_ON_WINE_APPLE
  // Wine PE process/thread start is ARM64 hybrid code. Keep the real process
  // stack (do NOT switch to EmulatorStack — that caused null ProcessHeap /
  // heap handle 0 after attach on gate fe). Resolve TEB, load Rip from Context.
  // Gate fr: C/Darwin clobber x18 across Sync/BeforeNative; stash TEB and
  // re-install tpidr+x18 immediately before br so CRT/wmain see a live TEB.
  bl "#FEXWineAppleBeginSimSetup"
  cbz x0, 1f
  mov x17, x0 // CHPE_V2_CPU_AREA_INFO*
  // x18 holds TEB after BeginSimSetup when restore succeeded.
  mov x15, x18
  // Preserve Area + TEB across C calls (x15/x17 not callee-saved).
  stp x17, x15, [sp, #-16]!
  ldr x0, [x17, #0x18] // ContextAmd64
  bl "#SyncThreadContext"
  ldp x17, x15, [sp], #16
  stp x17, x15, [sp, #-16]!
  ldr x0, [x17, #0x18] // ContextAmd64 for BeforeNativeEntry
  bl "#FEXWineAppleBeforeNativeEntry"
  ldp x17, x15, [sp], #16
  // x0 = Rip (0 = fail)
  cbz x0, 1f
  mov x16, x0
  // Reload args from context (BeforeNative may clobber)
  ldr x8, [x17, #0x18]
  ldr x9, [x8, #0x98]  // Rsp
  ldr x0, [x8, #0x80]  // Rcx
  ldr x1, [x8, #0x88]  // Rdx
  // Re-sync TEB into tpidr/x18 before native entry (Darwin may have wiped x18).
  cbz x15, 3f
  msr tpidr_el0, x15
  mov x18, x15
3:
  // S1: Context.Rip is RtlUserThreadStart; rcx is x64 EP. ntdll check_call
  // with NULL EcBitMap treats EP as native ARM64 (never WineAppleEnterEC).
  // Offer the same FillSRA br here. Miss rets; then br ntdll as before.
  // No C/svc on the FillSRA br. x17=CPUArea.
  mov x4, x16                    // ntdll Rip
  mov x5, x0                     // rcx = guest EP
  mov x6, x9                     // guest Rsp
  mov x9, x0
  bl WineAppleEnterEC
  mov x16, x4
  mov x0, x5
  mov x9, x6
  // Restore Context.Rsp (gn/go SP experiments did not help; keep classic).
  cbz x9, 2f
  mov sp, x9
2:
  br x16
1:
  brk #0x11
#else
  mrs x18, tpidr_el0
  ldr x17, [x18, #0x1788] // TEB->ChpeV2CpuAreaInfo
  ldr x16, [x17, #0x8] // EmulatorStackBase
  mov sp, x16
  ldr x0, [x17, #0x18] // ContextAmd64
  bl "#SyncThreadContext"
  mrs x18, tpidr_el0
  ldr x17, [x18, #0x1788]
  ldr x16, [x17, #0x48] // EmulatorData[3]
  mov x11, #0
  br x16
#endif


  // Called into by FEXCore
  // Expects the target code address in x9
.global ExitFunctionEC
ExitFunctionEC:
  mrs x18, tpidr_el0
  // Clear any the AFP NEP and AH bits in FPCR as native code won't expect their behaviour.
  mrs x17, fpcr
  and x17, x17, #~6 // NEP + AH
  msr fpcr, x17
  ldr x17, [x18, #0x1788] // TEB->ChpeV2CpuAreaInfo
  bl "#StoreJitStateToContextAmd64"
  mrs x18, tpidr_el0
  ldr x17, [x18, #0x1788] // TEB->ChpeV2CpuAreaInfo
  strb wzr, [x17, #0x0] // ChpeV2CpuAreaInfo->InSimulation
  ldr x17, [x17, #0x20] // ChpeV2CpuAreaInfo->SuspendDoorbell
  ldr w17, [x17]
  cbnz w17, ExitFunctionSuspendPoint

.global ExitFunctionSuspendResumePoint
ExitFunctionSuspendResumePoint:
  mrs x18, tpidr_el0
  // Either return to an exit thunk (return to ARM64EC function) or call an entry thunk (call to ARM64EC function).
  // It is assumed that a 'blr x16' instruction is only ever used to call into x86 code from an exit thunk, and that all
  // exported ARM64EC functions have a 4-byte offset to their entry thunk immediately before their first instruction.
  mov x17, x9
  mov w16, #0x200
  movk w16, #0xd63f, lsl 16 // blr x16
  ldursw x23, [x17, #-0x4] // Load either the entry thunk offset or the calling instruction.
  cmp w23, w16
  beq ret_sp_aligned

#ifdef FEX_ON_WINE_APPLE
  // llvm-mingw ARM64EC often has a prior insn at [fn-4], not a thunk offset.
  cmp w23, #0x4000
  b.ge 1f
  cmn w23, #0x4000
  b.lt 1f
#endif
  and x23, x23, #-0x4
  add x17, x17, x23 // Resolve entry thunk address.
#ifdef FEX_ON_WINE_APPLE
  b 2f
1:
  mov x17, x9
2:
#endif

  mov x23, sp
  tbz x23, #3, call_sp_misaligned
  ldr lr, [x23], #0x8 // Pop the return address into lr.
  mov sp, x23

call_sp_aligned:
  stp x9, x17, [sp, #-16]!
  bl "#ApplyJitStateToCpuForEcEntry"
  mrs x18, tpidr_el0
  ldp x9, x17, [sp], #16
  br x17

call_sp_misaligned:
  // In the case of the x64 caller leaving sp only 8-byte aligned, leave the return address on the stack to keep 16-byte
  // alignment and have the callee return to an x86 ret instruction. FEX can then return to the actual caller keeping
  // the misaligned RSP.
  // jul10ai: do not load PE global X64ReturnInstr (RO 16k page). Host-mmap page via helper.
  stp x9, x17, [sp, #-16]!
  bl "#FEXGetX64ReturnInstr"
  mov lr, x0
  ldp x9, x17, [sp], #16
  cbz lr, ret_sp_aligned
  stp x9, x17, [sp, #-16]!
  bl "#ApplyJitStateToCpuForEcEntry"
  mrs x18, tpidr_el0
  ldp x9, x17, [sp], #16
  br x17

ret_sp_aligned:
  br x17

.global ExitFunctionSuspendPoint
ExitFunctionSuspendPoint:
  brk #0xCAFE
  // Resume will jump back to `ExitFunctionSuspendResumePoint`

  // Makes a wrapper for calling a system call directly, skipping the usual ntdll thunks
#define HASH #
#define DIRECT_SYSCALL_WRAPPER(Name, WineIdName, WindowsId) \
  .global Name; \
  Name:; \
    adrp x16, WineSyscallDispatcher; \
    ldr x16, [x16, HASH:lo12:WineSyscallDispatcher]; \
    cbz x16, 1f; \
    mov x9, x30; \
    adrp x8, WineIdName; \
    ldr x8, [x8, HASH:lo12:WineIdName]; \
    blr x16; \
    ret; \
  1:; \
    svc HASH WindowsId; \
    ret

  // Allows for continuing from a full native context, as the NTDLL NtContinue export takes in an x64 context with EC and
  // the conversion to that loses the ARM64EC ABI-disallowed registers that FEX uses.
DIRECT_SYSCALL_WRAPPER("#NtContinueNative", WineNtContinueSyscallId, 0x43)

  // Both of these are wrapped as FEX needs them to setup its call checker at startup time and their NTDLL thunks could
  // already be patched by then (and because the call checker isn't installed, their patched x86 versions would be invoked
  // when called by FEX).
DIRECT_SYSCALL_WRAPPER("#NtAllocateVirtualMemoryNative", WineNtAllocateVirtualMemorySyscallId, 0x18)
DIRECT_SYSCALL_WRAPPER("#NtProtectVirtualMemoryNative", WineNtProtectVirtualMemorySyscallId, 0x50)
DIRECT_SYSCALL_WRAPPER("#NtFreeVirtualMemoryNative", WineNtFreeVirtualMemorySyscallId, 0x1e)

  // A replacement for the standard ARM64EC call checker that ignores any FFS patches and always redirects to a function's
  // native implementation. As the only library FEX calls into is NTDLL, this is done using a LUT generated at init time.
  // Expects the FFS address in x11, exit thunk address in x10 (unused) and it's own address in x9. Return address is in x11.
.global "CheckCall"
"CheckCall":
  adrp x9, NtDllBase
  ldr x9, [x9, #:lo12:NtDllBase]
  subs x16, x11, x9
  b.lo wine_fallback
  adrp x17, NtDllRedirectionLUTSize
  ldr x17, [x17, #:lo12:NtDllRedirectionLUTSize]
  cmp x16, x17
  b.hi wine_fallback
  adrp x17, NtDllRedirectionLUT
  ldr x17, [x17, #:lo12:NtDllRedirectionLUT]
  ldr w11, [x17, x16, lsl #2]
  add x11, x11, x9
#ifdef FEX_ON_WINE_APPLE
  mrs x18, tpidr_el0
#endif
  ret
wine_fallback:
#ifdef FEX_ON_WINE_APPLE
  // Inline Wine's arm64x_check_call_early (IAT + EcCodeBitMap, no syscall/JIT dispatch).
  mrs x18, tpidr_el0
  1:
  ldr x16, [x18, #0x60]
  lsr x17, x11, #18
  ldr x16, [x16, #0x368]
  lsr x9, x11, #12
  cbz x16, 2f
  ldr x16, [x16, x17, lsl #3]
  lsr x16, x16, x9
  tbnz x16, #0, 2f
  ldrb w16, [x11]
  cmp w16, #0xff
  b.ne 2f
  ldrb w16, [x11, #1]
  cmp w16, #0x25
  b.ne 2f
  ldr w9, [x11, #2]
  add x16, x11, #6
  ldr x11, [x16, w9, sxtw]
  b 1b
  2:
  ldr x16, [x18, #0x60]
  lsr x17, x11, #18
  ldr x16, [x16, #0x368]
  lsr x9, x11, #12
  cbz x16, 3f
  ldr x16, [x16, x17, lsl #3]
  lsr x16, x16, x9
  tbnz x16, #0, 3f
  mov x9, x11
  mov x11, x10
  3:
  mrs x18, tpidr_el0
  ret
#else
  ret
#endif

  // Expects target address in x0, and the SP to set in x1
.global "#JumpSetStack"
"#JumpSetStack":
  mov sp, x1
  br x0
