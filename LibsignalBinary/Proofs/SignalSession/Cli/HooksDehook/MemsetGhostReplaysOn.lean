/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Memory-Guarded `On` / `S` Replays & `(A1)`+`(A2)` Trap Corollaries (`HooksDehook.MemsetGhostReplaysOn`)

Fixes the unguarded `StubReachesTarget` applicability gap (`rev_c1.md` §4a, `rev_c5.md` §4) across
all `memset` ghost hook variants and wires the generalized `(A1)`+`(A2)` closed-trap lemmas
(`HooksDehook.MemsetLrTrapRet`) into memory-guarded `On`/`S` replays and `Steps` transfer:

1. **Per-Stub Guarded `On` Replays (`StubReachesTargetOn InvMem`)**:
   Instantiates `LinkedCallHookOn.ghostExternReplaysOn_of_linkedCallHook` for `memsetGhostHook`,
   `memsetGhostHookK` (both explicit-`lr` and `noException`-auto-`lr`), `memsetGhostHookBlk21`,
   `memsetGhostHookBlk21K`, `f3MemsetGhostHook`, `f3MemsetGhostHookK`, `f3MemsetGhostHookNarrow`,
   `f3MemsetGhostHookRx`, and `f3MemsetGhostHookRxK`.
2. **Single-Row `GhostExternReplaysS` Packagers**:
   Trajectory-independent `GhostExternReplaysS` witnesses for `memsetGhostHook`,
   `memsetGhostHookK` (polymorphic in outer `keep_any`), and `f3MemsetGhostHookNarrow` (retaining
   `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` as the ghost-arm binder).
3. **Closed-Trap `_of_trap_ret` Guarded `On` Replays & `Steps` Transfer (`(A1)` + `(A2)`)**:
   Discharges `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false` internally via
   `MemsetLrTrapRet.blk21_lr_trap_after_hook_ret` under:
   - `(A1)` `hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false`,
     `∀ msg, sf.status ≠ .Exception msg`, `sf.status ≠ .Halted` (covering `Exited`, `Panicked`,
     `OutOfMemory`, `Signaled`, and subroutine `Returned` when `keepMemsetBlk21 (s0.lr) = false`),
   - `(A2)` per-PC `Blk21TrapHook` existential `hblk21_ext` (supporting mixed ghost tables).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open VerifiedLibraries.Musl (memsetWordsSym)
open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn steps_transfer_ghostOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_linkedCallHook ghostExternReplaysOn_of_single_stub
  ghostExternReplaysS_of_single_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  KeepCoversBlk21 keepCoversBlk21_keepMemsetBlk21 keepMemsetBlk21
  masterMemset_outcome_setPC masterMemset_pre_setPC
  masterMemsetK_outcome_setPC masterMemsetK_pre_setPC
  memsetGhostHook memsetGhostHookBlk21 memsetGhostHookBlk21K memsetGhostHookK
  memsetGhostHookK_keepLr_false_of_noException
  specPreservesFsTrace_masterMemset specPreservesFsTrace_masterMemsetK
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  codeLoaded_stripExecOutside_blk21
  f3MemsetGhostHook f3MemsetGhostHookK f3MemsetGhostHookNarrow f3MemsetGhostHookNarrowK
  f3MemsetGhostHookRange f3MemsetGhostHookRangeK f3RealProg617 f3RealProg617_svc_eq
  keepCoversBlk21_keepRange keepRange mallocngBlockProg21_svc_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet (
  Blk21TrapHook blk21TrapHook_memsetGhostHook_of_cover blk21_lr_trap_after_hook_ret
  blk21_lr_trap_false_ret
)

/-! ## 1. Per-Stub Memory-Guarded `On` Replays (`StubReachesTargetOn InvMem`) -/

/-- Generic memory-guarded `On` replay for plain `memsetGhostHook`. -/
theorem ghostExternReplaysOn_memsetGhostHook
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {stubPc entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      P_sub.CodeLoaded (stripExecOutside keep m))
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg,
        (memsetGhostHook keep P_real P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHook keep P_real P_sub entryTarget u) ∧
      ExecFrozen (memsetGhostHook keep P_real P_sub entryTarget u).mem ∧
      InvMem (memsetGhostHook keep P_real P_sub entryTarget u).mem :=
  ghostExternReplaysOn_of_linkedCallHook
    hsvc_real hsvc_sub hreal_no hsub_no hreal_stub_none hStub hInvLoaded hInvKf
    (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemset keep)
    specPreservesFsTrace_masterMemset
    masterMemset_pre_setPC
    masterMemset_outcome_setPC

/-- `blk21`-specialized memory-guarded `On` replay for `memsetGhostHookBlk21` (lifts
    `(mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m` into `stripExecOutside keep m` via
    `KeepCoversBlk21 keep mmpl`, e.g. `F3CodeInv.mngBlockCodeLoaded` at `j = 21`). -/
theorem ghostExternReplaysOn_memsetGhostHookBlk21
    {InvMem : Memory → Prop}
    {keep : BitVec 64 → Bool} {P_real : Program}
    {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hcover : KeepCoversBlk21 keep mmpl)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m') :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (memsetGhostHookBlk21 keep P_real mmpl u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      InvMem u.mem →
      Steps P_real u (memsetGhostHookBlk21 keep P_real mmpl u) ∧
      ExecFrozen (memsetGhostHookBlk21 keep P_real mmpl u).mem ∧
      InvMem (memsetGhostHookBlk21 keep P_real mmpl u).mem :=
  ghostExternReplaysOn_memsetGhostHook
    hsvc_real (mallocngBlockProg21_svc_eq mmpl) hreal_no
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    hreal_stub_none hStub
    (fun m hfr hinv => codeLoaded_stripExecOutside_blk21 hcover (hInvLoaded m hfr hinv))
    hInvKf

/-! ## 2. Single-Row `GhostExternReplaysS` Packagers -/

/-! ## 3. `(A1)` + `(A2)` Closed-Trap `_of_trap` Guarded `On` Replays & `Steps` Transfer -/

/-- **Per-stub `(A1)` + `(A2)` trap-discharged guarded `On` replay
    (`ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret`):**
    Parametric in `P_ghost` and `P_real` (applicable both to Pass 1 `P_ghost8 → P_A` of a 2-pass
    cutover and to mixed passes), discharging `keepMemsetBlk21 mmpl (u.readReg64 .lr) = false`
    internally from `Steps P_ghost (f_ms u) sf` via `blk21_lr_trap_after_hook_ret` under `(A1)`
    (`hrun_sf'`, `hnoex_sf`, `hnhalt_sf`) and `(A2)` (`hblk21_ext`). -/
theorem ghostExternReplaysOn_memsetGhostHookNarrow_of_trap_ret
    {InvMem : Memory → Prop}
    {P_ghost P_real : Program} {mmpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hblk21_ext : ∀ pc, keepMemsetBlk21 mmpl pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepMemsetBlk21 mmpl pc = true → P_real.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTargetOn InvMem P_real stubPc (mmpl.base 21))
    (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m →
      (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    {sf : State}
    (hrun_sf' : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let f_ms := memsetGhostHookBlk21 (keepMemsetBlk21 mmpl) P_real mmpl
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      Steps P_ghost (f_ms u) sf →
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (f_ms u).status ≠ .Exception msg) →
      u.mem.KeepsFrozen (f_ms u).mem →
      ExecFrozen u.mem →
      InvMem u.mem →
      Steps P_real u (f_ms u) ∧ ExecFrozen (f_ms u).mem ∧ InvMem (f_ms u).mem := by
  have hRep := ghostExternReplaysOn_memsetGhostHookBlk21
    hsvc_real hreal_no (keepCoversBlk21_keepMemsetBlk21 mmpl)
    hreal_stub_none hStub hInvLoaded hInvKf
  refine ⟨hRep.1, fun u hrest hpc hrun hnoex hkf hfr hinv => ?_⟩
  have hlr_false : keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
    blk21_lr_trap_after_hook_ret
      (blk21TrapHook_memsetGhostHook_of_cover (fun _ h => h) P_real
        (mallocngBlockProg mmpl 21 Syscall.standard) (mmpl.base 21))
      hblk21_ext
      ((hInvLoaded u.mem hfr hinv).of_keepsFrozen hkf)
      hrest hrun hrun_sf' hnoex_sf hnhalt_sf
  exact hRep.2 u hpc hrun hnoex hfr hlr_false hinv

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplaysOn
