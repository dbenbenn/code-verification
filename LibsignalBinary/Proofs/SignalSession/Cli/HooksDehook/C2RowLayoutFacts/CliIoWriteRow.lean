/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbcRow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic

/-!
# Stage-B `GhostRowOk` / `ExtraRowFullOk` & `HookOk` Glue for `write_stdout` and `write_file` (`C2RowLayoutFacts.CliIoWriteRow`)

Instantiates `CliIoWriteGhostReplays` (`writeStdoutGhost`, `writeFileGhost`, and
`writeFileFdsGhost`) on the 0-hook stock ELF (`0d6227d2…`) using `c2CliIoMpl`, `c2MuslSysMpl`,
`f3WriteLoRxProg`, and the `seg[1]` `:text_a` + `seg[2]` keep hull `c2KeepWriteIo`:
1. Concrete `W`-independent `(γ, tp)`-independent ghost hooks `c2WriteStdoutGhost`,
   `c2WriteFileGhost`, and `c2WriteFileFdsGhost`.
2. Concrete `HookOk` theorems (`c2_writeStdoutGhost_ok_sat`, `c2_writeFileGhost_ok_sat`,
   `c2_writeFileGhost_ok_sat_clampedGuard`, `c2_writeFileFdsGhost_ok_noFds_sat`,
   `c2_writeFileFdsGhost_ok_sat`).
3. Trajectory-aware `GhostRowOk`, `ExtraRowFullOk`, and `ExtraRowReplayOn` theorems (generic
   `_of_inv`, specialized `F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs` / `True` / `FdsGe3Closed`
   forms, and `guardOf` forms for `ExtraListReplaysOn`).
4. Unconditional `HookNoAllocFailed` witnesses (`c2_writeStdoutGhost_noAllocFailed`,
   `c2_writeFileGhost_noAllocFailed`, `c2_writeFileFdsGhost_noAllocFailed`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Musl (muslSysPlacedLib)
open CryptoVerification
  (LibsignalPlacement libsignalSessionExterns lsmpl signalSessionIoMultiLib)
open CryptoVerification.SignalSession
  (CliHooks cliCratePanicSyms cliElfBytes cliExternsPlaced isCliPanicSymbolPlaced
   libsignalSessionLib lsWriteFileSym lsWriteStdoutSym writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine (f3RxWordCount fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed TraceDeltaNoAllocFailed execSyscall_noAllocFailed
   steps_traceDeltaNoAllocFailed traceDeltaNoAllocFailed_of_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (c2_aesCbc_hKeep c2_mallocng_lt_writeLo keepRxSeg keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWrite
  (c2CliIoMpl c2CliIoMpl_placeable c2MuslSysMpl c2MuslSysMpl_placeable c2WriteLoByteLen
   c2_cliIo_codeLoaded_of_f3CodeInv c2_cliIo_seg2_in_writeLo c2_lsRetAddr624_lt_writeFile
   c2_muslSys_codeLoadedWhere9_of_writeLo c2_resolve_writeFile_eq c2_resolve_writeFile_resolve
   c2_resolve_writeStdout_eq c2_resolve_writeStdout_resolve f3WriteLoRxProg f3WriteLoRxProg_base
   f3WriteLoRxProg_codeLoaded_of_trial f3WriteLoRxProg_code_len f3WriteLoRxProg_no_ext
   f3WriteLoRxProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen libsignalSessionExterns_resolve_eq_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617 ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (withCallGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliIoWriteGhostReplays
  (writeFileCoreSpecOf writeFileFdsGhost writeFileFdsGhost_extraRowFullOk
   writeFileFdsGhost_ok_noFds_sat writeFileFdsGhost_ok_sat
   writeFileFdsGhost_rowOk writeFileFdsGhost_steps_or_fallback
   writeFileGhost writeFileGhost_extraRowFullOk
   writeFileGhost_ok_sat writeFileGhost_ok_sat_clampedGuard writeFileGhost_rowOk
   writeFileHook_traceDelta_noAllocFailed writeFileNoFdsSpecPlacedSat
   writeIoLinkedGhost writeIoLinkedGhost_steps_or_fallback writeStdoutCoreSpecOf writeStdoutGhost
   writeStdoutGhost_ok_sat writeStdoutGhost_rowOk writeStdoutGhost_rowSpecOk
   writeStdoutHook_traceDelta_noAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraRowFullOk GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
  (writeFileSpecPlacedSat writeStdoutSpecPlacedSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (GhostRowSpecOk WriteFileRowOk)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym
  (CliIoBlockNoExtern cliIoCloseSym cliIoErrnoLocationSym cliIoOpenSym
   cliIoWriteFileSym cliIoWriteStdoutSym cliIoWriteSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3RxSegBase)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4WriteFileAddr wp4WriteStdoutAddr)

/-! ## 1. `c2KeepWriteIo` Keep Hull & Concrete Ghost Definitions -/

/-- Segment-`1` `:text_a` interval `[wp4WriteFileAddr, c2FirstExternStubAddr)` (`0x473724..0x47390c`,
    covering `write_file` `0x473724..0x473854` and `write_stdout` `0x473854..0x47390c`) unioned with
    the panic-free `seg[2]` prefix `[f3RxSegBase, c2Lib2TextLo)` (`f3WriteLoRxProg`, covering
    `signalSessionIoMultiLib` blocks `0, 3, 4`, `muslSysPlacedLib` blocks `0..8`, `mallocng`,
    and `memcpy`). -/
@[expose] noncomputable def c2KeepWriteIo (a : BitVec 64) : Bool :=
  decide (wp4WriteFileAddr.toNat ≤ a.toNat ∧ a.toNat < c2FirstExternStubAddr.toNat) ||
    decide ((a - f3RxSegBase).toNat < c2WriteLoByteLen)

/-- Concrete 0-hook stock-ELF `writeStdoutGhost` (`lsWriteStdoutSym`). -/
@[expose] noncomputable def c2WriteStdoutGhost [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    State → State :=
  writeStdoutGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

/-- Concrete 0-hook stock-ELF `writeFileGhost` (`lsWriteFileSym`). -/
@[expose] noncomputable def c2WriteFileGhost [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    State → State :=
  writeFileGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

/-- Concrete 0-hook stock-ELF `writeFileFdsGhost` (`lsWriteFileSym`, `FdsGe3Closed`-fallback twin). -/
@[expose] noncomputable def c2WriteFileFdsGhost [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    State → State :=
  writeFileFdsGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

/-! ## 2. Closed Callee Tie, `keep`, `externAt?`, & `CodeLoaded` Dischargers -/

private theorem c2_cliIo_resOpen_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoOpenSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "open" := by
  rfl_kernel

private theorem c2_cliIo_resErrno_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoErrnoLocationSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "__errno_location" := by
  rfl_kernel

private theorem c2_cliIo_resWrite_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "write" := by
  rfl_kernel

private theorem c2_cliIo_resClose_fnAddr :
    signalSessionIoMultiLib.resolve c2CliIoMpl cliIoCloseSym =
      muslSysPlacedLib.fnAddr c2MuslSysMpl "close" := by
  rfl_kernel

theorem c2KeepWriteIo_of_writeLo {a : BitVec 64}
    (hk : decide ((a - f3RxSegBase).toNat < c2WriteLoByteLen) = true) :
    c2KeepWriteIo a = true := by
  unfold c2KeepWriteIo
  rw [hk, Bool.or_true]

theorem c2_writeIo_keepMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (a : BitVec 64) (hsome : (mallocngLib.findCodeBlock mmpl a).isSome = true) :
    c2KeepWriteIo a = true := by
  have heq : c2WriteLoByteLen = 0x5798 := rfl
  exact c2KeepWriteIo_of_writeLo (heq ▸ c2_mallocng_lt_writeLo mmpl hMm a hsome)

theorem c2_writeIo_lr_out [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (lr : BitVec 64) (hlr : LsRetAddr624 lr) :
    c2KeepWriteIo lr = false := by
  have hlt := c2_lsRetAddr624_lt_writeFile hLsLsmpl hlr
  have hrx := c2_aesCbc_hKeep hLsLsmpl hlr
  rw [keepRxSeg_eq_lt, decide_eq_false_iff_not] at hrx
  have hle : c2WriteLoByteLen ≤ 4 * f3RxWordCount := by decide
  unfold c2KeepWriteIo
  rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  exact ⟨by omega, by omega⟩

set_option maxRecDepth 2000000 in
private theorem libsignalSessionExterns_sub_names :
    (libsignalSessionExterns.all lsInternedMultiLib.names.contains) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem externs_in_writeIo_unhooked :
    (libsignalSessionExterns.all fun e =>
      let a := cliElfMultiPlacement.ρ e
      let inSeg1 := Nat.ble wp4WriteFileAddr.toNat a.toNat &&
        Nat.blt a.toNat c2FirstExternStubAddr.toNat
      let inSeg2 := Nat.blt (a - f3RxSegBase).toNat c2WriteLoByteLen
      !(inSeg1 || inSeg2) ||
        !(cliCratePanicSyms.contains e || Arm64.Obj.isPanicSymbolFast e)) = true := by
  rfl_kernel

private theorem findSome?_eq_none_of_forall {α γ : Type}
    {xs : List α} {g : α → Option γ}
    (h : ∀ e ∈ xs, g e = none) :
    xs.findSome? g = none := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.findSome?_cons, h a (.head _)]
    exact ih (fun e he => h e (.tail _ he))

private theorem resolve_extern_eq_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {e : String} (he : e ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve mpl e = cliElfMultiPlacement.ρ e := by
  have hname : e ∈ lsInternedMultiLib.names :=
    List.contains_iff_mem.mp (List.all_eq_true.mp libsignalSessionExterns_sub_names e he)
  exact ((cliElf_linkedAt_unique hLs).2.1 e hname).trans
    (libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement e he)

theorem c2_writeIo_realNoExt {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (pc : BitVec 64) (hk : c2KeepWriteIo pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
  refine findSome?_eq_none_of_forall fun e he => ?_
  by_cases hres : libsignalSessionLib.resolve mpl e = pc
  · have hrho : cliElfMultiPlacement.ρ e = pc :=
      (resolve_extern_eq_rho hLs he).symm.trans hres
    have hall := List.all_eq_true.mp externs_in_writeIo_unhooked e he
    dsimp only at hall
    rw [hrho] at hall
    have hin :
        (Nat.ble wp4WriteFileAddr.toNat pc.toNat &&
            Nat.blt pc.toNat c2FirstExternStubAddr.toNat ||
          Nat.blt (pc - f3RxSegBase).toNat c2WriteLoByteLen) = true := by
      unfold c2KeepWriteIo at hk
      rcases Bool.or_eq_true_iff.mp hk with h1 | h2
      · obtain ⟨hlo, hhi⟩ := of_decide_eq_true h1
        rw [Nat.ble_eq.mpr hlo, Nat.blt_eq.mpr hhi]
        rfl
      · rw [Nat.blt_eq.mpr (of_decide_eq_true h2), Bool.or_true]
    rw [hin] at hall
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hall
    have hnone : cliExternsPlaced mmpl W e = none := by
      unfold cliExternsPlaced isCliPanicSymbolPlaced
      rw [Arm64.Obj.rust_isPanicSymbol_eq_fast, hall]
      rfl
    rw [hnone, ite_self]
  · simp [beq_eq_false_iff_ne.mpr hres]

private theorem c2KeepWriteIo_writeFileAddr : c2KeepWriteIo wp4WriteFileAddr = true := by
  unfold c2KeepWriteIo
  have h : wp4WriteFileAddr.toNat ≤ wp4WriteFileAddr.toNat ∧
      wp4WriteFileAddr.toNat < c2FirstExternStubAddr.toNat := by decide
  rw [decide_eq_true h, Bool.true_or]

private theorem c2KeepWriteIo_writeStdoutAddr : c2KeepWriteIo wp4WriteStdoutAddr = true := by
  unfold c2KeepWriteIo
  have h : wp4WriteFileAddr.toNat ≤ wp4WriteStdoutAddr.toNat ∧
      wp4WriteStdoutAddr.toNat < c2FirstExternStubAddr.toNat := by decide
  rw [decide_eq_true h, Bool.true_or]

theorem c2_writeFile_realStubNone {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
      (libsignalSessionLib.resolve mpl lsWriteFileSym) = none := by
  rw [c2_resolve_writeFile_eq hLs]
  exact c2_writeIo_realNoExt hLs W wp4WriteFileAddr c2KeepWriteIo_writeFileAddr

theorem c2_writeStdout_realStubNone {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
      (libsignalSessionLib.resolve mpl lsWriteStdoutSym) = none := by
  rw [c2_resolve_writeStdout_eq hLs]
  exact c2_writeIo_realNoExt hLs W wp4WriteStdoutAddr c2KeepWriteIo_writeStdoutAddr

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

theorem c2_writeFile_stubSteps {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsWriteFileSym)
    (_hrun : u.status = .Running) (_hFr : ExecFrozen u.mem) (_hInv : InvS u) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (u.setPC (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)) := by
  rw [setPC_eq_self_of_pc_eq (hpc.trans (c2_resolve_writeFile_resolve hLs))]
  exact Steps.refl u

theorem c2_writeStdout_stubSteps {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) (u : State)
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsWriteStdoutSym)
    (_hrun : u.status = .Running) (_hFr : ExecFrozen u.mem) (_hInv : InvS u) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u
      (u.setPC (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)) := by
  rw [setPC_eq_self_of_pc_eq (hpc.trans (c2_resolve_writeStdout_resolve hLs))]
  exact Steps.refl u

private theorem codeLoaded_strip_of_keep {P : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hL : P.CodeLoaded m)
    (hk : ∀ i : Nat, i < P.code.length → keep (P.base + BitVec.ofNat 64 i) = true) :
    P.CodeLoaded (stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  rw [strip_read8, strip_perm_of_keep (hk i hi), strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem c2KeepWriteIo_of_writeLo_offset {i : Nat} (hi : i < c2WriteLoByteLen) :
    c2KeepWriteIo (f3RxSegBase + BitVec.ofNat 64 i) = true := by
  have htop : c2WriteLoByteLen < 2 ^ 64 := by decide
  have hi64 : i < 2 ^ 64 := Nat.lt_trans hi htop
  have hlt : (f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase).toNat < c2WriteLoByteLen := by
    have hsub : f3RxSegBase + BitVec.ofNat 64 i - f3RxSegBase = BitVec.ofNat 64 i := by bv_omega
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    exact hi
  exact c2KeepWriteIo_of_writeLo (decide_eq_true hlt)

theorem c2_writeIo_invCodeSub {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (u : State) (_hFr : ExecFrozen u.mem) (hu : InvS u) :
    f3WriteLoRxProg.CodeLoaded (stripExecOutside c2KeepWriteIo u.mem) := by
  refine codeLoaded_strip_of_keep (f3WriteLoRxProg_codeLoaded_of_trial (hInv u hu).rxCode) fun i hi => ?_
  rw [f3WriteLoRxProg_code_len] at hi
  rw [f3WriteLoRxProg_base]
  exact c2KeepWriteIo_of_writeLo_offset hi

private theorem c2_cliIo_blk1_hi :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).base.toNat +
      (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).code.length ≤
      c2FirstExternStubAddr.toNat :=
  Nat.ble_eq.mp (by rfl_kernel)

private theorem c2_cliIo_blk2_hi :
    (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).base.toNat +
      (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).code.length ≤
      c2FirstExternStubAddr.toNat :=
  Nat.ble_eq.mp (by rfl_kernel)

private theorem c2KeepWriteIo_of_seg1_bounds {P : Program}
    (hlo : wp4WriteFileAddr.toNat ≤ P.base.toNat)
    (hhi : P.base.toNat + P.code.length ≤ c2FirstExternStubAddr.toNat)
    {i : Nat} (hi : i < P.code.length) :
    c2KeepWriteIo (P.base + BitVec.ofNat 64 i) = true := by
  have htop : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  have hi64 : i < 2 ^ 64 := by omega
  have hadd : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
  unfold c2KeepWriteIo
  rw [decide_eq_true (by omega), Bool.true_or]

private theorem c2KeepWriteIo_of_seg2_block {j : Nat} (hj : j ∈ [0, 3, 4])
    {i : Nat} (hi : i < (signalSessionIoMultiLib.blockProgram c2CliIoMpl j).code.length) :
    c2KeepWriteIo
      ((signalSessionIoMultiLib.blockProgram c2CliIoMpl j).base + BitVec.ofNat 64 i) = true := by
  have hbnd := List.all_eq_true.mp c2_cliIo_seg2_in_writeLo j hj
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Nat.ble_eq] at hbnd
  obtain ⟨hlo, hhi⟩ := hbnd
  generalize signalSessionIoMultiLib.blockProgram c2CliIoMpl j = P at hi hlo hhi ⊢
  have htop : f3RxSegBase.toNat + c2WriteLoByteLen < 2 ^ 64 := by decide
  have hadd : (P.base + BitVec.ofNat 64 i).toNat = P.base.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlt_lo : (P.base + BitVec.ofNat 64 i - f3RxSegBase).toNat < c2WriteLoByteLen := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
    omega
  exact c2KeepWriteIo_of_writeLo (decide_eq_true hlt_lo)

theorem c2_writeIo_invCodeIo {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (u : State) (_hFr : ExecFrozen u.mem) (hu : InvS u) :
    signalSessionIoMultiLib.CodeLoaded c2CliIoMpl (stripExecOutside c2KeepWriteIo u.mem) := by
  have hCode := c2_cliIo_codeLoaded_of_f3CodeInv hLs (hInv u hu)
  have hlen : signalSessionIoMultiLib.blocks.length = 5 := by decide
  intro j hj
  have hblk := hCode j hj
  rw [hlen] at hj
  match j, hj with
  | 0, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWriteIo_of_seg2_block (by decide) hi
  | 1, _ =>
    have hlo : wp4WriteFileAddr.toNat ≤
        (signalSessionIoMultiLib.blockProgram c2CliIoMpl 1).base.toNat := Nat.le_refl _
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWriteIo_of_seg1_bounds hlo c2_cliIo_blk1_hi hi
  | 2, _ =>
    have hlo : wp4WriteFileAddr.toNat ≤
        (signalSessionIoMultiLib.blockProgram c2CliIoMpl 2).base.toNat := by
      change wp4WriteFileAddr.toNat ≤ wp4WriteStdoutAddr.toNat
      decide
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWriteIo_of_seg1_bounds hlo c2_cliIo_blk2_hi hi
  | 3, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWriteIo_of_seg2_block (by decide) hi
  | 4, _ =>
    exact codeLoaded_strip_of_keep hblk fun _ hi =>
      c2KeepWriteIo_of_seg2_block (by decide) hi

/-! ## 3. Concrete `HookOk` Theorems -/

theorem c2_writeStdoutGhost_ok_sat [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (c2WriteStdoutGhost mmpl brkStart lim stk)
      (withLsRet (writeStdoutSpecPlacedSat
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeStdoutGhost_ok_sat
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 2)
    c2_cliIo_resWrite_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    γ tp hEnf

theorem c2_writeFileGhost_ok_sat [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (c2WriteFileGhost mmpl brkStart lim stk)
      (withLsRet (writeFileSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeFileGhost_ok_sat
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    γ tp hEnf

theorem c2_writeFileGhost_ok_sat_clampedGuard [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (c2WriteFileGhost mmpl brkStart lim stk)
      (withLsRet (withCallGuard (fun (x, _) _ => x.bs.length ≤ Arm64.FS_SAFE_MAX_FILESIZE)
        (writeFileSpecPlacedSat cliIo
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk))) :=
  writeFileGhost_ok_sat_clampedGuard
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    γ tp hEnf

theorem c2_writeFileFdsGhost_ok_noFds_sat [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (c2WriteFileFdsGhost mmpl brkStart lim stk)
      (withLsRet (writeFileNoFdsSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeFileFdsGhost_ok_noFds_sat
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    γ tp hEnf

theorem c2_writeFileFdsGhost_ok_sat [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (γ : GhostName) (tp : BitVec 64)
    (hEnf : lim.enforced = true := by decide) :
    HookOk (c2WriteFileFdsGhost mmpl brkStart lim stk)
      (withLsRet (writeFileSpecPlacedSat cliIo
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim stk)) :=
  writeFileFdsGhost_ok_sat
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    γ tp hEnf

/-! ## 4. `GhostRowSpecOk` / `WriteFileRowOk`, `GhostRowOk`, & `ExtraRowFullOk` Theorems -/

theorem c2_writeStdoutGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    GhostRowSpecOk lsWriteStdoutSym (c2WriteStdoutGhost mmpl brkStart lim stk) :=
  writeStdoutGhost_rowSpecOk c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

theorem c2_writeFileGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowOk (c2WriteFileGhost mmpl brkStart lim stk) :=
  writeFileGhost_rowOk c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

theorem c2_writeFileFdsGhost_rowSpecOk [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    WriteFileRowOk (c2WriteFileFdsGhost mmpl brkStart lim stk) :=
  writeFileFdsGhost_rowOk c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk

theorem c2_writeStdoutGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    GhostRowOk mpl mmpl InvS EG lsWriteStdoutSym (fun _ => True)
      (c2WriteStdoutGhost mmpl brkStart lim stk) :=
  writeStdoutGhost_rowOk
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 2)
    c2_cliIo_resWrite_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    (c2_writeIo_lr_out hLsLsmpl)
    (c2_writeStdout_realStubNone hLs)
    (fun _ => rfl)
    (c2_writeIo_realNoExt hLs)
    (c2_writeStdout_stubSteps hLs)
    (c2_writeIo_invCodeSub hInv)
    (c2_writeIo_invCodeIo hLs hInv)
    (fun _ u v _ hkf _ hfs hu => hInvKeep u v hu hkf hfs)
    hEnf

theorem c2_writeStdoutGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsWriteStdoutSym
      (fun _ => True)
      (c2WriteStdoutGhost mmpl brkStart lim stk) :=
  c2_writeStdoutGhost_rowOk_of_inv lsmpl mmpl brkStart lim stk
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hLs hLs hMm
    (fun _ h => h.1)
    (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
    hEnf

theorem c2_writeStdoutGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsWriteStdoutSym
      (guardOf lsWriteStdoutSym)
      (c2WriteStdoutGhost mmpl brkStart lim stk) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_writeStdoutGhost_rowOk_lsmpl_and_fs mmpl brkStart lim stk PredFs EG hLs hMm hEnf
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

theorem c2_writeStdoutGhost_extraRowFullOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsWriteStdoutSym (guardOf lsWriteStdoutSym)
      (c2WriteStdoutGhost mmpl brkStart lim stk) :=
  (c2_writeStdoutGhost_rowOk_guardOf mmpl brkStart lim stk PredFs EG guardOf hLs hMm
    hEnf).toExtraRowFullOk

theorem c2_writeFileGhost_extraRowFullOk_of_inv [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (c2WriteFileGhost mmpl brkStart lim stk) :=
  writeFileGhost_extraRowFullOk
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    (c2_writeIo_lr_out hLsLsmpl)
    (c2_writeFile_realStubNone hLs)
    (fun _ => rfl)
    (c2_writeIo_realNoExt hLs)
    (c2_writeFile_stubSteps hLs)
    (c2_writeIo_invCodeSub hInv)
    (c2_writeIo_invCodeIo hLs hInv)
    hInvStep
    hEnf

theorem c2_writeFileGhost_extraRowFullOk_lsmpl_fds [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (PredFs : FsState → Prop)
    (hPredFds : ∀ fs1 fs2 : FsState, fs2.fds = fs1.fds → PredFs fs1 → PredFs fs2)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsWriteFileSym
      (fun _ => True)
      (c2WriteFileGhost mmpl brkStart lim stk) :=
  c2_writeFileGhost_extraRowFullOk_of_inv lsmpl mmpl brkStart lim stk
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    hLs hLs hMm
    (fun _ h => h.1)
    (fun _ u v _ hkf _ hfds _ hinv =>
      ⟨F3CodeInv.of_keepsFrozen hinv.1 hkf, hPredFds u.fs v.fs hfds hinv.2⟩)
    hEnf

theorem c2_writeFileGhost_extraRowFullOk_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (PredFs : FsState → Prop)
    (hPredFds : ∀ fs1 fs2 : FsState, fs2.fds = fs1.fds → PredFs fs1 → PredFs fs2)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsWriteFileSym
      (guardOf lsWriteFileSym)
      (c2WriteFileGhost mmpl brkStart lim stk) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_writeFileGhost_extraRowFullOk_lsmpl_fds mmpl brkStart lim stk PredFs hPredFds EG hLs hMm hEnf
  exact ⟨hSpec, hRep.mono_guard (fun _ _ => trivial)⟩

theorem c2_writeFileGhost_extraRowFullOk_true_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ True) EG lsWriteFileSym
      (guardOf lsWriteFileSym)
      (c2WriteFileGhost mmpl brkStart lim stk) :=
  c2_writeFileGhost_extraRowFullOk_guardOf mmpl brkStart lim stk (fun _ => True)
    (fun _ _ _ h => h) EG guardOf hLs hMm hEnf

theorem c2_writeFileFdsGhost_extraRowFullOk_of_inv [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvFds : ∀ u : State, InvS u → FdsGe3Closed u.fs)
    (hInvStep : ∀ (W : CliHooks) (u v : State),
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v →
      u.mem.KeepsFrozen v.mem → ExecFrozen v.mem →
      v.fs.fds = u.fs.fds → FsTraced IsFsC u v → InvS u → InvS v)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk mpl mmpl InvS EG lsWriteFileSym (fun _ => True)
      (c2WriteFileFdsGhost mmpl brkStart lim stk) :=
  writeFileFdsGhost_extraRowFullOk
    f3WriteLoRxProg_svc
    f3WriteLoRxProg_no_ext
    c2CliIoMpl_placeable
    c2MuslSysMpl_placeable
    (fun _ hRx => c2_muslSys_codeLoadedWhere9_of_writeLo hRx)
    (CliIoBlockNoExtern.of_no_extern f3WriteLoRxProg_no_ext 1)
    c2_cliIo_resOpen_fnAddr
    c2_cliIo_resErrno_fnAddr
    c2_cliIo_resWrite_fnAddr
    c2_cliIo_resClose_fnAddr
    (c2_writeIo_keepMallocng mmpl hMm)
    (c2_writeIo_lr_out hLsLsmpl)
    (c2_writeFile_realStubNone hLs)
    (fun _ => rfl)
    (c2_writeIo_realNoExt hLs)
    (c2_writeFile_stubSteps hLs)
    (c2_writeIo_invCodeSub hInv)
    (c2_writeIo_invCodeIo hLs hInv)
    hInvFds
    hInvStep
    hEnf

theorem c2_writeFileFdsGhost_extraRowFullOk_fdsClosed_guardOf [LibsignalPlacement]
    (mmpl : MultiPlacement)
    (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hEnf : lim.enforced = true := by decide) :
    ExtraRowFullOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ FdsGe3Closed u.fs) EG
      lsWriteFileSym (guardOf lsWriteFileSym)
      (c2WriteFileFdsGhost mmpl brkStart lim stk) := by
  have hFull :=
    c2_writeFileFdsGhost_extraRowFullOk_of_inv lsmpl mmpl brkStart lim stk
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ FdsGe3Closed u.fs) EG
      hLs hLs hMm
      (fun _ h => h.1)
      (fun _ h => h.2)
      (fun _ u v _ hkf _ hfds _ hinv =>
        ⟨F3CodeInv.of_keepsFrozen hinv.1 hkf,
         fun fd hlo hhi => by rw [hfds]; exact hinv.2 fd hlo hhi⟩)
      hEnf
  exact ⟨hFull.1, hFull.2.mono_guard (fun _ _ => trivial)⟩

/-! ## 5. Unconditional `HookNoAllocFailed` Dischargers -/

private theorem f3WriteLoRxProg_steps_traceDeltaNoAllocFailed
    {s0 sf : State} {pc : BitVec 64}
    (hs : Steps f3WriteLoRxProg (s0.setPC pc) sf) :
    TraceDeltaNoAllocFailed s0 sf := by
  have hsvc : HookNoAllocFailed f3WriteLoRxProg.svc :=
    f3WriteLoRxProg_svc ▸ execSyscall_noAllocFailed
  have hhooks : ∀ pc f, f3WriteLoRxProg.externAt? pc = some f → HookNoAllocFailed f :=
    fun pc _ h => nomatch (f3WriteLoRxProg_no_ext pc).symm.trans h
  have htd := steps_traceDeltaNoAllocFailed hsvc hhooks hs
  have htr : (s0.setPC pc).trace = s0.trace := by cases s0; rfl
  rcases htd with ⟨d, hd, hnd⟩
  exact ⟨d, htr ▸ hd, hnd⟩

theorem c2_writeStdoutGhost_noAllocFailed [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookNoAllocFailed (c2WriteStdoutGhost mmpl brkStart lim stk) := by
  intro s0
  rcases writeIoLinkedGhost_steps_or_fallback c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
      (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)
      (writeStdoutCoreSpecOf mmpl brkStart lim stk)
      (fun a b => b.fs = a.fs) writeStdoutHook s0 with
    ⟨sf, hs, heq⟩ | heq | htr
  · change TraceDeltaNoAllocFailed s0
      (writeIoLinkedGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)
        (writeStdoutCoreSpecOf mmpl brkStart lim stk)
        (fun a b => b.fs = a.fs) writeStdoutHook s0)
    rw [heq]
    exact f3WriteLoRxProg_steps_traceDeltaNoAllocFailed hs
  · change TraceDeltaNoAllocFailed s0
      (writeIoLinkedGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteStdoutSym)
        (writeStdoutCoreSpecOf mmpl brkStart lim stk)
        (fun a b => b.fs = a.fs) writeStdoutHook s0)
    rw [heq]
    exact writeStdoutHook_traceDelta_noAllocFailed s0
  · exact traceDeltaNoAllocFailed_of_eq htr

theorem c2_writeFileGhost_noAllocFailed [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookNoAllocFailed (c2WriteFileGhost mmpl brkStart lim stk) := by
  intro s0
  rcases writeIoLinkedGhost_steps_or_fallback c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
      (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
      (writeFileCoreSpecOf mmpl brkStart lim stk)
      (fun a b => b.fs.fds = a.fs.fds) writeFileHook s0 with
    ⟨sf, hs, heq⟩ | heq | htr
  · change TraceDeltaNoAllocFailed s0
      (writeIoLinkedGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
        (writeFileCoreSpecOf mmpl brkStart lim stk)
        (fun a b => b.fs.fds = a.fs.fds) writeFileHook s0)
    rw [heq]
    exact f3WriteLoRxProg_steps_traceDeltaNoAllocFailed hs
  · change TraceDeltaNoAllocFailed s0
      (writeIoLinkedGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl
        (signalSessionIoMultiLib.resolve c2CliIoMpl cliIoWriteFileSym)
        (writeFileCoreSpecOf mmpl brkStart lim stk)
        (fun a b => b.fs.fds = a.fs.fds) writeFileHook s0)
    rw [heq]
    exact writeFileHook_traceDelta_noAllocFailed s0
  · exact traceDeltaNoAllocFailed_of_eq htr

theorem c2_writeFileFdsGhost_noAllocFailed [LibsignalPlacement]
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (stk : Nat) :
    HookNoAllocFailed (c2WriteFileFdsGhost mmpl brkStart lim stk) := by
  intro s0
  rcases writeFileFdsGhost_steps_or_fallback c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl
      brkStart lim stk s0 with
    ⟨sf, hs, heq⟩ | heq | htr
  · change TraceDeltaNoAllocFailed s0
      (writeFileFdsGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk s0)
    rw [heq]
    exact f3WriteLoRxProg_steps_traceDeltaNoAllocFailed hs
  · change TraceDeltaNoAllocFailed s0
      (writeFileFdsGhost c2KeepWriteIo f3WriteLoRxProg c2CliIoMpl mmpl brkStart lim stk s0)
    rw [heq]
    exact writeFileHook_traceDelta_noAllocFailed s0
  · exact traceDeltaNoAllocFailed_of_eq htr

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliIoWriteRow
