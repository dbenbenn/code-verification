/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook

/-!
# AES-256-CBC Linked Ghost Hooks and `GhostRowOk`

`(γ, tp)`- and `W`-independent linked ghost-call hooks (`aesEncGhost`, `aesDecGhost`),
pointwise `HookOk` (`aesEncGhost_ok`, `aesDecGhost_ok`, `aesDecGhost_weak_ok`), and
`GhostRowOk` (`aesEncGhost_rowOk`, `aesDecGhost_rowOk`) for the linked `.text.lib2`
AES-256-CBC functions (`lsAesEncSym`, `lsAesDecSym`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open CryptoGames.AES256 (aes256Dec aes256Enc)
open CryptoGames.CBC (bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (aesDecHookMallocng aesEncHookMallocng)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsAesDecSym lsAesEncSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocEvent BudgetLimits)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecErrStr2Addr)
open LibsignalBinary.Heap.Fine (f3StdLayout fineCostModel fineCostModelSound)
open LibsignalBinary.Heap.SpecBudget
  (aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec aesEncBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
  (fineAesDec_budget_hookOk fineAesEnc_budget_hookOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant keepFsTrace keepFsTrace_ok
   satisfies_of_stripExecOutside satisfies_stripExecOutside)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
  (aesDecHookMallocng_fs_eq_of_pre aesEncHookMallocng_fs_eq_of_pre)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (fineHookRustCliAllocBudget_pool_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (StubReachesTargetOn execFrozen_aesDecHookMallocng execFrozen_aesEncHookMallocng)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StripRunPanicExterns
  (StripCommExtern externOnlyStdProg externOnlyStdProg_externAt keepOrSubExtern
   stepsVisitedIn_of_stripS_with_externs_inKeep
   steps_externOnly_to_real_of_visitedIn_inKeep stripCommExtern_rustPanicked)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det)

/-! ## 1. Row Anchor Definitions (`aesEncEntryGuard`, `aesDecEntryGuard`, `aesEncGhost`, `aesDecGhost`) -/

/-- Trivial entry guard for `lsAesEncSym` (`.text.lib2`). -/
@[expose] def aesEncEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

theorem aesEncEntryGuard_intro (mpl : Obj.MultiPlacement) (s0 : State) :
    aesEncEntryGuard mpl s0 :=
  trivial

/-- Trivial entry guard for `lsAesDecSym` (`.text.lib2`). -/
@[expose] def aesDecEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

theorem aesDecEntryGuard_intro (mpl : Obj.MultiPlacement) (s0 : State) :
    aesDecEntryGuard mpl s0 :=
  trivial

/-- Guard asserting every extern stub PC of `P_sub` is mapped readable and non-writable (`r = true`,
    `w = false`) in `s.mem`, so `stripExecOutside keep s.mem` leaves it `Frozen` and non-executable. -/
@[expose] def stubFrozenGuard (P_sub : Program) (s : State) : Prop :=
  ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
    (s.mem.perm pc).r = true ∧ (s.mem.perm pc).w = false

/-- Prepend pure read-only extern-stub guard (`r = true ∧ w = false`) and `ExecFrozen s0.mem`
    on `s0.mem` to `spec.pre`. -/
@[expose] def withStubPermRO (P_sub : Program) {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 =>
      ⌜(∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
        (s0.mem.perm pc).r = true ∧ (s0.mem.perm pc).w = false) ∧ ExecFrozen s0.mem⌝ ∗
      spec.pre x s0 }

/-- `.rodata.lib2` address of the 40-byte AES `RCON` round-constant table (`0x414478#64`),
    expressed relative to `cliAesDecErrStr2Addr` (`0x414550#64`). -/
abbrev c2AesRconAddr : BitVec 64 := cliAesDecErrStr2Addr - 216#64

/-- Guard for real ARMv8/Fixslice64 AES-256-CBC execution: extern stubs of `P_sub` are mapped
    readable/non-writable, `c2AesRconAddr` holds `aesRconBytes` read-only in `s.mem`, and
    `brkStart = f3StdLayout.brkStart`. -/
@[expose] def aesStubRconGuard (P_sub : Program) (brkStart : BitVec 64) (s : State) : Prop :=
  stubFrozenGuard P_sub s ∧ RoDataAt s.mem c2AesRconAddr aesRconBytes ∧
    brkStart = f3StdLayout.brkStart

/-- Prepend both `withStubPermRO P_sub` and `withRoData c2AesRconAddr aesRconBytes` to `spec`. -/
@[expose] def withAesStubRconRO (P_sub : Program) {α : Type} (spec : Spec α) : Spec α :=
  withStubPermRO P_sub (withRoData c2AesRconAddr aesRconBytes spec)

/-- `(γ, tp)`-indexed `withLsRet`-narrowed `aesEncBudgetSpec` for `f3LinkedCallHook`. -/
@[expose] def aesEncSpecOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) : Spec (AesCall × fineCostModel.σ) :=
  withLsRet (aesEncBudgetSpec aes256Enc fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)

/-- `(γ, tp)`-indexed `withLsRet`-narrowed `aesDecBudgetSpec` for `f3LinkedCallHook`. -/
@[expose] def aesDecSpecOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) : Spec (AesCall × fineCostModel.σ) :=
  withLsRet (aesDecBudgetSpec aes256Dec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)

/-- `(γ, tp)`-indexed `withLsRet`-narrowed `aesDecWeakBudgetSpec` companion. -/
@[expose] def aesDecWeakSpecOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    (γ : GhostName) (tp : BitVec 64) : Spec (AesCall × fineCostModel.σ) :=
  withLsRet (aesDecWeakBudgetSpec aes256Dec fineCostModel
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)

/-- `(γ, tp)`- and `W`-independent linked ghost-call hook for `lsAesEncSym`. -/
@[expose] noncomputable def aesEncGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) : State :=
  letI := Classical.propDecidable
  if aesStubRconGuard P_sub brkStart s0 then
    f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesEncSpecOf mmpl brkStart lim)
      (aesEncHookMallocng mmpl aes256Enc) s0
  else if ActiveF3CallPre (aesEncSpecOf mmpl brkStart lim) s0 then
    keepFsTrace (aesEncHookMallocng mmpl aes256Enc) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

/-- `(γ, tp)`- and `W`-independent linked ghost-call hook for `lsAesDecSym`. -/
@[expose] noncomputable def aesDecGhost [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) : State :=
  letI := Classical.propDecidable
  if aesStubRconGuard P_sub brkStart s0 then
    f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecSpecOf mmpl brkStart lim)
      (aesDecHookMallocng mmpl aes256Dec) s0
  else if ActiveF3CallPre (aesDecSpecOf mmpl brkStart lim) s0 then
    keepFsTrace (aesDecHookMallocng mmpl aes256Dec) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hG : aesStubRconGuard P_sub brkStart s0) :
    aesEncGhost keep P_sub entryTarget mmpl brkStart lim s0 =
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
        (aesEncSpecOf mmpl brkStart lim)
        (aesEncHookMallocng mmpl aes256Enc) s0 := by
  classical
  unfold aesEncGhost
  simp only [hG, ↓reduceIte]

theorem aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {s0 : State} (hG : aesStubRconGuard P_sub brkStart s0) :
    aesDecGhost keep P_sub entryTarget mmpl brkStart lim s0 =
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
        (aesDecSpecOf mmpl brkStart lim)
        (aesDecHookMallocng mmpl aes256Dec) s0 := by
  classical
  unfold aesDecGhost
  simp only [hG, ↓reduceIte]

/-! ## 2. Unconditional State Preservation & `GhostRowSpecOk` -/

theorem aesEncGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (aesEncGhost keep P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs := by
  classical
  unfold aesEncGhost
  split
  · exact f3LinkedCallHook_fs keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesEncSpecOf mmpl brkStart lim) (aesEncHookMallocng mmpl aes256Enc) s0
  · split <;> rfl

theorem aesDecGhost_fs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) (s0 : State) :
    (aesDecGhost keep P_sub entryTarget mmpl brkStart lim s0).fs = s0.fs := by
  classical
  unfold aesDecGhost
  split
  · exact f3LinkedCallHook_fs keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecSpecOf mmpl brkStart lim) (aesDecHookMallocng mmpl aes256Dec) s0
  · split <;> rfl

theorem aesEncGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (aesEncGhost keep P_sub entryTarget mmpl brkStart lim) := by
  classical
  intro s0
  unfold aesEncGhost
  split
  · exact f3LinkedCallHook_fsT keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesEncSpecOf mmpl brkStart lim) (aesEncHookMallocng mmpl aes256Enc) s0
  · split <;> exact FsTraced.of_eq rfl rfl

theorem aesDecGhost_fsT [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    HookFsTraced IsFsC (aesDecGhost keep P_sub entryTarget mmpl brkStart lim) := by
  classical
  intro s0
  unfold aesDecGhost
  split
  · exact f3LinkedCallHook_fsT keep (externOnlyStdProg P_sub) P_sub entryTarget
      (aesDecSpecOf mmpl brkStart lim) (aesDecHookMallocng mmpl aes256Dec) s0
  · split <;> exact FsTraced.of_eq rfl rfl

theorem aesEncGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (aesEncGhost keep P_sub entryTarget mmpl brkStart lim u).mem := by
  classical
  unfold aesEncGhost
  split
  · unfold f3LinkedCallHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · exact execFrozen_aesEncHookMallocng mmpl aes256Enc u hfr
    · exact hfr
  · split
    · exact execFrozen_aesEncHookMallocng mmpl aes256Enc u hfr
    · exact hfr

theorem aesDecGhost_preserves_execFrozen [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (aesDecGhost keep P_sub entryTarget mmpl brkStart lim u).mem := by
  classical
  unfold aesDecGhost
  split
  · unfold f3LinkedCallHook
    split
    · split
      · rename_i hReal
        exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
      · exact execFrozen_aesDecHookMallocng mmpl aes256Dec u hfr
    · exact hfr
  · split
    · exact execFrozen_aesDecHookMallocng mmpl aes256Dec u hfr
    · exact hfr

theorem aesEncGhost_rowSpecOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsAesEncSym
      (aesEncGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesEncGhost_fs keep P_sub entryTarget mmpl brkStart lim,
   aesEncGhost_fsT keep P_sub entryTarget mmpl brkStart lim, by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.ExtraRowSpec
    have hd1 : (lsAesEncSym == "bcmp") = false := by decide
    have hd2 : (lsAesEncSym == "strlen") = false := by decide
    have hd3 : (lsAesEncSym == "memmove") = false := by decide
    have hd4 : (lsAesEncSym == CryptoVerification.SignalSession.lsFromUtf8Sym) = false := by decide
    have hd5 : (lsAesEncSym == CryptoVerification.SignalSession.lsMemrchrSym) = false := by decide
    have hd6 : (lsAesEncSym == CryptoVerification.SignalSession.lsDurationSinceSym) = false := by decide
    have hd7 : (lsAesEncSym == CryptoVerification.SignalSession.lsTimeAddSym) = false := by decide
    have hd8 : (lsAesEncSym == CryptoVerification.SignalSession.lsBlackBoxSym) = false := by decide
    have hd9 : (lsAesEncSym == CryptoVerification.SignalSession.lsStaticSecretDropSym) = false := by decide
    have hd10 : (lsAesEncSym == CryptoVerification.SignalSession.lsSharedSecretDropSym) = false := by decide
    have hd11 : (lsAesEncSym == lsAesEncSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, Bool.false_eq_true,
      ↓reduceIte]
    trivial⟩

theorem aesDecGhost_rowSpecOk [LibsignalPlacement]
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (mmpl : Obj.MultiPlacement) (brkStart : BitVec 64) (lim : BudgetLimits) :
    GhostRowSpecOk lsAesDecSym
      (aesDecGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesDecGhost_fs keep P_sub entryTarget mmpl brkStart lim,
   aesDecGhost_fsT keep P_sub entryTarget mmpl brkStart lim, by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.ExtraRowSpec
    have hd1 : (lsAesDecSym == "bcmp") = false := by decide
    have hd2 : (lsAesDecSym == "strlen") = false := by decide
    have hd3 : (lsAesDecSym == "memmove") = false := by decide
    have hd4 : (lsAesDecSym == CryptoVerification.SignalSession.lsFromUtf8Sym) = false := by decide
    have hd5 : (lsAesDecSym == CryptoVerification.SignalSession.lsMemrchrSym) = false := by decide
    have hd6 : (lsAesDecSym == CryptoVerification.SignalSession.lsDurationSinceSym) = false := by decide
    have hd7 : (lsAesDecSym == CryptoVerification.SignalSession.lsTimeAddSym) = false := by decide
    have hd8 : (lsAesDecSym == CryptoVerification.SignalSession.lsBlackBoxSym) = false := by decide
    have hd9 : (lsAesDecSym == CryptoVerification.SignalSession.lsStaticSecretDropSym) = false := by decide
    have hd10 : (lsAesDecSym == CryptoVerification.SignalSession.lsSharedSecretDropSym) = false := by decide
    have hd11 : (lsAesDecSym == lsAesEncSym) = false := by decide
    have hd12 : (lsAesDecSym == lsAesDecSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, Bool.false_eq_true,
      ↓reduceIte]
    trivial⟩

/-! ## 3. `withFsTraceExact` Post-Strengthening & Panic-Extern `f3LinkedCallHook` Combinators -/

/-- Strengthen `spec.post` and `spec.onPanic` with `⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝`
    (with `onExit = False` and `onOom = False`), keeping `spec.pre` definitionally (`rfl`) unchanged. -/
@[expose] def withFsTraceExact {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.post x s0 sf
    onPanic := fun x s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ spec.onPanic x s0 sf
    onExit := fun _ _ _ _ => ⌜False⌝
    onOom := fun _ _ _ => ⌜False⌝ }

theorem specPreservesFsTrace_withFsTraceExact {α : Type} (spec : Spec α) :
    SpecPreservesFsTrace (withFsTraceExact spec) := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, FsTraced.of_eq hpost.1.2 (congrArg FsState.files hpost.1.1)⟩
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact ⟨hpan.1.1, FsTraced.of_eq hpan.1.2 (congrArg FsState.files hpan.1.1)⟩
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_of_withFsTraceExact {α : Type} {f : State → State} {spec : Spec α}
    (hok : HookOk f (withFsTraceExact spec)) : HookOk f spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.2
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem stubPermRO_stripExecOutside_of_stubFrozen
    {keep : BitVec 64 → Bool} {P_sub : Program} {u : State}
    (hSF : stubFrozenGuard P_sub u) :
    ∀ pc : BitVec 64,
      P_sub.externAt? pc ≠ none →
      ((stripExecOutside keep u.mem).perm pc).r = true ∧
        ((stripExecOutside keep u.mem).perm pc).w = false := by
  intro pc hext
  have hfr_u : (u.mem.perm pc).r = true ∧ (u.mem.perm pc).w = false := hSF pc hext
  unfold Memory.perm at hfr_u
  unfold Memory.perm stripExecOutside stripPerm
  dsimp only
  cases hc : u.mem.cells pc with
  | none => simp [hc, Option.r] at hfr_u
  | some v =>
    rcases v with ⟨op, b⟩
    cases op with
    | none => simp [hc, Option.r] at hfr_u
    | some p =>
      simp only [hc, Option.r, Option.w, Perm.rwx] at hfr_u
      rcases p with ⟨r, w, x, lf, an⟩
      cases hkp : keep pc <;> cases r <;> cases w <;> cases x <;>
        simp_all [Option.r, Option.w, Perm.rwx]

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨h1, _, _⟩ | ⟨h2, _⟩ | ⟨c, h3, _⟩ | ⟨h4, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨c, h3⟩))
  · exact Or.inr (Or.inr (Or.inr h4))

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hst⟩, _, _⟩ | ⟨hst, _⟩ | ⟨_, hst, _⟩ | ⟨hst, _⟩ <;>
    (rw [hst]; nofun)

private theorem real_subroutine_run_visitedIn_of_stripS_with_stubPermRO {α : Type}
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hSF : stubFrozenGuard P_sub s0)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧ SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧ sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hro : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false :=
    stubPermRO_stripExecOutside_of_stubFrozen hSF
  have hfr_s1' : ExecFrozen s1'.mem := fun a hx => by
    dsimp only [s1', stripS, State.setMem] at hx ⊢
    obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
    rw [strip_perm_of_keep hk]
    exact hFr a hx_m
  have hs1'_pre_ro : s1'.mem ⊨ (withStubPermRO P_sub spec).pre x s1' ∗ R := by
    dsimp only [withStubPermRO]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hro, hfr_s1'⟩, hs1'_pre⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre_ro hSp hCodeSub
  have hout_base : SubroutineOutcome spec x R s1' sf' := hout'
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout_base
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout_base
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs_inKeep hsvc1 hsvc_sub hext1_no hext_sub
      hlr_out hlr_ne hsteps' hstop0' hnhalt' hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout_base
    rcases hout_base with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, ?_, ?_⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf, hvis⟩

theorem f3LinkedCallHook_ok_at_stubFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withStubPermRO P_sub (specOf γ tp)))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp))
    {x : α} {R : SepProp} {s0 : State}
    (hSF : stubFrozenGuard P_sub s0)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    s0.mem.KeepsFrozen
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).mem ∧
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).symtab = s0.symtab ∧
      SubroutineOutcome (specOf γ tp) x R s0
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0) := by
  classical
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold f3LinkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_subroutine_run_visitedIn_of_stripS_with_stubPermRO hsvc_real hsvc_sub hreal_no
        hext_sub hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

private theorem f3LinkedCallHook_activeF3CallPre_of_noException {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status ≠ .Exception msg) :
    ActiveF3CallPre specOf u := by
  classical
  by_contra hnot
  have hex :
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback u).status =
        .Exception "ghost-hook precondition violated" := by
    unfold f3LinkedCallHook
    simp only [hnot, ↓reduceDIte]
  exact hnoex _ hex

theorem f3LinkedCallHook_externOnly_visitedIn_with_externs {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (withStubPermRO P_sub (specOf γ tp)))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hSF : stubFrozenGuard P_sub u)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub)
        (u.setPC entryTarget)
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) ∧
      ExecFrozen
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).mem ∧
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).fs =
        u.fs := by
  classical
  obtain ⟨hrun, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHook_activeF3CallPre_of_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  obtain ⟨sf, huntil_sf, hstop_sf, _, hfs_sf, hfst_sf, hfr_sf, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_stubPermRO
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub
      (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩)
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

private theorem readBytes_stripExecOutside (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (n : Nat) (addr : BitVec 64),
      (stripExecOutside keep m).readBytes addr n = m.readBytes addr n
  | 0, _ => rfl
  | n + 1, addr => by
    simp only [Memory.readBytes, strip_read8, readBytes_stripExecOutside keep m n (addr + 1#64)]

theorem roDataAt_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory}
    {tbl : BitVec 64} {bytes : List (BitVec 8)}
    (h : RoDataAt m tbl bytes) :
    RoDataAt (stripExecOutside keep m) tbl bytes := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hpa, hlfa⟩ := h.1 a ha
    refine ⟨?_, (strip_isLazyFree keep m a).trans hlfa⟩
    rw [strip_perm, hpa]
    simp [Option.map, stripPerm, Perm.ro]
  · exact (readBytes_stripExecOutside keep m bytes.length tbl).trans h.2

private theorem real_subroutine_run_visitedIn_of_stripS_with_aesStubRconRO {α : Type}
    {keep : BitVec 64 → Bool} {P1 P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    {s0 : State} (hsvc1 : P1.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hext1_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P1.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → P1.externAt? pc = some f ∧ StripCommExtern keep f)
    (hOk : subroutine_ok P_sub entryTarget (withAesStubRconRO P_sub spec))
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} (hRun : s0.status = .Running) (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R) (hFr : ExecFrozen s0.mem)
    (hSF : stubFrozenGuard P_sub s0) (hRo : RoDataAt s0.mem c2AesRconAddr aesRconBytes)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P1 (SubroutineStop s0) (s0.setPC entryTarget) sf ∧ SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧ sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem ∧
      h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) P1 (s0.setPC entryTarget) sf := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hro_stub : ∀ pc : BitVec 64, P_sub.externAt? pc ≠ none →
      (s1'.mem.perm pc).r = true ∧ (s1'.mem.perm pc).w = false :=
    stubPermRO_stripExecOutside_of_stubFrozen hSF
  have hro_rcon : RoDataAt s1'.mem c2AesRconAddr aesRconBytes :=
    roDataAt_stripExecOutside keep hRo
  have hfr_s1' : ExecFrozen s1'.mem := fun a hx => by
    dsimp only [s1', stripS, State.setMem] at hx ⊢
    obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
    rw [strip_perm_of_keep hk]
    exact hFr a hx_m
  have hs1'_pre_ro : s1'.mem ⊨ (withAesStubRconRO P_sub spec).pre x s1' ∗ R := by
    dsimp only [withAesStubRconRO, withStubPermRO, withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_stub, hfr_s1'⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro_rcon, hs1'_pre⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre_ro hSp hCodeSub
  have hout_base : SubroutineOutcome spec x R s1' sf' := hout'
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout_base
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout_base
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf, hvis⟩ :=
    stepsVisitedIn_of_stripS_with_externs_inKeep hsvc1 hsvc_sub hext1_no hext_sub
      hlr_out hlr_ne hsteps' hstop0' hnhalt' hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout_base
    rcases hout_base with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨⟨hret'.1, hret'.2.1, hret'.2.2⟩, ?_, ?_⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf, hvis⟩

theorem f3LinkedCallHook_ok_at_aesStubRcon {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_sub.externAt? pc = none → P_real.externAt? pc = none)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧ StripCommExtern keep f)
    (γ : GhostName) (tp : BitVec 64)
    (hlr_ne_pre : ∀ x (R : SepProp) (s0 : State),
      (s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R) →
      ∀ (pc : BitVec 64) (f : State → State),
        P_sub.externAt? pc = some f → pc ≠ s0.readReg64 .lr)
    (hOk : subroutine_ok P_sub entryTarget (withAesStubRconRO P_sub (specOf γ tp)))
    (hInv : SpecStripSInvariant keep (specOf γ tp))
    (hFsT : SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (specOf γ tp))
    {x : α} {R : SepProp} {s0 : State}
    (hSF : stubFrozenGuard P_sub s0)
    (hRo : RoDataAt s0.mem c2AesRconAddr aesRconBytes)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (specOf γ tp).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    s0.mem.KeepsFrozen
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).mem ∧
      (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0).symtab = s0.symtab ∧
      SubroutineOutcome (specOf γ tp) x R s0
        (f3LinkedCallHook keep P_real P_sub entryTarget specOf fallback s0) := by
  classical
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  unfold f3LinkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _, _⟩ :=
      real_subroutine_run_visitedIn_of_stripS_with_aesStubRconRO hsvc_real hsvc_sub hreal_no
        hext_sub hOk hInv hFsT hPrePC hOutPC hrun hsp hpre hReal.1 hSF hRo
        hReal.2.1 (hlr_ne_pre x R s0 hpre) hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

theorem f3LinkedCallHook_externOnly_visitedIn_with_aesStubRcon {α : Type}
    {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {specOf : GhostName → BitVec 64 → Spec α}
    {fallback : State → State}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget (withAesStubRconRO P_sub (specOf γ tp)))
    (hInv : ∀ γ tp, SpecStripSInvariant keep (specOf γ tp))
    (hFsT : ∀ γ tp, SpecPreservesFsTrace (specOf γ tp))
    (hPrePC : ∀ γ tp x (s : State) (pc : BitVec 64),
      (specOf γ tp).pre x (s.setPC pc) = (specOf γ tp).pre x s)
    (hOutPC : ∀ γ tp x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (specOf γ tp) x R (s0.setPC pc) sf →
      SubroutineOutcome (specOf γ tp) x R s0 sf)
    {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).status ≠
        .Exception msg)
    (hFr : ExecFrozen u.mem) (hSF : stubFrozenGuard P_sub u)
    (hRo : RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hlr_out : keep (u.readReg64 .lr) = false)
    (hlr_ne : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → pc ≠ u.readReg64 .lr)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    h2fsgen_StepsVisitedIn (keepOrSubExtern keep P_sub) (externOnlyStdProg P_sub)
        (u.setPC entryTarget)
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u) ∧
      ExecFrozen
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).mem ∧
      (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u).fs =
        u.fs := by
  classical
  obtain ⟨hrun, hsp, γ, tp, x, R, hpre⟩ := f3LinkedCallHook_activeF3CallPre_of_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  obtain ⟨sf, huntil_sf, hstop_sf, _, hfs_sf, hfst_sf, hfr_sf, hvis_sf⟩ :=
    real_subroutine_run_visitedIn_of_stripS_with_aesStubRconRO
      (P1 := externOnlyStdProg P_sub) rfl hsvc_sub
      (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩)
      (hOk γ tp) (hInv γ tp) (hFsT γ tp) (hPrePC γ tp) (hOutPC γ tp)
      hrun hsp hpre hFr hSF hRo hlr_out hlr_ne hCodeSub
  have hReal : ActiveRealRun keep (externOnlyStdProg P_sub) P_sub entryTarget u :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil_sf, hstop_sf, hfs_sf, hfst_sf, hfr_sf⟩
  have hhook_eq :
      f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget specOf fallback u = sf := by
    unfold f3LinkedCallHook
    simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil_sf hstop_sf
  rw [hhook_eq]
  exact ⟨hvis_sf, hfr_sf, hfs_sf⟩

/-! ## 4. `aesEncSpecOf` / `aesDecSpecOf` Invariants, Fallback `HookOk`, & `aesEncGhost_ok` / `aesDecGhost_ok` -/

theorem specStripSInvariant_aesEncSpecOf [LibsignalPlacement]
    {keep : BitVec 64 → Bool} (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)) where
  pre_eq := by
    intro ⟨x, st⟩ s
    dsimp only [withFsTraceExact, aesEncSpecOf, withLsRet, aesEncBudgetSpec, aesCallPreBudget]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    intro ⟨x, st⟩ s0 sf
    dsimp only [withFsTraceExact, aesEncSpecOf, withLsRet, aesEncBudgetSpec]
    congr 1
    exact congrArg sepExists (funext fun evs => by
      rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
      rfl)
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_aesDecSpecOf [LibsignalPlacement]
    {keep : BitVec 64 → Bool} (γ : GhostName) (mmpl : Obj.MultiPlacement)
    (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)) where
  pre_eq := by
    intro ⟨x, st⟩ s
    dsimp only [withFsTraceExact, aesDecSpecOf, withLsRet, aesDecBudgetSpec, aesCallPreBudget]
    rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim st s]
    rfl
  post_eq := by
    intro ⟨x, st⟩ s0 sf
    dsimp only [withFsTraceExact, aesDecSpecOf, withLsRet, aesDecBudgetSpec]
    congr 1
    exact congrArg sepExists (funext fun evs => by
      rw [fineHookRustCliAllocBudget_pool_stripS γ mmpl tp brkStart hKeepMallocng lim _ sf]
      rfl)
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem prePC_aesEncSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (s : State) (pc : BitVec 64),
      (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)).pre x (s.setPC pc) =
        (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)).pre x s := by
  intro ⟨_, _⟩ s _
  cases s
  rfl

private theorem prePC_aesDecSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (s : State) (pc : BitVec 64),
      (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)).pre x (s.setPC pc) =
        (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)).pre x s := by
  intro ⟨_, _⟩ s _
  cases s
  rfl

private theorem outPC_aesEncSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))
        x R (s0.setPC pc) sf →
      SubroutineOutcome (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))
        x R s0 sf := by
  intro _ _ s0 _ _
  cases s0
  exact id

private theorem outPC_aesDecSpecOf [LibsignalPlacement]
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) (lim : BudgetLimits) :
    ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))
        x R (s0.setPC pc) sf →
      SubroutineOutcome (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))
        x R s0 sf := by
  intro _ _ s0 _ _
  cases s0
  exact id

private theorem aesEncFallback_withFsTraceExact_ok [LibsignalPlacement]
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookOk (keepFsTrace (aesEncHookMallocng mmpl aes256Enc))
      (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)) := by
  have hBase : HookOk (aesEncHookMallocng mmpl aes256Enc)
      (aesEncSpecOf mmpl brkStart lim γ tp) :=
    hookOk_withLsRet (fineAesEnc_budget_hookOk γ tp brkStart lim hPl aes256Enc)
  have hExact : HookOk (aesEncHookMallocng mmpl aes256Enc)
      (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)) := by
    intro ⟨x, st⟩ R s0 hrun hpre hsp
    have hpre_ls : s0.mem ⊨ (aesEncSpecOf mmpl brkStart lim γ tp).pre (x, st) s0 ∗ R := hpre
    dsimp only [aesEncSpecOf, withLsRet] at hpre_ls
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ls
    have hpre_bud : s0.mem ⊨
        (aesEncBudgetSpec aes256Enc fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre (x, st) s0 ∗ R := hpre_ls.2
    have hfs : (aesEncHookMallocng mmpl aes256Enc s0).fs = s0.fs :=
      aesEncHookMallocng_fs_eq_of_pre fineCostModelSound γ tp brkStart lim hPl aes256Enc
        hpre_bud hsp
    obtain ⟨hkf, hsym, hout⟩ := hBase (x, st) R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have htr : (aesEncHookMallocng mmpl aes256Enc s0).trace = s0.trace := by
        dsimp only [aesEncSpecOf, withLsRet, aesEncBudgetSpec] at hpost
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
        rcases hpost with ⟨_, hevs⟩
        simp only [sepConj_assoc] at hevs
        rw [satisfies_pure_sepConj] at hevs
        exact hevs.1.1
      dsimp only [withFsTraceExact]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfs, htr⟩, hpost⟩
    · dsimp only [aesEncSpecOf, withLsRet, aesEncBudgetSpec] at hpan
      rw [satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · dsimp only [aesEncSpecOf, withLsRet, aesEncBudgetSpec] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [aesEncSpecOf, withLsRet, aesEncBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1
  refine keepFsTrace_ok hExact (fun _ _ s0 hout => ?_)
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

private theorem aesDecFallback_withFsTraceExact_ok [LibsignalPlacement]
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookOk (keepFsTrace (aesDecHookMallocng mmpl aes256Dec))
      (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)) := by
  have hBase : HookOk (aesDecHookMallocng mmpl aes256Dec)
      (aesDecSpecOf mmpl brkStart lim γ tp) :=
    hookOk_withLsRet (fineAesDec_budget_hookOk γ tp brkStart lim hPl aes256Dec)
  have hExact : HookOk (aesDecHookMallocng mmpl aes256Dec)
      (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)) := by
    intro ⟨x, st⟩ R s0 hrun hpre hsp
    have hpre_ls : s0.mem ⊨ (aesDecSpecOf mmpl brkStart lim γ tp).pre (x, st) s0 ∗ R := hpre
    dsimp only [aesDecSpecOf, withLsRet] at hpre_ls
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ls
    have hpre_bud : s0.mem ⊨
        (aesDecBudgetSpec aes256Dec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim).pre (x, st) s0 ∗ R := hpre_ls.2
    have hfs : (aesDecHookMallocng mmpl aes256Dec s0).fs = s0.fs :=
      aesDecHookMallocng_fs_eq_of_pre fineCostModelSound γ tp brkStart lim hPl aes256Dec
        hpre_bud hsp
    obtain ⟨hkf, hsym, hout⟩ := hBase (x, st) R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have htr : (aesDecHookMallocng mmpl aes256Dec s0).trace = s0.trace := by
        dsimp only [aesDecSpecOf, withLsRet, aesDecBudgetSpec] at hpost
        rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
        rcases hpost with ⟨_, hevs⟩
        simp only [sepConj_assoc] at hevs
        rw [satisfies_pure_sepConj] at hevs
        exact hevs.1.1
      dsimp only [withFsTraceExact]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfs, htr⟩, hpost⟩
    · dsimp only [aesDecSpecOf, withLsRet, aesDecBudgetSpec] at hpan
      rw [satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · dsimp only [aesDecSpecOf, withLsRet, aesDecBudgetSpec] at hex
      rw [satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · dsimp only [aesDecSpecOf, withLsRet, aesDecBudgetSpec] at hoom
      rw [satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1
  refine keepFsTrace_ok hExact (fun _ _ s0 hout => ?_)
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [withFsTraceExact] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · dsimp only [withFsTraceExact] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · dsimp only [withFsTraceExact] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withFsTraceExact] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- Pointwise `HookOk` for `aesEncGhost` at every `(γ, tp)` and arbitrary `brkStart`. -/
theorem aesEncGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesEncGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesEncSpecOf mmpl brkStart lim γ tp) := by
  classical
  apply hookOk_of_withFsTraceExact
  intro x R s0 hrun hpre hsp
  by_cases hG : aesStubRconGuard P_sub brkStart s0
  · rw [aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart lim hG]
    exact f3LinkedCallHook_ok_at_aesStubRcon
      (P_real := externOnlyStdProg P_sub)
      (specOf := fun γ' tp' => withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ' tp'))
      (fallback := aesEncHookMallocng mmpl aes256Enc)
      rfl hsvc_sub (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩) γ tp
      (fun _ _ s0' hpre' => by
        dsimp only [withFsTraceExact, aesEncSpecOf, withLsRet] at hpre'
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
        exact hlr_ne_stub (s0'.readReg64 .lr) hpre'.1)
      (hOk hG.2.2)
      (specStripSInvariant_aesEncSpecOf γ mmpl tp brkStart hKeepMallocng lim)
      (specPreservesFsTrace_withFsTraceExact _)
      (prePC_aesEncSpecOf γ mmpl tp brkStart lim)
      (outPC_aesEncSpecOf γ mmpl tp brkStart lim)
      (aesEncFallback_withFsTraceExact_ok γ tp brkStart lim hPl)
      hG.1 hG.2.1 hrun hpre hsp
  · have hActPre : ActiveF3CallPre (aesEncSpecOf mmpl brkStart lim) s0 :=
      ⟨hrun, hsp, γ, tp, x, R, hpre⟩
    have heq : aesEncGhost keep P_sub entryTarget mmpl brkStart lim s0 =
        keepFsTrace (aesEncHookMallocng mmpl aes256Enc) s0 := by
      unfold aesEncGhost
      simp only [hG, hActPre, ↓reduceIte]
    rw [heq]
    exact aesEncFallback_withFsTraceExact_ok γ tp brkStart lim hPl x R s0 hrun hpre hsp

/-- Pointwise `HookOk` for `aesDecGhost` at every `(γ, tp)` and arbitrary `brkStart`. -/
theorem aesDecGhost_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesDecGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesDecSpecOf mmpl brkStart lim γ tp) := by
  classical
  apply hookOk_of_withFsTraceExact
  intro x R s0 hrun hpre hsp
  by_cases hG : aesStubRconGuard P_sub brkStart s0
  · rw [aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart lim hG]
    exact f3LinkedCallHook_ok_at_aesStubRcon
      (P_real := externOnlyStdProg P_sub)
      (specOf := fun γ' tp' => withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ' tp'))
      (fallback := aesDecHookMallocng mmpl aes256Dec)
      rfl hsvc_sub (fun pc _ h => (externOnlyStdProg_externAt P_sub pc).trans h)
      (fun pc f he => ⟨(externOnlyStdProg_externAt P_sub pc).trans he, hcomm pc f he⟩) γ tp
      (fun _ _ s0' hpre' => by
        dsimp only [withFsTraceExact, aesDecSpecOf, withLsRet] at hpre'
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
        exact hlr_ne_stub (s0'.readReg64 .lr) hpre'.1)
      (hOk hG.2.2)
      (specStripSInvariant_aesDecSpecOf γ mmpl tp brkStart hKeepMallocng lim)
      (specPreservesFsTrace_withFsTraceExact _)
      (prePC_aesDecSpecOf γ mmpl tp brkStart lim)
      (outPC_aesDecSpecOf γ mmpl tp brkStart lim)
      (aesDecFallback_withFsTraceExact_ok γ tp brkStart lim hPl)
      hG.1 hG.2.1 hrun hpre hsp
  · have hActPre : ActiveF3CallPre (aesDecSpecOf mmpl brkStart lim) s0 :=
      ⟨hrun, hsp, γ, tp, x, R, hpre⟩
    have heq : aesDecGhost keep P_sub entryTarget mmpl brkStart lim s0 =
        keepFsTrace (aesDecHookMallocng mmpl aes256Dec) s0 := by
      unfold aesDecGhost
      simp only [hG, hActPre, ↓reduceIte]
    rw [heq]
    exact aesDecFallback_withFsTraceExact_ok γ tp brkStart lim hPl x R s0 hrun hpre hsp

private theorem aesErr_entails_weak (ret : BitVec 64) :
    (ret ↦₆₄ errTag) ∗
      (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ∗ memRegion (ret + 16#64) 8 ⊢
      (ret ↦₆₄ errTag) ∗ memRegion (ret + 8#64) 16 := by
  have hp8 : (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((ret + 8#64) ↦₆₄ p)) ⊢ memRegion (ret + 8#64) 8 := by
    rw [memRegion_eight (ret + 8#64)]
    refine Entails.sepExists_elim fun p => Entails.pure_left fun _ => ?_
    exact @Entails.sepExists_intro (BitVec 64) (fun q => (ret + 8#64) ↦₆₄ q) p
  have h16 : memRegion (ret + 8#64) 8 ∗ memRegion (ret + 16#64) 8 = memRegion (ret + 8#64) 16 :=
    (memRegion_split' (b := ret + 8#64) (n := 8) (k := 8) (b' := ret + 16#64)
      rfl (by bv_omega) (by decide)).symm
  rw [← h16]
  exact sepConj_mono_right (sepConj_mono_left hp8)

/-- Pointwise `aesDecWeakSpecOf` companion `HookOk` for `aesDecGhost`. -/
theorem aesDecGhost_weak_ok [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hcomm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f → StripCommExtern keep f)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (γ : GhostName) (tp : BitVec 64)
    (hOk : brkStart = f3StdLayout.brkStart → subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp)))) :
    HookOk (aesDecGhost keep P_sub entryTarget mmpl brkStart lim)
      (aesDecWeakSpecOf mmpl brkStart lim γ tp) := by
  refine HookOk.mono
    (aesDecGhost_ok hsvc_sub hcomm hlr_ne_stub hPl hKeepMallocng γ tp hOk)
    (fun _ _ _ h => h) ?_ (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
  rintro ⟨x, st⟩ R s0 sf _ hpost
  dsimp only [aesDecSpecOf, aesDecWeakSpecOf, withLsRet, aesDecBudgetSpec,
    aesDecWeakBudgetSpec, aesDecFnBudgetSpec] at hpost ⊢
  refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_elim fun evs => ?_)) hpost
  refine Entails.trans ?_
    (@Entails.sepExists_intro (List AllocEvent) _ evs)
  cases aesCbcDecrypt aes256Dec (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
  | none =>
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (aesErr_entails_weak x.ret)))
  | some _ =>
    exact Entails.refl _

/-! ## 5. `GhostRowReplayOn` & `GhostRowOk` -/

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem lsRetAddr624_of_aesEncGhost_noException [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {u : State}
    (hnoex : ∀ msg,
      (aesEncGhost keep P_sub entryTarget mmpl brkStart lim u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) := by
  classical
  have hAct : ActiveF3CallPre (aesEncSpecOf mmpl brkStart lim) u := by
    by_cases hG : aesStubRconGuard P_sub brkStart u
    · rw [aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart
        lim hG] at hnoex
      exact f3LinkedCallHook_activeF3CallPre_of_noException hnoex
    · by_contra hnot
      have hex : (aesEncGhost keep P_sub entryTarget mmpl brkStart lim u).status =
          .Exception "ghost-hook precondition violated" := by
        unfold aesEncGhost
        simp only [hG, hnot, ↓reduceIte]
      exact hnoex _ hex
  rcases hAct with ⟨_, _, γ, tp, x, R, hpre⟩
  dsimp only [aesEncSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

private theorem lsRetAddr624_of_aesDecGhost_noException [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    {mmpl : Obj.MultiPlacement} {brkStart : BitVec 64} {lim : BudgetLimits} {u : State}
    (hnoex : ∀ msg,
      (aesDecGhost keep P_sub entryTarget mmpl brkStart lim u).status ≠ .Exception msg) :
    LsRetAddr624 (u.readReg64 .lr) := by
  classical
  have hAct : ActiveF3CallPre (aesDecSpecOf mmpl brkStart lim) u := by
    by_cases hG : aesStubRconGuard P_sub brkStart u
    · rw [aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon keep P_sub entryTarget mmpl brkStart
        lim hG] at hnoex
      exact f3LinkedCallHook_activeF3CallPre_of_noException hnoex
    · by_contra hnot
      have hex : (aesDecGhost keep P_sub entryTarget mmpl brkStart lim u).status =
          .Exception "ghost-hook precondition violated" := by
        unfold aesDecGhost
        simp only [hG, hnot, ↓reduceIte]
      exact hnoex _ hex
  rcases hAct with ⟨_, _, γ, tp, x, R, hpre⟩
  dsimp only [aesDecSpecOf, withLsRet] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

theorem aesEncGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsAesEncSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => P_sub.CodeLoaded (stripExecOutside keep m))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsAesEncSym)
        entryTarget) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesEncSym (fun _ => True)
      (aesEncGhost keep P_sub entryTarget mmpl brkStart lim) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨aesEncGhost_preserves_execFrozen keep P_sub entryTarget mmpl brkStart lim hfr,
     aesEncGhost_fs keep P_sub entryTarget mmpl brkStart lim u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealStubNone W, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hSF : stubFrozenGuard P_sub u := hStubFrozen u hInvU
    have hRo : RoDataAt u.mem c2AesRconAddr aesRconBytes := hRconRo u hInvU
    have hG : aesStubRconGuard P_sub brkStart u := ⟨hSF, hRo, hbrk⟩
    have hlr624 : LsRetAddr624 (u.readReg64 .lr) := lsRetAddr624_of_aesEncGhost_noException hnoex
    have hlr_out : keep (u.readReg64 .lr) = false := hKeep _ hlr624
    have hlr_ne := hlr_ne_stub _ hlr624
    have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hCL_strip u hfr hInvU
    have heq_f3 := aesEncGhost_eq_f3LinkedCallHook_of_aesStubRcon
      keep P_sub entryTarget mmpl brkStart lim hG
    have hnoex_f3 : ∀ msg,
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
          (aesEncSpecOf mmpl brkStart lim)
          (aesEncHookMallocng mmpl aes256Enc) u).status ≠ .Exception msg := by
      rwa [← heq_f3]
    obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
      f3LinkedCallHook_externOnly_visitedIn_with_aesStubRcon
        (specOf := fun γ tp => withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))
        (fallback := aesEncHookMallocng mmpl aes256Enc)
        hsvc_sub
        (fun pc f he => by
          obtain ⟨rfl, _⟩ := hPanReal W pc f he
          exact stripCommExtern_rustPanicked keep)
        hOk
        (fun γ tp => specStripSInvariant_aesEncSpecOf γ mmpl tp brkStart hKeepMallocng lim)
        (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
        (fun γ tp => prePC_aesEncSpecOf γ mmpl tp brkStart lim)
        (fun γ tp => outPC_aesEncSpecOf γ mmpl tp brkStart lim)
        hnoex_f3 hfr hSF hRo hlr_out hlr_ne hCodeSub
    have hhook_exact_eq :
        f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (fun γ tp => withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))
            (aesEncHookMallocng mmpl aes256Enc) u =
          f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (aesEncSpecOf mmpl brkStart lim)
            (aesEncHookMallocng mmpl aes256Enc) u := rfl
    rw [hhook_exact_eq] at hvis hfr_sf hfs_sf
    have hStubSteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        u (u.setPC entryTarget) :=
      hStub W u hpc hrun hfr hCodeSub
    have hBodySteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget)
        (aesEncGhost keep P_sub entryTarget mmpl brkStart lim u) := by
      rw [heq_f3]
      exact steps_externOnly_to_real_of_visitedIn_inKeep rfl
        (fun _ hk hsub => hRealHullNoExt W hk hsub)
        (fun pc f he => by
          obtain ⟨rfl, hreal⟩ := hPanReal W pc f he
          exact hreal)
        hvis
    rw [← heq_f3] at hfr_sf hfs_sf
    exact ⟨hStubSteps.trans hBodySteps, hfr_sf,
      hInvKeep u (aesEncGhost keep P_sub entryTarget mmpl brkStart lim u) hInvU hkf hfs_sf⟩

theorem aesEncGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesEncSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesEncSym (fun _ => True)
      (aesEncGhost keep P_sub entryTarget mmpl brkStart lim) :=
  aesEncGhost_rowReplayOn_of_stub mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
    hsvc_sub hKeepMallocng hOk hStubFrozen hRconRo hbrk hCL_strip hInvKeep hKeep
    hlr_ne_stub hRealHullNoExt hPanReal
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W hkeep_entry hsub_entry_none)
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

theorem aesEncGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesEncSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesEncSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowOk mpl mmpl InvS EG lsAesEncSym (fun _ => True)
      (aesEncGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesEncGhost_rowSpecOk keep P_sub entryTarget mmpl brkStart lim,
   aesEncGhost_rowReplayOn mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
     hsvc_sub hsub_entry_none hkeep_entry hKeepMallocng hOk hStubFrozen hRconRo hbrk hTargetEq
     hCL_strip hInvKeep hKeep hlr_ne_stub hRealHullNoExt hPanReal⟩

theorem aesDecGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsAesDecSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => P_sub.CodeLoaded (stripExecOutside keep m))
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsAesDecSym)
        entryTarget) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecGhost keep P_sub entryTarget mmpl brkStart lim) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨aesDecGhost_preserves_execFrozen keep P_sub entryTarget mmpl brkStart lim hfr,
     aesDecGhost_fs keep P_sub entryTarget mmpl brkStart lim u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealStubNone W, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hSF : stubFrozenGuard P_sub u := hStubFrozen u hInvU
    have hRo : RoDataAt u.mem c2AesRconAddr aesRconBytes := hRconRo u hInvU
    have hG : aesStubRconGuard P_sub brkStart u := ⟨hSF, hRo, hbrk⟩
    have hlr624 : LsRetAddr624 (u.readReg64 .lr) := lsRetAddr624_of_aesDecGhost_noException hnoex
    have hlr_out : keep (u.readReg64 .lr) = false := hKeep _ hlr624
    have hlr_ne := hlr_ne_stub _ hlr624
    have hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem) := hCL_strip u hfr hInvU
    have heq_f3 := aesDecGhost_eq_f3LinkedCallHook_of_aesStubRcon
      keep P_sub entryTarget mmpl brkStart lim hG
    have hnoex_f3 : ∀ msg,
        (f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
          (aesDecSpecOf mmpl brkStart lim)
          (aesDecHookMallocng mmpl aes256Dec) u).status ≠ .Exception msg := by
      rwa [← heq_f3]
    obtain ⟨hvis, hfr_sf, hfs_sf⟩ :=
      f3LinkedCallHook_externOnly_visitedIn_with_aesStubRcon
        (specOf := fun γ tp => withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))
        (fallback := aesDecHookMallocng mmpl aes256Dec)
        hsvc_sub
        (fun pc f he => by
          obtain ⟨rfl, _⟩ := hPanReal W pc f he
          exact stripCommExtern_rustPanicked keep)
        hOk
        (fun γ tp => specStripSInvariant_aesDecSpecOf γ mmpl tp brkStart hKeepMallocng lim)
        (fun _ _ => specPreservesFsTrace_withFsTraceExact _)
        (fun γ tp => prePC_aesDecSpecOf γ mmpl tp brkStart lim)
        (fun γ tp => outPC_aesDecSpecOf γ mmpl tp brkStart lim)
        hnoex_f3 hfr hSF hRo hlr_out hlr_ne hCodeSub
    have hhook_exact_eq :
        f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (fun γ tp => withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))
            (aesDecHookMallocng mmpl aes256Dec) u =
          f3LinkedCallHook keep (externOnlyStdProg P_sub) P_sub entryTarget
            (aesDecSpecOf mmpl brkStart lim)
            (aesDecHookMallocng mmpl aes256Dec) u := rfl
    rw [hhook_exact_eq] at hvis hfr_sf hfs_sf
    have hStubSteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        u (u.setPC entryTarget) :=
      hStub W u hpc hrun hfr hCodeSub
    have hBodySteps : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget)
        (aesDecGhost keep P_sub entryTarget mmpl brkStart lim u) := by
      rw [heq_f3]
      exact steps_externOnly_to_real_of_visitedIn_inKeep rfl
        (fun _ hk hsub => hRealHullNoExt W hk hsub)
        (fun pc f he => by
          obtain ⟨rfl, hreal⟩ := hPanReal W pc f he
          exact hreal)
        hvis
    rw [← heq_f3] at hfr_sf hfs_sf
    exact ⟨hStubSteps.trans hBodySteps, hfr_sf,
      hInvKeep u (aesDecGhost keep P_sub entryTarget mmpl brkStart lim u) hInvU hkf hfs_sf⟩

theorem aesDecGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesDecSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowReplayOn mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecGhost keep P_sub entryTarget mmpl brkStart lim) :=
  aesDecGhost_rowReplayOn_of_stub mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
    hsvc_sub hKeepMallocng hOk hStubFrozen hRconRo hbrk hCL_strip hInvKeep hKeep
    hlr_ne_stub hRealHullNoExt hPanReal
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W hkeep_entry hsub_entry_none)
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

theorem aesDecGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    (brkStart : BitVec 64) (lim : BudgetLimits)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_entry_none : P_sub.externAt? entryTarget = none)
    (hkeep_entry : keep entryTarget = true)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hOk : ∀ γ tp, subroutine_ok P_sub entryTarget
      (withAesStubRconRO P_sub (withFsTraceExact (aesDecSpecOf mmpl brkStart lim γ tp))))
    (hStubFrozen : ∀ u : State, InvS u → stubFrozenGuard P_sub u)
    (hRconRo : ∀ u : State, InvS u → RoDataAt u.mem c2AesRconAddr aesRconBytes)
    (hbrk : brkStart = f3StdLayout.brkStart)
    (hTargetEq : libsignalSessionLib.resolve mpl lsAesDecSym = entryTarget)
    (hCL_strip : ∀ u : State, ExecFrozen u.mem → InvS u →
      P_sub.CodeLoaded (stripExecOutside keep u.mem))
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keep lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr →
      ∀ (pc : BitVec 64) (f : State → State), P_sub.externAt? pc = some f → pc ≠ lr)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keep pc = true → P_sub.externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ (W : CliHooks) (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      f = Rust.panicked ∧
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some Rust.panicked) :
    GhostRowOk mpl mmpl InvS EG lsAesDecSym (fun _ => True)
      (aesDecGhost keep P_sub entryTarget mmpl brkStart lim) :=
  ⟨aesDecGhost_rowSpecOk keep P_sub entryTarget mmpl brkStart lim,
   aesDecGhost_rowReplayOn mpl mmpl keep P_sub entryTarget brkStart lim InvS EG
     hsvc_sub hsub_entry_none hkeep_entry hKeepMallocng hOk hStubFrozen hRconRo hbrk hTargetEq
     hCL_strip hInvKeep hKeep hlr_ne_stub hRealHullNoExt hPanReal⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesCbcGhostReplays
