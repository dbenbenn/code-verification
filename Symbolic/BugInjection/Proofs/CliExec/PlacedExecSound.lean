/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Process.Core
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastEval
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.SyscallSoundnessPlaced
public import Symbolic.BugInjection.Proofs.CliExec.CliRunBridgePlaced

/-!
# Soundness of the Placed CLI Evaluator

Proves instruction, single-step, and multi-chunk run soundness for `PlacedExecCore` against
`Placed.cliProgPlacedSig` and `Placed.cliRunPlacedSig`. Defines `FastProgSoundPlaced` purely in
terms of `Program.fetchMem` and `Program.externAt?`, discharges `SubroutineRunnerSound` for
`mallocng` subroutines, and lifts `FastReachablePlaced` traces with exit or abort checks to
`ProcessRunsTo` and `cliRunPlacedSig` outcomes.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound

open Arm64 (Instr Memory Perm Program State Step Steps evalSvc)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessExitsWith ProcessOutcome ProcessRunsTo)
open CryptoVerification.SignalSession (CliHooks Inputs Outcome OutcomeMatchesProcess cliProcessInputs filesOf)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced (cliExternsPlacedSig)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig cliRunPlacedSig)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 btGet btGet_btSet_ne
  btGet_btSet_same btGet_empty rawCellAt withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (listUInt8Eq listUInt8IsPrefix lookupStrUtf8
  panicPrefixBs strUtf8Bytes)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs fastExecExternPlaced
  fastExternPlacedRaw? fastHookTablePlaced fastIsCliPanicSymbolPlacedBs hasCliHookPlaced
  panicPlacedExactNamesBs)
open Symbolic.BugInjection.Proofs.CliExec.FastEval (fastEvalInst fastEvalInst_sound)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound (EvalSound MallocngCallAddrsMatches
  SubStepSound SubroutineRunnerSound fastExecExternPlaced_compHooks0_exists_sound
  fastExecExternPlaced_exists_sound fastExecExternPlaced_sound fastStepMem fastStepMem_subStepSound
  mallocngCallAddrsOf mallocngCallAddrsOf_matches subroutineRunnerSound_of_subStepSound)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (FastProgPlaced FastReachablePlaced
  FastReachablePlacedCoreW FastReachablePlacedW StepEntryPlaced checkFastAborted
  checkFastAborted_sound checkFastExited checkFastExited0 checkFastExited0_sound
  checkFastExited_sound decodeStepFromLinePlaced fastEvalInstPlaced fastExecBarrier_sound
  fastExecLdxr_sound fastExecStxr_sound fastExecSyscallPlaced fastRunChunkCachedPlaced
  fastRunChunkCachedPlacedCoreW fastRunChunkCachedPlacedCoreW_eq fastRunChunkCachedPlacedW
  fastRunPow2Placed fastRunPow2PlacedCoreW fastRunPow2PlacedW fastRunStepsPlaced
  fastRunStepsPlacedCoreW fastRunStepsPlacedW fastStepMemPlaced fastStepPlaced fastStepPlacedCoreW
  fastStepPlacedSub fastStepPlacedW hasHookPlacedBs hookPlacedExactNamesBs isExitedWith
  isSignaledWith lookupStepEntryPlaced overlayHooksPlaced overlayHooksPlacedAux progPlacedDepth
  progPlacedWordBound withForcedNameTablePlaced_eq withForcedUInt8ListPlaced_eq)
open Symbolic.BugInjection.Proofs.CliExec.SyscallSoundnessPlaced (fastExecSyscallPlaced_sound)
open Symbolic.BugInjection.Proofs.CliExec.CliRunBridgePlaced (cliRunPlacedSig_eq_some
  cliRunPlacedSig_eq_some_of_signaled cliRunPlacedSig_eq_some_of_steps
  cliRunPlacedSig_eq_some_of_terminated cliRunsToPlaced_unique)

export Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (isExitedWith isSignaledWith
  checkFastExited checkFastExited0 checkFastAborted)
export Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (checkFastExited_sound
  checkFastExited0_sound checkFastAborted_sound)
export Symbolic.BugInjection.Proofs.CliExec.CliRunBridgePlaced (cliRunsToPlaced_unique
  cliRunPlacedSig_eq_some cliRunPlacedSig_eq_some_of_terminated cliRunPlacedSig_eq_some_of_steps
  cliRunPlacedSig_eq_some_of_signaled)

theorem subStepSound_mallocng {E : Instr → FastState → Option FastState}
    (heval : EvalSound E) (mmpl : MultiPlacement) (m0 : Memory) :
    SubStepSound mmpl m0 (fastStepMem E) :=
  fastStepMem_subStepSound heval mmpl m0

/-- Soundness predicate for an `SVC #0` (`Instr.system false 0#16`) evaluator under
`Arm64.Syscall.standard`. -/
def FastSysSound (sysF : FastState → Option FastState) : Prop :=
  ∀ {prog : Program}, prog.svc = Arm64.Syscall.standard →
    ∀ {fs fs' : FastState} {s : State},
      fs.Agrees s → sysF fs = some fs' → fs'.Agrees (prog.evalInst (.system false 0#16) s)

theorem fastEvalInstPlaced_sound_of_sys
    (hsys : FastSysSound fastExecSyscallPlaced)
    {prog : Program} (hsvc : prog.svc = Arm64.Syscall.standard)
    {inst : Instr} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s)
    (heval : fastEvalInstPlaced inst fs = some fs') :
    fs'.Agrees (prog.evalInst inst s) := by
  cases inst with
  | system isHalt imm =>
    cases isHalt with
    | false =>
      by_cases himm : imm = 0#16
      · subst himm
        exact hsys hsvc hag heval
      · have hval : fastEvalInst (.system false imm) fs = some fs' := by
          simpa [fastEvalInstPlaced, himm] using heval
        exact fastEvalInst_sound hsvc hag hval
    | true =>
      exact fastEvalInst_sound hsvc hag heval
  | ldxr sz acq rn rt =>
    exact fastExecLdxr_sound hag (evalSvc prog.svc) heval
  | stxr sz rel rs rn rt =>
    exact fastExecStxr_sound hag (evalSvc prog.svc) heval
  | barrier crm op2 =>
    dsimp only [fastEvalInstPlaced] at heval
    injection heval with heval
    subst heval
    exact fastExecBarrier_sound hag (evalSvc prog.svc) crm op2
  | _ =>
    exact fastEvalInst_sound hsvc hag heval

theorem evalSound_fastEvalInstPlaced_of_sys
    (hsys : FastSysSound fastExecSyscallPlaced) : EvalSound fastEvalInstPlaced :=
  fun {_} hsvc {_ _ _ _} hag heval => fastEvalInstPlaced_sound_of_sys hsys hsvc hag heval

/-- Soundness of a placed program table `fp` against `cliProgPlacedSig mpl mmpl W` and initial
memory `m0`: `fp.addrs` matches the `mallocng` placement `mmpl`, and every 4-byte-aligned lookup in
`fp` agrees with `fetchMem` or `externAt?` across any `m` that preserves frozen cells of `m0`. -/
structure FastProgSoundPlaced (mpl mmpl : MultiPlacement) (W : CliHooks)
    (fp : FastProgPlaced) (m0 : Memory) : Prop where
  addrs_matches : MallocngCallAddrsMatches fp.addrs mmpl
  step_sound :
    ∀ (pc : BitVec 64) (m : Memory),
      m0.KeepsFrozen m →
      pc.toNat % 4 = 0 →
      match lookupStepEntryPlaced fp (pc.toNat / 4) with
      | .instr inst => (cliProgPlacedSig mpl mmpl W).fetchMem m pc = some inst
      | .hook name =>
          ∀ h, cliExternsPlacedSig mmpl W name = some h →
            (cliProgPlacedSig mpl mmpl W).externAt? pc = some h
      | .unmapped => True

private theorem cliProgPlacedSig_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgPlacedSig mpl mmpl W).svc = Arm64.Syscall.standard :=
  rfl

private theorem cell_frozen_exec_read8_placed {m0 m : Memory} {a : BitVec 64}
    {p : Perm} {b : BitVec 8}
    (hkf : m0.KeepsFrozen m) (hcell : m0.cells a = some (some p, b))
    (hx : p.x = true) (hw : p.w = false) :
    (m.perm a).x = true ∧ m.read8 a = b := by
  have hm0_perm : m0.perm a = some p.rwx := by simp [Memory.perm, hcell]
  have hm0_read : m0.read8 a = b := by simp [Memory.read8, hcell]
  have hfrz : m0.Frozen a := by simp [Memory.Frozen, hm0_perm, Perm.frozen, Perm.rwx, hx, hw]
  rcases hkf a hfrz with ⟨hr, hp, _, _⟩
  rw [hp, hm0_perm]
  exact ⟨by simp [Perm.rwx, hx], hr.trans hm0_read⟩

/-- Extract the four frozen executable byte cells from
`decodeStepFromLinePlaced line w = .instr inst`. -/
theorem decodeStepFromLinePlaced_valid (rxLines : BinTree Line64) (hi w : Nat) (line : Line64)
    (hline : btGet 58 rxLines hi = some line) (hw : w < 16) :
    match decodeStepFromLinePlaced line w with
    | .instr inst =>
        ∃ p0 b0 p1 b1 p2 b2 p3 b3,
          (rawCellAt rxLines (64 * hi + 4 * w) = some (some p0, b0) ∧ p0.x = true ∧ p0.w = false) ∧
          (rawCellAt rxLines (64 * hi + 4 * w + 1) = some (some p1, b1) ∧ p1.x = true ∧ p1.w = false) ∧
          (rawCellAt rxLines (64 * hi + 4 * w + 2) = some (some p2, b2) ∧ p2.x = true ∧ p2.w = false) ∧
          (rawCellAt rxLines (64 * hi + 4 * w + 3) = some (some p3, b3) ∧ p3.x = true ∧ p3.w = false) ∧
          Arm64.decode (b3 ++ b2 ++ b1 ++ b0) = some inst
    | .hook _ => False
    | .unmapped => True := by
  have hc : ∀ j, j < 4 → rawCellAt rxLines (64 * hi + 4 * w + j) = btGet 6 line (4 * w + j) := by
    intro j hj
    dsimp only [rawCellAt]
    have hdiv : (64 * hi + 4 * w + j) / 64 = hi := by omega
    have hmod : (64 * hi + 4 * w + j) % 64 = 4 * w + j := by omega
    rw [hdiv, hmod, hline]
  have hc0 : rawCellAt rxLines (64 * hi + 4 * w) = btGet 6 line (4 * w) := by
    simpa only [Nat.add_zero] using hc 0 (by omega)
  have hc1 := hc 1 (by omega)
  have hc2 := hc 2 (by omega)
  have hc3 := hc 3 (by omega)
  unfold decodeStepFromLinePlaced
  cases h0 : btGet 6 line (4 * w) with
  | none => trivial
  | some c0 =>
    rcases c0 with ⟨op0, b0⟩
    cases op0 with
    | none => trivial
    | some p0 =>
      cases h1 : btGet 6 line (4 * w + 1) with
      | none => trivial
      | some c1 =>
        rcases c1 with ⟨op1, b1⟩
        cases op1 with
        | none => trivial
        | some p1 =>
          cases h2 : btGet 6 line (4 * w + 2) with
          | none => trivial
          | some c2 =>
            rcases c2 with ⟨op2, b2⟩
            cases op2 with
            | none => trivial
            | some p2 =>
              cases h3 : btGet 6 line (4 * w + 3) with
              | none => trivial
              | some c3 =>
                rcases c3 with ⟨op3, b3⟩
                cases op3 with
                | none => trivial
                | some p3 =>
                  by_cases hflags :
                      (p0.x && !p0.w && p1.x && !p1.w && p2.x && !p2.w && p3.x && !p3.w) = true
                  · simp only [hflags, ↓reduceIte]
                    cases hdec : Arm64.decode (b3 ++ b2 ++ b1 ++ b0) with
                    | none => trivial
                    | some inst =>
                      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hflags
                      rcases hflags with ⟨⟨⟨⟨⟨⟨⟨hx0, hw0⟩, hx1⟩, hw1⟩, hx2⟩, hw2⟩, hx3⟩, hw3⟩
                      exact ⟨p0, b0, p1, b1, p2, b2, p3, b3,
                        ⟨hc0.trans h0, hx0, hw0⟩, ⟨hc1.trans h1, hx1, hw1⟩,
                        ⟨hc2.trans h2, hx2, hw2⟩, ⟨hc3.trans h3, hx3, hw3⟩, hdec⟩
                  · simp [hflags]

/-- A decoded `.instr inst` in `rxLines` at a non-hooked, 4-byte-aligned `pc` implies
`(cliProgPlacedSig mpl mmpl W).fetchMem m pc = some inst` whenever `m0` agrees with `rxLines` on
`pc .. pc + 3` and `m0.KeepsFrozen m`. -/
theorem decodeStepFromLinePlaced_fetchMem
    {mpl mmpl : MultiPlacement} {W : CliHooks} {rxLines : BinTree Line64}
    {m0 m : Memory} {pc : BitVec 64} {line : Line64} {inst : Instr}
    (hm0 : ∀ j < 4, m0.cells (pc + BitVec.ofNat 64 j) =
      rawCellAt rxLines (pc + BitVec.ofNat 64 j).toNat)
    (hkf : m0.KeepsFrozen m)
    (hmod4 : pc.toNat % 4 = 0)
    (hext_none : (cliProgPlacedSig mpl mmpl W).externAt? pc = none)
    (hline : btGet 58 rxLines ((pc.toNat / 4) / 16) = some line)
    (hdec : decodeStepFromLinePlaced line ((pc.toNat / 4) % 16) = .instr inst) :
    (cliProgPlacedSig mpl mmpl W).fetchMem m pc = some inst := by
  have hv := decodeStepFromLinePlaced_valid rxLines
    ((pc.toNat / 4) / 16) ((pc.toNat / 4) % 16) line hline (by omega)
  rw [hdec] at hv
  rcases hv with ⟨p0, b0, p1, b1, p2, b2, p3, b3,
    ⟨hc0, hx0, hw0⟩, ⟨hc1, hx1, hw1⟩, ⟨hc2, hx2, hw2⟩, ⟨hc3, hx3, hw3⟩, hdecode⟩
  have hpc_lt : pc.toNat < 2 ^ 64 := pc.isLt
  have hbase_eq : 64 * ((pc.toNat / 4) / 16) + 4 * ((pc.toNat / 4) % 16) = pc.toNat := by omega
  rw [hbase_eq] at hc0 hc1 hc2 hc3
  have htoNat_j : ∀ j < 4, (pc + BitVec.ofNat 64 j).toNat = pc.toNat + j := by
    intro j hj
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hm0_0 : m0.cells (pc + 0#64) = some (some p0, b0) :=
    (hm0 0 (by omega)).trans (by rw [htoNat_j 0 (by omega), Nat.add_zero]; exact hc0)
  have hm0_1 : m0.cells (pc + 1#64) = some (some p1, b1) :=
    (hm0 1 (by omega)).trans (by rw [htoNat_j 1 (by omega)]; exact hc1)
  have hm0_2 : m0.cells (pc + 2#64) = some (some p2, b2) :=
    (hm0 2 (by omega)).trans (by rw [htoNat_j 2 (by omega)]; exact hc2)
  have hm0_3 : m0.cells (pc + 3#64) = some (some p3, b3) :=
    (hm0 3 (by omega)).trans (by rw [htoNat_j 3 (by omega)]; exact hc3)
  obtain ⟨hex0, hrd0⟩ := cell_frozen_exec_read8_placed hkf hm0_0 hx0 hw0
  obtain ⟨hex1, hrd1⟩ := cell_frozen_exec_read8_placed hkf hm0_1 hx1 hw1
  obtain ⟨hex2, hrd2⟩ := cell_frozen_exec_read8_placed hkf hm0_2 hx2 hw2
  obtain ⟨hex3, hrd3⟩ := cell_frozen_exec_read8_placed hkf hm0_3 hx3 hw3
  rw [BitVec.add_zero] at hex0
  have ha2 : pc + 1#64 + 1#64 = pc + 2#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : pc + 2#64 + 1#64 = pc + 3#64 := by rw [BitVec.add_assoc]; rfl
  have hcanExec : m.canExec pc 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, hex0, Bool.true_and, ha2, hex1, ha3, hex2, hex3]
  have hread32 : m.read32 pc = b3 ++ b2 ++ b1 ++ b0 := by
    simp only [Memory.read32, hrd0, hrd1, hrd2, hrd3]
  simp only [Program.fetchMem, hext_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    hmod4, ne_eq, not_true_eq_false, hcanExec, Bool.not_true, hread32, hdecode]

/-- First hooked `(symbolName, absoluteVaddr)` stub in `stubs` with address `vaddr`. -/
def hookStubPlacedAt? (W : CliHooks) (stubs : List (String × Nat)) (vaddr : Nat) : Option String :=
  stubs.findSome? fun (n, va) =>
    if va == vaddr then (if hasCliHookPlaced W n then some n else none) else none

private theorem hookStubPlacedAt_cons (W : CliHooks) (name : String) (va : Nat)
    (rest : List (String × Nat)) (vaddr : Nat) :
    hookStubPlacedAt? W ((name, va) :: rest) vaddr =
      match if va == vaddr then (if hasCliHookPlaced W name then some name else none) else none with
      | some b => some b
      | none => hookStubPlacedAt? W rest vaddr := by
  unfold hookStubPlacedAt?
  rw [List.findSome?_cons]
  dsimp only
  cases va == vaddr <;> cases hasCliHookPlaced W name <;> rfl

private theorem lookupStrUtf8_isSome_placed {β : Type} (bs : List UInt8) :
    ∀ (tbl : List (String × β)),
      (lookupStrUtf8 bs tbl).isSome = ((tbl.map Prod.fst).map strUtf8Bytes).any (listUInt8Eq bs)
  | [] => rfl
  | (k, _) :: rest => by
    simp only [lookupStrUtf8, List.map_cons, List.any_cons]
    cases listUInt8Eq bs (strUtf8Bytes k) <;> simp [lookupStrUtf8_isSome_placed bs rest]

private theorem hasHookPlacedBs_eq_hasCliHookPlaced (W : CliHooks) (name : String) :
    hasHookPlacedBs panicPrefixBs (hookPlacedExactNamesBs W) (strUtf8Bytes name) =
      hasCliHookPlaced W name := by
  unfold hasHookPlacedBs hookPlacedExactNamesBs hasCliHookPlaced fastExternPlacedRaw?
    fastIsCliPanicSymbolPlacedBs
  dsimp only
  rw [List.any_append, ← Bool.or_assoc]
  cases listUInt8IsPrefix panicPrefixBs (strUtf8Bytes name) ||
      panicPlacedExactNamesBs.any (fun p => listUInt8Eq (strUtf8Bytes name) p)
  · simp [lookupStrUtf8_isSome_placed]
  · simp

private theorem overlayHooksPlacedAux_cond_eq (W : CliHooks) (name : String) (va : Nat) :
    (Nat.beq (Nat.mod va 4) 0 && Nat.blt (Nat.div va 4) progPlacedWordBound &&
      hasHookPlacedBs panicPrefixBs (hookPlacedExactNamesBs W) (strUtf8Bytes name)) =
    (va % 4 == 0 && decide (va / 4 < progPlacedWordBound) && hasCliHookPlaced W name) := by
  have hmod : Nat.mod va 4 = va % 4 := rfl
  have hdiv : Nat.div va 4 = va / 4 := rfl
  rw [hmod, hdiv, hasHookPlacedBs_eq_hasCliHookPlaced]
  have hbeq : Nat.beq (va % 4) 0 = (va % 4 == 0) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.beq_eq]
  have hblt : Nat.blt (va / 4) progPlacedWordBound = decide (va / 4 < progPlacedWordBound) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]
  rw [hbeq, hblt]

/-- Characterize `btGet` on `overlayHooksPlaced` via `hookStubPlacedAt?` at `4 * idx`. -/
theorem btGet_overlayHooksPlaced (W : CliHooks) (stubs : List (String × Nat))
    (tr : BinTree String) {idx : Nat} (hidx : idx < progPlacedWordBound) :
    btGet progPlacedDepth (overlayHooksPlaced W stubs tr) idx =
      match hookStubPlacedAt? W stubs (4 * idx) with
      | some name => some name
      | none => btGet progPlacedDepth tr idx := by
  simp only [overlayHooksPlaced, withForcedUInt8ListPlaced_eq, withForcedNameTablePlaced_eq]
  induction stubs with
  | nil => simp [overlayHooksPlacedAux, hookStubPlacedAt?]
  | cons hd rest ih =>
    rcases hd with ⟨name, va⟩
    rw [hookStubPlacedAt_cons]
    have hdiv_eq : Nat.div va 4 = va / 4 := rfl
    simp only [overlayHooksPlacedAux, withForcedBinTree_eq]
    rw [overlayHooksPlacedAux_cond_eq, hdiv_eq]
    have hidx' : idx < 2 ^ progPlacedDepth := hidx
    by_cases hcond : (va % 4 == 0 && decide (va / 4 < progPlacedWordBound) &&
        hasCliHookPlaced W name) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨hmod, hdiv_lt⟩, hhook⟩
      have hva_lt : va / 4 < 2 ^ progPlacedDepth := hdiv_lt
      by_cases heq : va / 4 = idx
      · have hva_eq : va = 4 * idx := by omega
        subst heq
        rw [btGet_btSet_same progPlacedDepth (va / 4) _ _ hva_lt]
        have hvab : (va == 4 * (va / 4)) = true := beq_iff_eq.mpr hva_eq
        simp only [hvab, hhook, ↓reduceIte]
      · have hva_ne : (va == 4 * idx) = false :=
          Bool.eq_false_iff.mpr fun hb => heq (by have := eq_of_beq hb; omega)
        rw [btGet_btSet_ne progPlacedDepth (va / 4) idx _ _ hva_lt hidx' heq, ih]
        simp only [hva_ne, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hcond
      simp only [hcond, Bool.false_eq_true, ↓reduceIte, ih]
      have hhead_none :
          (if va == 4 * idx then if hasCliHookPlaced W name then some name else none else none) =
            none := by
        by_cases hva : (va == 4 * idx) = true
        · have hva_eq : va = 4 * idx := eq_of_beq hva
          have hmod : (va % 4 == 0) = true := beq_iff_eq.mpr (by omega)
          have hlt : decide (va / 4 < progPlacedWordBound) = true := decide_eq_true (by omega)
          have hh_false : hasCliHookPlaced W name = false := by
            cases hh : hasCliHookPlaced W name
            · rfl
            · exfalso
              have : (va % 4 == 0 && decide (va / 4 < progPlacedWordBound) &&
                  hasCliHookPlaced W name) = true := by
                simp [hmod, hlt, hh]
              exact absurd this (by simpa using hcond)
          simp [hva, hh_false]
        · simp only [Bool.not_eq_true] at hva
          simp [hva]
      rw [hhead_none]

/-- Single-step soundness of `fastStepPlacedCoreW`: a fast step simulates a semantic `Step` on
`cliProgPlacedSig mpl mmpl W` and preserves `m0.KeepsFrozen` across pointwise-equal extern hooks. -/
theorem fastStepPlacedCoreW_sound_of_hooks_eq
    {mpl mmpl : MultiPlacement} {Wexec W : CliHooks}
    {evalF : Instr → FastState → Option FastState}
    {fp : FastProgPlaced} {m0 : Memory} {fs fs' : FastState} {s : State}
    (heval : EvalSound evalF)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hstep : fastStepPlacedCoreW Wexec evalF (fastStepMem evalF) fp fs = some fs') :
    ∃ s' : State,
      Step (cliProgPlacedSig mpl mmpl W) s s' ∧
      fs'.Agrees s' ∧
      m0.KeepsFrozen s'.mem := by
  unfold fastStepPlacedCoreW at hstep
  cases hst : fs.status <;> rw [hst] at hstep
  · dsimp only at hstep
    have hmod_eq : ∀ x, Nat.mod x 4 = x % 4 := fun _ => rfl
    have hdiv_eq : ∀ x, Nat.div x 4 = x / 4 := fun _ => rfl
    rw [hag.pc, hmod_eq, hdiv_eq] at hstep
    have h_run : s.status = .Running := hag.status.symm.trans hst
    split at hstep; swap; · nomatch hstep
    rename_i hcond
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hcond
    rcases hcond with ⟨hmod4, _⟩
    have hspec := hfp.step_sound s.pc s.mem hkf hmod4
    cases hget : lookupStepEntryPlaced fp (s.pc.toNat / 4) with
    | unmapped =>
      rw [hget] at hstep
      nomatch hstep
    | instr inst =>
      rw [hget] at hstep hspec
      set prog := cliProgPlacedSig mpl mmpl W
      have hsem : Step prog s (prog.evalInst inst s) := Step.exec h_run hspec
      exact ⟨prog.evalInst inst s, hsem, heval (cliProgPlacedSig_svc mpl mmpl W) hag hstep,
        hkf.trans hsem.keepsFrozen⟩
    | hook name =>
      rw [hget] at hstep hspec
      have hrun_sub : SubroutineRunnerSound mmpl m0 fp.addrs (fastStepMem evalF) :=
        subroutineRunnerSound_of_subStepSound hfp.addrs_matches (subStepSound_mallocng heval mmpl m0)
      obtain ⟨h, hext, hag', hkeep, hsym⟩ :=
        fastExecExternPlaced_exists_sound hrun_sub hcl0 hkf hag hstep
      rw [hW name] at hext
      have hsem : Step (cliProgPlacedSig mpl mmpl W) s (h s) :=
        Step.extern h_run (hspec h hext) hkeep hsym
      exact ⟨h s, hsem, hag', hkf.trans hkeep⟩
  all_goals nomatch hstep

private theorem steps_trans_placed {prog : Program} {s1 s2 s3 : State}
    (h1 : Steps prog s1 s2) (h2 : Steps prog s2 s3) : Steps prog s1 s3 := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem fastRunStepsPlacedCoreW_sound_of_hooks_eq
    {mpl mmpl : MultiPlacement} {Wexec W : CliHooks}
    {evalF : Instr → FastState → Option FastState}
    {fuel : Nat} {fp : FastProgPlaced} {m0 : Memory} {fs fsf : FastState} {s : State}
    (heval : EvalSound evalF)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hrun : fastRunStepsPlacedCoreW Wexec evalF (fastStepMem evalF) fuel fp fs = some fsf) :
    ∃ sf : State,
      Steps (cliProgPlacedSig mpl mmpl W) s sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction fuel generalizing fs s with
  | zero =>
    injection hrun with hrun
    subst hrun
    exact ⟨s, .refl s, hag, hkf⟩
  | succ n ih =>
    unfold fastRunStepsPlacedCoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    · dsimp only at hrun
      cases hstep : fastStepPlacedCoreW Wexec evalF (fastStepMem evalF) fp fs with
      | none => rw [hstep] at hrun; nomatch hrun
      | some fs' =>
        rw [hstep] at hrun
        obtain ⟨s', hsem1, hag', hkf'⟩ :=
          fastStepPlacedCoreW_sound_of_hooks_eq heval hcl0 hfp hW hag hkf hstep
        obtain ⟨sf, hsems, hagf, hkff⟩ := ih hag' hkf' hrun
        exact ⟨sf, .step hsem1 hsems, hagf, hkff⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩

theorem fastRunPow2PlacedCoreW_sound_of_hooks_eq
    {mpl mmpl : MultiPlacement} {Wexec W : CliHooks}
    {evalF : Instr → FastState → Option FastState}
    {fp : FastProgPlaced} {k : Nat} {m0 : Memory} {fs fsf : FastState} {s : State}
    (heval : EvalSound evalF)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag : fs.Agrees s)
    (hkf : m0.KeepsFrozen s.mem)
    (hrun : fastRunPow2PlacedCoreW Wexec evalF (fastStepMem evalF) fp k fs = some fsf) :
    ∃ sf : State,
      Steps (cliProgPlacedSig mpl mmpl W) s sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction k generalizing fs fsf s with
  | zero =>
    unfold fastRunPow2PlacedCoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    · obtain ⟨s', hsem1, hag', hkf'⟩ :=
        fastStepPlacedCoreW_sound_of_hooks_eq heval hcl0 hfp hW hag hkf hrun
      exact ⟨s', .step hsem1 (.refl s'), hag', hkf'⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩
  | succ n ih =>
    unfold fastRunPow2PlacedCoreW at hrun
    cases hst : fs.status <;> rw [hst] at hrun
    · dsimp only at hrun
      cases hmid : fastRunPow2PlacedCoreW Wexec evalF (fastStepMem evalF) fp n fs with
      | none => rw [hmid] at hrun; nomatch hrun
      | some fs' =>
        rw [hmid] at hrun
        obtain ⟨s', hst1, hag', hkf'⟩ := ih hag hkf hmid
        obtain ⟨sf, hst2, hagf, hkff⟩ := ih hag' hkf' hrun
        exact ⟨sf, steps_trans_placed hst1 hst2, hagf, hkff⟩
    all_goals
      injection hrun with hrun
      subst hrun
      exact ⟨s, .refl s, hag, hkf⟩

/-- Lift a `FastReachablePlacedCoreW` trace to semantic `Steps` on `cliProgPlacedSig mpl mmpl W`
with `FastState.Agrees` and `m0.KeepsFrozen` preserved across pointwise-equal extern hooks. -/
theorem fastReachablePlacedCoreW_sound_of_hooks_eq
    {mpl mmpl : MultiPlacement} {Wexec W : CliHooks}
    {evalF : Instr → FastState → Option FastState}
    {fp : FastProgPlaced} {m0 : Memory} {fs0 fsf : FastState} {s0 : State}
    (hreach : FastReachablePlacedCoreW Wexec evalF (fastStepMem evalF) fp fs0 fsf)
    (heval : EvalSound evalF)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag : fs0.Agrees s0)
    (hkf : m0.KeepsFrozen s0.mem) :
    ∃ sf : State,
      Steps (cliProgPlacedSig mpl mmpl W) s0 sf ∧
      fsf.Agrees sf ∧
      m0.KeepsFrozen sf.mem := by
  induction hreach generalizing s0 with
  | refl _ => exact ⟨s0, .refl s0, hag, hkf⟩
  | chunk fuel hrun =>
    exact fastRunStepsPlacedCoreW_sound_of_hooks_eq heval hcl0 hfp hW hag hkf hrun
  | pow2 k hrun =>
    exact fastRunPow2PlacedCoreW_sound_of_hooks_eq heval hcl0 hfp hW hag hkf hrun
  | trans _ _ ih1 ih2 =>
    obtain ⟨sm, hst1, hagm, hkfm⟩ := ih1 hag hkf
    obtain ⟨sf, hst2, hagf, hkff⟩ := ih2 hagm hkfm
    exact ⟨sf, steps_trans_placed hst1 hst2, hagf, hkff⟩

theorem cliRunPlacedSig_of_fastReachablePlacedCoreW_exited_hooks_eq
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {Wexec W : CliHooks} {inp : Inputs}
    {evalF : Instr → FastState → Option FastState}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    {code : BitVec 64} {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (heval : EvalSound evalF)
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlacedCoreW Wexec evalF (fastStepMem evalF) fp fs0 fsf)
    (hchk : checkFastExited fsf code outStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) := by
  obtain ⟨sf, hsteps, hagf, _⟩ :=
    fastReachablePlacedCoreW_sound_of_hooks_eq hreach heval hcl0 hfp hW hag0 hkf0
  obtain ⟨hst, hout⟩ := checkFastExited_sound hagf hchk
  exact cliRunPlacedSig_eq_some_of_steps hload hsteps hst hout

theorem cliRunPlacedSig_of_fastReachablePlacedCoreW_aborted_hooks_eq
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {Wexec W : CliHooks} {inp : Inputs}
    {evalF : Instr → FastState → Option FastState}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    (heval : EvalSound evalF)
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl Wexec name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlacedCoreW Wexec evalF (fastStepMem evalF) fp fs0 fsf)
    (hchk : checkFastAborted fsf = true) :
    cliRunPlacedSig mpl mmpl elf W inp = some .aborted := by
  obtain ⟨sf, hsteps, hagf, _⟩ :=
    fastReachablePlacedCoreW_sound_of_hooks_eq hreach heval hcl0 hfp hW hag0 hkf0
  obtain ⟨hst, hout⟩ := checkFastAborted_sound hagf hchk
  exact cliRunPlacedSig_eq_some_of_signaled hload hsteps hst hout

theorem cliRunPlacedSig_of_fastReachablePlaced_exited_of_sys
    (hsys : FastSysSound fastExecSyscallPlaced)
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    {code : BitVec 64} {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastExited fsf code outStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) :=
  cliRunPlacedSig_of_fastReachablePlacedCoreW_exited_hooks_eq
    (evalSound_fastEvalInstPlaced_of_sys hsys) hload hcl0 hfp hW hag0 hkf0 hreach hchk

theorem cliRunPlacedSig_of_fastReachablePlaced_of_sys
    (hsys : FastSysSound fastExecSyscallPlaced)
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastExited0 fsf outStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W inp =
      some (.exited 0 outStdout (filesOf outFiles)) :=
  cliRunPlacedSig_of_fastReachablePlaced_exited_of_sys
    hsys hload hcl0 hfp hW hag0 hkf0 hreach hchk

theorem cliRunPlacedSig_of_fastReachablePlaced_aborted_of_sys
    (hsys : FastSysSound fastExecSyscallPlaced)
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastAborted fsf = true) :
    cliRunPlacedSig mpl mmpl elf W inp = some .aborted :=
  cliRunPlacedSig_of_fastReachablePlacedCoreW_aborted_hooks_eq
    (evalSound_fastEvalInstPlaced_of_sys hsys) hload hcl0 hfp hW hag0 hkf0 hreach hchk

theorem fastSysSound_fastExecSyscallPlaced : FastSysSound fastExecSyscallPlaced :=
  fun {_} hsvc {_ _ _} hag heval => fastExecSyscallPlaced_sound hsvc hag heval

/-- Instruction-level soundness of `fastEvalInstPlaced` under `Arm64.Syscall.standard`. -/
theorem fastEvalInstPlaced_sound
    {prog : Program} (hsvc : prog.svc = Arm64.Syscall.standard)
    {inst : Instr} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s)
    (heval : fastEvalInstPlaced inst fs = some fs') :
    fs'.Agrees (prog.evalInst inst s) :=
  fastEvalInstPlaced_sound_of_sys fastSysSound_fastExecSyscallPlaced hsvc hag heval

/-- End-to-end exit soundness: a `FastReachablePlaced` trace (`compHooks0`) ending in
`checkFastExited` determines `cliRunPlacedSig mpl mmpl elf W inp` for any `W` whose placed externs
agree pointwise with `compHooks0`. -/
theorem cliRunPlacedSig_of_fastReachablePlaced_exited
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    {code : BitVec 64} {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastExited fsf code outStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W inp =
      some (.exited (code.toNat % 256) outStdout (filesOf outFiles)) :=
  cliRunPlacedSig_of_fastReachablePlaced_exited_of_sys
    fastSysSound_fastExecSyscallPlaced hload hcl0 hfp hW hag0 hkf0 hreach hchk

theorem cliRunPlacedSig_of_fastReachablePlaced
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    {outStdout : List (BitVec 8)} {outFiles : List (String × List (BitVec 8))}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastExited0 fsf outStdout outFiles = true) :
    cliRunPlacedSig mpl mmpl elf W inp =
      some (.exited 0 outStdout (filesOf outFiles)) :=
  cliRunPlacedSig_of_fastReachablePlaced_of_sys
    fastSysSound_fastExecSyscallPlaced hload hcl0 hfp hW hag0 hkf0 hreach hchk

theorem cliRunPlacedSig_of_fastReachablePlaced_aborted
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {W : CliHooks} {inp : Inputs}
    {fp : FastProgPlaced} {m0 : Memory} {s0 : State} {fs0 fsf : FastState}
    (hload : elf.loadState (cliProcessInputs inp) = .ok s0)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m0)
    (hfp : FastProgSoundPlaced mpl mmpl W fp m0)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hag0 : fs0.Agrees (cliTokenPatchPlaced mpl s0))
    (hkf0 : m0.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem)
    (hreach : FastReachablePlaced fp fs0 fsf)
    (hchk : checkFastAborted fsf = true) :
    cliRunPlacedSig mpl mmpl elf W inp = some .aborted :=
  cliRunPlacedSig_of_fastReachablePlaced_aborted_of_sys
    fastSysSound_fastExecSyscallPlaced hload hcl0 hfp hW hag0 hkf0 hreach hchk

end Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound
