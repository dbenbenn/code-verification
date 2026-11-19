/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `M24` (SWAR-Padded) ↔ `F3.L4B` `NeedLocks` Specification Equivalences

Establishes definitional and extensional equalities (`=`) and bi-implications (`↔`) between the
SWAR-padded `NeedLocks`, `argvAtROPad`, `MuslHarnessFineNeedLocks{,Guarded}PadPerInput`, and
`MainOkCliExt*B2NeedLocksPadPlacedAt` definitions in
`M24.{ArgvPad,CliElfMallocngHarness,CliStrictPlaced,CliStrictPlacedPadSat}` and the SWAR-padded
`F3.L4B.{F3HarnessPlaced,CliStrictPlaced2}` definitions (`M24.CliStrictPlaced.argvAtRO` stays
unpadded).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks CliRun Inputs Outcome cliExternsPlaced cliProcessInputs)
open CryptoVerification.SignalSession.Cli (MainGhost RunAnswer)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (FineBudget)

/-! ## `cStrAtRO`, `argvAtRO`, `B2MainEntryFacts`, and `b2MainSpecTightNeedLocksFineAt` -/

theorem cStrAtRO_eq (p : BitVec 64) (s : List (BitVec 8)) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.cStrAtROPad p s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cStrAtRO p s :=
  rfl

theorem argvAtRO_eq : ∀ (a : BitVec 64) (ss : List (List (BitVec 8))),
    LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.argvAtROPad a ss =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO a ss
  | _, [] => rfl
  | a, s :: ss => by
    simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.argvAtROPad,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO,
      cStrAtRO_eq, argvAtRO_eq (a + 8#64) ss]

theorem B2MainEntryFacts_eq (inputsOf : Inputs → ProcessInputs) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.B2MainEntryFacts inputsOf i s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.B2MainEntryFacts inputsOf i s :=
  rfl

theorem b2MainFrameFine_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainFrameFinePad
        A lim st stk Statics i s =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine
        A lim st stk Statics i s := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainFrameFinePad,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainFrameFine,
    argvAtRO_eq]

theorem b2MainSpecTightNeedLocksFineAt_eq (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainSpecTightNeedLocksFineAtPad
        libcAddr CodeOk A lim st stk Statics Run inputsOf =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
        libcAddr CodeOk A lim st stk Statics Run inputsOf := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainSpecTightNeedLocksFineAtPad
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
  congr 1
  funext g s
  rw [B2MainEntryFacts_eq, b2MainFrameFine_eq]

/-! ## `cliProgExtPlacedAt` and `cliStaticsPlacedAt` -/

theorem cliProgExtPlacedAt_eq (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
        mpl ext idx W =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
        mpl ext idx W :=
  rfl

theorem cliStaticsPlacedAt_eq (mpl : Obj.MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced.cliStaticsPlacedAt mpl =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliStaticsPlacedAt mpl :=
  rfl

/-! ## `subroutine_ok`, `MuslHarnessFineNeedLocksPerInput`, and `MainOkCliExt*` Bridges -/

theorem subroutine_ok_b2MainSpecTightNeedLocksFineAt_eq
    (mpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (idx : Nat) (W : CliHooks) (pc : BitVec 64)
    (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainSpecTightNeedLocksFineAtPad
          libcAddr CodeOk A lim st stk Statics Run inputsOf) =
      subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) := by
  rw [cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq]

theorem subroutine_ok_b2MainSpecTightNeedLocksFineAt_iff
    (mpl : Obj.MultiPlacement) (ext : CliHooks → String → Option (State → State))
    (idx : Nat) (W : CliHooks) (pc : BitVec 64)
    (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) :
    subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.ArgvPad.b2MainSpecTightNeedLocksFineAtPad
          libcAddr CodeOk A lim st stk Statics Run inputsOf) ↔
      subroutine_ok
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.cliProgExtPlacedAt
          mpl ext idx W)
        pc
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.b2MainSpecTightNeedLocksFineAt
          libcAddr CodeOk A lim st stk Statics Run inputsOf) := by
  rw [subroutine_ok_b2MainSpecTightNeedLocksFineAt_eq]

theorem mainOkCliExtPqB2NeedLocksPlacedAt_eq
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtPqB2NeedLocksPadPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtPqB2NeedLocksPadPlacedAt,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt,
    cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq, cliStaticsPlacedAt_eq]

theorem mainOkCliExtPqB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtPqB2NeedLocksPadPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtPqB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  rw [mainOkCliExtPqB2NeedLocksPlacedAt_eq]

theorem mainOkCliExtOverB2NeedLocksPlacedAt_eq
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtOverB2NeedLocksPadPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  simp only [LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtOverB2NeedLocksPadPlacedAt,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt,
    cliProgExtPlacedAt_eq, b2MainSpecTightNeedLocksFineAt_eq, cliStaticsPlacedAt_eq]

theorem mainOkCliExtOverB2NeedLocksPlacedAt_iff
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) :
    LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlacedPadSat.MainOkCliExtOverB2NeedLocksPadPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim ↔
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.MainOkCliExtOverB2NeedLocksPlacedAt
        mpl mmpl ext mainIdx inputsOf CodeOk libcAddr brkStart stk lim := by
  rw [mainOkCliExtOverB2NeedLocksPlacedAt_eq]

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
