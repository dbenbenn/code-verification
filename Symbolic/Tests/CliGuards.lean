/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.ElfBindingSha256
public import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ExternWitness
import all Init.Data.Repr
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

/-!
# Kernel-Checked Guards on the Symbolic CLI Setup and Panic-Only Extern Boundary

Checks CLI setup identifiers, `abortOnPanic` / `elfRel` / `elfRelPlaced` dispatch, and joint
satisfiability of `ExternContractsHoldCli`, `HooksMatchPlaced`, and `RealHooksAgreeOnInput` under
the panic-only `cliExternsPlacedSig`. Kept in a standalone test module so proof files do not import
kernel reflection checks.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open DY
open Arm64 CryptoVerification
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (CliHooks Inputs Outcome abortOnPanic)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)

theorem aliceUuid_ne_bobUuid : aliceUuid ≠ bobUuid := by
  decide +kernel

theorem nameOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    nameOf r r.alice ≠ nameOf r r.bob := by
  unfold nameOf
  simp only [↓reduceIte, hne.symm]
  exact aliceUuid_ne_bobUuid

theorem peerNameOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    peerNameOf r r.alice ≠ peerNameOf r r.bob := by
  unfold peerNameOf
  simp only [↓reduceIte, hne.symm]
  exact aliceUuid_ne_bobUuid.symm

theorem peerOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    peerOf r r.alice ≠ peerOf r r.bob := by
  intro h
  exact peerNameOf_alice_ne_bob hne (congrArg CryptoVerification.SignalSession.Address.name h)

theorem sessionPathOf_alice_ne_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    sessionPathOf r r.alice ≠ sessionPathOf r r.bob := by
  unfold sessionPathOf peerOf peerNameOf
  simp only [↓reduceIte, hne.symm]
  decide +kernel

theorem samePath_sessionPathOf_alice_bob_false {r : ProtocolSetup} (hne : r.alice ≠ r.bob) :
    SamePath (sessionPathOf r r.alice) (sessionPathOf r r.bob) = false := by
  unfold sessionPathOf peerOf peerNameOf
  simp only [↓reduceIte, hne.symm]
  decide +kernel

theorem abortOnPanic_of_ne_panicked (h : State → State) (s : State)
    (hne : (h s).status ≠ .Panicked) :
    abortOnPanic h s = h s := by
  unfold abortOnPanic
  cases hs : (h s).status <;> simp_all

theorem elfRel_eq_cliRunElf
    (elf : Arm64.Process.ElfImage) (addrs : CryptoVerification.SignalSession.CliElfAddrs)
    (interp : ExternInterpretation)
    (W : CliHooks) (i : Inputs) (o : Option Outcome) :
    elfRel elf addrs interp W i o ↔
      CryptoVerification.SignalSession.cliRunElf elf addrs i = o ∧ RealHooksAgreeOnInput W i :=
  Iff.rfl

theorem elfRelPlaced_eq_cliRunPlacedSig (mpl : Arm64.Obj.MultiPlacement)
    (elf : Arm64.Process.ElfImage) (interp : ExternInterpretation)
    (W : CliHooks) (i : Inputs) (o : Option Outcome) :
    elfRelPlaced mpl elf interp W i o ↔
      cliRunPlacedSig mpl elf i = o ∧ RealHooksAgreeOnInput W i :=
  Iff.rfl

/-- Joint satisfiability of panic-only `cliExternsPlacedSig`, `ExternContractsHoldCli`,
and `HooksMatchPlaced` (pinning `W₀.C.E = CryptoGames.AES256.aes256Enc` and
`W₀.C.D = CryptoGames.AES256.aes256Dec`). -/
theorem cliPlacedRealAesWitness_hooksAgree_and_guard :
    ∃ interp₀ W₀,
      ExternInterpretationTotalOnUsedSymbols interp₀ ∧
      ExternContractsHoldCli interp₀ ∧
      HooksMatchPlaced interp₀ W₀ ∧
      W₀.C.E = CryptoGames.AES256.aes256Enc ∧
      W₀.C.D = CryptoGames.AES256.aes256Dec ∧
      (∀ name, CryptoVerification.SignalSession.isCliPanicSymbolPlaced name = false →
        CryptoVerification.SignalSession.cliExternsPlacedSig name = none) :=
  ⟨Symbolic.Proofs.TopLevelHelpers.Composed.Cli.cliWitnessInterp,
   Symbolic.Proofs.TopLevelHelpers.Composed.Cli.cliWitnessHooks,
   Symbolic.Proofs.TopLevelHelpers.Composed.Cli.cliWitnessInterp_total,
   Symbolic.Proofs.TopLevelHelpers.Composed.Cli.cliWitnessInterp_contracts,
   Symbolic.Proofs.TopLevelHelpers.Composed.Cli.cliWitnessHooks_agree_placed,
   rfl, rfl,
   fun _ h => by simp [CryptoVerification.SignalSession.cliExternsPlacedSig, h]⟩

/-- Unconditional `RealHooksAgreeOnInput` and panic-only `cliExternsPlacedSig` at `realCliHooks`. -/
theorem cliPlacedRealHooks_guard :
    (∀ i, RealHooksAgreeOnInput realCliHooks i) ∧
    (∀ name, CryptoVerification.SignalSession.isCliPanicSymbolPlaced name = false →
      CryptoVerification.SignalSession.cliExternsPlacedSig name = none) :=
  ⟨fun i => (realHooksAgreeOnInput_iff_true_of_eq rfl i).mpr trivial,
   fun _ h => by simp [CryptoVerification.SignalSession.cliExternsPlacedSig, h]⟩

end DY.Libsignal.Composed.Refinement.Cli
