/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingSha256 -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
meta import ProofLib.ProgramReflection
import Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard
import Symbolic.Proofs.Refinement.Composed.Cli.Model
import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness

/-!
# `Sha256AgreesOnInput compHooks0` Proofs for `Cheval26SmallSubgroupHighBitCli`

Discharges `Sha256AgreesOnInput compHooks0` across **all** matching `PqParty` states in
`PqxdhPartyInSpecDomain` for the 3 concrete witness calls (`hbInp0`, `hbInp1 files0`, `hbInp2`) of
`Cheval26SmallSubgroupHighBitCli`.
-/

namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ShaGuard

open Arm64 (FsPath normalizePath)
open CryptoGames.HKDF (bytesToKey32)
open CryptoVerification.E2E (PreKeyMessageFields fitVec wirePrekey)
open CryptoVerification.SignalSession (coinsFile pqInitInputs pqRecvInputs pqSendInputs)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv RealHooksAgreeOnInput Sha256AgreesOnInput)
open DY.Libsignal.Composed.Refinement.Cli.ElfGuard (preKeyOfBody?)
open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace (
  ValidCall0Files hbC2Msg hbInp0 hbInp1 hbInp2 sameCliEval scrubList ssC0Coins ssC1Coins ssC1Pt
  ssC2Coins ssCall0 ssCall1 ssInp0 validCall0Files_sameCliEval validCall0Files_scrub_cliFilePath
)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PartyStates (
  hbAlice0 hbAlice1 hbAlice1Files hbBob0 hbBundleFields hbTape0
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkInitEq checkPartyWF checkRecvPrekeyEq checkSendEq compP0 pqInitInputsFast pqInitInputs_eq_fast
  pqRecvInputsFast pqRecvInputs_eq_fast pqSendInputsFast pqSendInputs_eq_fast
  sha256AgreesOnInput_of_pqInitInputs sha256AgreesOnInput_of_pqRecvPrekey_none
  sha256AgreesOnInput_of_pqSendInputs
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (
  checkInitEqReal checkPartyKeysInTable checkRecvPrekeyEqReal checkSendEqReal initiateStateFast
  reachReal_of_init realHooksAgreeOnInput_of_pqInitInputs realHooksAgreeOnInput_of_pqRecvPrekey_none
  realHooksAgreeOnInput_of_pqSendInputs_pending sessionPairOptEqBool
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (cliCoins0_eq_fast)
open Symbolic.Proofs.Tests.Refinement.Cli (
  CliFilePath cliEvalAt cliEvalAt_idle cliFilesOf_eq_evalAt
)

public section

set_option autoImplicit false

private theorem cliEvalAt_eq_of_sameCliEval {l1 l2 : List (String × HwBytes)}
    (hsame : sameCliEval l1 l2 = true) (q : FsPath) :
    cliEvalAt q none l1 = cliEvalAt q none l2 := by
  unfold sameCliEval at hsame
  obtain ⟨ha1, ha2⟩ := (Bool.and_eq_true _ _).mp hsame
  by_cases hm1 : ∃ x ∈ l1, normalizePath x.1 = q
  · obtain ⟨x, hx, hnx⟩ := hm1
    rw [← hnx]
    exact beq_iff_eq.mp (List.all_eq_true.mp ha1 x hx)
  · by_cases hm2 : ∃ x ∈ l2, normalizePath x.1 = q
    · obtain ⟨x, hx, hnx⟩ := hm2
      rw [← hnx]
      exact beq_iff_eq.mp (List.all_eq_true.mp ha2 x hx)
    · rw [cliEvalAt_idle (fun x hx h => hm1 ⟨x, hx, h⟩) none,
          cliEvalAt_idle (fun x hx h => hm2 ⟨x, hx, h⟩) none]

private theorem filesOf_append_eq_of_sameCliEval {l1 l2 extra : List (String × HwBytes)}
    (hl1 : ∀ x ∈ l1, CliFilePath x.1) (hl2 : ∀ x ∈ l2, CliFilePath x.1)
    (hex : ∀ x ∈ extra, CliFilePath x.1)
    (hsame : sameCliEval l1 l2 = true) (p : String) :
    CryptoVerification.SignalSession.filesOf (l1 ++ extra) p =
      CryptoVerification.SignalSession.filesOf (l2 ++ extra) p := by
  have hl1' : ∀ x ∈ l1 ++ extra, CliFilePath x.1 := fun x hx =>
    (List.mem_append.mp hx).elim (hl1 x) (hex x)
  have hl2' : ∀ x ∈ l2 ++ extra, CliFilePath x.1 := fun x hx =>
    (List.mem_append.mp hx).elim (hl2 x) (hex x)
  rw [cliFilesOf_eq_evalAt hl1', cliFilesOf_eq_evalAt hl2']
  split
  · rfl
  · split
    · rfl
    · unfold cliEvalAt
      rw [List.foldl_append, List.foldl_append]
      exact congrArg (fun v => extra.foldl _ v) (cliEvalAt_eq_of_sameCliEval hsame (normalizePath p))

private theorem inputsEquiv_of_eq {i j j' : CryptoVerification.SignalSession.Inputs}
    (hj : j = j') (h : InputsEquiv i j') : InputsEquiv i j :=
  ⟨h.1.trans (congrArg CryptoVerification.SignalSession.Inputs.argv hj.symm),
   h.2.1.trans (congrArg CryptoVerification.SignalSession.Inputs.dirs hj.symm),
   h.2.2.1.trans (congrArg CryptoVerification.SignalSession.Inputs.stdin hj.symm),
   fun p => (h.2.2.2 p).trans
     (congrArg (fun x => CryptoVerification.SignalSession.filesOf x.files p) hj.symm)⟩

private theorem hbInp0_files_eq :
    hbInp0.files = (pqInitInputsFast compP0 hbAlice0 hbBundleFields hbTape0).files := by
  unfold hbInp0 ssInp0 ssCall0 DY.Libsignal.Composed.Refinement.Cli.CliCall.extra ssC0Coins
  rw [cliCoins0_eq_fast]
  rfl_kernel

private theorem hbInp0_inputsEquiv :
    InputsEquiv hbInp0 (pqInitInputs compP0 hbAlice0 hbBundleFields hbTape0) :=
  inputsEquiv_of_eq (pqInitInputs_eq_fast compP0 hbAlice0 hbBundleFields hbTape0)
    ⟨by rfl_kernel, by rfl_kernel, rfl,
     fun p => congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p) hbInp0_files_eq⟩

theorem sha256AgreesOnInput_hbInp0 : Sha256AgreesOnInput compHooks0 hbInp0 := by
  rw [← compHooks0_placed_eq]
  exact sha256AgreesOnInput_of_pqInitInputs
    (st₀ := hbAlice0) (b₀ := hbBundleFields) (t₀ := hbTape0)
    (by rfl_kernel) rfl hbInp0_inputsEquiv (by rfl_kernel)

private def hbCoins1Vec : List.Vector (BitVec 8) 64 := fitVec 64 ssC1Coins

private theorem encodeDirFast_eq_ps (W : CryptoVerification.E2E.PEParams)
    (st : CryptoVerification.SignalSession.PqParty) :
    Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard.encodeDirFast W st =
      Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PartyStates.encodeDirFast W st :=
  rfl

private theorem hbAlice1Files_cliFilePath : ∀ x ∈ hbAlice1Files, CliFilePath x.1 := by
  have h : (hbAlice1Files.all fun f => decide (CliFilePath f.1)) = true := by decide +kernel
  exact fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

private theorem coinsFile_cliFilePath (c : HwBytes) :
    ∀ x ∈ ([(coinsFile, c)] : List (String × HwBytes)), CliFilePath x.1 := by
  have h : decide (CliFilePath coinsFile) = true := by decide +kernel
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact of_decide_eq_true h

private theorem hb1_checks :
    (let st := hbAlice1
     checkPartyWF compP0 st &&
     st.session.isSome &&
     (["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] ==
       (pqSendInputsFast compP0 st ssC1Pt hbCoins1Vec).argv) &&
     checkSendEq st ssC1Pt hbCoins1Vec) = true := by
  rfl_kernel

theorem sha256AgreesOnInput_hbInp1 {files0 : List (String × HwBytes)}
    (hValid0 : ValidCall0Files files0 = true) :
    Sha256AgreesOnInput compHooks0 (hbInp1 files0) := by
  rw [← compHooks0_placed_eq]
  have hchk := hb1_checks
  dsimp only at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hf_inp : (hbInp1 files0).files = scrubList files0 ++ [(coinsFile, ssC1Coins)] :=
    congrArg (scrubList files0 ++ ·) (by rfl_kernel : ssCall1.extra = [(coinsFile, ssC1Coins)])
  have hf_eq : (pqSendInputsFast compP0 hbAlice1 ssC1Pt hbCoins1Vec).files =
      hbAlice1Files ++ [(coinsFile, ssC1Coins)] :=
    congrArg₂ List.append (encodeDirFast_eq_ps compP0 hbAlice1)
      (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : hbCoins1Vec.toList = ssC1Coins))
  have heq : InputsEquiv (hbInp1 files0) (pqSendInputs compP0 hbAlice1 ssC1Pt hbCoins1Vec) :=
    inputsEquiv_of_eq (pqSendInputs_eq_fast compP0 hbAlice1 ssC1Pt hbCoins1Vec)
      ⟨hchk.1.2, rfl, rfl, fun p =>
        (congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p) hf_inp).trans
          ((filesOf_append_eq_of_sameCliEval
              (validCall0Files_scrub_cliFilePath hValid0)
              hbAlice1Files_cliFilePath
              (coinsFile_cliFilePath ssC1Coins)
              (validCall0Files_sameCliEval hValid0) p).trans
            (congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p) hf_eq.symm))⟩
  exact sha256AgreesOnInput_of_pqSendInputs
    (st₀ := hbAlice1) (m₀ := ssC1Pt) (r₀ := hbCoins1Vec)
    hchk.1.1.1 hchk.1.1.2 heq hchk.2

private def hbBody2 : HwBytes := hbC2Msg.drop 1

private def hbDummyMsg : PreKeyMessageFields where
  regId := 0
  opkId := none
  spkId := 0
  kpkId := 0
  kyberCt := List.Vector.replicate 1568 0#8
  baseKey := List.Vector.replicate 32 0#8
  idPub := List.Vector.replicate 32 0#8
  inner := []

private def hbMsg2 : PreKeyMessageFields := (preKeyOfBody? hbBody2).getD hbDummyMsg

private def hbRc2 : BitVec 256 := bytesToKey32 ssC2Coins

theorem sha256AgreesOnInput_hbInp2 : Sha256AgreesOnInput compHooks0 hbInp2 := by
  rw [← compHooks0_placed_eq]
  have heq : InputsEquiv hbInp2 (pqRecvInputs compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2) :=
    inputsEquiv_of_eq (pqRecvInputs_eq_fast compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2)
      ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel,
       fun p => congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p)
         (by rfl_kernel : hbInp2.files =
           (pqRecvInputsFast compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2).files)⟩
  exact sha256AgreesOnInput_of_pqRecvPrekey_none
    (st₀ := hbBob0) (body₀ := hbBody2) (m₀ := hbMsg2) (rc₀ := hbRc2)
    (by rfl_kernel) rfl heq (by rfl_kernel) (by rfl_kernel)

private theorem hb0_init_eq_real : checkInitEqReal hbAlice0 hbBundleFields hbTape0 = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_hbInp0 : RealHooksAgreeOnInput compHooks0 hbInp0 := by
  rw [← compHooks0_placed_eq]
  exact realHooksAgreeOnInput_of_pqInitInputs
    (st₀ := hbAlice0) (b₀ := hbBundleFields) (t₀ := hbTape0)
    (by rfl_kernel) rfl (by rfl_kernel) hbInp0_inputsEquiv hb0_init_eq_real

private theorem hb1_real_checks :
    (let st := hbAlice1
     checkPartyWF compP0 st &&
     checkPartyKeysInTable st &&
     (["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] ==
       (pqSendInputsFast compP0 st ssC1Pt hbCoins1Vec).argv) &&
     sessionPairOptEqBool
       (initiateStateFast compP0 hbAlice0.party hbAlice0.me hbBundleFields hbTape0)
       st.session &&
     checkSendEqReal st ssC1Pt hbCoins1Vec) = true := by
  rfl_kernel

private theorem hbAlice1_pending_some :
    (hbAlice1.session.map fun (_, g) => g.session.pendingPreKey) = some true := by
  rfl_kernel

theorem realHooksAgreeOnInput_hbInp1 {files0 : List (String × HwBytes)}
    (hValid0 : ValidCall0Files files0 = true) :
    RealHooksAgreeOnInput compHooks0 (hbInp1 files0) := by
  rw [← compHooks0_placed_eq]
  have hchk := hb1_real_checks
  dsimp only at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hppkOpt := hbAlice1_pending_some
  cases hs1 : hbAlice1.session with
  | none => rw [hs1] at hppkOpt; nomatch hppkOpt
  | some xg =>
    rcases xg with ⟨x1, g1⟩
    rw [hs1] at hppkOpt
    injection hppkOpt with hppk1
    have hReach1 := reachReal_of_init hb0_init_eq_real hs1
      (by rfl_kernel : hbAlice1.me = hbAlice0.me) hchk.1.2
    have hf_inp : (hbInp1 files0).files = scrubList files0 ++ [(coinsFile, ssC1Coins)] :=
      congrArg (scrubList files0 ++ ·) (by rfl_kernel : ssCall1.extra = [(coinsFile, ssC1Coins)])
    have hf_eq : (pqSendInputsFast compP0 hbAlice1 ssC1Pt hbCoins1Vec).files =
        hbAlice1Files ++ [(coinsFile, ssC1Coins)] :=
      congrArg₂ List.append (encodeDirFast_eq_ps compP0 hbAlice1)
        (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : hbCoins1Vec.toList = ssC1Coins))
    have heq : InputsEquiv (hbInp1 files0) (pqSendInputs compP0 hbAlice1 ssC1Pt hbCoins1Vec) :=
      inputsEquiv_of_eq (pqSendInputs_eq_fast compP0 hbAlice1 ssC1Pt hbCoins1Vec)
        ⟨hchk.1.1.2, rfl, rfl, fun p =>
          (congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p) hf_inp).trans
            ((filesOf_append_eq_of_sameCliEval
                (validCall0Files_scrub_cliFilePath hValid0)
                hbAlice1Files_cliFilePath
                (coinsFile_cliFilePath ssC1Coins)
                (validCall0Files_sameCliEval hValid0) p).trans
              (congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p) hf_eq.symm))⟩
    exact realHooksAgreeOnInput_of_pqSendInputs_pending
      (st₀ := hbAlice1) (x₀ := x1) (g₀ := g1) (m₀ := ssC1Pt) (r₀ := hbCoins1Vec)
      hchk.1.1.1.1 hs1 hppk1 hchk.1.1.1.2 hReach1 heq hchk.2

theorem realHooksAgreeOnInput_hbInp2 : RealHooksAgreeOnInput compHooks0 hbInp2 := by
  rw [← compHooks0_placed_eq]
  have heq : InputsEquiv hbInp2 (pqRecvInputs compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2) :=
    inputsEquiv_of_eq (pqRecvInputs_eq_fast compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2)
      ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel,
       fun p => congrArg (fun fs => CryptoVerification.SignalSession.filesOf fs p)
         (by rfl_kernel : hbInp2.files =
           (pqRecvInputsFast compP0 hbBob0 (wirePrekey :: hbBody2) hbRc2).files)⟩
  exact realHooksAgreeOnInput_of_pqRecvPrekey_none
    (st₀ := hbBob0) (body₀ := hbBody2) (m₀ := hbMsg2) (rc₀ := hbRc2)
    (by rfl_kernel) rfl (by rfl_kernel) heq (by rfl_kernel) (by rfl_kernel)

end

end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ShaGuard
