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
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
meta import ProofLib.ProgramReflection
import Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon

/-!
# `RealHooksAgreeOnInput compHooks0` Proofs for `wsInp0`..`wsInp2`
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02

open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification.E2E (fitVec pqxdhSpqrSession)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (coinsFile filesOf pqInitInputs pqSendInputs)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv RealHooksAgreeOnInput)
open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (
  FileList ValidStepFiles coins1 coins2 isCliFilePath pt1 pt2 scrubList validFileList wsAlice0
  wsAlice1 wsAlice1Files wsAlice2 wsAlice2Files wsBundleFields wsCall1 wsCall2 wsInp0 wsInp1
  wsInp2 wsTape0
)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (
  coinsExtra_paths encodeDirFast_eq_ws filesOf_append_eq_of_sameEvalFileList inputsEquiv_of_eq
  validFileList_filter validFileList_paths
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkPartyWF compP0 optEqBool pqInitInputsFast pqInitInputs_eq_fast pqSendInputsFast
  pqSendInputs_eq_fast pqxdhSessionParamsFast sessionStateEqBool
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (
  checkInitEqReal checkPartyKeysInTable checkSendEqReal initiateStateFast reachReal_of_init
  reachReal_of_send realHooksAgreeOnInput_of_pqInitInputs
  realHooksAgreeOnInput_of_pqSendInputs_pending recordExtrasEqBool sessionPairOptEqBool
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)

public section

set_option autoImplicit false

private theorem ws0_init_eq : checkInitEqReal wsAlice0 wsBundleFields wsTape0 = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp0 : RealHooksAgreeOnInput compHooks0 wsInp0 := by
  rw [← compHooks0_placed_eq]
  have heq : InputsEquiv wsInp0 (pqInitInputs compP0 wsAlice0 wsBundleFields wsTape0) :=
    inputsEquiv_of_eq (pqInitInputs_eq_fast compP0 wsAlice0 wsBundleFields wsTape0)
      ⟨by rfl_kernel, by rfl_kernel, rfl,
       fun p => congrArg (fun fs => filesOf fs p)
         (by rfl_kernel : wsInp0.files =
           (pqInitInputsFast compP0 wsAlice0 wsBundleFields wsTape0).files)⟩
  exact realHooksAgreeOnInput_of_pqInitInputs
    (st₀ := wsAlice0) (b₀ := wsBundleFields) (t₀ := wsTape0)
    (by rfl_kernel) rfl (by rfl_kernel) heq ws0_init_eq

private def wsCoins1Vec : List.Vector (BitVec 8) 64 := fitVec 64 coins1
private def wsCoins2Vec : List.Vector (BitVec 8) 64 := fitVec 64 coins2

private theorem ws1_checks :
    (let st := wsAlice1
     (wsAlice1Files.all fun x => isCliFilePath x.1) &&
     checkPartyWF compP0 st &&
     checkPartyKeysInTable st &&
     (["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] ==
       (pqSendInputsFast compP0 st pt1 wsCoins1Vec).argv) &&
     sessionPairOptEqBool
       (initiateStateFast compP0 wsAlice0.party wsAlice0.me wsBundleFields wsTape0)
       st.session &&
     checkSendEqReal st pt1 wsCoins1Vec) = true := by
  rfl_kernel

private theorem wsAlice1_pending_some :
    (wsAlice1.session.map fun (_, g) => g.session.pendingPreKey) = some true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp1 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp1 f0) := by
  rw [← compHooks0_placed_eq]
  have hchk := ws1_checks; dsimp only at hchk; simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hppkOpt := wsAlice1_pending_some
  cases hs1 : wsAlice1.session with
  | none => rw [hs1] at hppkOpt; nomatch hppkOpt
  | some xg1 =>
    rcases xg1 with ⟨x1, g1⟩
    rw [hs1] at hppkOpt
    injection hppkOpt with hppk1
    have hReach1 := reachReal_of_init ws0_init_eq hs1
      (by rfl_kernel : wsAlice1.me = wsAlice0.me) hchk.1.2
    have hv0 : validFileList f0 = true := by
      unfold ValidStepFiles at hValid; simp only [Bool.and_eq_true] at hValid
      exact hValid.1.1.1.1.1.1.1.1.1.1
    have hsd := ValidStepFiles.sameDirs hValid
    unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.sameStepDirs at hsd
    simp only [Bool.and_eq_true] at hsd
    have hf_inp : (wsInp1 f0).files = scrubList f0 ++ [(coinsFile, coins1)] :=
      congrArg (scrubList f0 ++ ·) (by rfl_kernel : wsCall1.extra = [(coinsFile, coins1)])
    have hf_eq : (pqSendInputsFast compP0 wsAlice1 pt1 wsCoins1Vec).files =
        wsAlice1Files ++ [(coinsFile, coins1)] :=
      congrArg₂ List.append (encodeDirFast_eq_ws compP0 wsAlice1)
        (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : wsCoins1Vec.toList = coins1))
    have heq : InputsEquiv (wsInp1 f0) (pqSendInputs compP0 wsAlice1 pt1 wsCoins1Vec) :=
      inputsEquiv_of_eq (pqSendInputs_eq_fast compP0 wsAlice1 pt1 wsCoins1Vec)
        ⟨hchk.1.1.2, rfl, rfl, fun p =>
          (congrArg (fun fs => filesOf fs p) hf_inp).trans
            ((filesOf_append_eq_of_sameEvalFileList
                (validFileList_paths (validFileList_filter _ hv0))
                hchk.1.1.1.1.1 (coinsExtra_paths coins1) hsd.1.1.1.1 p).trans
              (congrArg (fun fs => filesOf fs p) hf_eq.symm))⟩
    exact realHooksAgreeOnInput_of_pqSendInputs_pending
      (st₀ := wsAlice1) (x₀ := x1) (g₀ := g1) (m₀ := pt1) (r₀ := wsCoins1Vec)
      hchk.1.1.1.1.2 hs1 hppk1 hchk.1.1.1.2 hReach1 heq hchk.2

private theorem ws2_checks :
    (let st := wsAlice2
     (wsAlice2Files.all fun x => isCliFilePath x.1) &&
     checkPartyWF compP0 st &&
     checkPartyKeysInTable st &&
     (["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] ==
       (pqSendInputsFast compP0 st pt2 wsCoins2Vec).argv) &&
     checkSendEqReal st pt2 wsCoins2Vec) = true := by
  rfl_kernel

private theorem ws2_step_ok :
    (match wsAlice1.session, wsAlice2.session with
     | some (x1, g1), some (x2, g2) =>
       g2.session.pendingPreKey &&
       (g2.party == g1.party) &&
       recordExtrasEqBool x2 x1 &&
       optEqBool sessionStateEqBool
         (match SessionState.messageEncrypt compP0.C protoSignalCodec (pqxdhSpqrSession compP0)
             ((pqxdhSessionParamsFast compP0).sendAddrs g1.party) pt1 wsCoins1Vec.toList g1.session with
          | (.ok _, s) => some s | (.error _, _) => none)
         (some g2.session)
     | _, _ => false) = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp2 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp2 f1) := by
  rw [← compHooks0_placed_eq]
  have hchk1 := ws1_checks; dsimp only at hchk1; simp only [Bool.and_eq_true, beq_iff_eq] at hchk1
  have hchk2 := ws2_checks; dsimp only at hchk2; simp only [Bool.and_eq_true, beq_iff_eq] at hchk2
  have hstep2 := ws2_step_ok
  cases hs1 : wsAlice1.session with
  | none => rw [hs1] at hstep2; cases hstep2
  | some xg1 =>
    rcases xg1 with ⟨x1, g1⟩
    cases hs2 : wsAlice2.session with
    | none => rw [hs1, hs2] at hstep2; cases hstep2
    | some xg2 =>
      rcases xg2 with ⟨x2, g2⟩
      rw [hs1, hs2] at hstep2
      dsimp only at hstep2
      simp only [Bool.and_eq_true, beq_iff_eq] at hstep2
      have hReach1 := reachReal_of_init ws0_init_eq hs1
        (by rfl_kernel : wsAlice1.me = wsAlice0.me) hchk1.1.2
      have hReach2 := reachReal_of_send hs1 hchk1.1.1.1.1.2 hReach1 hchk1.2 hs2
        (by rfl_kernel : wsAlice2.me = wsAlice1.me) hstep2.1.2 hstep2.2 hstep2.1.1.2
      have hv1 : validFileList f1 = true := by
        unfold ValidStepFiles at hValid; simp only [Bool.and_eq_true] at hValid
        exact hValid.1.1.1.1.1.1.1.1.1.2
      have hsd := ValidStepFiles.sameDirs hValid
      unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.sameStepDirs at hsd
      simp only [Bool.and_eq_true] at hsd
      have hf_inp : (wsInp2 f1).files = scrubList f1 ++ [(coinsFile, coins2)] :=
        congrArg (scrubList f1 ++ ·) (by rfl_kernel : wsCall2.extra = [(coinsFile, coins2)])
      have hf_eq : (pqSendInputsFast compP0 wsAlice2 pt2 wsCoins2Vec).files =
          wsAlice2Files ++ [(coinsFile, coins2)] :=
        congrArg₂ List.append (encodeDirFast_eq_ws compP0 wsAlice2)
          (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : wsCoins2Vec.toList = coins2))
      have heq : InputsEquiv (wsInp2 f1) (pqSendInputs compP0 wsAlice2 pt2 wsCoins2Vec) :=
        inputsEquiv_of_eq (pqSendInputs_eq_fast compP0 wsAlice2 pt2 wsCoins2Vec)
          ⟨hchk2.1.2, rfl, rfl, fun p =>
            (congrArg (fun fs => filesOf fs p) hf_inp).trans
              ((filesOf_append_eq_of_sameEvalFileList
                  (validFileList_paths (validFileList_filter _ hv1))
                  hchk2.1.1.1.1 (coinsExtra_paths coins2) hsd.1.1.1.2 p).trans
                (congrArg (fun fs => filesOf fs p) hf_eq.symm))⟩
      exact realHooksAgreeOnInput_of_pqSendInputs_pending
        (st₀ := wsAlice2) (x₀ := x2) (g₀ := g2) (m₀ := pt2) (r₀ := wsCoins2Vec)
        hchk2.1.1.1.2 hs2 hstep2.1.1.1 hchk2.1.1.2 hReach2 heq hchk2.2

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard02
