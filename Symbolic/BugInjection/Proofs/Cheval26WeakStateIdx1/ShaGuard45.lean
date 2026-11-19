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
# `RealHooksAgreeOnInput compHooks0` Proofs for `wsInp4` and `wsInp5`
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard45

open CryptoVerification.E2E (fitVec)
open CryptoVerification.SignalSession (bundleDir coinsFile filesOf pqInitInputs pqSendInputs)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv RealHooksAgreeOnInput)
open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (
  FileList ValidStepFiles clearSessionList coins4 coins5 isCliFilePath pt5 scrubList validFileList
  wsAlice0 wsAlice0Files wsAlice5 wsAlice5Files wsAliceSessPath wsBundle wsBundleFields wsCall4
  wsCall5 wsInp4 wsInp5 wsTape4
)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (
  bundleCoinsExtra_paths coinsExtra_paths encodeDirFast_eq_ws filesOf_append_eq_of_sameEvalFileList
  inputsEquiv_of_eq validFileList_filter validFileList_paths
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkPartyWF compP0 pqInitInputsFast pqInitInputs_eq_fast pqSendInputsFast pqSendInputs_eq_fast
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (
  checkInitEqReal checkPartyKeysInTable checkSendEqReal initiateStateFast reachReal_of_init
  realHooksAgreeOnInput_of_pqInitInputs realHooksAgreeOnInput_of_pqSendInputs_pending
  sessionPairOptEqBool
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)

public section

set_option autoImplicit false

private def wsCoins5Vec : List.Vector (BitVec 8) 64 := fitVec 64 coins5

private theorem ws4_checks :
    ((wsAlice0Files.all fun x => isCliFilePath x.1) &&
     checkPartyWF compP0 wsAlice0 &&
     checkPartyKeysInTable wsAlice0 &&
     (["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] ==
       (pqInitInputsFast compP0 wsAlice0 wsBundleFields wsTape4).argv) &&
     checkInitEqReal wsAlice0 wsBundleFields wsTape4) = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp4 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp4 f2) := by
  rw [← compHooks0_placed_eq]
  have hchk := ws4_checks; simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hv2 : validFileList f2 = true := by
    unfold ValidStepFiles at hValid; simp only [Bool.and_eq_true] at hValid
    exact hValid.1.1.1.1.1.1.1.1.2
  have hsd := ValidStepFiles.sameDirs hValid
  unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.sameStepDirs at hsd
  simp only [Bool.and_eq_true] at hsd
  have hf_inp : (wsInp4 f2).files =
      clearSessionList wsAliceSessPath (scrubList f2) ++
        (wsBundle.files bundleDir ++ [(coinsFile, coins4)]) :=
    congrArg (clearSessionList wsAliceSessPath (scrubList f2) ++ ·)
      (by rfl_kernel : wsCall4.extra = wsBundle.files bundleDir ++ [(coinsFile, coins4)])
  have hf_eq : (pqInitInputsFast compP0 wsAlice0 wsBundleFields wsTape4).files =
      wsAlice0Files ++ (wsBundle.files bundleDir ++ [(coinsFile, coins4)]) := by rfl_kernel
  have heq : InputsEquiv (wsInp4 f2) (pqInitInputs compP0 wsAlice0 wsBundleFields wsTape4) :=
    inputsEquiv_of_eq (pqInitInputs_eq_fast compP0 wsAlice0 wsBundleFields wsTape4)
      ⟨hchk.1.2, rfl, rfl, fun p =>
        (congrArg (fun fs => filesOf fs p) hf_inp).trans
          ((filesOf_append_eq_of_sameEvalFileList
              (validFileList_paths (validFileList_filter _ (validFileList_filter _ hv2)))
              hchk.1.1.1.1 (bundleCoinsExtra_paths coins4) hsd.1.1.2 p).trans
            (congrArg (fun fs => filesOf fs p) hf_eq.symm))⟩
  exact realHooksAgreeOnInput_of_pqInitInputs
    (st₀ := wsAlice0) (b₀ := wsBundleFields) (t₀ := wsTape4)
    hchk.1.1.1.2 rfl hchk.1.1.2 heq hchk.2

private theorem ws5_meta :
    (let st := wsAlice5
     (wsAlice5Files.all fun x => isCliFilePath x.1) &&
     checkPartyWF compP0 st &&
     checkPartyKeysInTable st &&
     sessionPairOptEqBool
       (initiateStateFast compP0 wsAlice0.party wsAlice0.me wsBundleFields wsTape4)
       st.session &&
     (["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] ==
       (pqSendInputsFast compP0 st pt5 wsCoins5Vec).argv)) = true := by
  rfl_kernel

private theorem wsAlice5_pending_some :
    (wsAlice5.session.map fun (_, g) => g.session.pendingPreKey) = some true := by
  rfl_kernel

private theorem ws5_send_eq :
    checkSendEqReal wsAlice5 pt5 wsCoins5Vec = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp5 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp5 f4) := by
  rw [← compHooks0_placed_eq]
  have hchk4 := ws4_checks; simp only [Bool.and_eq_true, beq_iff_eq] at hchk4
  have hchk := ws5_meta; dsimp only at hchk; simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hppkOpt := wsAlice5_pending_some
  cases hs5 : wsAlice5.session with
  | none => rw [hs5] at hppkOpt; nomatch hppkOpt
  | some xg5 =>
    rcases xg5 with ⟨x5, g5⟩
    rw [hs5] at hppkOpt
    injection hppkOpt with hppk5
    have hReach5 := reachReal_of_init hchk4.2 hs5
      (by rfl_kernel : wsAlice5.me = wsAlice0.me) hchk.1.2
    have hv4 : validFileList f4 = true := by
      unfold ValidStepFiles at hValid; simp only [Bool.and_eq_true] at hValid
      exact hValid.1.1.1.1.1.1.2
    have hsd := ValidStepFiles.sameDirs hValid
    unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.sameStepDirs at hsd
    simp only [Bool.and_eq_true] at hsd
    have hf_inp : (wsInp5 f4).files = scrubList f4 ++ [(coinsFile, coins5)] :=
      congrArg (scrubList f4 ++ ·) (by rfl_kernel : wsCall5.extra = [(coinsFile, coins5)])
    have hf_eq : (pqSendInputsFast compP0 wsAlice5 pt5 wsCoins5Vec).files =
        wsAlice5Files ++ [(coinsFile, coins5)] :=
      congrArg₂ List.append (encodeDirFast_eq_ws compP0 wsAlice5)
        (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : wsCoins5Vec.toList = coins5))
    have heq : InputsEquiv (wsInp5 f4) (pqSendInputs compP0 wsAlice5 pt5 wsCoins5Vec) :=
      inputsEquiv_of_eq (pqSendInputs_eq_fast compP0 wsAlice5 pt5 wsCoins5Vec)
        ⟨hchk.2, rfl, rfl, fun p =>
          (congrArg (fun fs => filesOf fs p) hf_inp).trans
            ((filesOf_append_eq_of_sameEvalFileList
                (validFileList_paths (validFileList_filter _ hv4))
                hchk.1.1.1.1 (coinsExtra_paths coins5) hsd.2 p).trans
              (congrArg (fun fs => filesOf fs p) hf_eq.symm))⟩
    exact realHooksAgreeOnInput_of_pqSendInputs_pending
      (st₀ := wsAlice5) (x₀ := x5) (g₀ := g5) (m₀ := pt5) (r₀ := wsCoins5Vec)
      hchk.1.1.1.2 hs5 hppk5 hchk.1.1.2 hReach5 heq ws5_send_eq

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard45
