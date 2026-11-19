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
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6Dk
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6Tail

/-!
# `RealHooksAgreeOnInput compHooks0` Proof for `wsInp6`
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6

open CryptoVerification.E2E (responderRecordExtras wirePrekey)
open CryptoVerification.SignalSession (coinsFile filesOf pqRecvInputs preKeysNamedBy)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv RealHooksAgreeOnInput)
open DY.Libsignal.Composed.Refinement.Cli.ElfGuard (preKeyOfBody?)
open scoped ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (
  FileList ValidStepFiles c6In coins6 isCliFilePath scrubList validFileList wsBob0 wsBob3
  wsBob3Files wsCall6 wsInp6 wsMsg3 wsRc3
)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard3 (ws3_recv_eq)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6Dk (ws6_dk_eq)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6Tail (ws6_tail_eq)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon (
  checkRecvPrekeyEqAt_congr_st checkRecvPrekeyEqAt_of_split checkWs6NonMatch coinsExtra_paths
  encodeDirFast_eq_ws filesOf_append_eq_of_sameEvalFileList inputsEquiv_of_eq localIdEqBool
  of_checkWs6NonMatch respSecretsEqBool validFileList_filter validFileList_paths wsBob3NoSess
  wsBody6 wsMsg6 wsRc6
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkPartyWF compP0 optEqBool pqRecvInputsFast pqRecvInputs_eq_fast prodEqBool
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealGuard (
  checkNotRawDir0 checkPartyKeysInTable checkRecvPrekeyEqReal ghostStateEqBool
  reachReal_of_recvPrekey realHooksAgreeOnInput_of_pqRecvPrekey_noMatch_resp realP0Hybrid
  recordExtrasEqBool recvPrekeyStateFast
)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)

public section

set_option autoImplicit false

private theorem ws6_meta :
    (let st := wsBob3
     let stNo := { st with session := none }
     (wsBob3Files.all fun x => isCliFilePath x.1) &&
     checkPartyWF compP0 st &&
     (["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] ==
       (pqRecvInputsFast compP0 st (wirePrekey :: wsBody6) wsRc6).argv) &&
     checkWs6NonMatch &&
     ((stNo.party == wsBob3NoSess.party) && localIdEqBool stNo.me wsBob3NoSess.me &&
      optEqBool respSecretsEqBool (preKeysNamedBy stNo wsMsg6)
        (preKeysNamedBy wsBob3NoSess wsMsg6))) = true := by
  rfl_kernel

private theorem ws6_resp_checks :
    (checkPartyKeysInTable wsBob3 &&
     match wsBob3.session with
     | some (x₀, g₀) =>
       recordExtrasEqBool x₀ (responderRecordExtras wsBob3.me wsMsg3) &&
       checkNotRawDir0 g₀.session.pqRatchetState &&
       optEqBool (optEqBool (optEqBool (prodEqBool recordExtrasEqBool ghostStateEqBool)))
         ((preKeysNamedBy wsBob0 wsMsg3).map fun k =>
           (recvPrekeyStateFast compP0 wsBob0.party wsBob0.me k wsMsg3 wsRc3).map
             (Option.map fun (x, g, _) => (x, g)))
         (some (some (some (x₀, g₀))))
     | none => false) = true := by
  rfl_kernel

theorem realHooksAgreeOnInput_wsInp6 {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (hValid : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    RealHooksAgreeOnInput compHooks0 (wsInp6 f3) := by
  rw [← compHooks0_placed_eq]
  obtain ⟨hchkL, hstEq⟩ := (Bool.and_eq_true _ _).mp ws6_meta
  obtain ⟨⟨⟨hfiles3, hwf3⟩, hargv3⟩, hnm⟩ :=
    (Bool.and_eq_true _ _).mp hchkL |>.imp_left fun h =>
      (Bool.and_eq_true _ _).mp h |>.imp_left (Bool.and_eq_true _ _).mp
  have hv3 : validFileList f3 = true := by
    unfold ValidStepFiles at hValid; simp only [Bool.and_eq_true] at hValid
    exact hValid.1.1.1.1.1.1.1.2
  have hsd := ValidStepFiles.sameDirs hValid
  unfold Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.sameStepDirs at hsd
  simp only [Bool.and_eq_true] at hsd
  have hf_inp : (wsInp6 f3).files = scrubList f3 ++ [(coinsFile, coins6)] :=
    congrArg (scrubList f3 ++ ·) (by rfl_kernel : wsCall6.extra = [(coinsFile, coins6)])
  have hf_eq : (pqRecvInputsFast compP0 wsBob3 (wirePrekey :: wsBody6) wsRc6).files =
      wsBob3Files ++ [(coinsFile, coins6)] :=
    congrArg₂ List.append (encodeDirFast_eq_ws compP0 wsBob3)
      (congrArg (fun c => [(coinsFile, c)]) (by rfl_kernel : CryptoGames.HMAC.keyToBytes32 wsRc6 = coins6))
  have heq : InputsEquiv (wsInp6 f3) (pqRecvInputs compP0 wsBob3 (wirePrekey :: wsBody6) wsRc6) :=
    inputsEquiv_of_eq (pqRecvInputs_eq_fast compP0 wsBob3 (wirePrekey :: wsBody6) wsRc6)
      ⟨beq_iff_eq.mp hargv3, rfl, (by rfl_kernel : c6In = wirePrekey :: wsBody6), fun p =>
        (congrArg (fun fs => filesOf fs p) hf_inp).trans
          ((filesOf_append_eq_of_sameEvalFileList
              (validFileList_paths (validFileList_filter _ hv3))
              hfiles3 (coinsExtra_paths coins6) hsd.1.2 p).trans
            (congrArg (fun fs => filesOf fs p) hf_eq.symm))⟩
  have hm : preKeyOfBody? wsBody6 = some wsMsg6 := by rfl_kernel
  obtain ⟨x₀, g₀, q₀, hs, hq, hne1, hne2⟩ := of_checkWs6NonMatch hnm
  have hresp := ws6_resp_checks
  rw [hs] at hresp
  dsimp only at hresp
  simp only [Bool.and_eq_true] at hresp
  rcases hresp with ⟨hKeys3, ⟨hx₀, hNotDir0⟩, hStep3⟩
  have hReach3 := reachReal_of_recvPrekey ws3_recv_eq hs
    (by rfl_kernel : wsBob3.me = wsBob0.me) hStep3
  have heval : checkRecvPrekeyEqReal { wsBob3 with session := none } wsMsg6 wsRc6 = true :=
    (checkRecvPrekeyEqAt_congr_st (W₁ := compP0) (W₂ := realP0Hybrid)
      (st₁ := { wsBob3 with session := none }) (st₂ := wsBob3NoSess) (rc := wsRc6) hstEq).trans
      (checkRecvPrekeyEqAt_of_split ws6_dk_eq ws6_tail_eq)
  exact realHooksAgreeOnInput_of_pqRecvPrekey_noMatch_resp
    (st₀ := wsBob3) (x₀ := x₀) (g₀ := g₀) (mInit := wsMsg3)
    (body₀ := wsBody6) (m₀ := wsMsg6) (q₀ := q₀) (rc₀ := wsRc6)
    hwf3 hs hx₀ hNotDir0 hKeys3 hReach3 heq hm hq
    (fun _ _ hse hm' => hne1 (hse.aliceBase_eq.symm.trans hm'.1))
    (fun _ _ hse hq' => hne2 (hse.aliceBase_eq.symm.trans hq'.1))
    heval

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuard6
