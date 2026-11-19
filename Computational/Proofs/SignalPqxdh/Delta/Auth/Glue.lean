/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.AuthDefs
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c5 -- proof-setup: allow-public-import
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game

/-!
# PQXDH δ Authentication: `G3 → G3.5` Cutoff Glue

Proves `authCutoffGlue : AuthCutoffGlueStmt S` (DEV-PQ21), combining the `.recvOPK` and
`.recvNoOPK` step couplings with monotonicity of `hasBadAuthKemCorr` to bound the `G3 → G3.5`
cutoff under `badSendδ`.
-/

public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

theorem relProbUpToBad_weaken_badSendδ {S : Setup} (P : Primitives) (maxRo : ℕ)
    {R : AuthResponse × AuthSendLatchedState S → AuthResponse × AuthSendLatchedState S → Prop}
    {m35 m3 : ProbComp (AuthResponse × AuthSendLatchedState S)}
    (h : RelProbUpToBad R
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg || y3.2.respEkCollLatched) m35 m3) :
    RelProbUpToBad R (fun y3 => badSendδ P maxRo y3.2) m35 m3 :=
  RelProbUpToBad.mono h (fun _ _ hR _ => hR) (fun y3 hb => by
    unfold badSendδ; rw [hb, Bool.true_or])

theorem fgAuthStepCoupling_sendLatched_winGuardedδ
    (S : Setup) (hOPK : AuthRecvOPKδStmt S) (hNoOPK : AuthRecvNoOPKδStmt S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (s35 s3 : AuthSendLatchedState S)
    (hInv : AuthSendWinGuardedCoupledInv P s35 s3)
    (_hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hAbF : isAuthG3Abort P s3.hyb = false)
    (hWonF : s3.hyb.base.hasWonAuth = false)
    (hbF : badSendδ P maxRo s3 = false)
    (hRoStep : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecvStep : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot) :
    RelProbUpToBad
      (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badSendδ P maxRo y3.2)
      ((pqxdhAuthSendLatchedStageImpl .g3_5 S P q).run s35)
      ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s3) := by
  have hFull : AuthFullG3G3_5CoupledInv P s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState :=
    authFullG3G3_5CoupledInv_of_winGuarded_not_won P hInv.1 hWonF
  have hbF' : (badAuthFgAnyLatchedMono P maxRo s3.toFg || s3.respEkCollLatched) = false :=
    (Bool.or_eq_false_iff.mp hbF).1
  cases q with
  | initPrin u =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.initPrin u) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_initPrin S P maxRo u _ _ hFull.1)))
  | corruptIK u =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.corruptIK u) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_corruptIK S P maxRo u _ _ hFull.1)))
  | genSPK u j =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.genSPK u j) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_genSPK S P maxRo u j _ _ hFull.1)))
  | genOPK u j o =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.genOPK u j o) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_genOPK S P maxRo u j o _ _ hFull.1)))
  | registerKey sk =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.registerKey sk) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_registerKey S P maxRo sk _ _ hFull.1)))
  | roRootQuery rk dh =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo (.roRootQuery rk dh) rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_roRootQuery S P maxRo rk dh _ _ hFull.1)))
  | revealDhSecrets =>
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_nonRo_full P maxRo .revealDhSecrets rfl _ _ hFull
        (fgAuthStepCoupling_cutoff_latched_revealDhSecrets S P maxRo _ _ hFull.1)))
  | roQuery secrets =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_liftSendLatched_full P maxRo hInv.2
      (fgAuthStepCoupling_cutoff_latched_roQuery_full S P hP maxRo secrets _ _
        hFull hAbF hRoStep))
  | sendOPK u i bundle m0 m1 =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_wrapSendLatched_full P maxRo hFull
      hInv.2
      (fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl_full S P hP maxRo u i
        bundle m0 m1 _ _ hFull hAbF hRoStep (by unfold Setup.N_sess_tot; omega)))
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact relProbUpToBad_weaken_badSendδ P maxRo (relProbUpToBad_wrapSendLatched_full P maxRo hFull
      hInv.2
      (fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl_full S P hP maxRo u i
        bundle m0 m1 _ _ hFull hAbF hRoStep (by unfold Setup.N_sess_tot; omega)))
  | recvOPK k j o msg =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact hOPK P hP maxRo k j o msg s35 s3 hInv hAbF hWonF hbF hRoStep
      (by unfold Setup.N_sess_tot; omega)
  | recvNoOPK k j l msg =>
    dsimp only [authRoStepInc, authRecvStepInc, Nat.add_zero] at hRoStep hRecvStep
    exact hNoOPK P hP maxRo k j l msg s35 s3 hInv hAbF hWonF hbF hRoStep
      (by unfold Setup.N_sess_tot; omega)

theorem badSendδ_mono (S : Setup) (hMono : AuthCorrMonoStmt S) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (q : AuthQuery S) (s3 : AuthSendLatchedState S)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hRo : s3.adv.advRoLog.length + authRoStepInc q ≤ maxRo)
    (hRecv : s3.adv.respRecs.length + authRecvStepInc q ≤ S.N_recv_tot)
    (hBad : badSendδ P maxRo s3 = true) :
    ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s3),
      badSendδ P maxRo y.2 = true := by
  intro y hy
  unfold badSendδ at hBad ⊢
  rcases Bool.or_eq_true_iff.mp hBad with h1 | h2
  · rw [badFg_or_respEkCollLatched_mono_pqxdhAuthSendLatchedStageImpl
      .g3 P maxRo S.N_recv_tot (badAuthFgAnyLatchedMono P maxRo)
      (badAuthFgAnyLatchedMono_mono_advLatched_g3 P hP maxRo) q s3 hRunInv hRo hRecv h1 y hy,
      Bool.true_or]
  · rw [hMono P q s3 h2 y hy, Bool.or_true]

end Proofs.SignalPqxdh.Security.PqxdhDelta
