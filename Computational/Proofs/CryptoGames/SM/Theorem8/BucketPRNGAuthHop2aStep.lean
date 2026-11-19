/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aBase -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import VCVio.OracleComp.EvalDist.Measure

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aStep

public section

set_option autoImplicit false

open scoped ENNReal
open OracleComp OracleSpec
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.SM
  (Config GameState Pos Record RecvResult
   authLosingConditionsAvoided healedBy lastLeakGuessAdmissible ltOpt spec)
open _root_.CryptoGames.SM.Engine
  (VP Ctx HM EState EM Hooks commitE abortE liftH vSend vRecv deliverE injectE)
open _root_.CryptoGames.SM.Construction
  (Header PartyState healEpoch realParty mkParties sampleT
   SchemeAdversary CKAState hooksCKA initCKA Mode liftC cacheC)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
  (postLeak hooksCKABucket bucketAuthCfg CKABucketEState implCKABucket runCKAAuthBucket redCKAAuthBucket
   PRNGBucketAuthState resolveCorrRoot liftPBucketAuth lookupPRNGBucketAuthF
   rootPRNGBucketAuthHybrid hooksPRNGBucketAuthHybrid initPRNGBucketAuthHybrid PRNGBucketAuthEState
   isHonestHdrPRNGBucket hooksPRNGBucketAuthMain hooksPRNGBucketAuthForgedHdr
   implPRNGBucketAuthGen implPRNGBucketAuth runPRNGAuthBucketHybridGen runPRNGAuthBucketHybrid
   redPRNGAuthBucketHybridMain redPRNGAuthBucketHybridForgedHdr redPRNGAuthBucketHybrid)

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aBase
  (twoLayer_dead_eq_false twoLayer_sync_le healEpoch_none_eq healEpoch_some_eq ltOpt_none_eq ltOpt_some_eq
   leak_tL_eq maxOpt_none_eq maxOpt_some_eq afterCorr_epoch_eq mo0 mo0_auth
   mo0_tL mo0_tStar mo0_tH knownRoot_mo0 hooksCKABucket_fsSend hooksCKABucket_fsRecv
   hooksCKABucket_commit hooksPRNGBucketAuthHybrid_fsSend hooksPRNGBucketAuthHybrid_fsRecv hooksPRNGBucketAuthHybrid_commit projP projP_g
   projP_abort Sync2a deadStep_2a step_pure_2a step_abort_2a postLeak_leak_false_of_lt_tH
   postLeak_afterCorr_false_of_lt_tH epoch_accept_le_qep max_epoch_le_accept step_corr_2a step_deliver_2a unsplitRedPRNGAuthBucketHybrid
   initES_PBucket)

section Hop2aProof

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open _root_.CryptoGames.SM.Construction.AuthL10
  (Sync cImpl pImpl knownRoot localCKA localCKA_mono
   evalDist_bind_false_of_support
   eraseSt_win eraseSt_epoch eraseSt_idx eraseSt_inTransit eraseSt_safeInj
   eraseSt_trivial eraseSt_corrAllowed eraseSt_chall eraseSt_tL eraseSt_authOK
   estate_mk_abort_false trivial_false_of_safeInj
   healedBy_leak_false comp_inv_record comp_inv_accept comp_inv_afterCorr
   party_eq_or_eq_other party_cases_of_epoch epoch_eq_of_synced
   senderOf_other receiverOf_other sendsIn_other
   inTransit_some_props sendsIn_of_succ_false sendsIn_pred_false
   accept_epoch_of_le accept_epoch_of_succ max_epoch_update_succ
   epMgmtNew epMgmt_eq_epMgmtNew eraseSt_epMgmtNew epMgmtNew_st epMgmtNew_epoch
   simulateQ_sampleT_cImpl simulateQ_sampleT_pImpl simulateQ_sampleT_run
   initES_C initES_P initSP initSP_zero sync_init_none_zero)


attribute [local simp] healEpoch_none_eq healEpoch_some_eq ltOpt_none_eq ltOpt_some_eq leak_tL_eq maxOpt_none_eq maxOpt_some_eq afterCorr_epoch_eq mo0_auth mo0_tL mo0_tStar mo0_tH hooksCKABucket_fsSend hooksCKABucket_fsRecv hooksCKABucket_commit hooksPRNGBucketAuthHybrid_fsSend hooksPRNGBucketAuthHybrid_fsRecv hooksPRNGBucketAuthHybrid_commit projP_g projP_abort

set_option maxHeartbeats 800000 in
private theorem step_inject_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    (contL : Option (RecvResult M) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (RecvResult M) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hDead : ∀ u esCw' sc', esCw'.1.abort = true →
      𝒟[contL u esCw' sc'] = 𝒟[(pure false : ProbComp Bool)])
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) (.inr (.inl (.inr (P, c))))).run esCw)).run sc >>=
        fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inr (P, c))))).run esPw)).run sp >>=
        fun r => contR r.1.1 r.1.2 r.2] {true} := by
  rcases esCw with ⟨esC, winEpC⟩
  rcases esPw with ⟨esP, winEpP⟩
  have hwinEp : winEpP = winEpC := hS.winEp_eq
  subst winEpP
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  have hg_eq : _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esP.g =
      _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esC.g := hsync.g_eq
  have hidC : (esC.g.st P).id = P := hsync.id_C P
  have hidP : (esP.g.st P).id = P := hsync.id_P P
  have htcurC : (esC.g.st P).tcur = esC.g.epoch P := hsync.tcur_C P
  have htcurP : (esP.g.st P).tcur = esC.g.epoch P := hsync.tcur_P P
  have hvRP_fn : (esP.g.st P).vR = (esC.g.st P).vR := hsync.vR_eq P
  have hqepP : esC.g.epoch P ≤ qep := hS.epoch_le_qep P
  have hγC_eq : (esC.g.st P).γ =
      if localCKA (mo0 tL) Δcka (esC.g.epoch P) then some (esP.g.st P).γ else none :=
    hsync.γ_C P
  have habC : esC.abort = false := hsync.abort_C
  have habP : esP.abort = false := hsync.abort_P
  have hwin : esP.g.win = esC.g.win := eraseSt_win hg_eq
  have htrans : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hg_eq P.other c
  have hsafe : esP.g.safeInj (2 + Δcka) = esC.g.safeInj (2 + Δcka) :=
    eraseSt_safeInj hg_eq (2 + Δcka)
  have hesC_eq : ({ g := esC.g, h := esC.h, abort := false } :
      EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) = esC :=
    estate_mk_abort_false habC
  have hesP_eq : ({ g := esP.g, h := esP.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) = esP := by
    rcases esP with ⟨g, h, ab⟩; dsimp only at habP; subst ab; rfl
  by_cases hguard : esC.g.win || (esC.g.inTransit P.other c).isSome || !esC.g.safeInj (2 + Δcka)
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    exact step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, injectE, habC, hguard,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, habP, hwin, htrans, hsafe, hguard,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (ih none _ _ _ _ hS)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨⟨hwin0, htrans0⟩, hsafe0⟩
    by_cases hsend : P.sendsIn c.1.1 || decide (esC.g.epoch P + 1 < c.1.1)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hsend
      exact step_pure_2a
        (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0, hsafe0,
          hidC, htcurC, hsend, StateT.lift, StateT.run_bind,
          StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          map_eq_bind_pure_comp, hesC_eq])
        (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans, hsafe,
          hwin0, htrans0, hsafe0, hidP, htcurP, hsend, StateT.lift,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind,
          simulateQ_pure, map_eq_bind_pure_comp, hesP_eq])
        (ih (some .rejected) _ _ _ _ hS)
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsend
      rcases hsend with ⟨hsend0, hle⟩
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        have htriv_false : ∀ i', esC.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false :=
          fun i' => trivial_false_of_safeInj esC.g (2 + Δcka) P i' hsafe0 hsync.comp_inv
        have htrivP_false : ∀ i', esP.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := by
          intro i'
          rw [eraseSt_trivial hg_eq]
          exact htriv_false i'
        cases hTn : c.1.2 with
        | none =>
          exact step_pure_2a
            (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0, hsafe0,
              hidC, htcurC, hsend0', hnew, hTn, StateT.lift, StateT.run_bind,
              StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
              map_eq_bind_pure_comp, hesC_eq])
            (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
              hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0', hnew, hTn,
              StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesP_eq])
            (ih (some .rejected) _ _ _ _ hS)
        | some Tn =>
          have hqep_ok : ¬ (qep + 1 < esC.g.epoch P + 1) := by omega
          have hafter : ∀ (γC' : Option Γ) (σC' : Sig) (γP' : Γ) (σP' : Option Sig) (rs : RS)
              (hsC : ((hooksCKABucket cka prng fs Δcka tL).startRecv esC.g P (esC.g.epoch P + 1)
                (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                pure (some (some (γC', σC', rs)), esC.h))
              (hsP : (simulateQ (pImpl prng)
                (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                  esP.g P (esC.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h)).run sp =
                pure ((some (some (γP', σP', rs)), esP.h), sp)),
              𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
                  (((implCKABucket cka prng fs Δcka qep tL) (.inr (.inl (.inr (P, c))))).run
                    (esC, winEpC))).run sc >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤
                𝒟[(simulateQ (pImpl prng)
                  (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
                    (.inr (.inl (.inr (P, c))))).run (esP, winEpC))).run sp >>=
                  fun r => contR r.1.1 r.1.2 r.2] {true} := by
            intro γC' σC' γP' σP' rs hsC hsP
            rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨v', i', m'⟩
            · exact step_pure_2a
                (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0,
                  hsafe0, hidC, htcurC, hsend0', hnew, hTn, hsC, hfs,
                  StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
                (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
                  hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0',
                  hnew, hTn, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
                  simulateQ_bind, hsP, hfs, StateT.run_pure, simulateQ_pure,
                  map_eq_bind_pure_comp, hesP_eq])
                (ih (some .rejected) _ _ _ _ hS)
            · have htrivC := htriv_false i'
              have htrivP := htrivP_false i'
              by_cases hinj : lastLeakGuessAdmissible (2 + Δcka) tL (esC.g.epoch P + 1)
              · refine step_pure_2a
                  (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, bucketAuthCfg,
                    habC, hwin0, htrans0, hsafe0, hidC, htcurC, hsend0',
                    hnew, hTn, hsC, hfs, hqep_ok, htrivC, hinj, StateT.lift, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, StateT.run_modify,
                    simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
                  (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, bucketAuthCfg,
                    habP, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidP,
                    htcurP, hsend0', hnew, hTn, StateT.lift, StateT.run_bind,
                    StateT.run_get, StateT.run_set, simulateQ_bind, hsP, hfs, hqep_ok, htrivP,
                    hinj, StateT.run_pure, StateT.run_modify, simulateQ_pure,
                    map_eq_bind_pure_comp])
                  (ih (some .rejected)
                    ({ esC with g := { esC.g with win := true } }, some (esC.g.epoch P + 1)) sc
                    ({ esP with g := { esP.g with win := true } }, some (esC.g.epoch P + 1)) sp
                    ⟨?_, rfl, fun Q => hS.epoch_le_qep Q, fun hlt => hS.pre_tH hlt⟩)
                have hsync' := hsync.set_win_prf true sp.prf (Or.inl rfl)
                have hsp_id : ({ sp with prf := sp.prf } : PRFPRNG.GameState Sig I K) = sp := by
                  cases sp; rfl
                rw [hsp_id] at hsync'
                exact hsync'
              · simp only [Bool.not_eq_true] at hinj
                exact step_pure_2a
                  (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, bucketAuthCfg,
                    habC, hwin0, htrans0, hsafe0, hidC, htcurC, hsend0',
                    hnew, hTn, hsC, hfs, hqep_ok, htrivC, hinj, StateT.lift, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind,
                    simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
                  (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, bucketAuthCfg,
                    habP, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidP,
                    htcurP, hsend0', hnew, hTn, StateT.lift, StateT.run_bind,
                    StateT.run_get, StateT.run_set, simulateQ_bind, hsP, hfs, hqep_ok, htrivP,
                    hinj, StateT.run_pure, simulateQ_pure, map_eq_bind_pure_comp, hesP_eq])
                  (ih (some .rejected) _ _ _ _ hS)
          have hnone :
              (∀ Im, esC.h.cache (esC.g.epoch P + 1) ≠ some (Tn, Im)) →
              (∀ σc k, esP.h.cache (esC.g.epoch P + 1) ≠ some (Tn, σc, k)) →
              𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
                  (((implCKABucket cka prng fs Δcka qep tL) (.inr (.inl (.inr (P, c))))).run
                    (esC, winEpC))).run sc >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤
                𝒟[(simulateQ (pImpl prng)
                  (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
                    (.inr (.inl (.inr (P, c))))).run (esP, winEpC))).run sp >>=
                  fun r => contR r.1.1 r.1.2 r.2] {true} := by
            intro hcC_none hcP_none
            have hsC_un : ((hooksCKABucket cka prng fs Δcka tL).startRecv esC.g P
                (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                (if lastLeakGuessAdmissible (2 + Δcka) tL (esC.g.epoch P + 1) then
                  match (esC.g.st P).γ with
                  | some γ =>
                    let k := cka.receive γ Tn
                    let p := prng.up (esC.g.st P).root k.2
                    pure (some (some (some k.1, p.1, fs.initReceiver p.2)), esC.h)
                  | none => pure (none, esC.h)
                else pure (some none, esC.h)) := by
              rcases hcache : esC.h.cache (esC.g.epoch P + 1) with _ | ⟨Tc, Ik⟩
              · simp only [hooksCKABucket, hcache, StateT.run_bind, StateT.run_get, pure_bind]
                split
                · cases (esC.g.st P).γ <;> rfl
                · rfl
              · have hne : Tc ≠ Tn := fun heq => hcC_none Ik (by rw [← heq, hcache])
                simp only [hooksCKABucket, hcache, hne, ↓reduceIte, StateT.run_bind,
                  StateT.run_get, pure_bind]
                split
                · cases (esC.g.st P).γ <;> rfl
                · rfl
            by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL (esC.g.epoch P + 1)
            · by_cases hloc : localCKA (mo0 tL) Δcka (esC.g.epoch P)
              · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
                  rw [hγC_eq, hloc]; rfl
                have htH_lt : healEpoch tL < esC.g.epoch P + 1 := by
                  simp only [localCKA, mo0_tL, mo0_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
                  rcases hloc with hnone | hge
                  · cases tL <;> simp [healEpoch] at hnone ⊢
                  · omega
                have hnot_eq_tH : esC.g.epoch P + 1 ≠ healEpoch tL := by omega
                have hrootP : (esP.g.st P).root = some (esC.g.st P).root := hS.root_P_eq P
                have hcond1 : (!(decide (qep + 1 < esC.g.epoch P + 1)) &&
                    lastLeakGuessAdmissible (2 + Δcka) tL (esC.g.epoch P + 1)) = true := by
                  simp [hqep_ok, hvg]
                have hcond2 : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
                  simp [hnot_eq_tH]
                have hcond3 : (postLeak tL esP.g || esP.h.corrRoot.isSome ||
                    decide (healEpoch tL < esC.g.epoch P + 1)) = true := by
                  simp [htH_lt]
                let kk := cka.receive (esP.g.st P).γ Tn
                let p := prng.up (esC.g.st P).root kk.2
                refine hafter (some kk.1) p.1 kk.1 (some p.1) (fs.initReceiver p.2) ?_ ?_
                · rw [hsC_un]; simp [hvg, hγC, kk, p]
                · rcases hcacheP : esP.h.cache (esC.g.epoch P + 1) with _ | ⟨Tc, σc, kVal⟩
                  · dsimp only [hooksPRNGBucketAuthHybrid]
                    simp [resolveCorrRoot, hcacheP, hqep_ok, hvg, hnot_eq_tH, htH_lt, hrootP, kk, p,
                      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure]
                  · have hne : Tc ≠ Tn := fun heq => hcP_none σc kVal (by rw [← heq, hcacheP])
                    dsimp only [hooksPRNGBucketAuthHybrid]
                    simp [resolveCorrRoot, hcacheP, hne, hqep_ok, hvg, hnot_eq_tH, htH_lt, hrootP, kk, p,
                      StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure]
              · simp only [Bool.not_eq_true] at hloc
                have hγC : (esC.g.st P).γ = none := by
                  rw [hγC_eq, hloc]; rfl
                have hsC_abort : ((hooksCKABucket cka prng fs Δcka tL).startRecv esC.g P
                    (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                    pure (none, esC.h) := by
                  rw [hsC_un]; simp [hvg, hγC]
                exact step_abort_2a hDead
                  (by simp [-Prod.mk.injEq, implCKABucket, injectE, abortE, vRecv, habC, hwin0,
                    htrans0, hsafe0, hidC, htcurC, hsend0', hnew, hTn,
                    hsC_abort, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
                    StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure,
                    map_eq_bind_pure_comp]; rfl)
                  rfl
            · simp only [Bool.not_eq_true] at hvg
              have hsC_rej : ((hooksCKABucket cka prng fs Δcka tL).startRecv esC.g P
                  (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                  pure (some none, esC.h) := by
                rw [hsC_un]; simp [hvg]
              have hsP_rej : (simulateQ (pImpl prng)
                  (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                    esP.g P (esC.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h)).run sp =
                  pure ((some none, esP.h), sp) := by
                have h0 : ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                    esP.g P (esC.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h =
                    pure (some none, esP.h) := by
                  rcases hcacheP : esP.h.cache (esC.g.epoch P + 1) with _ | ⟨Tc, σc, kVal⟩
                  · dsimp only [hooksPRNGBucketAuthHybrid]
                    simp [hcacheP, hvg, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
                  · have hne : Tc ≠ Tn := fun heq => hcP_none σc kVal (by rw [← heq, hcacheP])
                    dsimp only [hooksPRNGBucketAuthHybrid]
                    simp [hcacheP, hne, hvg, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
                rw [h0, simulateQ_pure, StateT.run_pure]
              exact step_pure_2a
                (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0,
                  hsafe0, hidC, htcurC, hsend0', hnew, hTn, hsC_rej,
                  StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
                (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
                  hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0',
                  hnew, hTn, hsP_rej, StateT.lift, StateT.run_bind, StateT.run_get,
                  StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                  map_eq_bind_pure_comp, hesP_eq])
                (ih (some .rejected) _ _ _ _ hS)
          rcases hsync.cache_at_succ P c.1.1 hnew with ⟨hcC, hcP⟩ | ⟨Tm, Im, hcC, hcP⟩
          · dsimp only [projP] at hcP
            rw [hnew] at hcC hcP
            exact hnone (by simp [hcC]) (by simp [hcP])
          · dsimp only [projP] at hcP
            rw [hnew] at hcC hcP
            by_cases hTm : Tm = Tn
            · subst Tn
              let p := prng.up (esC.g.st P).root Im
              have hrootS : (esP.g.st (Party.senderOf (esC.g.epoch P + 1))).root =
                  some (esC.g.st (Party.senderOf (esC.g.epoch P + 1))).root :=
                hS.root_P_eq (Party.senderOf (esC.g.epoch P + 1))
              refine hafter ((esC.g.st P).γ.map fun γ => (cka.receive γ Tm).1) p.1
                (cka.receive (esP.g.st P).γ Tm).1
                (esP.g.st (Party.senderOf (esC.g.epoch P + 1))).root
                (fs.initReceiver p.2) ?_ ?_
              · dsimp only [hooksCKABucket]
                simp [hcC, p, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
              · dsimp only [hooksPRNGBucketAuthHybrid]
                simp [resolveCorrRoot, hcP, hrootS, p,
                  StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure]
            · exact hnone (by simp [hcC, hTm]) (by simp [hcP, hTm])
      · have hle_ep : c.1.1 ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := congrFun hvRP_fn c.1.1
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          exact step_pure_2a
            (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0, hsafe0,
              hidC, htcurC, hsend0, hle, hnew, hvR, StateT.lift,
              StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind,
              simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
            (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
              hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0, hle,
              hnew, hvRP, hvR, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesP_eq])
            (ih (some .rejected) _ _ _ _ hS)
        | some v =>
          rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · exact step_pure_2a
              (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0,
                hsafe0, hidC, htcurC, hsend0, hle, hnew, hvR, hfs,
                StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
              (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
                hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0, hle,
                hnew, hvRP, hvR, hfs, StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                map_eq_bind_pure_comp, hesP_eq])
              (ih (some .rejected) _ _ _ _ hS)
          · by_cases hqep : qep + 1 < c.1.1
            · exact step_pure_2a
                (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, habC, hwin0, htrans0,
                  hsafe0, hidC, htcurC, hsend0, hle, hnew, hvR, hfs, hqep,
                  StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                  simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
                (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, habP, hwin, htrans,
                  hsafe, hwin0, htrans0, hsafe0, hidP, htcurP, hsend0, hle,
                  hnew, hvRP, hvR, hfs, hqep, StateT.lift, StateT.run_bind, StateT.run_get,
                  StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                  map_eq_bind_pure_comp, hesP_eq])
                (ih (some .rejected) _ _ _ _ hS)
            · let pos : Pos := ⟨P.other, c.1.1, i'⟩
              have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                eraseSt_trivial hg_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
                have hvR'_eq : Function.update (esP.g.st P).vR c.1.1 (some v') = vR' := by
                  simp [vR', hvRP_fn]
                have hpos_qep : pos.epoch ≤ qep := le_trans hle_ep hqepP
                have hwinC_acc : ∀ st', (esC.g.accept P st' pos).win = false := fun _ => hwin0
                have hwinP_acc : ∀ st', (esP.g.accept P st' pos).win = false :=
                  fun _ => hwin.trans hwin0
                let esCw' : CKABucketEState Γ T Sig SS RS M E I :=
                  ({ esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }, winEpC)
                let esPw' : PRNGBucketAuthEState Γ T Sig SS RS M E K I :=
                  ({ esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }, winEpC)
                have hS' : Sync2a prng Δcka qep tL esCw' sc esPw' sp :=
                  ⟨hsync.accept_old P vR' pos hle_ep, rfl,
                    epoch_accept_le_qep hS.epoch_le_qep P _ pos hpos_qep, fun hlt =>
                      hS.pre_tH (lt_of_le_of_lt (max_epoch_le_accept esC.g P _ pos) hlt)⟩
                exact step_pure_2a
                  (by simp [-Prod.mk.injEq, esCw', implCKABucket, injectE, vRecv, commitE,
                    hooksCKA, habC, hwin0, hwinC_acc, htrans0, hsafe0, hidC, htcurC,
                    hsend0, hle, hnew, hvR, hfs, hqep, htriv, pos, vR', StateT.lift,
                    StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                    StateT.run_modify, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
                  (by simp [-Prod.mk.injEq, esPw', implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, commitE,
                    hooksPRNGBucketAuthHybrid_commit,
                    habP, hwin, hwinP_acc, htrans, hsafe, hwin0, htrans0, hsafe0,
                    hidP, htcurP, hsend0, hle, hnew, hvRP, hvR, hfs, hqep,
                    htriv_eq, htriv, pos, hvR'_eq, StateT.lift, StateT.run_bind, StateT.run_get,
                    StateT.run_set, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                    simulateQ_pure, map_eq_bind_pure_comp])
                  (ih (some (.accepted c.1.1 i' (some m'))) esCw' sc esPw' sp hS')
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1
                · refine step_pure_2a
                    (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, bucketAuthCfg,
                      habC, hwin0, htrans0, hsafe0, hidC, htcurC, hsend0,
                      hle, hnew, hvR, hfs, hqep, htriv, hinj, pos, StateT.lift, StateT.run_bind,
                      StateT.run_get, StateT.run_set, StateT.run_pure, StateT.run_modify,
                      simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
                    (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, bucketAuthCfg,
                      habP, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidP,
                      htcurP, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, htriv_eq,
                      htriv, hinj, pos, StateT.lift, StateT.run_bind, StateT.run_get,
                      StateT.run_set, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                      simulateQ_pure, map_eq_bind_pure_comp])
                    (ih (some .rejected)
                      ({ esC with g := { esC.g with win := true } }, some c.1.1) sc
                      ({ esP with g := { esP.g with win := true } }, some c.1.1) sp
                      ⟨?_, rfl, fun Q => hS.epoch_le_qep Q, fun hlt => hS.pre_tH hlt⟩)
                  have hsync' := hsync.set_win_prf true sp.prf (Or.inl rfl)
                  have hsp_id : ({ sp with prf := sp.prf } : PRFPRNG.GameState Sig I K) = sp := by
                    cases sp; rfl
                  rw [hsp_id] at hsync'
                  exact hsync'
                · simp only [Bool.not_eq_true] at hinj
                  exact step_pure_2a
                    (by simp [-Prod.mk.injEq, implCKABucket, injectE, vRecv, bucketAuthCfg,
                      habC, hwin0, htrans0, hsafe0, hidC, htcurC, hsend0,
                      hle, hnew, hvR, hfs, hqep, htriv, hinj, pos, StateT.lift, StateT.run_bind,
                      StateT.run_get, StateT.run_set, StateT.run_pure, simulateQ_bind,
                      simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
                    (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, injectE, vRecv, bucketAuthCfg,
                      habP, hwin, htrans, hsafe, hwin0, htrans0, hsafe0, hidP,
                      htcurP, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, htriv_eq,
                      htriv, hinj, pos, StateT.lift, StateT.run_bind, StateT.run_get,
                      StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                      map_eq_bind_pure_comp, hesP_eq])
                    (ih (some .rejected) _ _ _ _ hS)

private theorem ltOpt_mono_right {tL : Option ℕ} {a b : ℕ} (hab : a ≤ b)
    (h : ltOpt tL a = true) : ltOpt tL b = true := by
  cases tL with
  | none => rfl
  | some l =>
    simp only [ltOpt, decide_eq_true_eq] at h ⊢
    omega

private theorem postLeak_leak_of_true {St Msg C : Type} {tL : Option ℕ}
    {s : GameState St Msg C} (l : ℕ) (h : postLeak tL s = true) :
    postLeak tL (s.leak l) = true := by
  cases htL : s.tL with
  | none => simp [postLeak, htL] at h
  | some cur =>
    simp only [postLeak, htL] at h
    simp only [postLeak, GameState.leak, htL, _root_.CryptoGames.SM.maxOpt]
    exact ltOpt_mono_right (Nat.le_max_left cur l) h

@[local simp] private theorem postLeak_record {St Msg C : Type} (tL : Option ℕ)
    (s : GameState St Msg C) (Δ : ℕ) (P : Party) (st' : St) (r : Record Msg C) (ic : Bool) :
    postLeak tL (s.record Δ P st' r ic) = postLeak tL s := rfl

@[local simp] private theorem postLeak_accept {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (tL : Option ℕ) (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    postLeak tL (s.accept P st' pos) = postLeak tL s := rfl

private theorem postLeak_afterCorr_of_true {St Msg C : Type} {tL : Option ℕ}
    {s : GameState St Msg C} (P : Party) (h : postLeak tL s = true) :
    postLeak tL (s.afterCorr P) = true := by
  unfold GameState.afterCorr
  exact postLeak_leak_of_true _ h

private theorem postLeak_epMgmt_of_true {St Msg C : Type} {tL : Option ℕ}
    {s s₁ : GameState St Msg C} {Δ qep : ℕ} {P : Party} {bad : Bool}
    (h : postLeak tL s = true) (hep : s.epMgmt Δ qep P bad = some s₁) :
    postLeak tL s₁ = true := by
  unfold GameState.epMgmt at hep
  split_ifs at hep with h1 h2 h3
  · injection hep with hep; subst hep
    exact postLeak_leak_of_true _ h
  · injection hep with hep; subst hep; exact h
  · injection hep with hep; subst hep; exact h

private theorem postLeak_epMgmtNew_false {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (Δ : ℕ) (P : Party) (bad : Bool)
    (hpl : postLeak tL g = false)
    (hbad : bad = false ∨ g.epoch P + 1 + 2 ≤ healEpoch tL) :
    postLeak tL (epMgmtNew g Δ P bad) = false := by
  rcases hbad with rfl | hle
  · simp [epMgmtNew, postLeak] at hpl ⊢; exact hpl
  · dsimp only [epMgmtNew]
    split_ifs with hcond
    · exact postLeak_leak_false_of_lt_tH hpl (by omega)
    · exact hpl

private theorem step_transmit_same_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hwin0 : esCw.1.g.win = false)
    (hsend : P.sendsIn (esCw.1.g.epoch P + 1) = false)
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL)
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esCw)).run sc >>=
        fun res => contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esPw)).run sp >>=
        fun res => contR res.1.1 res.1.2 res.2] {true} := by
  rcases esCw with ⟨esC, winEpC⟩
  rcases esPw with ⟨esP, winEpP⟩
  have hwinEp : winEpP = winEpC := hS.winEp_eq
  subst winEpP
  dsimp only at hwin0 hsend
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  have hg_eq : _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esP.g =
      _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esC.g := hsync.g_eq
  have hwin : esP.g.win = esC.g.win := eraseSt_win hg_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hg_eq) P
  have hidxP : esP.g.idx P = esC.g.idx P := congrFun (eraseSt_idx hg_eq) P
  have habC : esC.abort = false := hsync.abort_C
  have habP : esP.abort = false := hsync.abort_P
  have hidC : (esC.g.st P).id = P := hsync.id_C P
  have hidP : (esP.g.st P).id = P := hsync.id_P P
  have htcurC : (esC.g.st P).tcur = esC.g.epoch P := hsync.tcur_C P
  have htcurP : (esP.g.st P).tcur = esP.g.epoch P := (hsync.tcur_P P).trans hepP.symm
  have hvSP : (esP.g.st P).vS = (esC.g.st P).vS := hsync.vS_eq P
  have hTcurP : (esP.g.st P).curCkaMsg = (esC.g.st P).curCkaMsg := hsync.Tcur_eq P
  have hsend0 : P.sendsIn (esC.g.epoch P) = true := sendsIn_of_succ_false hsend
  have hqep : ¬ (qep < esC.g.epoch P) := Nat.not_lt.mpr (hS.epoch_le_qep P)
  cases hvS : (esC.g.st P).vS with
  | none =>
    have hstC : ({ esC.g.st P with vS := none } : VP (Option Γ) T Sig SS RS) = esC.g.st P := by
      rcases h : esC.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
      rw [h] at hvS; subst hvS; rfl
    have hstP : ({ esP.g.st P with vS := none } : VP Γ T (Option Sig) SS RS) = esP.g.st P := by
      have hvSP0 : (esP.g.st P).vS = none := hvSP.trans hvS
      rcases h : esP.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
      rw [h] at hvSP0; subst hvSP0; rfl
    let c : Header T × E := ((esC.g.epoch P, (esC.g.st P).curCkaMsg), default)
    let rcd : Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
    refine step_pure_2a
      (by rw [hstC]; simp [-Prod.mk.injEq, implCKABucket, vSend, GameState.epMgmt, habC, hwin0,
        hsend, hqep, hidC, htcurC, hvS, c, rcd, StateT.lift, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (by rw [hstP]; simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, vSend, GameState.epMgmt,
        habP, hwin, hwin0, hepP, hidxP, hsend, hqep, hidP, htcurP, hvSP, hvS, hTcurP, c, rcd,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (ih (some c)
        ({ esC with g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := none } rcd false }, winEpC) sc
        ({ esP with g := esP.g.record (2 + Δcka) P { esP.g.st P with vS := none } rcd false }, winEpC) sp
        ⟨?_, rfl, fun Q => hS.epoch_le_qep Q, fun hlt => ?_⟩)
    · simpa [projP, hstC, hstP, c, rcd] using
        hsync.record_same_epoch P none m_msg default hsend0
    · obtain ⟨hpl, hcr⟩ := hS.pre_tH (by simpa [GameState.record] using hlt)
      exact ⟨by rw [postLeak_record]; exact hpl, hcr⟩
  | some v =>
    let h : Header T := (esC.g.epoch P, (esC.g.st P).curCkaMsg)
    let fe := fs.send v h m_msg
    let c : Header T × E := (h, fe.2)
    let rcd : Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
    refine step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, vSend, hooksCKABucket_fsSend, FSAEADScheme.send, GameState.epMgmt,
        habC, hwin0, hsend, hqep, hidC, htcurC, hvS, h, fe, c, rcd,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, vSend,
        hooksPRNGBucketAuthHybrid_fsSend, FSAEADScheme.send, GameState.epMgmt, habP, hwin, hwin0,
        hepP, hidxP, hsend, hqep, hidP, htcurP, hvSP, hvS, hTcurP, h, fe, c, rcd,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (ih (some c)
        ({ esC with g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := some fe.1 } rcd false }, winEpC) sc
        ({ esP with g := esP.g.record (2 + Δcka) P { esP.g.st P with vS := some fe.1 } rcd false }, winEpC) sp
        ⟨?_, rfl, fun Q => hS.epoch_le_qep Q, fun hlt => ?_⟩)
    · exact hsync.record_same_epoch P (some fe.1) m_msg fe.2 hsend0
    · obtain ⟨hpl, hcr⟩ := hS.pre_tH (by simpa [GameState.record] using hlt)
      exact ⟨by rw [postLeak_record]; exact hpl, hcr⟩

private def postSendBucketC
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ)
    (P : Party) (m_msg : M) (bad : Bool)
    (esC : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ)
    (res : Option (Option Γ × T × Sig × SS) × CKAState T I) :
    Option (Header T × E) × CKABucketEState Γ T Sig SS RS M E I :=
  match res.1 with
  | none => (none, ({ esC with h := res.2, abort := true }, winEp))
  | some (γ', Tm, σ', ss) =>
    let m := esC.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gC₁ := epMgmtNew esC.g (2 + Δcka) P bad
    let rcd : Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), ({ esC with g := gC₁.record (2 + Δcka) P stC' rcd false, h := res.2 }, winEp))

private def postSendBucketP
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ)
    (P : Party) (m_msg : M) (bad : Bool)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp : Option ℕ)
    (res : Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) :
    Option (Header T × E) × PRNGBucketAuthEState Γ T Sig SS RS M E K I :=
  match res.1 with
  | none => (none, ({ esP with h := res.2, abort := true }, winEp))
  | some (γ', Tm, σ', ss) =>
    let m := esP.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gP₁ := epMgmtNew esP.g (2 + Δcka) P bad
    let rcd : Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), ({ esP with g := gP₁.record (2 + Δcka) P stP' rcd false, h := res.2 }, winEp))

private theorem stepC_bucket_transmit_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esC : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I))
    (winEp : Option ℕ) (sc : _root_.CryptoGames.CKA.GameState Γ T)
    (hab : esC.abort = false) (hwin : esC.g.win = false)
    (hid : (esC.g.st P).id = P) (htcur : (esC.g.st P).tcur = esC.g.epoch P)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep : ¬ qep < esC.g.epoch P + 1) :
    (simulateQ (cImpl cka Δcka (healEpoch tL))
      (((implCKABucket cka prng fs Δcka qep tL)
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run (esC, winEp))).run sc =
      (simulateQ (cImpl cka Δcka (mo0 tL).tH)
        (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
          (epMgmtNew esC.g (2 + Δcka) P r.isSome)
          P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root r).run esC.h)).run sc >>=
        fun out => pure (postSendBucketC fs Δcka P m_msg r.isSome esC winEp out.1, out.2) := by
  have hep := epMgmt_eq_epMgmtNew esC.g (2 + Δcka) qep P r.isSome hsend hqep
  have hstart : (hooksCKABucket cka prng fs Δcka tL).startSend =
      (hooksCKA cka prng fs Δcka (mo0 tL)).startSend := rfl
  simp only [implCKABucket, QueryImpl.add_apply, hab, hwin, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, hep, vSend, hstart, hooksCKABucket_fsSend, epMgmtNew_st, hid, htcur, hsend,
    mo0_tH, StateT.run_lift, StateT.run_bind, StateT.run_get,
    pure_bind, bind_assoc, simulateQ_bind, map_eq_bind_pure_comp]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sc'⟩
  cases ans with
  | none => simp [postSendBucketC, StateT.run_set, StateT.run_pure, simulateQ_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendBucketC, FSAEADScheme.send, hid, hab, epMgmtNew_st, htcur,
      StateT.run_set, StateT.run_pure, simulateQ_pure]

private theorem stepP_bucket_transmit_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (hab : esP.abort = false) (hwin : esP.g.win = false)
    (hid : (esP.g.st P).id = P) (htcur : (esP.g.st P).tcur = esP.g.epoch P)
    (hsend : P.sendsIn (esP.g.epoch P + 1) = true)
    (hqep : ¬ qep < esP.g.epoch P + 1) :
    (simulateQ (pImpl prng)
      (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run (esP, winEp))).run sp =
      (simulateQ (pImpl prng)
        (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startSend
          (epMgmtNew esP.g (2 + Δcka) P r.isSome)
          P (esP.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root r).run esP.h)).run sp >>=
        fun out => pure (postSendBucketP fs Δcka P m_msg r.isSome esP winEp out.1, out.2) := by
  have hep := epMgmt_eq_epMgmtNew esP.g (2 + Δcka) qep P r.isSome hsend hqep
  simp only [implPRNGBucketAuth, implPRNGBucketAuthGen, QueryImpl.add_apply, hab, hwin,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, hep, vSend, hooksPRNGBucketAuthHybrid_fsSend,
    epMgmtNew_st, hid, htcur, hsend, StateT.run_lift, StateT.run_bind, StateT.run_get,
    pure_bind, bind_assoc, simulateQ_bind, map_eq_bind_pure_comp]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sp'⟩
  cases ans with
  | none => simp [postSendBucketP, StateT.run_set, StateT.run_pure, simulateQ_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendBucketP, FSAEADScheme.send, hid, hab, epMgmtNew_st, htcur,
      StateT.run_set, StateT.run_pure, simulateQ_pure]

private def startSendPBucket_body [DecidableEq I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (tL : Option ℕ) (t m : ℕ) (pl : Bool) (γ : Γ) (σv : Option Sig) (coins : CCoins) :
    HM (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      (Option (Γ × T × Option Sig × SS)) := do
  let c := cka.send γ coins
  match ← rootPRNGBucketAuthHybrid prng tL t m pl c.2.2 σv with
  | none => return none
  | some (σ', kVal) =>
    modify fun s => { s with cache := Function.update s.cache m (some (c.2.1, σ', kVal)) }
    return some (c.1, c.2.1, σ', fs.initSender kVal)

private theorem startSendPBucket_some_eq [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ) (γ : Γ) (σv : Option Sig)
    (coins : CCoins) (h : PRNGBucketAuthState T Sig K I) :
    (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startSend ctx P m γ σv (some coins)).run h) =
      (startSendPBucket_body cka prng fs tL t m (postLeak tL ctx) γ σv coins).run h := rfl

private theorem startSendPBucket_none_eq [DecidableEq T] [DecidableEq I]
    [SampleableType KR] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (m : ℕ) (γ : Γ) (σv : Option Sig)
    (h : PRNGBucketAuthState T Sig K I) (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (pImpl prng)
      (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startSend ctx P m γ σv none).run h)).run sp =
      ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
        (simulateQ (pImpl prng)
          ((startSendPBucket_body cka prng fs tL t m (postLeak tL ctx) γ σv coins).run h)).run sp := by
  change (simulateQ (pImpl prng)
    ((StateT.lift (sampleT CCoins) >>= fun coins =>
      startSendPBucket_body cka prng fs tL t m (postLeak tL ctx) γ σv coins).run h)).run sp = _
  simp [StateT.run_lift, StateT.run_bind, simulateQ_bind, simulateQ_sampleT_pImpl,
    map_eq_bind_pure_comp, bind_assoc]

private theorem ih_postSendBucket_new
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (P : Party) (m_msg : M) (bad : Bool)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {winEp : Option ℕ} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL (esC, winEp) sc (esP, winEp) sp)
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true})
    (γP' : Γ) (Tm : T) (Im : I)
    (sc' : _root_.CryptoGames.CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : localCKA (mo0 tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esC.g.epoch P + 1 < healEpoch tL →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hpre' : esC.g.epoch P + 1 < healEpoch tL →
      postLeak tL (epMgmtNew esC.g (2 + Δcka) P bad) = false ∧ esP.h.corrRoot = none) :
    let m := esC.g.epoch P + 1
    let p := prng.up (esC.g.st P).root Im
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if localCKA (mo0 tL) Δcka m then some γP' else none, Tm, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (Tm, Im)) })
    let resP : Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I :=
      (some (γP', Tm, some p.1, fs.initSender p.2),
        { esP.h with cache := Function.update esP.h.cache m (some (Tm, some p.1, p.2)) })
    let outC := postSendBucketC fs Δcka P m_msg bad esC winEp resC
    let outP := postSendBucketP fs Δcka P m_msg bad esP winEp resP
    𝒟[contL outC.1 outC.2 sc'] {true} ≤ 𝒟[contR outP.1 outP.2 sp'] {true} := by
  intro m p resC resP outC outP
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hsync.g_eq) P
  obtain ⟨hO_ep, _, _⟩ := hsync.ping_pong_synced P hsend
  let fe := fs.send (fs.initSender p.2) (m, some Tm) m_msg
  have hsync' := hsync.record_new_epoch P bad γP' Tm Im fe.1 m_msg fe.2 sc' sp' hsend hb_sc' hb_sp'
    hcka'
    (fun hlt _ => hprng_before (by simpa [mo0_tStar] using hlt))
    (fun hlt hfalse => by
      have hlt' : esC.g.epoch P + 1 < healEpoch tL := by simpa [mo0_tStar] using hlt
      cases tL with
      | none => simp [healEpoch] at hlt'
      | some l => simp [mo0_tL, mo0_tH, healEpoch] at hlt' hfalse; omega)
    (fun heq hfalse => by
      have heq' : esC.g.epoch P + 1 = healEpoch tL := by simpa [mo0_tStar] using heq
      cases tL with
      | none => simp [healEpoch] at heq'
      | some l => simp [mo0_tL, mo0_tStar, mo0_tH] at hfalse)
  have hkr : (if knownRoot (mo0 tL) m then some p.1 else none) = some p.1 := by
    simp [knownRoot_mo0]
  dsimp only [outC, outP, resC, resP, postSendBucketC, postSendBucketP]
  simp only [hepP, m]
  refine ih (some ((m, some Tm), fe.2)) _ sc' _ sp' ⟨?_, rfl, fun Q => ?_, fun hlt => ?_⟩
  · simpa [projP, hkr, m, p, fe] using hsync'
  · dsimp only [GameState.record]
    rw [epMgmtNew_epoch]
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · rw [hQ]; simp [m, hqep_m]
    · rw [hQ]; simp [Party.other_ne, hS.epoch_le_qep P.other]
  · dsimp only [GameState.record] at hlt
    rw [epMgmtNew_epoch, max_epoch_update_succ hO_ep] at hlt
    obtain ⟨hpl', hcr'⟩ := hpre' hlt
    exact ⟨by simpa [postLeak_record] using hpl', hcr'⟩

private theorem startSendPBucket_coins_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (bad : Bool)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {winEp : Option ℕ} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL (esC, winEp) sc (esP, winEp) sp)
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true})
    (coins : CCoins) (sc' : _root_.CryptoGames.CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false)
    (hbad : esC.g.epoch P + 1 < healEpoch tL → bad = false ∨ esC.g.epoch P + 1 + 2 ≤ healEpoch tL)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA (mo0 tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    let p := prng.up (esC.g.st P).root c_cka.2.2
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
    let outC := postSendBucketC fs Δcka P m_msg bad esC winEp resC
    let pl := postLeak tL (epMgmtNew esP.g (2 + Δcka) P bad)
    𝒟[contL outC.1 outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendPBucket_body cka prng fs tL (healEpoch tL) m pl
            (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp >>=
        fun out =>
          let outP := postSendBucketP fs Δcka P m_msg bad esP winEp out.1
          contR outP.1 outP.2 out.2] {true} := by
  intro m c_cka p resC outC pl
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hsync.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  have hrootP0 : (esP.g.st P).root = some (esC.g.st P).root := hS.root_P_eq P
  by_cases hgt : healEpoch tL < m
  · let resP : Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I :=
      (some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
        { esP.h with cache := Function.update esP.h.cache m (some (c_cka.2.1, some p.1, p.2)) })
    have hP : (simulateQ (pImpl prng)
        ((startSendPBucket_body cka prng fs tL (healEpoch tL) m pl
          (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
        pure (resP, sp) := by
      simp only [startSendPBucket_body, rootPRNGBucketAuthHybrid, resolveCorrRoot,
        hgt, ↓reduceIte, hrootP0, c_cka, p, resP, StateT.run_bind, StateT.run_get, StateT.run_pure,
        StateT.run_modify, pure_bind, simulateQ_pure]
    rw [hP, pure_bind]
    exact ih_postSendBucket_new prng fs Δcka qep tL P m_msg bad contL contR hS ih
      c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp hsend hqep_m hb_sc' hsync.b_P hcka'
      (fun h => by omega) (fun h => by omega)
  · have hne_tH : m ≠ healEpoch tL := by
      intro heq
      cases htL : tL with
      | none => rw [htL, healEpoch_none_eq] at heq; omega
      | some l => simp [htL, m, heq] at hnot_tH
    have hlt : m < healEpoch tL := by omega
    have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < healEpoch tL := by omega
    obtain ⟨hpl0, hcr0⟩ := hS.pre_tH hmax_lt
    dsimp only at hpl0 hcr0
    have hplC : postLeak tL (epMgmtNew esC.g (2 + Δcka) P bad) = false :=
      postLeak_epMgmtNew_false (2 + Δcka) P bad hpl0 (hbad hlt)
    have hpl_eq : pl = false := by
      dsimp only [pl]
      have htL_eq : (epMgmtNew esP.g (2 + Δcka) P bad).tL =
          (epMgmtNew esC.g (2 + Δcka) P bad).tL :=
        eraseSt_tL (eraseSt_epMgmtNew hsync.g_eq (2 + Δcka) P bad)
      simpa [postLeak, htL_eq] using hplC
    have htL_some : tL.isSome = true := by
      cases tL with
      | none => simp [healEpoch] at hlt
      | some _ => rfl
    have hlt_tH0 : ((mo0 tL).tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < (mo0 tL).tH)) = true := by
      simp [mo0_tL, mo0_tH, htL_some, hmax_lt]
    obtain ⟨hσ, hcorr, hprng, hprf⟩ := hsync.prng_before_tH (by simpa [mo0] using hmax_lt) hlt_tH0
    rw [hroot_max] at hσ
    let resP : Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I :=
      (some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
        { esP.h with cache := Function.update esP.h.cache m (some (c_cka.2.1, some p.1, p.2)) })
    let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := true }
    have hP : (simulateQ (pImpl prng)
        ((startSendPBucket_body cka prng fs tL (healEpoch tL) m pl
          (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
        pure (resP, sp') := by
      simp [startSendPBucket_body, rootPRNGBucketAuthHybrid, resolveCorrRoot,
        hgt, hne_tH, hlt, hpl_eq, hcr0, hrootP0,
        liftPBucketAuth, PRFPRNG.processQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
        hsync.b_P, hcorr, hprng, hprf, hσ, c_cka, p, resP, sp',
        StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify]
    rw [hP, pure_bind]
    exact ih_postSendBucket_new prng fs Δcka qep tL P m_msg bad contL contR hS ih
      c_cka.1 c_cka.2.1 c_cka.2.2 sc' sp' hsend hqep_m hb_sc' hsync.b_P hcka'
      (fun _ => ⟨rfl, rfl, hprng, hprf⟩) (fun _ => ⟨hplC, hcr0⟩)

private theorem startSendPBucket_chall_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)}
    {esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {winEp : Option ℕ} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL (esC, winEp) sc (esP, winEp) sp)
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true})
    (coins : CCoins) (sc' : _root_.CryptoGames.CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep_m : esC.g.epoch P + 1 ≤ qep)
    (htH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = true)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA (mo0 tL) Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    let pl := postLeak tL (epMgmtNew esP.g (2 + Δcka) P false)
    𝒟[($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esC.g.st P).root I₁
        let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
          (some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) })
        let outC := postSendBucketC fs Δcka P m_msg false esC winEp resC
        contL outC.1 outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendPBucket_body cka prng fs tL (healEpoch tL) m pl
            (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp >>=
        fun out =>
          let outP := postSendBucketP fs Δcka P m_msg false esP winEp out.1
          contR outP.1 outP.2 out.2] {true} := by
  intro m c_cka pl
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hsync.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  obtain ⟨htL_some, hm_tH⟩ : tL.isSome = true ∧ m = healEpoch tL := by
    simpa [m, Bool.and_eq_true, decide_eq_true_eq] using htH
  have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < healEpoch tL := by omega
  obtain ⟨hpl0, hcr0⟩ := hS.pre_tH hmax_lt
  dsimp only at hpl0 hcr0
  have hplC : postLeak tL (epMgmtNew esC.g (2 + Δcka) P false) = false :=
    postLeak_epMgmtNew_false (2 + Δcka) P false hpl0 (Or.inl rfl)
  have hpl_eq : pl = false := by
    dsimp only [pl]
    have htL_eq : (epMgmtNew esP.g (2 + Δcka) P false).tL =
        (epMgmtNew esC.g (2 + Δcka) P false).tL :=
      eraseSt_tL (eraseSt_epMgmtNew hsync.g_eq (2 + Δcka) P false)
    simpa [postLeak, htL_eq] using hplC
  have hlt_tH0 : ((mo0 tL).tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < (mo0 tL).tH)) = true := by
    simp [mo0_tL, mo0_tH, htL_some, hmax_lt]
  obtain ⟨hσ, hcorr, hprng, hprf⟩ := hsync.prng_before_tH (by simpa [mo0] using hmax_lt) hlt_tH0
  rw [hroot_max] at hσ
  have hrootP0 : (esP.g.st P).root = some (esC.g.st P).root := hS.root_P_eq P
  have hgt : ¬ (healEpoch tL < m) := by omega
  have hP : (simulateQ (pImpl prng)
      ((startSendPBucket_body cka prng fs tL (healEpoch tL) m pl
        (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
      ($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esC.g.st P).root I₁
        pure ((some (c_cka.1, c_cka.2.1, some p.1, fs.initSender p.2),
          { esP.h with cache := Function.update esP.h.cache m (some (c_cka.2.1, some p.1, p.2)) }),
          { sp with σ := p.1, corr := true, prng := true }) := by
    simp [startSendPBucket_body, rootPRNGBucketAuthHybrid, resolveCorrRoot,
      hgt, hm_tH, htL_some, hpl_eq, hcr0, hrootP0,
      liftPBucketAuth, PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
      PRFPRNG.challPrngImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec, PRFPRNG.up,
      hcorr, hprng, hprf, hsync.b_P, hσ, c_cka,
      StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
      map_eq_bind_pure_comp, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify, bind_assoc]
  rw [hP, bind_assoc]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun I₁ _ => ?_
  rw [pure_bind]
  exact ih_postSendBucket_new prng fs Δcka qep tL P m_msg false contL contR hS ih
    c_cka.1 c_cka.2.1 I₁ sc'
    { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := true, prng := true }
    hsend hqep_m hb_sc' hsync.b_P hcka' (fun h => by omega) (fun h => by omega)

set_option maxHeartbeats 400000 in
private theorem step_transmit_new_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hDead : ∀ u esCw' sc', esCw'.1.abort = true →
      𝒟[contL u esCw' sc'] = 𝒟[(pure false : ProbComp Bool)])
    (hwin0 : esCw.1.g.win = false)
    (hsend : P.sendsIn (esCw.1.g.epoch P + 1) = true)
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL)
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esCw)).run sc >>=
        fun res => contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esPw)).run sp >>=
        fun res => contR res.1.1 res.1.2 res.2] {true} := by
  rcases esCw with ⟨esC, winEpC⟩
  rcases esPw with ⟨esP, winEpP⟩
  have hwinEp : winEpP = winEpC := hS.winEp_eq
  subst winEpP
  dsimp only at hwin0 hsend
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  have hwin : esP.g.win = esC.g.win := eraseSt_win hsync.g_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hsync.g_eq) P
  by_cases hqep : qep < esC.g.epoch P + 1
  · have hqep_le : qep ≤ esC.g.epoch P := by omega
    exact step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, GameState.epMgmt, hsync.abort_C, hwin0,
        hsend, hqep_le, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, GameState.epMgmt,
        hsync.abort_P, hwin, hwin0, hepP, hsend, hqep_le, StateT.run_bind, StateT.run_get,
        StateT.run_pure, simulateQ_pure])
      (ih none _ _ _ _ hS)
  · have hqep_m : esC.g.epoch P + 1 ≤ qep := Nat.not_lt.mp hqep
    rw [stepC_bucket_transmit_new cka prng fs Δcka qep tL P m_msg r esC winEpC sc
        hsync.abort_C hwin0 (hsync.id_C P) (hsync.tcur_C P) hsend hqep,
      stepP_bucket_transmit_new cka prng fs Δcka qep tL P m_msg r esP winEpC sp
        hsync.abort_P (hwin.trans hwin0) (hsync.id_P P) ((hsync.tcur_P P).trans hepP.symm)
        (by rw [hepP]; exact hsend) (by rw [hepP]; exact hqep),
      bind_assoc, bind_assoc]
    let m := esC.g.epoch P + 1
    by_cases hloc : localCKA (mo0 tL) Δcka (esC.g.epoch P)
    · have hloc_m : localCKA (mo0 tL) Δcka m = true :=
        localCKA_mono (mo0 tL) Δcka hloc (Nat.le_succ _)
      have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
        simp only [localCKA, mo0_tL, mo0_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with h | h
        · cases h' : tL <;> simp_all
        · simp [show esC.g.epoch P + 1 ≠ healEpoch tL by omega]
      have hnot_lt : ¬ (esC.g.epoch P + 1 < healEpoch tL) := by
        simp only [localCKA, mo0_tL, mo0_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with h | h
        · cases tL <;> simp [healEpoch] at h ⊢
        · omega
      have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
        simp [hsync.γ_C P, hloc]
      cases r with
      | some coins =>
        let c_cka := cka.send (esP.g.st P).γ coins
        let p := prng.up (esC.g.st P).root c_cka.2.2
        let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
          (some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
        have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
            (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
              (epMgmtNew esC.g (2 + Δcka) P true)
              P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
            pure (resC, sc) := by
          simp [hooksCKA, cacheC, hγC, hloc_m, m, c_cka, p, resC,
            StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
        simp only [Option.isSome_some]
        rw [hC, pure_bind, pure_bind, hepP, startSendPBucket_some_eq]
        simpa [m, c_cka, p, resC] using
          startSendPBucket_coins_2a cka prng fs Δcka qep tL P m_msg true contL contR hS ih coins sc
            hsend hqep_m hnot_tH (fun h => absurd h hnot_lt) hsync.b_C (fun h => by simp [hloc] at h)
      | none =>
        have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
            (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
              (epMgmtNew esC.g (2 + Δcka) P false)
              P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
            ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
              let c_cka := cka.send (esP.g.st P).γ coins
              let p := prng.up (esC.g.st P).root c_cka.2.2
              pure ((some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }), sc) := by
          simp [hooksCKA, cacheC, hγC, hloc_m, m,
            StateT.lift, StateT.run_bind, StateT.run_pure, StateT.run_modify,
            simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        simp only [Option.isSome_none]
        rw [hC, hepP, startSendPBucket_none_eq, bind_assoc, bind_assoc]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun coins _ => ?_
        rw [pure_bind, pure_bind]
        exact startSendPBucket_coins_2a cka prng fs Δcka qep tL P m_msg false contL contR hS ih coins sc
          hsend hqep_m hnot_tH (fun _ => Or.inl rfl) hsync.b_C (fun h => by simp [hloc] at h)
    · simp only [Bool.not_eq_true] at hloc
      have hγC : (esC.g.st P).γ = none := by
        simp [hsync.γ_C P, hloc]
      have htL_none : (mo0 tL).tL.isNone = false := by
        simp only [localCKA, Bool.or_eq_false_iff] at hloc
        exact hloc.1
      have htL_some : tL.isSome = true := by
        cases h' : tL <;> simp_all [mo0]
      obtain ⟨hsc_stP, hsc_epP⟩ := hsync.cka_st P (Or.inl hloc)
      obtain ⟨hsc_stO, hsc_epO⟩ := hsync.cka_st P.other (Or.inr (by simpa using hloc))
      dsimp only [projP] at hsc_stP hsc_stO
      obtain ⟨hO_ep, _, _⟩ := hsync.ping_pong_synced P hsend
      have hcanS : sc.canSend P = true := by
        simp [_root_.CryptoGames.CKA.GameState.canSend, hsc_epP, hsc_epO, hO_ep, hsend]
      have htL_ne : tL ≠ none := Option.isSome_iff_ne_none.mp htL_some
      have htL_isNone : tL.isNone = false := by cases tL <;> simp_all
      cases r with
      | some coins =>
        by_cases hbad_ok : healEpoch tL < esC.g.epoch P + 1 + 2
        · have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
              (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
                (epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
              pure ((none, esC.h), sc) := by
            simp [hooksCKA, liftC, _root_.CryptoGames.CKA.sendWithAdversaryCoinsQuery, cImpl,
              _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.sendWithAdversaryCoinsImpl,
              mo0_tH, hγC, hcanS, hsc_epP, hbad_ok,
              StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
              map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, pure_bind]
          dsimp only [postSendBucketC]
          rw [hDead none ({ esC with abort := true }, winEpC) sc rfl]
          simp
        · have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
            simp [show esC.g.epoch P + 1 ≠ healEpoch tL by omega]
          have hfin : ¬ (healEpoch tL + Δcka ≤ m) := by omega
          have hloc_m : localCKA (mo0 tL) Δcka m = false := by
            simp [localCKA, mo0_tH, htL_isNone]; omega
          let c_cka := cka.send (esP.g.st P).γ coins
          let p := prng.up (esC.g.st P).root c_cka.2.2
          let sc' := sc.afterSend P c_cka.1 c_cka.2.1
          let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
            (some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
              { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
          have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
              (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
                (epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
              pure (resC, sc') := by
            simp [hooksCKA, cacheC, liftC, _root_.CryptoGames.CKA.sendWithAdversaryCoinsQuery, cImpl,
              _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.sendWithAdversaryCoinsImpl,
              mo0_tH, hγC, hcanS, hsc_epP, hsc_stP, hbad_ok, hfin, hloc_m, m, c_cka, p, sc', resC,
              StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
              map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, pure_bind, hepP, startSendPBucket_some_eq]
          refine startSendPBucket_coins_2a cka prng fs Δcka qep tL P m_msg true contL contR hS ih coins sc'
            hsend hqep_m hnot_tH (fun _ => Or.inr (by omega))
            hsync.b_C fun _ => ?_
          simp [sc', c_cka, _root_.CryptoGames.CKA.GameState.afterSend, Party.other_ne,
            hsc_epP, hsc_stO, hsc_epO, hO_ep]
      | none =>
        by_cases heq_tH : esC.g.epoch P + 1 = healEpoch tL
        · have htH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = true := by
            simpa [htL_some] using heq_tH
          have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
              (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
                (epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins => ($ᵗ I : ProbComp I) >>= fun I₁ =>
                let c_cka := cka.send (esP.g.st P).γ coins
                let p := prng.up (esC.g.st P).root I₁
                pure ((some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) }),
                  sc.afterSend P c_cka.1 c_cka.2.1) := by
            by_cases hΔ : Δcka = 0
            · simp [hooksCKA, cacheC, liftC, _root_.CryptoGames.CKA.challQuery,
                _root_.CryptoGames.CKA.corrQuery, cImpl, _root_.CryptoGames.CKA.oracleImpl,
                _root_.CryptoGames.CKA.challImpl, _root_.CryptoGames.CKA.corrImpl,
                _root_.CryptoGames.CKA.GameState.afterSend, _root_.CryptoGames.CKA.GameState.finished,
                localCKA, mo0_tL, mo0_tH, htL_ne, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                hsync.b_C, hΔ, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            · simp [hooksCKA, cacheC, liftC, _root_.CryptoGames.CKA.challQuery, cImpl,
                _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.challImpl,
                localCKA, mo0_tL, mo0_tH, htL_ne, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                hsync.b_C, hΔ, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendPBucket_none_eq, bind_assoc, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
            fun coins _ => ?_
          rw [bind_assoc]
          have hstep := startSendPBucket_chall_2a cka prng fs Δcka qep tL P m_msg contL contR hS ih coins
            (sc.afterSend P (cka.send (esP.g.st P).γ coins).1 (cka.send (esP.g.st P).γ coins).2.1)
            hsend hqep_m htH hsync.b_C (fun _ => by
              simp [_root_.CryptoGames.CKA.GameState.afterSend, Party.other_ne,
                hsc_epP, hsc_stO, hsc_epO, hO_ep])
          simpa [pure_bind] using hstep
        · have hnot_tH : (tL.isSome && decide (esC.g.epoch P + 1 = healEpoch tL)) = false := by
            simp [heq_tH]
          have hC : (simulateQ (cImpl cka Δcka (mo0 tL).tH)
              (((hooksCKA cka prng fs Δcka (mo0 tL)).startSend
                (epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                let c_cka := cka.send (esP.g.st P).γ coins
                let p := prng.up (esC.g.st P).root c_cka.2.2
                pure ((some (if localCKA (mo0 tL) Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }),
                  sc.afterSend P c_cka.1 c_cka.2.1) := by
            by_cases hfin : healEpoch tL + Δcka ≤ m
            · have hloc_m : localCKA (mo0 tL) Δcka m = true := by simp [localCKA, mo0_tH, hfin]
              simp [hooksCKA, cacheC, liftC, _root_.CryptoGames.CKA.sendQuery,
                _root_.CryptoGames.CKA.corrQuery, cImpl, _root_.CryptoGames.CKA.oracleImpl,
                _root_.CryptoGames.CKA.sendImpl, _root_.CryptoGames.CKA.corrImpl,
                _root_.CryptoGames.CKA.GameState.afterSend, _root_.CryptoGames.CKA.GameState.finished,
                mo0_tH, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            · have hloc_m : localCKA (mo0 tL) Δcka m = false := by
                simp [localCKA, mo0_tH, htL_isNone]; omega
              simp [hooksCKA, cacheC, liftC, _root_.CryptoGames.CKA.sendQuery, cImpl,
                _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.sendImpl,
                mo0_tH, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendPBucket_none_eq, bind_assoc, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
            fun coins _ => ?_
          rw [pure_bind, pure_bind]
          refine startSendPBucket_coins_2a cka prng fs Δcka qep tL P m_msg false contL contR hS ih coins
            (sc.afterSend P (cka.send (esP.g.st P).γ coins).1 (cka.send (esP.g.st P).γ coins).2.1)
            hsend hqep_m hnot_tH (fun _ => Or.inl rfl) hsync.b_C fun _ => ?_
          simp [_root_.CryptoGames.CKA.GameState.afterSend, Party.other_ne,
            hsc_epP, hsc_stO, hsc_epO, hO_ep]

private theorem step_transmit_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hDead : ∀ u esCw' sc', esCw'.1.abort = true →
      𝒟[contL u esCw' sc'] = 𝒟[(pure false : ProbComp Bool)])
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL)
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esCw)).run sc >>=
        fun res => contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r))))))).run esPw)).run sp >>=
        fun res => contR res.1.1 res.1.2 res.2] {true} := by
  by_cases hwin0 : esCw.1.g.win = true
  · rcases esCw with ⟨esC, winEpC⟩
    rcases esPw with ⟨esP, winEpP⟩
    have hwinEp : winEpP = winEpC := hS.winEp_eq
    subst winEpP
    dsimp only at hwin0
    have hwin : esP.g.win = esC.g.win := eraseSt_win hS.sync.g_eq
    exact step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, hS.sync.abort_C, hwin0,
        StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, hS.sync.abort_P,
        hwin, hwin0, StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure])
      (ih none _ _ _ _ hS)
  · simp only [Bool.not_eq_true] at hwin0
    by_cases hsend : P.sendsIn (esCw.1.g.epoch P + 1) = true
    · exact step_transmit_new_2a cka prng fs Δcka qep tL P m_msg r contL contR hS hDead hwin0 hsend ih
    · simp only [Bool.not_eq_true] at hsend
      exact step_transmit_same_2a cka prng fs Δcka qep tL P m_msg r contL contR hS hwin0 hsend ih

private theorem step_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esCw : CKABucketEState Γ T Sig SS RS M E I) (sc : _root_.CryptoGames.CKA.GameState Γ T)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I) (sp : PRFPRNG.GameState Sig I K)
    (contL : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hDead : ∀ u esCw' sc', esCw'.1.abort = true →
      𝒟[contL u esCw' sc'] = 𝒟[(pure false : ProbComp Bool)])
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) q).run esCw)).run sc >>=
        fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL)) q).run esPw)).run sp >>=
        fun r => contR r.1.1 r.1.2 r.2] {true} := by
  rcases q with n | ((((⟨P, m_msg, r⟩ | ch) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · have hL : (simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) (.inl n)).run esCw)).run sc =
        (query (spec := unifSpec) n >>= fun u => pure ((u, esCw), sc)) := by
      simp [implCKABucket, cImpl, StateT.lift, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
    have hR : (simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL)) (.inl n)).run esPw)).run sp =
        (query (spec := unifSpec) n >>= fun u => pure ((u, esPw), sp)) := by
      simp [implPRNGBucketAuth, implPRNGBucketAuthGen, pImpl, StateT.lift, StateT.run_bind,
        StateT.run_pure, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, bind_assoc]
    rw [hL, hR, bind_assoc, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun u _ => ?_
    rw [pure_bind, pure_bind]
    exact ih u esCw sc esPw sp hS
  · exact step_transmit_2a cka prng fs Δcka qep tL P m_msg r contL contR hS hDead ih
  · exact step_pure_2a
      (by simp [implCKABucket, StateT.run_pure, simulateQ_pure])
      (by simp [implPRNGBucketAuth, implPRNGBucketAuthGen, StateT.run_pure, simulateQ_pure])
      (ih none esCw sc esPw sp hS)
  · exact step_deliver_2a cka prng fs Δcka qep tL P c contL contR hS ih
  · exact step_inject_2a cka prng fs Δcka qep tL P c contL contR hS hDead ih
  · exact step_corr_2a cka prng fs Δcka qep tL P contL contR hS hDead ih

private theorem sync_init_some_mo0
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka l : ℕ)
    (kr : KR) (kc : KC) :
    Sync prng Δcka (mo0 (some l))
      (initES_C cka prng fs lam (some l) kr kc)
      (_root_.CryptoGames.CKA.initState cka kc true)
      (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (initSP prng lam (some l) kr) := by
  have hloc0 : localCKA (mo0 (some l)) Δcka 0 = false := by
    simp [localCKA, mo0, Mode.tH, healEpoch]
  refine
    { abort_C := rfl
      abort_P := rfl
      b_C := rfl
      b_P := rfl
      g_eq := rfl
      id_C := fun P => by cases P <;> rfl
      id_P := fun P => by cases P <;> rfl
      tcur_C := fun P => by cases P <;> rfl
      tcur_P := fun P => by cases P <;> rfl
      vS_eq := fun P => by cases P <;> rfl
      vR_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      γ_C := fun P => by cases P <;> simp [initES_C, mkParties, hloc0]
      root_P := fun P => by
        cases P <;> simp [initES_P, initES_C, mkParties, knownRoot_mo0]
      cka_st := fun P _ => by cases P <;> exact ⟨rfl, rfl⟩
      trans_inv := fun r hr => by simp [initES_C] at hr
      comp_inv := fun pos hpos => by simp [initES_C] at hpos
      epoch_S := rfl
      cache_gt := fun _ _ => ⟨rfl, rfl⟩
      ping_pong := Or.inl ⟨rfl, rfl⟩
      prng_before_tH := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
      prng_after_tH := fun _ h => by simp [initES_C, mo0, Mode.tH, healEpoch] at h
      prng_at_tStar := fun h => by
        change 0 = l + 2 at h
        omega }

private theorem initPRNGBucket_run_none_zero
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (kr : KR) :
    (simulateQ (pImpl prng)
      ((initPRNGBucketAuthHybrid cka prng fs lam none 0).run {})).run
      { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP_zero prng kr)) := by
  unfold initPRNGBucketAuthHybrid
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_pImpl,
    simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1

private theorem initPRNGBucket_run_some
    [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (l : ℕ) (kr : KR) :
    (simulateQ (pImpl prng)
      ((initPRNGBucketAuthHybrid cka prng fs lam (some l) (l + 2)).run {})).run
      { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP prng lam (some l) kr)) := by
  unfold initPRNGBucketAuthHybrid
  simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_sampleT_pImpl,
    simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1

theorem cka_branch_true_redCKAAuthBucket_le_unsplit
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[_root_.CryptoGames.CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthBucket cka prng fs lam Δcka qep tL A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} := by
  let postC : Bool → CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool :=
    fun _ esCw _ =>
      match esCw.2 with
      | none => pure false
      | some tWin => pure (!esCw.1.abort && esCw.1.g.win &&
          authLosingConditionsAvoided (2 + Δcka) tL tWin esCw.1.g)
  let postP : Bool → PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool :=
    fun _ esPw _ =>
      match esPw.2 with
      | none => pure false
      | some tWin => pure (!esPw.1.abort && esPw.1.g.win &&
          authLosingConditionsAvoided (2 + Δcka) tL tWin esPw.1.g)
  have hPostDead : ∀ a (esCw' : CKABucketEState Γ T Sig SS RS M E I) sc',
      esCw'.1.abort = true → 𝒟[postC a esCw' sc'] = 𝒟[(pure false : ProbComp Bool)] := by
    intro _ ⟨esC', winEp'⟩ _ hab
    dsimp only at hab
    dsimp only [postC]
    cases winEp' <;> simp [hab]
  have hPostSync : ∀ a esCw' sc' esPw' sp',
      Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[postC a esCw' sc'] {true} ≤ 𝒟[postP a esPw' sp'] {true} := by
    intro _ ⟨esC', winEpC'⟩ sc' ⟨esP', winEpP'⟩ sp' hS
    have hw : winEpP' = winEpC' := hS.winEp_eq
    subst winEpP'
    dsimp only [postC, postP]
    cases winEpC' with
    | none => exact le_rfl
    | some tWin =>
      have hsync : Sync prng Δcka (mo0 tL) esC' sc' (projP esP') sp' := hS.sync
      have habC : esC'.abort = false := hsync.abort_C
      have habP : esP'.abort = false := hsync.abort_P
      have hwin : esP'.g.win = esC'.g.win := eraseSt_win hsync.g_eq
      have hauth : authLosingConditionsAvoided (2 + Δcka) tL tWin esP'.g =
          authLosingConditionsAvoided (2 + Δcka) tL tWin esC'.g :=
        eraseSt_authOK hsync.g_eq (2 + Δcka) tL tWin
      simp [habC, habP, hwin, hauth]
  have hRunLe : ∀ esCw sc esPw sp,
      Sync2a prng Δcka qep tL esCw sc esPw sp →
      𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
          ((simulateQ (implCKABucket cka prng fs Δcka qep tL) A).run esCw)).run sc >>=
          fun r => postC r.1.1 r.1.2 r.2] {true} ≤
        𝒟[(simulateQ (pImpl prng)
          ((simulateQ (implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL)) A).run esPw)).run sp >>=
          fun r => postP r.1.1 r.1.2 r.2] {true} := fun esCw sc esPw sp hS =>
    twoLayer_sync_le
      (cImpl cka Δcka (healEpoch tL))
      (implCKABucket cka prng fs Δcka qep tL)
      (pImpl prng)
      (implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
      (fun esCw _ => esCw.1.abort = true)
      (Sync2a prng Δcka qep tL)
      (deadStep_2a cka prng fs Δcka qep tL)
      (step_2a cka prng fs Δcka qep tL)
      A postC postP hPostDead hPostSync hS
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng = pImpl prng := rfl
  cases tL with
  | none =>
    have hL : _root_.CryptoGames.CKA.branch cka Δcka (healEpoch none) true
        (redCKAAuthBucket cka prng fs lam Δcka qep none A) =
        ($ᵗ KC >>= fun kc_ext => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          (simulateQ (cImpl cka Δcka 0)
            ((simulateQ (implCKABucket cka prng fs Δcka qep none) A).run
              (initES_C cka prng fs lam none kr kc, none))).run
            (_root_.CryptoGames.CKA.initState cka kc_ext true) >>=
            fun r => postC r.1.1 r.1.2 r.2) := by
      unfold _root_.CryptoGames.CKA.branch redCKAAuthBucket runCKAAuthBucket initCKA initES_C
      simp only [healEpoch_none_eq, StateT.run'_eq, StateT.run_lift,
        StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        simulateQ_sampleT_cImpl, simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, cImpl]
      congr 1; funext kc_ext; congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sc'⟩
      cases winEp <;> simp [postC, simulateQ_pure, StateT.run_pure]
    have hR : PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep none 0 A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          (simulateQ (pImpl prng)
            ((simulateQ (implPRNGBucketAuth cka prng fs Δcka qep none 0) A).run
              (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none))).run
            (initSP_zero prng kr) >>=
            fun r => postP r.1.1 r.1.2 r.2) := by
      unfold PRFPRNG.branch unsplitRedPRNGAuthBucketHybrid runPRNGAuthBucketHybrid
        runPRNGAuthBucketHybridGen implPRNGBucketAuth initES_PBucket
      simp only [StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postP, simulateQ_pure, StateT.run_pure]
    rw [hL, healEpoch_none_eq, hR]
    have hconst :
        𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          (simulateQ (pImpl prng)
            ((simulateQ (implPRNGBucketAuth cka prng fs Δcka qep none 0) A).run
              (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none))).run
            (initSP_zero prng kr) >>=
            fun r => postP r.1.1 r.1.2 r.2] {true} =
        𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          (simulateQ (pImpl prng)
            ((simulateQ (implPRNGBucketAuth cka prng fs Δcka qep none 0) A).run
              (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none))).run
            (initSP_zero prng kr) >>=
            fun r => postP r.1.1 r.1.2 r.2] {true} :=
      congrArg (fun μ => μ {true}) (OracleComp.evalDist_bind_const _ _)
    rw [← hconst]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kc_ext _ => ?_
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kr _ => ?_
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kc _ => ?_
    refine hRunLe _ _ _ _ ⟨?_, rfl, fun _ => Nat.zero_le _, fun h => by simp at h⟩
    exact sync_init_none_zero cka prng fs lam Δcka kr kc kc_ext
  | some l =>
    have hL : _root_.CryptoGames.CKA.branch cka Δcka (healEpoch (some l)) true
        (redCKAAuthBucket cka prng fs lam Δcka qep (some l) A) =
        ($ᵗ KC >>= fun kc => $ᵗ KR >>= fun kr =>
          (simulateQ (cImpl cka Δcka (l + 2))
            ((simulateQ (implCKABucket cka prng fs Δcka qep (some l)) A).run
              (initES_C cka prng fs lam (some l) kr kc, none))).run
            (_root_.CryptoGames.CKA.initState cka kc true) >>=
            fun r => postC r.1.1 r.1.2 r.2) := by
      unfold _root_.CryptoGames.CKA.branch redCKAAuthBucket runCKAAuthBucket initCKA initES_C
      simp only [healEpoch_some_eq, StateT.run'_eq, StateT.run_lift,
        StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
        simulateQ_sampleT_cImpl, simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply, cImpl]
      congr 1; funext kc; congr 1; funext kr; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sc'⟩
      cases winEp <;> simp [postC, simulateQ_pure, StateT.run_pure]
    have hR : PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep (some l) (l + 2) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          (simulateQ (pImpl prng)
            ((simulateQ (implPRNGBucketAuth cka prng fs Δcka qep (some l) (l + 2)) A).run
              (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none))).run
            (initSP prng lam (some l) kr) >>=
            fun r => postP r.1.1 r.1.2 r.2) := by
      unfold PRFPRNG.branch unsplitRedPRNGAuthBucketHybrid runPRNGAuthBucketHybrid
        runPRNGAuthBucketHybridGen implPRNGBucketAuth initES_PBucket
      simp only [StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_some cka prng fs lam l, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postP, simulateQ_pure, StateT.run_pure]
    rw [hL, healEpoch_some_eq, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kc _ => ?_
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun kr _ => ?_
    refine hRunLe _ _ _ _ ⟨?_, rfl, fun _ => Nat.zero_le _, fun _ => ⟨rfl, rfl⟩⟩
    exact sync_init_some_mo0 cka prng fs lam Δcka l kr kc


end Hop2aProof

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aStep
