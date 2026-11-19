/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10 -- proof-setup: allow-public-import
import VCVio.OracleComp.EvalDist.Measure

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aBase

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


theorem twoLayer_dead_eq_false
    {ι1 ι2 : Type} {S1 : OracleSpec ι1} {S2 : OracleSpec ι2} {EsL GsL α : Type}
    (outerL : QueryImpl S2 (StateT GsL ProbComp))
    (innerL : QueryImpl S1 (StateT EsL (OracleComp S2)))
    (DeadL : EsL → GsL → Prop)
    (hDeadStep : ∀ (q : ι1) (esL : EsL) (gsL : GsL),
      DeadL esL gsL →
      ∀ r ∈ support ((simulateQ outerL ((innerL q).run esL)).run gsL),
        DeadL r.1.2 r.2)
    (oa : OracleComp S1 α)
    (postL : α → EsL → GsL → ProbComp Bool)
    (hPost : ∀ a esL' gsL', DeadL esL' gsL' → 𝒟[postL a esL' gsL'] = 𝒟[(pure false : ProbComp Bool)])
    {esL : EsL} {gsL : GsL} (hD : DeadL esL gsL) :
    𝒟[(simulateQ outerL ((simulateQ innerL oa).run esL)).run gsL >>=
        fun r => postL r.1.1 r.1.2 r.2] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing esL gsL with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hPost a esL gsL hD
  | query_bind q cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    exact evalDist_bind_false_of_support _ _ fun r hr =>
      ih r.1.1 (hDeadStep q esL gsL hD r hr)

theorem twoLayer_sync_le
    {ι1 ι2L ι2R : Type}
    {S1 : OracleSpec ι1} {S2L : OracleSpec ι2L} {S2R : OracleSpec ι2R}
    {EsL GsL EsR GsR α : Type}
    (outerL : QueryImpl S2L (StateT GsL ProbComp))
    (innerL : QueryImpl S1 (StateT EsL (OracleComp S2L)))
    (outerR : QueryImpl S2R (StateT GsR ProbComp))
    (innerR : QueryImpl S1 (StateT EsR (OracleComp S2R)))
    (DeadL : EsL → GsL → Prop)
    (SyncR : EsL → GsL → EsR → GsR → Prop)
    (hDeadStep : ∀ (q : ι1) (esL : EsL) (gsL : GsL),
      DeadL esL gsL →
      ∀ r ∈ support ((simulateQ outerL ((innerL q).run esL)).run gsL),
        DeadL r.1.2 r.2)
    (hStep : ∀ (q : ι1) (esL : EsL) (gsL : GsL) (esR : EsR) (gsR : GsR)
        (contL : S1.Range q → EsL → GsL → ProbComp Bool)
        (contR : S1.Range q → EsR → GsR → ProbComp Bool),
      SyncR esL gsL esR gsR →
      (∀ u esL' gsL', DeadL esL' gsL' → 𝒟[contL u esL' gsL'] = 𝒟[(pure false : ProbComp Bool)]) →
      (∀ u esL' gsL' esR' gsR', SyncR esL' gsL' esR' gsR' →
        𝒟[contL u esL' gsL'] {true} ≤ 𝒟[contR u esR' gsR'] {true}) →
      𝒟[(simulateQ outerL ((innerL q).run esL)).run gsL >>=
          fun r => contL r.1.1 r.1.2 r.2] {true} ≤
        𝒟[(simulateQ outerR ((innerR q).run esR)).run gsR >>=
          fun r => contR r.1.1 r.1.2 r.2] {true})
    (oa : OracleComp S1 α)
    (postL : α → EsL → GsL → ProbComp Bool)
    (postR : α → EsR → GsR → ProbComp Bool)
    (hPostDead : ∀ a esL' gsL', DeadL esL' gsL' → 𝒟[postL a esL' gsL'] = 𝒟[(pure false : ProbComp Bool)])
    (hPostSync : ∀ a esL' gsL' esR' gsR', SyncR esL' gsL' esR' gsR' →
      𝒟[postL a esL' gsL'] {true} ≤ 𝒟[postR a esR' gsR'] {true})
    {esL : EsL} {gsL : GsL} {esR : EsR} {gsR : GsR}
    (hS : SyncR esL gsL esR gsR) :
    𝒟[(simulateQ outerL ((simulateQ innerL oa).run esL)).run gsL >>=
        fun r => postL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[(simulateQ outerR ((simulateQ innerR oa).run esR)).run gsR >>=
        fun r => postR r.1.1 r.1.2 r.2] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL gsL esR gsR with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hPostSync a esL gsL esR gsR hS
  | query_bind q cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    exact hStep q esL gsL esR gsR
      (fun u esL' gsL' =>
        (simulateQ outerL ((simulateQ innerL (cont u)).run esL')).run gsL' >>=
          fun r => postL r.1.1 r.1.2 r.2)
      (fun u esR' gsR' =>
        (simulateQ outerR ((simulateQ innerR (cont u)).run esR')).run gsR' >>=
          fun r => postR r.1.1 r.1.2 r.2)
      hS
      (fun u _ _ hD => twoLayer_dead_eq_false outerL innerL DeadL hDeadStep (cont u) postL hPostDead hD)
      (fun u _ _ _ _ hS' => ih u hS')

@[local simp] theorem healEpoch_none_eq : healEpoch none = 0 := rfl

@[local simp] theorem healEpoch_some_eq (l : ℕ) : healEpoch (some l) = l + 2 := rfl

@[local simp] theorem ltOpt_none_eq (t : ℕ) : ltOpt none t = true := rfl

@[local simp] theorem ltOpt_some_eq (l t : ℕ) : ltOpt (some l) t = decide (l < t) := rfl

@[local simp] theorem leak_tL_eq {St Msg C : Type} (g : GameState St Msg C) (e : ℕ) :
    (g.leak e).tL = some (_root_.CryptoGames.SM.maxOpt g.tL e) := rfl

@[local simp] theorem maxOpt_none_eq (e : ℕ) :
    _root_.CryptoGames.SM.maxOpt none e = e := rfl

@[local simp] theorem maxOpt_some_eq (cur e : ℕ) :
    _root_.CryptoGames.SM.maxOpt (some cur) e = max cur e := rfl

@[local simp] theorem afterCorr_epoch_eq {St Msg C : Type} (g : GameState St Msg C) (P Q : Party) :
    (g.afterCorr P).epoch Q = g.epoch Q := rfl

@[expose] def mo0 (tL : Option ℕ) : Mode := ⟨true, tL, healEpoch tL⟩

@[local simp] theorem mo0_auth (tL : Option ℕ) : (mo0 tL).auth = true := rfl
@[local simp] theorem mo0_tL (tL : Option ℕ) : (mo0 tL).tL = tL := rfl
@[local simp] theorem mo0_tStar (tL : Option ℕ) : (mo0 tL).tStar = healEpoch tL := rfl
@[local simp] theorem mo0_tH (tL : Option ℕ) : (mo0 tL).tH = healEpoch tL := by
  simp [mo0, _root_.CryptoGames.SM.Construction.Mode.tH]

theorem knownRoot_mo0 (tL : Option ℕ) (m : ℕ) : knownRoot (mo0 tL) m = true := by
  rcases le_or_gt (healEpoch tL) m with h | h
  · simp [knownRoot, mo0_tStar, h]
  · cases tL with
    | none => simp [healEpoch_none_eq] at h
    | some l =>
      rcases le_or_gt (l + 2) m with h2 | h2 <;>
        simp [knownRoot, mo0_tL, mo0_tH, h, h2]

@[local simp] theorem hooksCKABucket_fsSend [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx P t0 ss h m r) :
    (hooksCKABucket cka prng fs Δcka tL).fsSend ctx P t0 ss h m r =
      pure (some (fs.send ss h m)) := rfl

@[local simp] theorem hooksCKABucket_fsRecv [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx P t0 rs h e r) :
    (hooksCKABucket cka prng fs Δcka tL).fsRecv ctx P t0 rs h e r =
      pure (some (fs.receive rs h e)) := rfl

@[local simp] theorem hooksCKABucket_commit [DecidableEq T] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (tL : Option ℕ)
    (ctx P old new) :
    (hooksCKABucket cka prng fs Δcka tL).commit ctx P old new =
      (hooksCKA cka prng fs Δcka (mo0 tL)).commit ctx P old new := rfl

@[local simp] theorem hooksPRNGBucketAuthHybrid_fsSend [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P t0 ss h m r) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsSend ctx P t0 ss h m r =
      pure (some (fs.send ss h m)) := rfl

@[local simp] theorem hooksPRNGBucketAuthHybrid_fsRecv [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P t0 rs h e r) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsRecv ctx P t0 rs h e r =
      pure (some (fs.receive rs h e)) := rfl

@[local simp] theorem hooksPRNGBucketAuthHybrid_commit [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P old new) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).commit ctx P old new =
      pure (some new) := rfl

@[expose] def projP
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    _root_.CryptoGames.SM.Construction.AuthL10.EStateP Γ T Sig SS RS M E K :=
  { g := esP.g, h := { cache := esP.h.cache }, abort := esP.abort }

@[local simp] theorem projP_g
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    (projP esP).g = esP.g := rfl

@[local simp] theorem projP_abort
    (esP : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) :
    (projP esP).abort = esP.abort := rfl

structure Sync2a (prng : PRFPRNG KR Sig I K) (Δcka qep : ℕ) (tL : Option ℕ)
    (esCw : CKABucketEState Γ T Sig SS RS M E I) (sc : _root_.CryptoGames.CKA.GameState Γ T)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) : Prop where
  sync : Sync prng Δcka (mo0 tL) esCw.1 sc (projP esPw.1) sp
  winEp_eq : esPw.2 = esCw.2
  epoch_le_qep : ∀ P, esCw.1.g.epoch P ≤ qep
  pre_tH : max (esCw.1.g.epoch .A) (esCw.1.g.epoch .B) < healEpoch tL →
    postLeak tL esCw.1.g = false ∧ esPw.1.h.corrRoot = none

theorem Sync2a.root_P_eq
    {prng : PRFPRNG KR Sig I K} {Δcka qep : ℕ} {tL : Option ℕ}
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp) (P : Party) :
    (esPw.1.g.st P).root = some (esCw.1.g.st P).root := by
  have h := hS.sync.root_P P
  simpa [projP, knownRoot_mo0] using h

theorem deadStep_2a
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esCw : CKABucketEState Γ T Sig SS RS M E I)
    (sc : _root_.CryptoGames.CKA.GameState Γ T)
    (hD : esCw.1.abort = true) :
    ∀ r ∈ support ((simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) q).run esCw)).run sc),
      r.1.2.1.abort = true := by
  rcases esCw with ⟨esC, winEp⟩
  dsimp only at hD
  rcases q with n | ((((⟨P, m, r0⟩ | ch) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · intro r hr
    simp [implCKABucket, cImpl, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp] at hr
    rcases hr with ⟨_, rfl⟩
    exact hD
  · intro r hr
    simp [implCKABucket, hD, StateT.run_bind, StateT.run_get, StateT.run_pure,
      simulateQ_pure] at hr
    rcases hr with rfl
    exact hD
  · intro r hr
    simp [implCKABucket, StateT.run_pure, simulateQ_pure] at hr
    rcases hr with rfl
    exact hD
  · intro r hr
    simp [implCKABucket, deliverE, hD, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, simulateQ_pure,
      map_eq_bind_pure_comp] at hr
    rcases hr with rfl
    exact hD
  · intro r hr
    simp [implCKABucket, injectE, hD, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, simulateQ_pure,
      map_eq_bind_pure_comp] at hr
    rcases hr with rfl
    exact hD
  · intro r hr
    simp [implCKABucket, hD, StateT.run_bind, StateT.run_get, StateT.run_pure,
      simulateQ_pure] at hr
    rcases hr with rfl
    exact hD

theorem step_pure_2a {EsL GsL EsR GsR U : Type}
    {mL : ProbComp ((U × EsL) × GsL)} {mR : ProbComp ((U × EsR) × GsR)}
    {contL : U → EsL → GsL → ProbComp Bool} {contR : U → EsR → GsR → ProbComp Bool}
    {u : U} {esL' : EsL} {gsL' : GsL} {esR' : EsR} {gsR' : GsR}
    (hL : mL = pure ((u, esL'), gsL')) (hR : mR = pure ((u, esR'), gsR'))
    (hle : 𝒟[contL u esL' gsL'] {true} ≤ 𝒟[contR u esR' gsR'] {true}) :
    𝒟[mL >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[mR >>= fun r => contR r.1.1 r.1.2 r.2] {true} := by
  rw [hL, hR, pure_bind, pure_bind]; exact hle

theorem step_abort_2a {GsL U : Type}
    {mL : ProbComp ((U × CKABucketEState Γ T Sig SS RS M E I) × GsL)}
    {mR : ProbComp Bool}
    {contL : U → CKABucketEState Γ T Sig SS RS M E I → GsL → ProbComp Bool}
    {u : U} {esCw' : CKABucketEState Γ T Sig SS RS M E I} {gsL' : GsL}
    (hDead : ∀ u' esCw'' gsL'', esCw''.1.abort = true →
      𝒟[contL u' esCw'' gsL''] = 𝒟[(pure false : ProbComp Bool)])
    (hL : mL = pure ((u, esCw'), gsL'))
    (hD : esCw'.1.abort = true) :
    𝒟[mL >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤ 𝒟[mR] {true} := by
  rw [hL, pure_bind, hDead u esCw' gsL' hD]; simp

theorem postLeak_leak_false_of_lt_tH {St Msg C : Type}
    {tL : Option ℕ} {g : GameState St Msg C} {e : ℕ}
    (hpl : postLeak tL g = false) (he : e + 1 < healEpoch tL) :
    postLeak tL (g.leak e) = false := by
  cases tL with
  | none => simp at he
  | some l =>
    simp only [healEpoch_some_eq] at he
    cases htL : g.tL with
    | none =>
      simp [postLeak, htL]
      omega
    | some cur =>
      simp [postLeak, htL] at hpl ⊢
      omega

theorem postLeak_afterCorr_false_of_lt_tH {St Msg C : Type}
    {tL : Option ℕ} {g : GameState St Msg C} (P : Party)
    (hpl : postLeak tL g = false) (he : max (g.epoch .A) (g.epoch .B) + 1 < healEpoch tL) :
    postLeak tL (g.afterCorr P) = false := by
  have h := postLeak_leak_false_of_lt_tH hpl he
  dsimp [postLeak, GameState.afterCorr, GameState.leak] at h ⊢
  exact h

theorem epoch_accept_le_qep {St Msg C : Type}
    {g : GameState St Msg C} {qep : ℕ} (hle : ∀ Q, g.epoch Q ≤ qep)
    (P : Party) (st' : St) (pos : Pos) (hpos : pos.epoch ≤ qep) :
    ∀ Q, (g.accept P st' pos).epoch Q ≤ qep := fun Q => by
  by_cases hQP : Q = P
  · subst hQP
    simp [GameState.accept, GameState.delete]
    exact ⟨hle Q, hpos⟩
  · simp [GameState.accept, GameState.delete, hQP]
    exact hle Q

theorem max_epoch_le_accept {St Msg C : Type}
    (g : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    max (g.epoch .A) (g.epoch .B) ≤
      max ((g.accept P st' pos).epoch .A) ((g.accept P st' pos).epoch .B) := by
  cases P <;> simp [GameState.accept, GameState.delete] <;> omega

theorem step_corr_2a
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party)
    (contL : Option (PartyState Γ T Sig SS RS) →
      CKABucketEState Γ T Sig SS RS M E I → _root_.CryptoGames.CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (PartyState Γ T Sig SS RS) →
      PRNGBucketAuthEState Γ T Sig SS RS M E K I → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esCw : CKABucketEState Γ T Sig SS RS M E I} {sc : _root_.CryptoGames.CKA.GameState Γ T}
    {esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync2a prng Δcka qep tL esCw sc esPw sp)
    (hDead : ∀ u esCw' sc', esCw'.1.abort = true →
      𝒟[contL u esCw' sc'] = 𝒟[(pure false : ProbComp Bool)])
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) (.inr (.inr P))).run esCw)).run sc >>=
        fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL)) (.inr (.inr P))).run esPw)).run sp >>=
        fun r => contR r.1.1 r.1.2 r.2] {true} := by
  rcases esCw with ⟨esC, winEpC⟩
  rcases esPw with ⟨esP, winEpP⟩
  have hwinEp : winEpP = winEpC := hS.winEp_eq
  subst winEpP
  have hsync : Sync prng Δcka (mo0 tL) esC sc (projP esP) sp := hS.sync
  have hg_eq : _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esP.g =
      _root_.CryptoGames.SM.Construction.AuthL10.eraseSt esC.g := hsync.g_eq
  have hwin : esP.g.win = esC.g.win := eraseSt_win hg_eq
  have hca : esP.g.corrAllowed P = esC.g.corrAllowed P := eraseSt_corrAllowed hg_eq P
  have habC : esC.abort = false := hsync.abort_C
  have habP : esP.abort = false := hsync.abort_P
  have hesP_eq : ({ g := esP.g, h := esP.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) = esP := by
    rcases esP with ⟨g, h, ab⟩; dsimp only at habP; subst ab; rfl
  have hrealP : realParty (esP.g.st P) (esP.g.st P).γ (esC.g.st P).root
      (esP.g.st P).vS (esP.g.st P).vR =
      realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
      (esC.g.st P).vS (esC.g.st P).vR :=
    (hsync.realParty_eq P (esP.g.st P).γ (esC.g.st P).root).symm
  have hγC_eq : (esC.g.st P).γ =
      if localCKA (mo0 tL) Δcka (esC.g.epoch P) then some (esP.g.st P).γ else none :=
    hsync.γ_C P
  by_cases hguard : esC.g.win || !esC.g.corrAllowed P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    exact step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, habC, hguard, StateT.run_bind, StateT.run_get,
        StateT.run_pure, simulateQ_pure])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, habP, hwin, hca, hguard,
        StateT.run_bind, StateT.run_get, StateT.run_pure, simulateQ_pure])
      (ih none _ _ _ _ hS)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hrootP : (esP.g.st P).root = some (esC.g.st P).root := hS.root_P_eq P
    have htcurP : (esP.g.st P).tcur = esC.g.epoch P := hsync.tcur_P P
    let hP' : PRNGBucketAuthState T Sig K I :=
      if !(esC.g.epoch P < healEpoch tL) && esP.h.corrRoot.isNone then
        { esP.h with corrRoot := some (esC.g.epoch P, (esC.g.st P).root) }
      else esP.h
    have hhP'_cache : hP'.cache = esP.h.cache := by
      dsimp only [hP']; split <;> rfl
    have hsync_after : ∀ {sc' : _root_.CryptoGames.CKA.GameState Γ T}
        (hs : Sync prng Δcka (mo0 tL)
          { esC with g := esC.g.afterCorr P } sc'
          { projP esP with g := (projP esP).g.afterCorr P } sp),
        Sync prng Δcka (mo0 tL)
          { esC with g := esC.g.afterCorr P } sc'
          (projP { esP with g := esP.g.afterCorr P, h := hP' }) sp := by
      intro sc' hs
      have hprojP' : projP ({ esP with g := esP.g.afterCorr P, h := hP' }) =
          { projP esP with g := (projP esP).g.afterCorr P } := by
        simp [projP, hhP'_cache]
      rw [hprojP']
      exact hs
    have hP_step : (simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL)) (.inr (.inr P))).run
          (esP, winEpC))).run sp =
        pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
          (esC.g.st P).vS (esC.g.st P).vR),
          ({ esP with g := esP.g.afterCorr P, h := hP' }, winEpC)), sp) := by
      by_cases hcond : healEpoch tL ≤ esC.g.epoch P ∧ esP.h.corrRoot = none
      · have hhP' : hP' = { esP.h with corrRoot := some (esC.g.epoch P, (esC.g.st P).root) } := by
          simp [hP', hcond.1, hcond.2]
        rw [hhP']
        dsimp only [implPRNGBucketAuth, implPRNGBucketAuthGen, hooksPRNGBucketAuthHybrid]
        simp [-Prod.mk.injEq, resolveCorrRoot, habP, hwin, hca, hguard, hrootP, htcurP,
          hcond.1, hcond.2, hrealP, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
          StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_bind, simulateQ_pure,
          map_eq_bind_pure_comp]
      · have hcond_b : (!(decide (esC.g.epoch P < healEpoch tL)) && esP.h.corrRoot.isNone) = false := by
          cases hcr : esP.h.corrRoot <;> simp [hcr] at hcond ⊢ <;> omega
        have hhP' : hP' = esP.h := by
          dsimp only [hP']
          rw [hcond_b]
          rfl
        rw [hhP']
        dsimp only [implPRNGBucketAuth, implPRNGBucketAuthGen, hooksPRNGBucketAuthHybrid]
        simp [-Prod.mk.injEq, resolveCorrRoot, habP, hwin, hca, hguard, hrootP, htcurP,
          hcond, hrealP, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
          StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_bind, simulateQ_pure,
          map_eq_bind_pure_comp]
    by_cases hloc : localCKA (mo0 tL) Δcka (esC.g.epoch P)
    · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
        rw [hγC_eq, hloc]; rfl
      have hnot_pre : ¬ max ((esC.g.afterCorr P).epoch .A) ((esC.g.afterCorr P).epoch .B) < healEpoch tL := by
        dsimp only [GameState.afterCorr, GameState.leak]
        have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp
        simp only [localCKA, mo0_tL, mo0_tH, Bool.or_eq_true, decide_eq_true_eq] at hloc
        rcases hloc with hnone | hge
        · cases tL <;> simp at hnone ⊢
        · omega
      refine step_pure_2a
        (by simp [-Prod.mk.injEq, implCKABucket, hooksCKABucket, hooksCKA, habC, hguard, hγC,
          StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp]; rfl)
        hP_step (ih _ _ _ _ _ ?_)
      exact ⟨by simpa only [habC] using hsync_after (hsync.afterCorr P), rfl,
        fun Q => by dsimp only [GameState.afterCorr, GameState.leak]; exact hS.epoch_le_qep Q,
        fun hlt => (hnot_pre hlt).elim⟩
    · simp only [Bool.not_eq_true] at hloc
      have hγC : (esC.g.st P).γ = none := by
        rw [hγC_eq, hloc]; rfl
      obtain ⟨hcka_stP, hcka_epP⟩ := hsync.cka_st P (Or.inl hloc)
      obtain ⟨_, hcka_epO⟩ := hsync.cka_st P.other (Or.inr (by simpa using hloc))
      by_cases hcorr : sc.allowCorr (healEpoch tL) || sc.finished Δcka (healEpoch tL) P
      · simp only [Bool.or_eq_true] at hcorr
        refine step_pure_2a
          (by simp [-Prod.mk.injEq, implCKABucket, hooksCKABucket, hooksCKA,
            liftC, _root_.CryptoGames.CKA.corrQuery,
            cImpl, _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.corrImpl,
            habC, hguard, hγC, hcorr, hcka_stP,
            StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp]; rfl)
          hP_step (ih _ _ _ _ _ ?_)
        refine ⟨by simpa only [habC] using hsync_after (hsync.afterCorr P), rfl,
          fun Q => by simp only [afterCorr_epoch_eq]; exact hS.epoch_le_qep Q,
          fun hlt => ?_⟩
        simp only [afterCorr_epoch_eq] at hlt
        obtain ⟨hpl0, hcr0⟩ := hS.pre_tH hlt
        have hmax_sc : max (sc.epoch .A) (sc.epoch .B) = max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp [Party.other] at hcka_epP hcka_epO <;> simp [hcka_epP, hcka_epO]
        have hfin_f : sc.finished Δcka (healEpoch tL) P = false := by
          have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
            cases P <;> simp
          simp [_root_.CryptoGames.CKA.GameState.finished, hcka_epP]
          omega
        have hallow : sc.allowCorr (healEpoch tL) = true := by
          rcases hcorr with h1 | h2
          · exact h1
          · rw [hfin_f] at h2; cases h2
        have hmax_lt : max (esC.g.epoch .A) (esC.g.epoch .B) + 1 < healEpoch tL := by
          simp [_root_.CryptoGames.CKA.GameState.allowCorr, hmax_sc] at hallow
          omega
        refine ⟨postLeak_afterCorr_false_of_lt_tH P hpl0 hmax_lt, ?_⟩
        have hep_le : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
          cases P <;> simp
        have hlt_ep : esC.g.epoch P < healEpoch tL := by omega
        simp [hP', hlt_ep]; exact hcr0
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
        exact step_abort_2a hDead
          (by simp [-Prod.mk.injEq, implCKABucket, hooksCKABucket, hooksCKA,
            liftC, _root_.CryptoGames.CKA.corrQuery,
            cImpl, _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.corrImpl,
            habC, hguard, hγC, hcorr,
            StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
            simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp]; rfl)
          rfl

set_option maxHeartbeats 400000 in
theorem step_deliver_2a
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
    (ih : ∀ u esCw' sc' esPw' sp', Sync2a prng Δcka qep tL esCw' sc' esPw' sp' →
      𝒟[contL u esCw' sc'] {true} ≤ 𝒟[contR u esPw' sp'] {true}) :
    𝒟[(simulateQ (cImpl cka Δcka (healEpoch tL))
        (((implCKABucket cka prng fs Δcka qep tL) (.inr (.inl (.inl (.inr (P, c)))))).run esCw)).run sc >>=
        fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[(simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inl (.inr (P, c)))))).run esPw)).run sp >>=
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
  have hqepO : esC.g.epoch P.other ≤ qep := hS.epoch_le_qep P.other
  have habC : esC.abort = false := hsync.abort_C
  have habP : esP.abort = false := hsync.abort_P
  have hwin : esP.g.win = esC.g.win := eraseSt_win hg_eq
  have htrans : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hg_eq P.other c
  have hchall : esP.g.chall = esC.g.chall := eraseSt_chall hg_eq
  have hesC_eq : ({ g := esC.g, h := esC.h, abort := false } :
      EState (VP (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)) = esC :=
    estate_mk_abort_false habC
  have hesP_eq : ({ g := esP.g, h := esP.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) = esP := by
    rcases esP with ⟨g, h, ab⟩; dsimp only at habP; subst ab; rfl
  by_cases hwin0 : esC.g.win = true
  · exact step_pure_2a
      (by simp [-Prod.mk.injEq, implCKABucket, deliverE, habC, hwin0,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, habP, hwin, hwin0,
        StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
      (ih none _ _ _ _ hS)
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      exact step_pure_2a
        (by simp [-Prod.mk.injEq, implCKABucket, deliverE, habC, hwin0, hr,
          StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
        (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, habP, hwin, hwin0, htrans, hr,
          StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp])
        (ih none _ _ _ _ hS)
    | some r =>
      obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
      obtain ⟨ht1, hsend_other, hle_other, _⟩ := hsync.trans_inv r hmem
      rw [hct] at ht1
      rw [hsender] at hsend_other hle_other
      have hsend0 : P.sendsIn c.1.1 = false := by
        rw [ht1]
        have h1 := sendsIn_other P r.pos.epoch
        rw [hsend_other] at h1
        simpa using h1.symm
      have hmax_bound : esC.g.epoch P.other ≤ esC.g.epoch P + 1 := by
        rcases hsync.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
        · have hepP := epoch_eq_of_synced hsync.epoch_S hR P
          have hepO := epoch_eq_of_synced hsync.epoch_S hR P.other
          omega
        · rcases party_cases_of_epoch (max (esC.g.epoch .A) (esC.g.epoch .B)) P with hP | hP
          · have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
              rw [hP, senderOf_other]
            have hS_ep := hsync.epoch_S
            rw [← hP] at hS_ep; rw [← hO] at hR; omega
          · have hO : P.other = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
              rw [hP, receiverOf_other]
            have hS_ep := hsync.epoch_S
            rw [← hO] at hS_ep; rw [← hP] at hR; omega
      have hle : ¬ (esC.g.epoch P + 1 < c.1.1) := by omega
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        obtain ⟨hr_ep, _, _, hO_ep, _, Tm, Im, hct2, hcC, _, hSroot, hcP, hlast⟩ :=
          hsync.deliver_new_info hr hnew
        dsimp only [projP] at hcP
        have hcP' : esP.h.cache (esC.g.epoch P + 1) =
            some (Tm, (esP.g.st P.other).root, (prng.up (esC.g.st P).root Im).2) := hcP
        have hrootO : (esP.g.st P.other).root = some (esC.g.st P.other).root := hS.root_P_eq P.other
        let p := prng.up (esC.g.st P).root Im
        have hp1 : p.1 = (esC.g.st P.other).root := hSroot.symm
        let γP' := (cka.receive (esP.g.st P).γ Tm).1
        have hstartC : ∀ ctx γv,
            ((hooksCKABucket cka prng fs Δcka tL).startRecv ctx P (esC.g.epoch P + 1) γv
              (esC.g.st P).root Tm).run esC.h =
            pure (some (some (γv.map fun γ => (cka.receive γ Tm).1, p.1, fs.initReceiver p.2)),
              esC.h) := fun ctx γv => by
          dsimp only [hooksCKABucket]
          simp [hcC, p, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
        have hstartP : (simulateQ (pImpl prng)
            (((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
              esP.g P (esC.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
            pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h), sp) := by
          dsimp only [hooksPRNGBucketAuthHybrid]
          simp [resolveCorrRoot, hcP', hrootO, p, γP',
            StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure]
        cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none =>
            exact step_pure_2a
              (by simp [-Prod.mk.injEq, implCKABucket, deliverE, vRecv, bucketAuthCfg,
                habC, hwin0, hr, hidC, htcurC, hsend0', hnew, hct2,
                hstartC, hp1, p, hfs, StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                map_eq_bind_pure_comp, hesC_eq])
              (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, vRecv, bucketAuthCfg,
                habP, hwin, hwin0, htrans, hr, hidP, htcurP, hsend0',
                hnew, hct2, hstartP, hfs, StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                map_eq_bind_pure_comp, hesP_eq])
              (ih (some .rejected) _ _ _ _ hS)
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let m := esC.g.epoch P + 1
            let vR' := Function.update (Function.update (esC.g.st P).vR m
              (some (fs.initReceiver p.2))) m (some v')
            let γC_final := if localCKA (mo0 tL) Δcka m then some γP' else none
            let stC_final : VP (Option Γ) T Sig SS RS :=
              { esC.g.st P with tcur := m, γ := γC_final, root := (esC.g.st P.other).root, vR := vR' }
            let stP_final : VP Γ T (Option Sig) SS RS :=
              { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
            have hvRP : (esP.g.st P).vR = (esC.g.st P).vR := hvRP_fn
            have hpos_qep : r.pos.epoch ≤ qep := by omega
            have hP_step : (simulateQ (pImpl prng)
                (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
                  (.inr (.inl (.inl (.inr (P, c)))))).run (esP, winEpC))).run sp =
                pure ((some (.accepted m i' (if esC.g.chall.contains r.pos then none else some m')),
                  ({ esP with g := esP.g.accept P stP_final r.pos }, winEpC)), sp) := by
              simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, commitE, vRecv, bucketAuthCfg,
                habP, hwin, hwin0, htrans, hr, hchall,
                hidP, htcurP, hsend0', hnew, hct2, hvRP, hstartP, hfs,
                m, vR', stP_final, γP', StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                simulateQ_pure, map_eq_bind_pure_comp]
            have hSync2a_accept : ∀ {sc' : _root_.CryptoGames.CKA.GameState Γ T}
                (hSync' : Sync prng Δcka (mo0 tL)
                  { esC with g := esC.g.accept P stC_final r.pos } sc'
                  { projP esP with g := (projP esP).g.accept P stP_final r.pos } sp),
                Sync2a prng Δcka qep tL
                  ({ esC with g := esC.g.accept P stC_final r.pos }, winEpC) sc'
                  ({ esP with g := esP.g.accept P stP_final r.pos }, winEpC) sp := by
              intro sc' hSync'
              refine ⟨hSync', rfl, epoch_accept_le_qep hS.epoch_le_qep P stC_final r.pos hpos_qep,
                fun hlt => ?_⟩
              have hle_max := max_epoch_le_accept esC.g P stC_final r.pos
              exact hS.pre_tH (lt_of_le_of_lt hle_max hlt)
            have hγC_eq : (esC.g.st P).γ =
                if localCKA (mo0 tL) Δcka (esC.g.epoch P) then some (esP.g.st P).γ else none :=
              hsync.γ_C P
            by_cases hloc : localCKA (mo0 tL) Δcka (esC.g.epoch P) = true
            · have hloc_m : localCKA (mo0 tL) Δcka m = true :=
                localCKA_mono (mo0 tL) Δcka hloc (Nat.le_succ _)
              have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
                rw [hγC_eq, hloc]; rfl
              refine step_pure_2a
                (by simp [-Prod.mk.injEq, implCKABucket, deliverE, commitE, vRecv, bucketAuthCfg,
                  hooksCKA, habC, hwin0, hr, hidC, htcurC,
                  hsend0', hnew, hct2, hstartC, hp1, p, hfs, hγC, hloc_m, m, vR', γC_final,
                  stC_final, γP', StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
                  StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure,
                  map_eq_bind_pure_comp])
                hP_step
                (ih _ _ _ _ _ (hSync2a_accept (hsync.accept_new P γP' vR' r.pos hr_ep hO_ep
                  hsync.b_C (fun h => by simp [m, hloc_m] at h))))
            · simp only [Bool.not_eq_true] at hloc
              have hγC : (esC.g.st P).γ = none := by
                rw [hγC_eq, hloc]; rfl
              obtain ⟨hsc_stP, hsc_epP⟩ := hsync.cka_st P (Or.inl hloc)
              obtain ⟨hsc_stO, hsc_epO⟩ := hsync.cka_st P.other (Or.inr (by simpa using hloc))
              have hcanR : sc.canReceive P = true := by
                simp [_root_.CryptoGames.CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
              have hlast_eq : sc.lastMsg = some Tm := hlast hloc
              let sc' := sc.afterReceive P γP'
              have htL_none : (mo0 tL).tL.isNone = false := by
                simp only [localCKA, Bool.or_eq_false_iff] at hloc
                exact hloc.1
              by_cases hfin : healEpoch tL + Δcka ≤ m
              · have hloc_m : localCKA (mo0 tL) Δcka m = true := by
                  simp [localCKA, hfin]
                exact step_pure_2a
                  (by simp [-Prod.mk.injEq, implCKABucket, deliverE, commitE, vRecv, bucketAuthCfg,
                    hooksCKA, liftC, _root_.CryptoGames.CKA.receiveQuery,
                    _root_.CryptoGames.CKA.corrQuery, cImpl, _root_.CryptoGames.CKA.oracleImpl,
                    _root_.CryptoGames.CKA.receiveImpl, _root_.CryptoGames.CKA.corrImpl,
                    habC, hwin0, hr, hidC, htcurC, hsend0', hnew, hct2,
                    hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m, sc',
                    _root_.CryptoGames.CKA.GameState.afterReceive,
                    _root_.CryptoGames.CKA.GameState.finished, hsc_epP, m, vR', γC_final,
                    stC_final, γP', StateT.lift, StateT.run_bind, StateT.run_get,
                    StateT.run_set, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                    simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp])
                  hP_step
                  (ih _ _ _ _ _ (hSync2a_accept (hsync.accept_new (sc' := sc') P γP' vR' r.pos
                    hr_ep hO_ep hsync.b_C (fun h => by simp [m, hloc_m] at h))))
              · have hloc_m : localCKA (mo0 tL) Δcka m = false := by
                  cases tL with
                  | none => simp [mo0_tL] at htL_none
                  | some l =>
                    simp only [healEpoch_some_eq] at hfin
                    simp only [localCKA, mo0_tL, mo0_tH, healEpoch_some_eq]
                    simp [Nat.lt_of_not_ge hfin]
                refine step_pure_2a
                  (by simp [-Prod.mk.injEq, implCKABucket, deliverE, commitE, vRecv, bucketAuthCfg,
                    hooksCKA, liftC, _root_.CryptoGames.CKA.receiveQuery,
                    cImpl, _root_.CryptoGames.CKA.oracleImpl, _root_.CryptoGames.CKA.receiveImpl,
                    habC, hwin0, hr, hidC, htcurC, hsend0', hnew, hct2,
                    hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m, sc',
                    m, vR', γC_final, stC_final, γP', StateT.lift, StateT.run_bind,
                    StateT.run_get, StateT.run_set, StateT.run_pure, StateT.run_modify,
                    simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp])
                  hP_step
                  (ih _ _ _ _ _ (hSync2a_accept (hsync.accept_new (sc' := sc') P γP' vR' r.pos
                    hr_ep hO_ep hsync.b_C fun _ => ?_)))
                simp [sc', _root_.CryptoGames.CKA.GameState.afterReceive, Party.other_ne,
                  hsc_epP, hsc_stO, hsc_epO, hO_ep, m]
      · have hle_ep : r.pos.epoch ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := congrFun hvRP_fn c.1.1
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          exact step_pure_2a
            (by simp [-Prod.mk.injEq, implCKABucket, deliverE, vRecv, bucketAuthCfg,
              habC, hwin0, hr, hidC, htcurC, hsend0, hle, hnew, hvR,
              StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
              simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
            (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, vRecv, bucketAuthCfg,
              habP, hwin, hwin0, htrans, hr, hidP, htcurP, hsend0, hle,
              hnew, hvRP, hvR, StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesP_eq])
            (ih (some .rejected) _ _ _ _ hS)
        | some v =>
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            exact step_pure_2a
              (by simp [-Prod.mk.injEq, implCKABucket, deliverE, vRecv, bucketAuthCfg,
                habC, hwin0, hr, hidC, htcurC, hsend0, hle, hnew, hvR, hfs,
                StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
                simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, hesC_eq])
              (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, vRecv, bucketAuthCfg,
                habP, hwin, hwin0, htrans, hr, hidP, htcurP, hsend0, hle,
                hnew, hvRP, hvR, hfs, StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                map_eq_bind_pure_comp, hesP_eq])
              (ih (some .rejected) _ _ _ _ hS)
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
            have hvRP_all : (esP.g.st P).vR = (esC.g.st P).vR := hvRP_fn
            have hpos_qep : r.pos.epoch ≤ qep := le_trans hle_ep hqepP
            refine step_pure_2a
              (by simp [-Prod.mk.injEq, implCKABucket, deliverE, commitE, vRecv, bucketAuthCfg,
                hooksCKA, habC, hwin0, hr, hidC, htcurC,
                hsend0, hle, hnew, hvR, hfs, vR', StateT.lift, StateT.run_bind, StateT.run_get,
                StateT.run_set, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                simulateQ_pure, map_eq_bind_pure_comp]; rfl)
              (by simp [-Prod.mk.injEq, implPRNGBucketAuth, implPRNGBucketAuthGen, deliverE, commitE, vRecv,
                bucketAuthCfg, habP, hwin, hwin0, htrans, hr, hchall,
                hidP, htcurP, hsend0, hle, hnew, hvRP, hvR, hfs, hvRP_all,
                vR', StateT.lift, StateT.run_bind, StateT.run_get, StateT.run_set,
                StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure,
                map_eq_bind_pure_comp]; rfl)
              (ih _ _ _ _ _ ⟨by simpa only [projP, hidC, htcurC, habC, hidP, htcurP, habP] using
                  hsync.accept_old P vR' r.pos hle_ep, rfl,
                epoch_accept_le_qep hS.epoch_le_qep P _ r.pos hpos_qep, fun hlt => ?_⟩)
            have hle_max := max_epoch_le_accept esC.g P { esC.g.st P with vR := vR' } r.pos
            exact hS.pre_tH (lt_of_le_of_lt hle_max hlt)

set_option maxHeartbeats 400000 in

@[expose] def unsplitRedPRNGAuthBucketHybrid [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq E] [Inhabited E] [SampleableType KC] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
    match ← runPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL t A with
    | none => return false
    | some (_, es, winEp) =>
      match winEp with
      | none => return false
      | some tWin =>
        return (!es.abort && es.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin es.g)

@[expose] def initES_PBucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (σv : Option Sig) (kr : KR) (kc : KC) :
    EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I) :=
  let out := prng.up (prng.init kr) lam
  let vp := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
    (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }, h := {} }


end Hop2aProof

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aBase
