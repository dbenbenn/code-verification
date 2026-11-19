/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import VCVio.OracleComp.EvalDist.Measure

namespace Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aSplit

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


private theorem twoLayer_dead_eq_false
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


@[local simp] private theorem healEpoch_none_eq : healEpoch none = 0 := rfl

@[local simp] private theorem healEpoch_some_eq (l : ℕ) : healEpoch (some l) = l + 2 := rfl

@[local simp] private theorem ltOpt_none_eq (t : ℕ) : ltOpt none t = true := rfl

@[local simp] private theorem ltOpt_some_eq (l t : ℕ) : ltOpt (some l) t = decide (l < t) := rfl

@[local simp] private theorem leak_tL_eq {St Msg C : Type} (g : GameState St Msg C) (e : ℕ) :
    (g.leak e).tL = some (_root_.CryptoGames.SM.maxOpt g.tL e) := rfl

@[local simp] private theorem maxOpt_none_eq (e : ℕ) :
    _root_.CryptoGames.SM.maxOpt none e = e := rfl

@[local simp] private theorem maxOpt_some_eq (cur e : ℕ) :
    _root_.CryptoGames.SM.maxOpt (some cur) e = max cur e := rfl

@[local simp] private theorem afterCorr_epoch_eq {St Msg C : Type} (g : GameState St Msg C) (P Q : Party) :
    (g.afterCorr P).epoch Q = g.epoch Q := rfl


@[local simp] private theorem hooksPRNGBucketAuthHybrid_fsSend [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P t0 ss h m r) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsSend ctx P t0 ss h m r =
      pure (some (fs.send ss h m)) := rfl

@[local simp] private theorem hooksPRNGBucketAuthHybrid_fsRecv [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P t0 rs h e r) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).fsRecv ctx P t0 rs h e r =
      pure (some (fs.receive rs h e)) := rfl

@[local simp] private theorem hooksPRNGBucketAuthHybrid_commit [DecidableEq T] [DecidableEq I]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx P old new) :
    (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).commit ctx P old new =
      pure (some new) := rfl


private theorem postLeak_leak_false_of_lt_tH {St Msg C : Type}
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

private theorem postLeak_afterCorr_false_of_lt_tH {St Msg C : Type}
    {tL : Option ℕ} {g : GameState St Msg C} (P : Party)
    (hpl : postLeak tL g = false) (he : max (g.epoch .A) (g.epoch .B) + 1 < healEpoch tL) :
    postLeak tL (g.afterCorr P) = false := by
  have h := postLeak_leak_false_of_lt_tH hpl he
  dsimp [postLeak, GameState.afterCorr, GameState.leak] at h ⊢
  exact h


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

private def initES_PBucket
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (σv : Option Sig) (kr : KR) (kc : KC) :
    EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I) :=
  let out := prng.up (prng.init kr) lam
  let vp := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
    (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }, h := {} }


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


private theorem evalDist_bind_le_add_of_support_2a {α : Type} (p : ProbComp α)
    (F G₁ G₂ : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F a] {true} ≤ 𝒟[G₁ a] {true} + 𝒟[G₂ a] {true}) :
    𝒟[p >>= F] {true} ≤ 𝒟[p >>= G₁] {true} + 𝒟[p >>= G₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
        Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
        ≤ ∫⁻ u, (𝒟[r u >>= G₁] {true} + 𝒟[r u >>= G₂] {true}) ∂𝒟[query t] :=
          MeasureTheory.lintegral_mono fun u =>
            ih u fun a ha => h a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩)
      _ = (∫⁻ u, 𝒟[r u >>= G₁] {true} ∂𝒟[query t]) +
          (∫⁻ u, 𝒟[r u >>= G₂] {true} ∂𝒟[query t]) :=
          MeasureTheory.lintegral_add_left Measurable.of_discrete _

private def postPBucket (Δcka : ℕ) (tL : Option ℕ)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I) : Bool :=
  match esPw.2 with
  | none => false
  | some tWin =>
    !esPw.1.abort && esPw.1.g.win && authLosingConditionsAvoided (2 + Δcka) tL tWin esPw.1.g

private def frozenInrOut
    (q : (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain) :
    (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q :=
  match q with
  | .inl (.inl (.inl (.inl _))) => none
  | .inl (.inl (.inl (.inr _))) => none
  | .inl (.inl (.inr _)) => none
  | .inl (.inr _) => none
  | .inr _ => none

private theorem implPRNGBucketAuthGen_frozen_inl
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf : Bool)
    (n : unifSpec.Domain)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (pImpl prng)
      (((implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf) (.inl n)).run esPw)).run sp =
    (query (spec := unifSpec) n >>= fun u => pure ((u, esPw), sp)) := by
  simp [implPRNGBucketAuthGen, pImpl, StateT.run_lift, StateT.run_bind, StateT.run_pure,
    simulateQ_bind, simulateQ_query, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]

private theorem implPRNGBucketAuthGen_frozen_inr
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf : Bool)
    (q : (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp : Option ℕ)
    (hfr : es.abort = true ∨ es.g.win = true) :
    ((implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf) (.inr q)).run (es, winEp) =
      pure (frozenInrOut q, (es, winEp)) := by
  rcases q with (((⟨P, m, r0⟩ | x) | x) | x) | P
  · rcases hfr with h | h <;>
      simp [implPRNGBucketAuthGen, frozenInrOut, h, StateT.run_bind, StateT.run_get, StateT.run_pure]
  · simp [implPRNGBucketAuthGen, frozenInrOut, StateT.run_pure]
  · rcases hfr with h | h <;>
      simp [implPRNGBucketAuthGen, frozenInrOut, deliverE, h, StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · have hw : (!es.g.win && es.g.win && (!onf || (decide (x.2.1.1 = (es.g.st x.1).tcur + 1) &&
        !isHonestHdrPRNGBucket es.h x.2.1))) = false := by
      cases es.g.win <;> simp
    rcases hfr with h | h <;>
      simp [implPRNGBucketAuthGen, frozenInrOut, injectE, h, hw, StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · rcases hfr with h | h <;>
      simp [implPRNGBucketAuthGen, frozenInrOut, h, StateT.run_bind, StateT.run_get, StateT.run_pure]

private theorem implPRNGBucketAuthGen_frozen_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk₁ hk₂ : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf₁ onf₂ : Bool)
    {α : Type} (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (winEp : Option ℕ) (sp : PRFPRNG.GameState Sig I K)
    (hfr : es.abort = true ∨ es.g.win = true) :
    (simulateQ (pImpl prng)
      ((simulateQ (implPRNGBucketAuthGen hk₁ Δcka qep maxSkip tL onf₁) oa).run (es, winEp))).run sp =
    (simulateQ (pImpl prng)
      ((simulateQ (implPRNGBucketAuthGen hk₂ Δcka qep maxSkip tL onf₂) oa).run (es, winEp))).run sp := by
  induction oa using OracleComp.inductionOn generalizing sp with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    cases q with
    | inl n =>
      rw [implPRNGBucketAuthGen_frozen_inl prng hk₁ Δcka qep maxSkip tL onf₁ n (es, winEp) sp,
        implPRNGBucketAuthGen_frozen_inl prng hk₂ Δcka qep maxSkip tL onf₂ n (es, winEp) sp]
      simp only [bind_assoc, pure_bind]
      congr 1; funext u
      exact ih u sp
    | inr q' =>
      rw [implPRNGBucketAuthGen_frozen_inr hk₁ Δcka qep maxSkip tL onf₁ q' es winEp hfr,
        implPRNGBucketAuthGen_frozen_inr hk₂ Δcka qep maxSkip tL onf₂ q' es winEp hfr]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact ih (frozenInrOut q') sp

private theorem implPRNGBucketAuthGen_dead_zero
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf : Bool)
    {α : Type} (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K)
    (hfr : esPw.1.abort = true ∨ esPw.1.g.win = true)
    (hpost : postPBucket Δcka tL esPw = false) :
    𝒟[(simulateQ (pImpl prng)
        ((simulateQ (implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf) oa).run esPw)).run sp >>=
        fun r => pure (postPBucket Δcka tL r.1.2)] {true} = 0 := by
  have heq := twoLayer_dead_eq_false
    (pImpl prng)
    (implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf)
    (fun esPw' (_ : PRFPRNG.GameState Sig I K) =>
      (esPw'.1.abort = true ∨ esPw'.1.g.win = true) ∧ postPBucket Δcka tL esPw' = false)
    (fun q ⟨es', winEp'⟩ sp' ⟨hfr', hpost'⟩ r hr => by
      cases q with
      | inl n =>
        rw [implPRNGBucketAuthGen_frozen_inl prng hk Δcka qep maxSkip tL onf n (es', winEp') sp'] at hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        rcases hr with ⟨_, _, rfl⟩
        exact ⟨hfr', hpost'⟩
      | inr q' =>
        rw [implPRNGBucketAuthGen_frozen_inr hk Δcka qep maxSkip tL onf q' es' winEp' hfr'] at hr
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        rcases hr with rfl
        exact ⟨hfr', hpost'⟩)
    oa
    (fun _ esPw' _ => pure (postPBucket Δcka tL esPw'))
    (fun _ esPw' _ ⟨_, hp⟩ => by rw [hp])
    (esL := esPw) (gsL := sp)
    ⟨hfr, hpost⟩
  have h0 : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
  exact (congrArg (fun μ => μ {true}) heq).trans h0

private structure UnsplitInv [DecidableEq T] (Δcka qep : ℕ)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) : Prop where
  abort_false : es.abort = false
  win_false : es.g.win = false
  id_eq : ∀ P, (es.g.st P).id = P
  tcur_eq : ∀ P, (es.g.st P).tcur = es.g.epoch P
  root_some : ∀ P, ((es.g.st P).root).isSome = true
  cache_some : ∀ m Tc σc kc, es.h.cache m = some (Tc, σc, kc) → σc.isSome = true
  epoch_le_qep : ∀ P, es.g.epoch P ≤ qep
  cache_gt : ∀ m, max (es.g.epoch .A) (es.g.epoch .B) < m → es.h.cache m = none
  epoch_le : ∀ P, es.g.epoch P ≤ es.g.epoch P.other + 1
  epoch_sends : ∀ P, es.g.epoch P.other < es.g.epoch P → P.sendsIn (es.g.epoch P) = true
  sender_cur : ∀ P, 1 ≤ es.g.epoch P → P.sendsIn (es.g.epoch P) = true →
    isHonestHdrPRNGBucket es.h (es.g.epoch P, (es.g.st P).curCkaMsg) = true
  trans_inv : ∀ r ∈ es.g.trans,
    r.ct.1.1 = r.pos.epoch ∧ r.pos.epoch ≤ es.g.epoch r.pos.sender ∧
    (1 ≤ r.pos.epoch → isHonestHdrPRNGBucket es.h r.ct.1 = true)
  comp_inv : ∀ pos ∈ es.g.comp, healedBy es.g.tL (2 + Δcka) pos.epoch = false

private theorem UnsplitInv.init [DecidableEq T]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (σ0 : Sig) (kr : KR) (kc : KC) :
    UnsplitInv Δcka qep (initES_PBucket cka prng fs lam (some σ0) kr kc) where
  abort_false := rfl
  win_false := rfl
  id_eq P := by cases P <;> rfl
  tcur_eq P := by cases P <;> rfl
  root_some P := by cases P <;> rfl
  cache_some _ _ _ _ h := by simp [initES_PBucket] at h
  epoch_le_qep _ := Nat.zero_le _
  cache_gt _ _ := rfl
  epoch_le _ := Nat.zero_le _
  epoch_sends _ h := by simp [initES_PBucket] at h
  sender_cur _ h := by simp [initES_PBucket] at h
  trans_inv _ h := by simp [initES_PBucket] at h
  comp_inv _ h := by simp [initES_PBucket] at h

private theorem sendsIn_succ_not_2a (P : Party) (e : ℕ) :
    P.sendsIn (e + 1) = !P.sendsIn e := by
  cases h : P.sendsIn (e + 1)
  · simpa using sendsIn_of_succ_false h
  · simpa using sendsIn_pred_false h

private theorem UnsplitInv.synced_of_sendsIn_succ [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) {P : Party}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true) :
    es.g.epoch P.other = es.g.epoch P ∧
      max (es.g.epoch .A) (es.g.epoch .B) = es.g.epoch P := by
  have heq : es.g.epoch P.other = es.g.epoch P := by
    by_cases hlt1 : es.g.epoch P.other < es.g.epoch P
    · have hs := hI.epoch_sends P hlt1
      have hsucc := sendsIn_succ_not_2a P (es.g.epoch P)
      rw [hs] at hsucc
      simp [hsend] at hsucc
    · by_cases hlt2 : es.g.epoch P < es.g.epoch P.other
      · have hle := hI.epoch_le P.other
        rw [Party.other_other] at hle
        have hop : es.g.epoch P.other = es.g.epoch P + 1 := by omega
        have hs := hI.epoch_sends P.other (by rw [Party.other_other]; exact hlt2)
        rw [hop, sendsIn_other, hsend] at hs
        simp at hs
      · omega
  refine ⟨heq, ?_⟩
  cases P with
  | A =>
    change es.g.epoch .B = es.g.epoch .A at heq
    omega
  | B =>
    change es.g.epoch .A = es.g.epoch .B at heq
    omega

private theorem rootPRNGBucketAuthHybrid_at_tH_mem_support
    [DecidableEq I] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K) (tL : Option ℕ) (t0 : ℕ) (pl : Bool)
    (ik0 : I) (σv0 : Option Sig)
    (h0 : PRNGBucketAuthState T Sig K I) (sp0 : PRFPRNG.GameState Sig I K)
    {out : (Option (Option Sig × K) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hmem : out ∈ support ((simulateQ (pImpl prng)
      ((rootPRNGBucketAuthHybrid prng tL (healEpoch tL) t0 pl ik0 σv0).run h0)).run sp0)) :
    out.1.2.cache = h0.cache ∧
      ∀ σ' kVal, out.1.1 = some (σ', kVal) → σ'.isSome = true := by
  unfold rootPRNGBucketAuthHybrid at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  by_cases h1 : healEpoch tL < t0
  · simp only [h1, ↓reduceIte] at hmem
    rcases hσv : resolveCorrRoot h0 (t0 - 1) σv0 with _ | σ <;>
      · simp only [hσv, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl
        simp
  · simp only [h1, ↓reduceIte] at hmem
    by_cases h2 : (pl || h0.corrRoot.isSome) = true
    · simp only [h2, ↓reduceIte] at hmem
      rcases hσv : resolveCorrRoot h0 (t0 - 1) σv0 with _ | σ
      · simp only [hσv, liftPBucketAuth, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem
        rcases hmem with ⟨⟨qOut, sp1⟩, _, hmem2⟩
        cases qOut <;>
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl
            simp
      · simp only [hσv, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl
        simp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h3 : t0 = healEpoch tL
      · simp only [h3, ↓reduceIte, decide_true, Bool.and_true] at hmem
        cases htL : tL.isSome
        · simp only [htL, Bool.false_eq_true, ↓reduceIte, liftPBucketAuth, StateT.run_bind,
            StateT.run_lift, map_eq_bind_pure_comp, bind_assoc, pure_bind, simulateQ_bind,
            mem_support_bind_iff] at hmem
          rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
          cases qOut1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl
            simp
          | some pOut =>
            rcases pOut with ⟨σOut, kOut⟩
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl
            simp
        · simp only [htL, ↓reduceIte, liftPBucketAuth, StateT.run_bind, StateT.run_lift,
            map_eq_bind_pure_comp, bind_assoc, pure_bind, simulateQ_bind,
            mem_support_bind_iff] at hmem
          rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
          cases qOut1 with
          | none =>
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
            rcases hmem2 with rfl
            simp
          | some kOut =>
            simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc,
              pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem2
            rcases hmem2 with ⟨⟨qOut2, sp2⟩, _, hmem3⟩
            cases qOut2 <;>
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hmem3
                rcases hmem3 with rfl
                simp
      · have hlt : t0 < healEpoch tL := by omega
        simp only [h3, hlt, decide_true, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, liftPBucketAuth, StateT.run_bind, StateT.run_lift,
          map_eq_bind_pure_comp, bind_assoc, pure_bind, simulateQ_bind,
          mem_support_bind_iff] at hmem
        rcases hmem with ⟨⟨qOut1, sp1⟩, _, hmem2⟩
        cases qOut1 with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem2
          rcases hmem2 with rfl
          simp
        | some kOut =>
          simp only [StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp, bind_assoc,
            pure_bind, simulateQ_bind, mem_support_bind_iff] at hmem2
          rcases hmem2 with ⟨⟨qOut2, sp2⟩, _, hmem3⟩
          cases qOut2 <;>
            · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hmem3
              rcases hmem3 with rfl
              simp

private theorem UnsplitInv.record_same [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) {P : Party}
    (hsend0 : P.sendsIn (es.g.epoch P + 1) = false)
    (st' : VP Γ T (Option Sig) SS RS) (m_msg : M) (e_ct : E)
    (hid' : st'.id = P) (htcur' : st'.tcur = es.g.epoch P)
    (hroot' : st'.root = (es.g.st P).root) (hcur' : st'.curCkaMsg = (es.g.st P).curCkaMsg) :
    let hdr : Header T := (es.g.epoch P, (es.g.st P).curCkaMsg)
    let recE : Record M (Header T × E) := ⟨⟨P, es.g.epoch P, es.g.idx P + 1⟩, m_msg, (hdr, e_ct)⟩
    UnsplitInv Δcka qep { es with g := es.g.record (2 + Δcka) P st' recE false } where
  abort_false := hI.abort_false
  win_false := hI.win_false
  id_eq Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, hid']
    · simp [GameState.record, hQ, hI.id_eq Q]
  tcur_eq Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, htcur']
    · simp [GameState.record, hQ, hI.tcur_eq Q]
  root_some Q := by
    by_cases hQ : Q = P
    · subst Q; simp [GameState.record, hroot', hI.root_some P]
    · simp [GameState.record, hQ, hI.root_some Q]
  cache_some := hI.cache_some
  epoch_le_qep := hI.epoch_le_qep
  cache_gt := hI.cache_gt
  epoch_le := hI.epoch_le
  epoch_sends := hI.epoch_sends
  sender_cur Q h1 hs := by
    by_cases hQ : Q = P
    · subst Q
      simp only [GameState.record, Function.update_self, hcur'] at hs ⊢
      exact hI.sender_cur P h1 hs
    · simp only [GameState.record, Function.update_of_ne hQ] at hs ⊢
      exact hI.sender_cur Q h1 hs
  trans_inv r hr := by
    simp only [GameState.record, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨rfl, le_rfl, fun h1 => ?_⟩
      exact hI.sender_cur P h1 (sendsIn_of_succ_false hsend0)
    · exact hI.trans_inv r hr
  comp_inv := comp_inv_record es.g (2 + Δcka) P st' _ false rfl hI.comp_inv

private theorem UnsplitInv.record_new [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) {P : Party}
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hqep : es.g.epoch P + 1 ≤ qep)
    {s₁ : Ctx Γ T (Option Sig) SS RS M E}
    (hs1_st : s₁.st = es.g.st)
    (hs1_win : s₁.win = es.g.win)
    (hs1_ep : s₁.epoch = Function.update es.g.epoch P (es.g.epoch P + 1))
    (hs1_trans : s₁.trans = es.g.trans)
    (hs1_comp : ∀ pos ∈ s₁.comp, healedBy s₁.tL (2 + Δcka) pos.epoch = false)
    (γ' : Γ) (Tm : T) (σ' : Option Sig) (kVal : K) (vS' : Option SS)
    (m_msg : M) (e_ct : E) (h' : PRNGBucketAuthState T Sig K I)
    (hσ' : σ'.isSome = true)
    (hcache' : h'.cache = Function.update es.h.cache (es.g.epoch P + 1) (some (Tm, σ', kVal))) :
    let m := es.g.epoch P + 1
    let st' : VP Γ T (Option Sig) SS RS :=
      { es.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := vS' }
    let recE : Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, ((m, some Tm), e_ct)⟩
    UnsplitInv Δcka qep { es with g := s₁.record (2 + Δcka) P st' recE false, h := h' } := by
  obtain ⟨hepO, hmax⟩ := hI.synced_of_sendsIn_succ hsend
  have hs1P : s₁.epoch P = es.g.epoch P + 1 := by simp [hs1_ep]
  have hs1O : s₁.epoch P.other = es.g.epoch P := by
    rw [hs1_ep, Function.update_of_ne (Party.other_ne P), hepO]
  have hmax1 : max (s₁.epoch .A) (s₁.epoch .B) = es.g.epoch P + 1 := by
    cases P with
    | A =>
      change s₁.epoch .B = es.g.epoch .A at hs1O
      rw [hs1P, hs1O]; omega
    | B =>
      change s₁.epoch .A = es.g.epoch .B at hs1O
      rw [hs1O, hs1P]; omega
  refine
    { abort_false := hI.abort_false
      win_false := by simp [GameState.record, hs1_win, hI.win_false]
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hI.id_eq P]
        · simp [GameState.record, hQ, hs1_st, hI.id_eq Q]
      tcur_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, Party.other_ne P, hs1_st, hs1O, ← hepO, hI.tcur_eq P.other]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hσ']
        · simp [GameState.record, hQ, hs1_st, hI.root_some Q]
      cache_some := fun k Tc σc kc hk => by
        rw [hcache'] at hk
        by_cases hkP : k = es.g.epoch P + 1
        · subst k
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hk
          rcases hk with ⟨_, rfl, _⟩
          exact hσ'
        · simp only [Function.update_of_ne hkP] at hk
          exact hI.cache_some k Tc σc kc hk
      epoch_le_qep := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P, hqep]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, hs1O, ← hepO, hI.epoch_le_qep P.other]
      cache_gt := fun k hk => by
        simp only [GameState.record, hmax1] at hk
        have hne : k ≠ es.g.epoch P + 1 := by omega
        rw [hcache', Function.update_of_ne hne]
        exact hI.cache_gt k (by omega)
      epoch_le := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.record, hs1P, hs1O]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.record, Party.other_other, hs1P, hs1O]; omega
      epoch_sends := fun Q hlt => by
        simp only [GameState.record] at hlt ⊢
        by_cases hQ : Q = P
        · subst Q; rw [hs1P]; exact hsend
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; rw [Party.other_other, hs1P, hs1O] at hlt; omega
      sender_cur := fun Q h1 hs => by
        simp only [GameState.record] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q
          simp [hs1P, isHonestHdrPRNGBucket, hcache']
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q
          rw [hs1O, ← hepO] at h1 hs ⊢
          simp only [Function.update_of_ne (Party.other_ne P), hs1_st]
          have hprev := hI.sender_cur P.other h1 hs
          have hne : es.g.epoch P.other ≠ es.g.epoch P + 1 := by omega
          simpa [isHonestHdrPRNGBucket, hcache', Function.update_of_ne hne] using hprev
      trans_inv := fun r hr => by
        simp only [GameState.record, hs1_trans, List.mem_cons] at hr
        rcases hr with rfl | hr
        · refine ⟨hs1P.symm, le_rfl, fun _ => ?_⟩
          simp [isHonestHdrPRNGBucket, hcache']
        · obtain ⟨ht1, hle_r, hhon_r⟩ := hI.trans_inv r hr
          have hle_max : es.g.epoch r.pos.sender ≤ es.g.epoch P := by
            rw [← hmax]
            cases r.pos.sender with
            | A => exact le_max_left _ _
            | B => exact le_max_right _ _
          have hle_s1 : es.g.epoch r.pos.sender ≤ s₁.epoch r.pos.sender := by
            rw [hs1_ep]
            by_cases hS : r.pos.sender = P
            · subst hS; simp
            · simp [hS]
          refine ⟨ht1, le_trans hle_r hle_s1, fun h1 => ?_⟩
          have hprev := hhon_r h1
          have hne : r.ct.1.1 ≠ es.g.epoch P + 1 := by omega
          simpa [isHonestHdrPRNGBucket, hcache', Function.update_of_ne hne] using hprev
      comp_inv := comp_inv_record s₁ (2 + Δcka) P _ _ false rfl hs1_comp }

private theorem UnsplitInv.accept_old [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) {P : Party} {pos : Pos}
    (hle : pos.epoch ≤ es.g.epoch P)
    (st' : VP Γ T (Option Sig) SS RS)
    (hid' : st'.id = P) (htcur' : st'.tcur = es.g.epoch P)
    (hroot' : st'.root = (es.g.st P).root) (hcur' : st'.curCkaMsg = (es.g.st P).curCkaMsg) :
    UnsplitInv Δcka qep { es with g := es.g.accept P st' pos } := by
  have hep_eq : (es.g.accept P st' pos).epoch = es.g.epoch := by
    funext Q
    by_cases hQ : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, Nat.max_eq_left hle]
    · simp [GameState.accept, GameState.delete, hQ]
  refine
    { abort_false := hI.abort_false
      win_false := hI.win_false
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hid']
        · simp [GameState.accept, GameState.delete, hQ, hI.id_eq Q]
      tcur_eq := fun Q => by
        rw [hep_eq]
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, htcur']
        · simp [GameState.accept, GameState.delete, hQ, hI.tcur_eq Q]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hroot', hI.root_some P]
        · simp [GameState.accept, GameState.delete, hQ, hI.root_some Q]
      cache_some := hI.cache_some
      epoch_le_qep := fun Q => by rw [hep_eq]; exact hI.epoch_le_qep Q
      cache_gt := fun m hm => by rw [hep_eq] at hm; exact hI.cache_gt m hm
      epoch_le := fun Q => by rw [hep_eq]; exact hI.epoch_le Q
      epoch_sends := fun Q hlt => by rw [hep_eq] at hlt ⊢; exact hI.epoch_sends Q hlt
      sender_cur := fun Q h1 hs => by
        rw [hep_eq] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q
          simp only [GameState.accept, GameState.delete, Function.update_self, hcur']
          exact hI.sender_cur P h1 hs
        · simp only [GameState.accept, GameState.delete, Function.update_of_ne hQ]
          exact hI.sender_cur Q h1 hs
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        rw [hep_eq]
        exact hI.trans_inv r hr.1
      comp_inv := comp_inv_accept es.g (2 + Δcka) P st' pos hI.comp_inv }

private theorem UnsplitInv.accept_new [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) {P : Party} {pos : Pos}
    (heq_m : pos.epoch = es.g.epoch P + 1)
    (hle_other : pos.epoch ≤ es.g.epoch P.other)
    (hsendP : P.sendsIn pos.epoch = false)
    (st' : VP Γ T (Option Sig) SS RS)
    (hid' : st'.id = P) (htcur' : st'.tcur = pos.epoch)
    (hroot' : st'.root.isSome = true) :
    UnsplitInv Δcka qep { es with g := es.g.accept P st' pos } := by
  have hepO : es.g.epoch P.other = es.g.epoch P + 1 := by
    have hbound := hI.epoch_le P.other
    rw [Party.other_other] at hbound
    omega
  have hacc_ep : ∀ Q, (es.g.accept P st' pos).epoch Q = es.g.epoch P + 1 := by
    intro Q
    by_cases hQ : Q = P
    · subst Q; simp [GameState.accept, GameState.delete, heq_m]
    · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
      subst Q; simp [GameState.accept, GameState.delete, Party.other_ne P, hepO]
  have hmax_before : max (es.g.epoch .A) (es.g.epoch .B) = es.g.epoch P + 1 := by
    cases P with
    | A =>
      change es.g.epoch .B = es.g.epoch .A + 1 at hepO
      omega
    | B =>
      change es.g.epoch .A = es.g.epoch .B + 1 at hepO
      omega
  refine
    { abort_false := hI.abort_false
      win_false := hI.win_false
      id_eq := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hid']
        · simp [GameState.accept, GameState.delete, hQ, hI.id_eq Q]
      tcur_eq := fun Q => by
        rw [hacc_ep Q]
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, htcur', heq_m]
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q; simp [GameState.accept, GameState.delete, Party.other_ne P, hI.tcur_eq P.other, hepO]
      root_some := fun Q => by
        by_cases hQ : Q = P
        · subst Q; simp [GameState.accept, GameState.delete, hroot']
        · simp [GameState.accept, GameState.delete, hQ, hI.root_some Q]
      cache_some := hI.cache_some
      epoch_le_qep := fun Q => by rw [hacc_ep Q, ← hepO]; exact hI.epoch_le_qep P.other
      cache_gt := fun m hm => by
        rw [hacc_ep .A, hacc_ep .B, max_self] at hm
        exact hI.cache_gt m (by omega)
      epoch_le := fun Q => by rw [hacc_ep Q, hacc_ep Q.other]; omega
      epoch_sends := fun Q hlt => by rw [hacc_ep Q, hacc_ep Q.other] at hlt; omega
      sender_cur := fun Q h1 hs => by
        rw [hacc_ep Q] at h1 hs ⊢
        by_cases hQ : Q = P
        · subst Q
          rw [← heq_m, hsendP] at hs
          simp at hs
        · have hQ' : Q = P.other := by cases P <;> cases Q <;> simp_all [Party.other]
          subst Q
          rw [← hepO] at h1 hs ⊢
          simp only [GameState.accept, GameState.delete, Function.update_of_ne (Party.other_ne P)]
          exact hI.sender_cur P.other h1 hs
      trans_inv := fun r hr => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
        obtain ⟨ht1, hle_r, hhon_r⟩ := hI.trans_inv r hr.1
        have hle_acc : es.g.epoch r.pos.sender ≤ (es.g.accept P st' pos).epoch r.pos.sender := by
          rw [hacc_ep r.pos.sender, ← hmax_before]
          cases r.pos.sender with
          | A => exact le_max_left _ _
          | B => exact le_max_right _ _
        exact ⟨ht1, le_trans hle_r hle_acc, hhon_r⟩
      comp_inv := comp_inv_accept es.g (2 + Δcka) P st' pos hI.comp_inv }

private theorem UnsplitInv.afterCorr [DecidableEq T] {Δcka qep : ℕ}
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) (P : Party)
    (h' : PRNGBucketAuthState T Sig K I) (hcache' : h'.cache = es.h.cache) :
    UnsplitInv Δcka qep { es with g := es.g.afterCorr P, h := h' } where
  abort_false := hI.abort_false
  win_false := hI.win_false
  id_eq := hI.id_eq
  tcur_eq := hI.tcur_eq
  root_some := hI.root_some
  cache_some m Tc σc kc hk := hI.cache_some m Tc σc kc (hcache' ▸ hk)
  epoch_le_qep := hI.epoch_le_qep
  cache_gt m hm := hcache' ▸ hI.cache_gt m hm
  epoch_le := hI.epoch_le
  epoch_sends := hI.epoch_sends
  sender_cur Q h1 hs := by
    have hprev := hI.sender_cur Q h1 hs
    simpa [isHonestHdrPRNGBucket, GameState.afterCorr, GameState.leak, hcache'] using hprev
  trans_inv r hr := by
    simp only [GameState.afterCorr, GameState.leak] at hr ⊢
    obtain ⟨h1, h2, h3⟩ := hI.trans_inv r hr
    exact ⟨h1, h2, fun hge => by simpa [isHonestHdrPRNGBucket, hcache'] using h3 hge⟩
  comp_inv := comp_inv_afterCorr es.g (2 + Δcka) (by omega) P
    (fun r hr => (hI.trans_inv r hr).2.1) hI.comp_inv

private def PostTHLeak {St Msg C : Type} (tL : Option ℕ) (g : GameState St Msg C) : Prop :=
  ∃ l ∈ g.leaks, ltOpt tL l = true ∧ ∃ cur, g.tL = some cur ∧ l ≤ cur

private theorem PostTHLeak.leak {St Msg C : Type} {tL : Option ℕ} {g : GameState St Msg C}
    (hPL : PostTHLeak tL g) (m : ℕ) : PostTHLeak tL (g.leak m) := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  refine ⟨l, List.mem_cons_of_mem _ hl_mem, hlt, max cur m, ?_, le_trans hle (le_max_left _ _)⟩
  simp [GameState.leak, htL, CryptoGames.SM.maxOpt]

private theorem PostTHLeak.afterCorr_preserve {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (hPL : PostTHLeak tL g) (P : Party) :
    PostTHLeak tL (g.afterCorr P) := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  refine ⟨l, List.mem_cons_of_mem _ hl_mem, hlt, max cur (max (g.epoch .A) (g.epoch .B)), ?_,
    le_trans hle (le_max_left _ _)⟩
  simp [GameState.afterCorr, GameState.leak, htL, CryptoGames.SM.maxOpt]

private theorem PostTHLeak.afterCorr_of_ge_tH {St Msg C : Type} {tL : Option ℕ}
    {g : GameState St Msg C} (P : Party)
    (hge : healEpoch tL ≤ max (g.epoch .A) (g.epoch .B)) :
    PostTHLeak tL (g.afterCorr P) := by
  let eMax := max (g.epoch .A) (g.epoch .B)
  let L := CryptoGames.SM.maxOpt g.tL eMax
  have heMax_le : eMax ≤ L := by
    dsimp only [L]
    cases g.tL <;> simp [CryptoGames.SM.maxOpt]
  have hlt : ltOpt tL L = true := by
    cases tL with
    | none => rfl
    | some l =>
      simp only [healEpoch] at hge
      simp only [ltOpt, decide_eq_true_eq]
      omega
  refine ⟨L, ?_, hlt, L, ?_, le_rfl⟩
  · simp [GameState.afterCorr, GameState.leak, L, eMax]
  · simp [GameState.afterCorr, GameState.leak, L, eMax]

private theorem authOK_false_of_postTHLeak {St Msg C : Type} {Δcka : ℕ} {tL : Option ℕ}
    {g g' : GameState St Msg C} (P : Party)
    (hPL : PostTHLeak tL g)
    (hsafe : g.safeInj (2 + Δcka) = true)
    (hleaks : g'.leaks = g.leaks) :
    authLosingConditionsAvoided (2 + Δcka) tL (g.epoch P + 1) g' = false := by
  rcases hPL with ⟨l, hl_mem, hlt, cur, htL, hle⟩
  simp only [GameState.safeInj, htL, healedBy, decide_eq_true_eq] at hsafe
  have hmin : min (g.epoch .A) (g.epoch .B) ≤ g.epoch P := by
    cases P <;> simp
  have hlt_win : l < g.epoch P + 1 := by omega
  have hl_mem' : l ∈ g'.leaks := hleaks ▸ hl_mem
  by_contra htrue
  simp only [Bool.not_eq_false] at htrue
  unfold authLosingConditionsAvoided at htrue
  simp only [Bool.and_eq_true] at htrue
  have hall := List.all_eq_true.mp htrue.1.2 l hl_mem'
  simp [hlt, hlt_win] at hall

private theorem startRecv_main_eq_hybrid_of_honest
    [DecidableEq T] [DecidableEq I] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t0 : ℕ)
    (γ0 : Γ) (σv0 : Option Sig) (Tn : T)
    (h0 : PRNGBucketAuthState T Sig K I)
    (hhon : isHonestHdrPRNGBucket h0 (t0, some Tn) = true)
    (hc_some : ∀ m Tc σc kc, h0.cache m = some (Tc, σc, kc) → σc.isSome = true) :
    ∃ σc' kVal,
      σc'.isSome = true ∧
      ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL t).startRecv ctx P t0 γ0 σv0 Tn).run h0 =
        pure (some (some ((cka.receive γ0 Tn).1, σc', fs.initReceiver kVal)), h0) ∧
      ((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL t).startRecv ctx P t0 γ0 σv0 Tn).run h0 =
        pure (some (some ((cka.receive γ0 Tn).1, σc', fs.initReceiver kVal)), h0) := by
  rcases hcache : h0.cache t0 with _ | ⟨Tc, σc, kVal⟩
  · simp [isHonestHdrPRNGBucket, hcache] at hhon
  · have hTc : Tc = Tn := by simpa [isHonestHdrPRNGBucket, hcache] using hhon
    subst Tc
    have hσc := hc_some t0 Tn σc kVal hcache
    rcases σc with _ | σ
    · simp at hσc
    · refine ⟨some σ, kVal, rfl, ?_, ?_⟩
      · simp [hooksPRNGBucketAuthHybrid, hcache, resolveCorrRoot, StateT.run_bind, StateT.run_get,
          StateT.run_pure]
      · simp [hooksPRNGBucketAuthMain, hcache, resolveCorrRoot, StateT.run_bind, StateT.run_get,
          StateT.run_pure]

private theorem startSendPBucket_body_support_unsplitInv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (bad : Bool) (coins : CCoins)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hI : UnsplitInv Δcka qep es)
    (hsend : P.sendsIn (es.g.epoch P + 1) = true)
    (hqep_m : es.g.epoch P + 1 ≤ qep)
    {out : (Option (Γ × T × Option Sig × SS) × PRNGBucketAuthState T Sig K I) × PRFPRNG.GameState Sig I K}
    (hout : out ∈ support ((simulateQ (pImpl prng)
      ((startSendPBucket_body cka prng fs tL (healEpoch tL) (es.g.epoch P + 1)
        (postLeak tL (epMgmtNew es.g (2 + Δcka) P bad))
        (es.g.st P).γ (es.g.st P).root coins).run es.h)).run sp)) :
    let res := (postSendBucketP fs Δcka P m_msg bad es none out.1, out.2)
    res.1.2.1.abort = true ∨
      ∃ es', res.1.2 = (es', none) ∧ UnsplitInv Δcka qep es' ∧
        (PostTHLeak tL es.g → PostTHLeak tL es'.g) := by
  simp only [startSendPBucket_body, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨⟨⟨rootAns, h₁⟩, sp₁⟩, hroot_mem, hout2⟩
  obtain ⟨hcache1, hsome1⟩ := rootPRNGBucketAuthHybrid_at_tH_mem_support
    prng tL (es.g.epoch P + 1) (postLeak tL (epMgmtNew es.g (2 + Δcka) P bad))
    (cka.send (es.g.st P).γ coins).2.2 (es.g.st P).root es.h sp hroot_mem
  cases rootAns with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    exact Or.inl rfl
  | some pOut =>
    rcases pOut with ⟨σ', kVal⟩
    have hσ' : σ'.isSome = true := hsome1 σ' kVal rfl
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hout2
    rcases hout2 with rfl
    right
    let gP₁ := epMgmtNew es.g (2 + Δcka) P bad
    have hg1_st : gP₁.st = es.g.st := epMgmtNew_st es.g (2 + Δcka) P bad
    have hg1_win : gP₁.win = es.g.win := by
      dsimp only [gP₁, epMgmtNew]; split <;> rfl
    have hg1_ep : gP₁.epoch = Function.update es.g.epoch P (es.g.epoch P + 1) :=
      epMgmtNew_epoch es.g (2 + Δcka) P bad
    have hg1_trans : gP₁.trans = es.g.trans := by
      dsimp only [gP₁, epMgmtNew]; split <;> rfl
    have hg1_comp : ∀ pos ∈ gP₁.comp, healedBy gP₁.tL (2 + Δcka) pos.epoch = false := by
      intro pos hp
      dsimp only [gP₁, epMgmtNew] at hp ⊢
      split at hp
      · rename_i hc
        simp only [hc, ↓reduceIte, GameState.leak] at hp ⊢
        exact healedBy_leak_false _ _ _ _ (hI.comp_inv pos hp)
      · rename_i hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
        exact hI.comp_inv pos hp
    have hg1_idx : gP₁.idx P = 0 := by
      dsimp only [gP₁, epMgmtNew]; simp
    have hg1_epP : gP₁.epoch P = es.g.epoch P + 1 := by
      rw [hg1_ep]; simp
    let cOut := cka.send (es.g.st P).γ coins
    let cache' := Function.update h₁.cache (es.g.epoch P + 1) (some (cOut.2.1, σ', kVal))
    let h' : PRNGBucketAuthState T Sig K I := { h₁ with cache := cache' }
    have hcache' : h'.cache =
        Function.update es.h.cache (es.g.epoch P + 1) (some (cOut.2.1, σ', kVal)) := by
      dsimp only [h', cache', cOut] at hcache1 ⊢
      rw [hcache1]
    have hInv' := UnsplitInv.record_new hI hsend hqep_m hg1_st hg1_win hg1_ep hg1_trans hg1_comp
      cOut.1 cOut.2.1 σ' kVal
      (some (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).1)
      m_msg
      (fs.send (fs.initSender kVal) (es.g.epoch P + 1, some cOut.2.1) m_msg).2
      h' hσ' hcache'
    refine ⟨_, rfl, ?_, ?_⟩
    · dsimp only [gP₁, h', cache', cOut] at hInv'
      rw [hg1_epP, hg1_idx] at hInv'
      exact hInv'
    · intro hPL
      dsimp only [GameState.record, gP₁, epMgmtNew]
      split
      · obtain ⟨l, hl_mem, hlt, cur, htL, hle⟩ := PostTHLeak.leak hPL (es.g.epoch P + 1)
        exact ⟨l, hl_mem, hlt, cur, htL, hle⟩
      · exact hPL

private theorem transmit_support_unsplitInv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (m_msg : M) (r0 : Option CCoins)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    {sp : PRFPRNG.GameState Sig I K}
    (hI : UnsplitInv Δcka qep es)
    {r : (Option (Header T × E) × PRNGBucketAuthEState Γ T Sig SS RS M E K I) × PRFPRNG.GameState Sig I K}
    (hr : r ∈ support ((simulateQ (pImpl prng)
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inl (.inl (P, m_msg, r0))))))).run
        (es, none))).run sp)) :
    r.1.2.1.abort = true ∨
      ∃ es', r.1.2 = (es', none) ∧ UnsplitInv Δcka qep es' ∧
        (PostTHLeak tL es.g → PostTHLeak tL es'.g) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
  · by_cases hqep : qep < es.g.epoch P + 1
    · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, hab0, hwin0, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, GameState.epMgmt, hsend, hqep,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      rcases hr with rfl
      exact Or.inr ⟨es, rfl, hI, id⟩
    · have hqep_m : es.g.epoch P + 1 ≤ qep := by omega
      have hstep := stepP_bucket_transmit_new cka prng fs Δcka qep tL P m_msg r0 es none sp
        hab0 hwin0 (hI.id_eq P) (hI.tcur_eq P) hsend hqep
      change r ∈ support ((simulateQ (pImpl prng)
        (((implPRNGBucketAuth cka prng fs Δcka qep tL (healEpoch tL))
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r0))))))).run (es, none))).run sp) at hr
      rw [hstep] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      rcases hr with ⟨out, hout, rfl⟩
      cases r0 with
      | some coins =>
        rw [startSendPBucket_some_eq] at hout
        exact startSendPBucket_body_support_unsplitInv cka prng fs Δcka qep tL P m_msg true coins
          hI hsend hqep_m hout
      | none =>
        rw [startSendPBucket_none_eq] at hout
        simp only [mem_support_bind_iff] at hout
        rcases hout with ⟨coins, _, hout'⟩
        exact startSendPBucket_body_support_unsplitInv cka prng fs Δcka qep tL P m_msg false coins
          hI hsend hqep_m hout'
  · simp only [Bool.not_eq_true] at hsend
    have hqep0 : ¬ qep < es.g.epoch P := by have := hI.epoch_le_qep P; omega
    have hep : es.g.epMgmt (2 + Δcka) qep P r0.isSome = some es.g := by
      simp [GameState.epMgmt, hsend, hqep0]
    have hidP := hI.id_eq P
    have htcurP := hI.tcur_eq P
    rcases hvS : (es.g.st P).vS with _ | v
    · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, hab0, hwin0, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, hep, vSend, hidP, htcurP, hsend, hvS,
        StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      rcases hr with rfl
      refine Or.inr ⟨_, rfl, ?_, fun hPL => hPL⟩
      have hInv' := UnsplitInv.record_same hI hsend (es.g.st P) m_msg default hidP htcurP rfl rfl
      simpa [htcurP, hab0] using hInv'
    · simp only [implPRNGBucketAuthGen, QueryImpl.add_apply, hab0, hwin0, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte, hep, vSend, hooksPRNGBucketAuthHybrid_fsSend,
        hidP, htcurP, hsend, hvS,
        StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
        pure_bind, bind_assoc, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      rcases hr with rfl
      refine Or.inr ⟨_, rfl, ?_, fun hPL => hPL⟩
      let fe := fs.send v (es.g.epoch P, (es.g.st P).curCkaMsg) m_msg
      have hInv' := UnsplitInv.record_same hI hsend { es.g.st P with vS := some fe.1 } m_msg fe.2
        hidP htcurP rfl rfl
      simpa [fe, hidP, htcurP, hab0] using hInv'

private theorem vRecv_main_hybrid_of_not_newForged
    [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (s : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (rec : Option (Record M (Header T × E)))
    (h0 : PRNGBucketAuthState T Sig K I)
    (hc_some : ∀ m Tc σc kc, h0.cache m = some (Tc, σc, kc) → σc.isSome = true)
    (hnf : (decide (c.1.1 = s.tcur + 1) && !isHonestHdrPRNGBucket h0 c.1) = false) :
    ((vRecv (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c rec).run h0 =
      pure (some none, h0) ∧
     (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c rec).run h0 =
      pure (some none, h0)) ∨
    (∃ st' i' m',
      ((vRecv (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c rec).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0) ∧
       (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c rec).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0)) ∧
      s.id.sendsIn c.1.1 = false ∧
      c.1.1 ≤ s.tcur + 1 ∧
      st'.id = s.id ∧
      st'.tcur = max s.tcur c.1.1 ∧
      st'.curCkaMsg = s.curCkaMsg ∧
      (c.1.1 = s.tcur + 1 → st'.root.isSome = true) ∧
      (c.1.1 ≠ s.tcur + 1 → st'.root = s.root)) := by
  unfold vRecv
  by_cases hsend : s.id.sendsIn c.1.1 = true
  · left; constructor <;> simp only [hsend, Bool.true_or, ↓reduceIte, StateT.run_pure]
  · simp only [Bool.not_eq_true] at hsend
    by_cases hgt : s.tcur + 1 < c.1.1
    · left
      constructor <;>
        simp only [hsend, Bool.false_or, decide_eq_true hgt, ↓reduceIte, StateT.run_pure]
    · have hgt_f : decide (s.tcur + 1 < c.1.1) = false := decide_eq_false hgt
      have hm_fsRecv : (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)).fsRecv =
          (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).fsRecv := rfl
      by_cases hnew : c.1.1 = s.tcur + 1
      · have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = x :=
          fun x y => by split <;> [rfl; contradiction]
        have hhon : isHonestHdrPRNGBucket h0 c.1 = true := by simpa [hnew] using hnf
        rcases hTn : c.1.2 with _ | Tn
        · simp [isHonestHdrPRNGBucket, hTn] at hhon
        · have hc_pair : (c.1.1, some Tn) = c.1 := Prod.ext rfl hTn.symm
          have hhon' : isHonestHdrPRNGBucket h0 (c.1.1, some Tn) = true := hc_pair.symm ▸ hhon
          obtain ⟨σc', kVal, hσc', hsH, hsM⟩ := startRecv_main_eq_hybrid_of_honest
            cka prng fs Δcka qep tL (healEpoch tL) ctx P c.1.1 s.γ s.root Tn h0 hhon' hc_some
          rcases hfs : fs.receive (fs.initReceiver kVal) c.1 c.2 with _ | ⟨v', i', m'⟩
          · left; constructor
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                Function.update_self, hooksPRNGBucketAuthHybrid_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, hTn, StateT.run_bind, hsM, StateT.run_pure, pure_bind,
                Function.update_self, hm_fsRecv, hooksPRNGBucketAuthHybrid_fsRecv, hfs]
          · right
            let s₁ : VP Γ T (Option Sig) SS RS :=
              { s with tcur := c.1.1, γ := (cka.receive s.γ Tn).1, root := σc',
                       vR := Function.update s.vR c.1.1 (some (fs.initReceiver kVal)) }
            refine ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, i', m',
              ⟨?_, ?_⟩, hsend, by omega, rfl, by dsimp [s₁]; omega, rfl,
              fun _ => hσc', fun hne => absurd hnew hne⟩
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                Function.update_self, hooksPRNGBucketAuthHybrid_fsRecv, hfs, s₁]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, hTn, StateT.run_bind, hsM, StateT.run_pure, pure_bind,
                Function.update_self, hm_fsRecv, hooksPRNGBucketAuthHybrid_fsRecv, hfs, s₁]
      · have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = y :=
          fun x y => by split <;> [contradiction; rfl]
        rcases hvR : s.vR c.1.1 with _ | v
        · left; constructor <;>
            simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, StateT.run_bind, StateT.run_pure, pure_bind, hvR]
        · rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · left; constructor
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, StateT.run_pure, pure_bind, hvR,
                hooksPRNGBucketAuthHybrid_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, StateT.run_pure, pure_bind, hvR,
                hm_fsRecv, hooksPRNGBucketAuthHybrid_fsRecv, hfs]
          · right
            refine ⟨{ s with vR := Function.update s.vR c.1.1 (some v') }, i', m',
              ⟨?_, ?_⟩, hsend, by omega, rfl, by dsimp; omega, rfl,
              fun heq => absurd heq hnew, fun _ => rfl⟩
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, StateT.run_pure, pure_bind, hvR,
                hooksPRNGBucketAuthHybrid_fsRecv, hfs]
            · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                hnew_ite, StateT.run_bind, StateT.run_pure, pure_bind, hvR,
                hm_fsRecv, hooksPRNGBucketAuthHybrid_fsRecv, hfs]

private theorem liftH_run
    {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS α : Type}
    (x : HM tspec HS α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun p => pure (p.1, { es with h := p.2 })) :=
  rfl

private theorem commitE_trivial_run
    {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (hcom : ∀ s P old new, hk.commit s P old new = pure (some new))
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) HS) :
    (commitE hk s P old new pos).run es = pure (some (s.accept P new pos), es) := by
  have hAcc_st : { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
    have hup : Function.update (s.accept P new pos).st P new = (s.accept P new pos).st := by
      simp [GameState.accept]
    rw [hup]
  have hes_eq : { es with h := es.h } = es := by cases es; rfl
  simp only [commitE, liftH_run, hcom, StateT.run_bind, StateT.run_pure, pure_bind, hAcc_st, hes_eq]

private theorem deliverE_eq_and_unsplitInv
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) :
    ∃ out es',
      ((deliverE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        fs.maxSkip (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') ∧
      ((deliverE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        fs.maxSkip (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') ∧
      UnsplitInv Δcka qep es' ∧
      es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have hes_h0 : ({ g := es.g, h := es.h, abort := false } :
      EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) = es := by
    cases es; dsimp only at hab0; subst hab0; rfl
  have hes_acc : ∀ (g1 : Ctx Γ T (Option Sig) SS RS M E),
      ({ g := g1, h := es.h, abort := false } :
        EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)) =
      { es with g := g1 } :=
    fun g1 => by cases es; dsimp only at hab0; subst hab0; rfl
  cases hr : es.g.inTransit P.other c with
  | none =>
    refine ⟨none, es, ?_, ?_, hI, rfl, rfl⟩ <;>
      simp only [deliverE, StateT.run_bind, StateT.run_get, pure_bind,
        hab0, hwin0, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hr, StateT.run_pure]
  | some r =>
    obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
    obtain ⟨ht1, hle_other, hhon_r⟩ := hI.trans_inv r hmem
    rw [hct] at ht1 hhon_r
    rw [hsender] at hle_other
    have hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false := by
      by_cases h1 : c.1.1 = (es.g.st P).tcur + 1
      · have hhon : isHonestHdrPRNGBucket es.h c.1 = true := hhon_r (by omega)
        simp [h1, hhon]
      · simp [h1]
    rcases vRecv_main_hybrid_of_not_newForged cka prng fs Δcka qep tL es.g P (es.g.st P) c (some r)
        es.h hI.cache_some hnf with ⟨hvH, hvM⟩ |
        ⟨st', i', m', ⟨hvH, hvM⟩, hsend0, hle1, hid', htcur', hcur', hroot_new, hroot_old⟩
    · refine ⟨some .rejected, es, ?_, ?_, hI, rfl, rfl⟩
      · simp only [deliverE, liftH_run, bucketAuthCfg, StateT.run_bind, StateT.run_get, pure_bind,
          hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvH, hes_h0, StateT.run_pure]
      · simp only [deliverE, liftH_run, bucketAuthCfg, StateT.run_bind, StateT.run_get, pure_bind,
          hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvM, hes_h0, StateT.run_pure]
    · have hcomH := commitE_trivial_run
        (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' r.pos es
      have hcomM := commitE_trivial_run
        (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' r.pos es
      refine ⟨some (.accepted c.1.1 i'
          (if es.g.chall.contains r.pos then none else some m')),
        { es with g := es.g.accept P st' r.pos }, ?_, ?_, ?_, rfl, rfl⟩
      · simp only [deliverE, liftH_run, bucketAuthCfg, StateT.run_bind, StateT.run_get, pure_bind,
          hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvH, hes_h0, hcomH, StateT.run_modify, StateT.run_pure, hes_acc]
      · simp only [deliverE, liftH_run, bucketAuthCfg, StateT.run_bind, StateT.run_get, pure_bind,
          hab0, hwin0, Bool.or_self, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
          hr, hvM, hes_h0, hcomM, StateT.run_modify, StateT.run_pure, hes_acc]
      · rw [hidP] at hid' hsend0
        rw [htcurP] at hle1 htcur' hroot_new hroot_old
        by_cases hnew : r.pos.epoch = es.g.epoch P + 1
        · have htcur_new : st'.tcur = r.pos.epoch := by omega
          exact UnsplitInv.accept_new hI hnew hle_other (ht1 ▸ hsend0) st' hid' htcur_new
            (hroot_new (ht1.trans hnew))
        · have hle_ep : r.pos.epoch ≤ es.g.epoch P := by omega
          have htcur_old : st'.tcur = es.g.epoch P := by omega
          exact UnsplitInv.accept_old hI hle_ep st' hid' htcur_old
            (hroot_old (fun heq => hnew (ht1.symm.trans heq))) hcur'

private theorem injectE_eq_of_isNewForged_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false) :
    ∃ out es',
      ((injectE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') ∧
      ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') ∧
      es'.abort = false ∧
      (es'.g.win = false →
        UnsplitInv Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have hidP := hI.id_eq P
  have htcurP := hI.tcur_eq P
  have hes_h : { es with h := es.h } = es := by cases es; rfl
  by_cases hguard :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
  · refine ⟨none, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩ <;>
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
  · simp only [Bool.not_eq_true] at hguard
    have hsafe0 : es.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
      exact hguard.2
    rcases vRecv_main_hybrid_of_not_newForged cka prng fs Δcka qep tL es.g P (es.g.st P) c none
        es.h hI.cache_some hnf with ⟨hvH, hvM⟩ |
        ⟨st', i', m', ⟨hvH, hvM⟩, hsend0, hle1, hid', htcur', hcur', _, hroot_old⟩
    · refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
      · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, StateT.run_pure]
      · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvM, hes_h, StateT.run_pure]
    · rw [hidP] at hid' hsend0
      rw [htcurP] at hle1 htcur' hroot_old
      have hqep_ok : ¬ (qep + 1 < c.1.1) := by have := hI.epoch_le_qep P; omega
      let pos : Pos := ⟨P.other, c.1.1, i'⟩
      by_cases htriv : es.g.trivial (2 + Δcka) pos = true
      · have hne_succ : c.1.1 ≠ es.g.epoch P + 1 := by
          intro heq
          have htf := trivial_false_of_safeInj es.g (2 + Δcka) P i' hsafe0 hI.comp_inv
          dsimp only [pos] at htriv
          rw [heq] at htriv
          rw [htriv] at htf
          cases htf
        have hle_ep : pos.epoch ≤ es.g.epoch P := by dsimp only [pos]; omega
        have htcur_old : st'.tcur = es.g.epoch P := by omega
        have hcomH := commitE_trivial_run
          (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
          (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
        have hcomM := commitE_trivial_run
          (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
          (fun _ _ _ _ => rfl) es.g P (es.g.st P) st' pos es
        refine ⟨some (.accepted c.1.1 i' (some m')),
          { es with g := es.g.accept P st' pos }, ?_, ?_, hab0,
          fun _ => ⟨UnsplitInv.accept_old hI hle_ep st' hid' htcur_old (hroot_old hne_succ) hcur', rfl, rfl⟩⟩
        · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
            hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, hqep_ok,
            pos, htriv, hcomH, StateT.run_modify, StateT.run_pure]
        · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
            hguard, Bool.false_eq_true, ↓reduceIte, hvM, hes_h, hqep_ok,
            pos, htriv, hcomM, StateT.run_modify, StateT.run_pure]
      · simp only [Bool.not_eq_true] at htriv
        by_cases hinj : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true
        · refine ⟨some .rejected, { es with g := { es.g with win := true } },
            ?_, ?_, hab0, fun hw => by simp at hw⟩
          · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, hqep_ok,
              pos, htriv, hinj, StateT.run_modify, StateT.run_pure]
          · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvM, hes_h, hqep_ok,
              pos, htriv, hinj, StateT.run_modify, StateT.run_pure]
        · simp only [Bool.not_eq_true] at hinj
          refine ⟨some .rejected, es, ?_, ?_, hab0, fun _ => ⟨hI, rfl, rfl⟩⟩
          · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, hqep_ok,
              pos, htriv, hinj, StateT.run_pure]
          · simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
              hguard, Bool.false_eq_true, ↓reduceIte, hvM, hes_h, hqep_ok,
              pos, htriv, hinj, StateT.run_pure]

private theorem healEpoch_lt_of_admissible_ne (Δcka : ℕ) (tL : Option ℕ) (t0 : ℕ)
    (ht0 : 1 ≤ t0)
    (hadm : lastLeakGuessAdmissible (2 + Δcka) tL t0 = true)
    (hne : (tL.isSome && decide (t0 = healEpoch tL)) = false) :
    healEpoch tL < t0 := by
  cases tL with
  | none =>
    simp only [healEpoch]
    omega
  | some l =>
    have hne' : t0 ≠ l + 2 := by
      intro heq
      subst heq
      simp [healEpoch] at hne
    simp [lastLeakGuessAdmissible, healedBy, healEpoch] at hadm ⊢
    omega

private theorem honest_none_of_isHonestHdr_false [DecidableEq T]
    (h0 : PRNGBucketAuthState T Sig K I) (t0 : ℕ) (Tn : T)
    (hhon : isHonestHdrPRNGBucket h0 (t0, some Tn) = false) :
    (match h0.cache t0 with
     | some (tCached, σc, kVal) => if tCached = Tn then some (σc, kVal) else none
     | none => none) = none := by
  rcases hcache : h0.cache t0 with _ | ⟨Tc, σc, kVal⟩
  · rfl
  · have hne : Tc ≠ Tn := by
      intro heq
      subst heq
      simp [isHonestHdrPRNGBucket, hcache] at hhon
    simp [hne]

private theorem vRecv_newForged_cases
    [DecidableEq T] [DecidableEq I] [Inhabited E] [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (s : VP Γ T (Option Sig) SS RS) (c : Header T × E)
    (h0 : PRNGBucketAuthState T Sig K I)
    (hroot : s.root.isSome = true)
    (hqep : s.tcur ≤ qep)
    (hnf : (decide (c.1.1 = s.tcur + 1) && !isHonestHdrPRNGBucket h0 c.1) = true) :
    ((vRecv (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c none).run h0 =
      pure (some none, h0) ∧
     (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c none).run h0 =
      pure (some none, h0)) ∨
    ((vRecv (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c none).run h0 =
      pure (none, h0)) ∨
    (∃ st' i' m',
      (vRecv (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c none).run h0 =
        pure (some (some (st', c.1.1, i', m')), h0) ∧
      (vRecv (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)) ctx P s c none).run h0 =
        pure (some none, h0) ∧
      lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = true ∧
      c.1.1 = s.tcur + 1) := by
  have hnew : c.1.1 = s.tcur + 1 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnf
    exact hnf.1
  have hhon_f : isHonestHdrPRNGBucket h0 c.1 = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnf
    exact hnf.2
  have hgt_f : decide (s.tcur + 1 < c.1.1) = false := decide_eq_false (by omega)
  have hqep_f : decide (qep + 1 < c.1.1) = false := decide_eq_false (by omega)
  have hnew_ite : ∀ {α : Type} (x y : α), (if c.1.1 = s.tcur + 1 then x else y) = x :=
    fun x y => by split <;> [rfl; contradiction]
  rcases hroot_eq : s.root with _ | σ
  · simp [hroot_eq] at hroot
  · unfold vRecv
    by_cases hsend : s.id.sendsIn c.1.1 = true
    · left; constructor <;> simp only [hsend, Bool.true_or, ↓reduceIte, StateT.run_pure]
    · simp only [Bool.not_eq_true] at hsend
      rcases hTn : c.1.2 with _ | Tn
      · left; constructor <;>
          simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            hnew_ite, hTn, StateT.run_bind, StateT.run_pure, pure_bind]
      · have hc_pair : (c.1.1, some Tn) = c.1 := Prod.ext rfl hTn.symm
        have hhon_none := honest_none_of_isHonestHdr_false h0 c.1.1 Tn (hc_pair.symm ▸ hhon_f)
        by_cases hadm : lastLeakGuessAdmissible (2 + Δcka) tL c.1.1 = true
        · by_cases htH : (tL.isSome && decide (c.1.1 = healEpoch tL)) = true
          · have hsH : ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 = pure (none, h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, hqep_f, Bool.not_false, hadm, Bool.and_self, ↓reduceIte, htH,
                StateT.run_pure]
              · have htc_ne : tCached ≠ Tn := by intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hqep_f, Bool.not_false, hadm, Bool.and_self, ↓reduceIte, htH,
                StateT.run_pure]
            right; left
            simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind]
          · simp only [Bool.not_eq_true] at htH
            have hlt_tH : healEpoch tL < c.1.1 :=
              healEpoch_lt_of_admissible_ne Δcka tL c.1.1 (by omega) hadm htH
            have hsM : ((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketAuthMain, StateT.run_bind, StateT.run_get, pure_bind, hcache, htH, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
              · have htc_ne : tCached ≠ Tn := by intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketAuthMain, StateT.run_bind, StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, htH, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
            let kk := cka.receive s.γ Tn
            let p := prng.up σ kk.2
            have hsH : ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
                ctx P c.1.1 s.γ s.root Tn).run h0 =
                pure (some (some (kk.1, some p.1, fs.initReceiver p.2)), h0) := by
              rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
              · simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, hqep_f, Bool.not_false, hadm, Bool.and_self, ↓reduceIte,
                htH, Bool.false_eq_true, decide_eq_true hlt_tH, Bool.or_true,
                hroot_eq, resolveCorrRoot, StateT.run_pure, kk, p]
              · have htc_ne : tCached ≠ Tn := by intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
                simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hqep_f, Bool.not_false, hadm, Bool.and_self, ↓reduceIte,
                htH, Bool.false_eq_true, decide_eq_true hlt_tH, Bool.or_true,
                hroot_eq, resolveCorrRoot, StateT.run_pure, kk, p]
            rcases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with _ | ⟨v', i', m'⟩
            · left
              refine ⟨?_, ?_⟩
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                  Function.update_self, hooksPRNGBucketAuthHybrid_fsRecv, hfs]
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, hTn, StateT.run_bind, hsM, StateT.run_pure, pure_bind]
            · right; right
              let s₁ : VP Γ T (Option Sig) SS RS :=
                { s with tcur := c.1.1, γ := kk.1, root := some p.1,
                         vR := Function.update s.vR c.1.1 (some (fs.initReceiver p.2)) }
              refine ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, i', m',
                ?_, ?_, hadm, hnew⟩
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind,
                  Function.update_self, hooksPRNGBucketAuthHybrid_fsRecv, hfs, s₁]
              · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  hnew_ite, hTn, StateT.run_bind, hsM, StateT.run_pure, pure_bind]
        · simp only [Bool.not_eq_true] at hadm
          have hsH : ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).startRecv
              ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
            rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
            · simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, hadm, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
            · have htc_ne : tCached ≠ Tn := by intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
              simp only [hooksPRNGBucketAuthHybrid, StateT.run_bind, StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hadm, Bool.and_false, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
          have hsM : ((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)).startRecv
              ctx P c.1.1 s.γ s.root Tn).run h0 = pure (some none, h0) := by
            rcases hcache : h0.cache c.1.1 with _ | ⟨tCached, σc, kVal⟩
            · simp only [hooksPRNGBucketAuthMain, StateT.run_bind, StateT.run_get, pure_bind, hcache, hadm, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure]
            · have htc_ne : tCached ≠ Tn := by intro heq; subst heq; simp [isHonestHdrPRNGBucket, hTn, hcache] at hhon_f
              simp only [hooksPRNGBucketAuthMain, StateT.run_bind, StateT.run_get, pure_bind, hcache, htc_ne, ↓reduceIte, hadm, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure]
          left; constructor
          · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, hTn, StateT.run_bind, hsH, StateT.run_pure, pure_bind]
          · simp only [hsend, hgt_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
              hnew_ite, hTn, StateT.run_bind, hsM, StateT.run_pure, pure_bind]

private theorem implPRNGBucketAuthGen_transmit_main_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (x : Party × M × Option CCoins)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) :
    (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
      Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inl (.inl x)))))).run st) =
    (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
      Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inl (.inl x)))))).run st) := by
  have hv : vSend (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)) =
      vSend (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) := rfl
  simp [implPRNGBucketAuthGen, hv]

private theorem implPRNGBucketAuthGen_transmit_forged_eq
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (x : Party × M × Option CCoins)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) :
    (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
      Δcka qep fs.maxSkip tL true) (.inr (.inl (.inl (.inl (.inl x)))))).run st) =
    (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
      Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inl (.inl x)))))).run st) := by
  have hv : vSend (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL)) =
      vSend (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)) := rfl
  simp [implPRNGBucketAuthGen, hv]

private theorem implPRNGBucketAuthGen_chall_eq
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf : Bool)
    (x : Party × M × M × Option CCoins)
    (st : PRNGBucketAuthEState Γ T Sig SS RS M E K I) :
    (((implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf)
      (.inr (.inl (.inl (.inl (.inr x)))))).run st) = pure (none, st) := by
  simp [implPRNGBucketAuthGen, StateT.run_pure]

private theorem deliver_step_all_three
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) :
    ∃ out es',
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL true) (.inr (.inl (.inl (.inr (P, c)))))).run (es, none)) =
        pure (out, (es', none)) ∧
      UnsplitInv Δcka qep es' ∧
      es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks := by
  obtain ⟨out, es', hdH, hdM, hI', htL', hleaks'⟩ :=
    deliverE_eq_and_unsplitInv cka prng fs Δcka qep tL P c hI
  have hdF : ((deliverE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
      fs.maxSkip (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') := hdH
  refine ⟨out, es', ?_, ?_, ?_, hI', htL', hleaks'⟩
  · simp [implPRNGBucketAuthGen, hdH, StateT.lift, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · simp [implPRNGBucketAuthGen, hdM, StateT.lift, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · simp [implPRNGBucketAuthGen, hdF, StateT.lift, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private theorem inject_step_of_isNewForged_false
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = false) :
    (∃ out es',
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es', none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL true) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es', none)) ∧
      UnsplitInv Δcka qep es' ∧ es'.g.tL = es.g.tL ∧ es'.g.leaks = es.g.leaks) ∨
    (∃ out es',
      es'.g.win = true ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es', some c.1.1)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es', some c.1.1))) := by
  obtain ⟨out, es', hiH, hiM, _, hwin_false⟩ :=
    injectE_eq_of_isNewForged_false cka prng fs Δcka qep tL P c hI hnf
  have hiF : ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
      (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (out, es') := hiH
  have hwin0 := hI.win_false
  cases hwin' : es'.g.win
  · obtain ⟨hI', htL', hleaks'⟩ := hwin_false hwin'
    left
    refine ⟨out, es', ?_, ?_, ?_, hI', htL', hleaks'⟩
    · simp [implPRNGBucketAuthGen, hiH, hwin0, hwin', StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · simp [implPRNGBucketAuthGen, hiM, hwin0, hwin', StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · simp [implPRNGBucketAuthGen, hiF, hwin0, hwin', StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · right
    refine ⟨out, es', hwin', ?_, ?_⟩
    · simp [implPRNGBucketAuthGen, hiH, hwin0, hwin', StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · simp [implPRNGBucketAuthGen, hiM, hwin0, hwin', StateT.lift, StateT.run_bind,
        StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private theorem inject_step_of_isNewForged_true
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party) (c : Header T × E)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es)
    (hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true) :
    (∃ out,
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es, none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es, none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL true) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (out, (es, none))) ∨
    ((((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
      pure (none, ({ es with abort := true }, none))) ∨
    (es.g.safeInj (2 + Δcka) = true ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (some .rejected, ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1))) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL true) (.inr (.inl (.inr (P, c))))).run (es, none)) =
        pure (some .rejected, ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1)))) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have htcurP := hI.tcur_eq P
  have hes_h : { es with h := es.h } = es := by cases es; rfl
  by_cases hguard :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka))) = true
  · have hiH : ((injectE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (none, es) := by
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    have hiM : ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (none, es) := by
      simp only [injectE, StateT.run_bind, StateT.run_get, pure_bind, hguard, ↓reduceIte, StateT.run_pure]
    have hiF : ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (none, es) := hiH
    left
    refine ⟨none, ?_, ?_, ?_⟩
    · simp [implPRNGBucketAuthGen, hiH, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · simp [implPRNGBucketAuthGen, hiM, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · simp [implPRNGBucketAuthGen, hiF, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
  · simp only [Bool.not_eq_true] at hguard
    have hsafe0 : es.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
      exact hguard.2
    have hqep_tcur : (es.g.st P).tcur ≤ qep := by rw [htcurP]; exact hI.epoch_le_qep P
    rcases vRecv_newForged_cases cka prng fs Δcka qep tL es.g P (es.g.st P) c es.h
        (hI.root_some P) hqep_tcur hnf with ⟨hvH, hvM⟩ | hvAbort |
        ⟨st', i', m', hvH, _, hadm, hnew⟩
    · have hiH : ((injectE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (some .rejected, es) := by
        simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, StateT.run_pure]
      have hiM : ((injectE (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (some .rejected, es) := by
        simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvM, hes_h, StateT.run_pure]
      have hiF : ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es = pure (some .rejected, es) := hiH
      left
      refine ⟨some .rejected, ?_, ?_, ?_⟩
      · simp [implPRNGBucketAuthGen, hiH, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
          StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
      · simp [implPRNGBucketAuthGen, hiM, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
          StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
      · simp [implPRNGBucketAuthGen, hiF, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
          StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · have hiH : ((injectE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es =
          pure (none, { es with abort := true }) := by
        simp only [injectE, liftH_run, abortE, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvAbort, hes_h, StateT.run_modify, StateT.run_pure]
      right; left
      simp [implPRNGBucketAuthGen, hiH, hwin0, StateT.lift, StateT.run_bind, StateT.run_get,
        StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
    · have hnew_ep : c.1.1 = es.g.epoch P + 1 := by rw [← htcurP]; exact hnew
      have hhon_f : isHonestHdrPRNGBucket es.h c.1 = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnf
        exact hnf.2
      have hqep_ok : ¬ (qep + 1 < c.1.1) := by have := hI.epoch_le_qep P; omega
      have htriv : es.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = false := by
        rw [hnew_ep]
        exact trivial_false_of_safeInj es.g (2 + Δcka) P i' hsafe0 hI.comp_inv
      have hinj : (bucketAuthCfg (M := M) Δcka tL).injectFull c.1.1 = true := hadm
      have hiH : ((injectE (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es =
          pure (some .rejected, { es with g := { es.g with win := true } }) := by
        simp only [injectE, liftH_run, StateT.run_bind, StateT.run_get, pure_bind,
          hguard, Bool.false_eq_true, ↓reduceIte, hvH, hes_h, hqep_ok,
          htriv, hinj, StateT.run_modify, StateT.run_pure]
      have hiF : ((injectE (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
          (2 + Δcka) qep (bucketAuthCfg Δcka tL)) (P, c)).run es =
          pure (some .rejected, { es with g := { es.g with win := true } }) := hiH
      right; right
      refine ⟨hsafe0, ?_, ?_⟩
      · simp [implPRNGBucketAuthGen, hiH, hwin0, hnew_ep, htcurP, hhon_f, StateT.lift,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
      · simp [implPRNGBucketAuthGen, hiF, hwin0, hnew_ep, htcurP, hhon_f, StateT.lift,
          StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private theorem corr_step_cases
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    (P : Party)
    {es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I)}
    (hI : UnsplitInv Δcka qep es) :
    (es.g.corrAllowed P = false ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inr P))).run (es, none)) =
        pure (none, (es, none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false) (.inr (.inr P))).run (es, none)) =
        pure (none, (es, none)) ∧
      (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL true) (.inr (.inr P))).run (es, none)) =
        pure (none, (es, none))) ∨
    (es.g.corrAllowed P = true ∧
      ∃ stOut h',
        UnsplitInv Δcka qep { es with g := es.g.afterCorr P, h := h' } ∧
        (((implPRNGBucketAuthGen (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
          Δcka qep fs.maxSkip tL false) (.inr (.inr P))).run (es, none)) =
          pure (some stOut, ({ es with g := es.g.afterCorr P, h := h' }, none)) ∧
        (((implPRNGBucketAuthGen (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
          Δcka qep fs.maxSkip tL false) (.inr (.inr P))).run (es, none)) =
          pure (some stOut, ({ es with g := es.g.afterCorr P, h := h' }, none)) ∧
        (max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL →
          h' = es.h ∧
          (((implPRNGBucketAuthGen (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
            Δcka qep fs.maxSkip tL true) (.inr (.inr P))).run (es, none)) =
            pure (some stOut, ({ es with g := es.g.afterCorr P, h := es.h }, none)))) := by
  have hab0 := hI.abort_false
  have hwin0 := hI.win_false
  have htcurP := hI.tcur_eq P
  cases hcorr : es.g.corrAllowed P
  · left
    refine ⟨rfl, ?_, ?_, ?_⟩ <;>
      simp [implPRNGBucketAuthGen, hab0, hwin0, hcorr, StateT.run_bind, StateT.run_get, StateT.run_pure]
  · right
    have hrootP := hI.root_some P
    rcases hroot_eq : (es.g.st P).root with _ | σ
    · simp [hroot_eq] at hrootP
    · let stOut := realParty (es.g.st P) (es.g.st P).γ σ (es.g.st P).vS (es.g.st P).vR
      let cond := !decide ((es.g.st P).tcur < healEpoch tL) && es.h.corrRoot.isNone
      let h' : PRNGBucketAuthState T Sig K I :=
        if cond then { es.h with corrRoot := some ((es.g.st P).tcur, σ) } else es.h
      have hcache' : h'.cache = es.h.cache := by dsimp only [h']; split <;> rfl
      have hrevH : ((hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL)).reveal
          es.g P (es.g.st P)).run es.h = pure (some stOut, h') := by
        dsimp only [hooksPRNGBucketAuthHybrid, h', cond, stOut]
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hroot_eq, resolveCorrRoot]
        split <;> simp [StateT.run_bind, StateT.run_modify, StateT.run_pure]
      have hrevM : ((hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL)).reveal
          es.g P (es.g.st P)).run es.h = pure (some stOut, h') := hrevH
      refine ⟨rfl, stOut, h', UnsplitInv.afterCorr hI P h' hcache', ?_, ?_, ?_⟩
      · simp [implPRNGBucketAuthGen, hab0, hwin0, hcorr, hrevH, StateT.lift, StateT.run_bind,
          StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
      · simp [implPRNGBucketAuthGen, hab0, hwin0, hcorr, hrevM, StateT.lift, StateT.run_bind,
          StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]
      · intro hlt_max
        have hep_le : es.g.epoch P ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
          cases P <;> simp
        have htcur_lt : (es.g.st P).tcur < healEpoch tL := by omega
        have hltA : es.g.epoch .A < healEpoch tL := (Nat.le_max_left _ _).trans_lt hlt_max
        have hltB : es.g.epoch .B < healEpoch tL := (Nat.le_max_right _ _).trans_lt hlt_max
        have hh' : h' = es.h := by
          dsimp only [h', cond]
          simp [htcur_lt]
        have hrevF : ((hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL)).reveal
            es.g P (es.g.st P)).run es.h = pure (some stOut, es.h) := by
          simp [hooksPRNGBucketAuthForgedHdr, htcur_lt, hltA, hltB,
            not_le_of_gt htcur_lt, not_le_of_gt hltA, not_le_of_gt hltB,
            hroot_eq, stOut, StateT.run_pure]
        refine ⟨hh', ?_⟩
        simp [implPRNGBucketAuthGen, hab0, hwin0, hcorr, hrevF, StateT.lift, StateT.run_bind,
          StateT.run_get, StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp]

private def runPostPBucket [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR Sig I K)
    (hk : Hooks (PRFPRNG.spec Sig I K) (PRNGBucketAuthState T Sig K I)
      Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS)
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (onf : Bool)
    {α : Type}
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (esPw : PRNGBucketAuthEState Γ T Sig SS RS M E K I)
    (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool :=
  (simulateQ (pImpl prng)
    ((simulateQ (implPRNGBucketAuthGen hk Δcka qep maxSkip tL onf) oa).run esPw)).run sp >>=
    fun r => pure (postPBucket Δcka tL r.1.2)

private theorem unsplit_le_main_of_post_tH_leak
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    {α : Type}
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hI : UnsplitInv Δcka qep es)
    (hPL : PostTHLeak tL es.g) :
    𝒟[runPostPBucket prng (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false oa (es, none) sp] {true} ≤
      𝒟[runPostPBucket prng (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false oa (es, none) sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing es sp with
  | pure a =>
    exact le_rfl
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      dsimp only [runPostPBucket]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc,
        implPRNGBucketAuthGen_frozen_inl prng _ Δcka qep fs.maxSkip tL false n (es, none) sp,
        pure_bind]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun u _ => ih u es sp hI hPL
    | inr q' =>
      rcases q' with (((⟨P, m_msg, r0⟩ | x) | ⟨P, c⟩) | ⟨P, c⟩) | P
      · dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, bind_assoc,
          implPRNGBucketAuthGen_transmit_main_eq cka prng fs Δcka qep tL (P, m_msg, r0) (es, none)]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun r hr => ?_
        rcases transmit_support_unsplitInv cka prng fs Δcka qep tL P m_msg r0 hI hr with
          hab | ⟨es', hes', hI', hPL_imp⟩
        · have hpost : postPBucket Δcka tL r.1.2 = false := by
            rcases hr2 : r.1.2 with ⟨es1, w1⟩
            have hab1 : es1.abort = true := by simpa [hr2] using hab
            cases w1 <;> simp [postPBucket, hab1]
          rw [implPRNGBucketAuthGen_dead_zero prng _ Δcka qep fs.maxSkip tL false (cont r.1.1)
            r.1.2 r.2 (Or.inl hab) hpost]
          exact zero_le
        · rw [hes']
          exact ih r.1.1 es' r.2 hI' (hPL_imp hPL)
      · dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, implPRNGBucketAuthGen_chall_eq, simulateQ_pure, StateT.run_pure,
          pure_bind]
        exact ih none es sp hI hPL
      · obtain ⟨out, es', hdH, hdM, _, hI', htL', hleaks'⟩ :=
          deliver_step_all_three cka prng fs Δcka qep tL P c hI
        have hPL' : PostTHLeak tL es'.g := by
          rcases hPL with ⟨l, hl, hlt, cur, htL0, hle⟩
          exact ⟨l, hleaks' ▸ hl, hlt, cur, htL'.trans htL0, hle⟩
        dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, hdH, hdM, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih out es' sp hI' hPL'
      · by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true
        · rcases inject_step_of_isNewForged_true cka prng fs Δcka qep tL P c hI hnf with
            ⟨out, hiH, hiM, _⟩ | hiAbort | ⟨hsafe0, hiH, _⟩
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact ih out es sp hI hPL
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiAbort,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_dead_zero prng _ Δcka qep fs.maxSkip tL false
              (cont none) ({ es with abort := true }, none) sp (Or.inl rfl) rfl]
            exact zero_le
          · have hauth_f : authLosingConditionsAvoided (2 + Δcka) tL (es.g.epoch P + 1)
                { es.g with win := true } = false :=
              authOK_false_of_postTHLeak P hPL hsafe0 rfl
            have hpost_f : postPBucket Δcka tL
                ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1)) = false := by
              simp [postPBucket, hauth_f]
            dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_dead_zero prng _ Δcka qep fs.maxSkip tL false
              (cont (some .rejected))
              ({ es with g := { es.g with win := true } }, some (es.g.epoch P + 1))
              sp (Or.inr rfl) hpost_f]
            exact zero_le
        · simp only [Bool.not_eq_true] at hnf
          rcases inject_step_of_isNewForged_false cka prng fs Δcka qep tL P c hI hnf with
            ⟨out, es', hiH, hiM, _, hI', htL', hleaks'⟩ | ⟨out, es', hwin', hiH, hiM⟩
          · have hPL' : PostTHLeak tL es'.g := by
              rcases hPL with ⟨l, hl, hlt, cur, htL0, hle⟩
              exact ⟨l, hleaks' ▸ hl, hlt, cur, htL'.trans htL0, hle⟩
            dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact ih out es' sp hI' hPL'
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_frozen_eq prng
              (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
              (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
              Δcka qep fs.maxSkip tL false false (cont out) es' (some c.1.1) sp (Or.inr hwin')]
      · rcases corr_step_cases cka prng fs Δcka qep tL P hI with
          ⟨_, hcH, hcM, _⟩ | ⟨_, stOut, h', hI', hcH, hcM, _⟩
        · dsimp only [runPostPBucket]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
            simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih none es sp hI hPL
        · dsimp only [runPostPBucket]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
            simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih (some stOut) { es with g := es.g.afterCorr P, h := h' } sp hI'
            (PostTHLeak.afterCorr_preserve hPL P)

private theorem unsplit_le_main_add_forgedHdr_from
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ)
    {α : Type}
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) α)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGBucketAuthState T Sig K I))
    (sp : PRFPRNG.GameState Sig I K)
    (hI : UnsplitInv Δcka qep es) :
    𝒟[runPostPBucket prng (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
        Δcka qep fs.maxSkip tL false oa (es, none) sp] {true} ≤
      𝒟[runPostPBucket prng (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
          Δcka qep fs.maxSkip tL false oa (es, none) sp] {true} +
        𝒟[runPostPBucket prng (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
          Δcka qep fs.maxSkip tL true oa (es, none) sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing es sp with
  | pure a =>
    dsimp only [runPostPBucket, postPBucket]
    simp
  | query_bind q cont ih =>
    cases q with
    | inl n =>
      dsimp only [runPostPBucket]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, bind_assoc,
        implPRNGBucketAuthGen_frozen_inl prng _ Δcka qep fs.maxSkip tL _ n (es, none) sp,
        pure_bind]
      exact evalDist_bind_le_add_of_support_2a _ _ _ _ fun u _ => ih u es sp hI
    | inr q' =>
      rcases q' with (((⟨P, m_msg, r0⟩ | x) | ⟨P, c⟩) | ⟨P, c⟩) | P
      · dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, bind_assoc,
          implPRNGBucketAuthGen_transmit_main_eq cka prng fs Δcka qep tL (P, m_msg, r0) (es, none),
          implPRNGBucketAuthGen_transmit_forged_eq cka prng fs Δcka qep tL (P, m_msg, r0) (es, none)]
        refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun r hr => ?_
        rcases transmit_support_unsplitInv cka prng fs Δcka qep tL P m_msg r0 hI hr with
          hab | ⟨es', hes', hI', _⟩
        · have hpost : postPBucket Δcka tL r.1.2 = false := by
            rcases hr2 : r.1.2 with ⟨es1, w1⟩
            have hab1 : es1.abort = true := by simpa [hr2] using hab
            cases w1 <;> simp [postPBucket, hab1]
          rw [implPRNGBucketAuthGen_dead_zero prng _ Δcka qep fs.maxSkip tL false (cont r.1.1)
            r.1.2 r.2 (Or.inl hab) hpost]
          exact zero_le
        · rw [hes']
          exact ih r.1.1 es' r.2 hI'
      · dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, implPRNGBucketAuthGen_chall_eq, simulateQ_pure, StateT.run_pure,
          pure_bind]
        exact ih none es sp hI
      · obtain ⟨out, es', hdH, hdM, hdF, hI', _, _⟩ :=
          deliver_step_all_three cka prng fs Δcka qep tL P c hI
        dsimp only [runPostPBucket]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind, hdH, hdM, hdF, simulateQ_pure, StateT.run_pure, pure_bind]
        exact ih out es' sp hI'
      · by_cases hnf : (decide (c.1.1 = (es.g.st P).tcur + 1) && !isHonestHdrPRNGBucket es.h c.1) = true
        · rcases inject_step_of_isNewForged_true cka prng fs Δcka qep tL P c hI hnf with
            ⟨out, hiH, hiM, hiF⟩ | hiAbort | ⟨_, hiH, hiF⟩
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM, hiF,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact ih out es sp hI
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiAbort,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_dead_zero prng _ Δcka qep fs.maxSkip tL false
              (cont none) ({ es with abort := true }, none) sp (Or.inl rfl) rfl]
            exact zero_le
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiF,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_frozen_eq prng
              (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
              (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep tL (healEpoch tL))
              Δcka qep fs.maxSkip tL false true (cont (some .rejected))
              { es with g := { es.g with win := true } } (some (es.g.epoch P + 1)) sp (Or.inr rfl)]
            exact le_add_self
        · simp only [Bool.not_eq_true] at hnf
          rcases inject_step_of_isNewForged_false cka prng fs Δcka qep tL P c hI hnf with
            ⟨out, es', hiH, hiM, hiF, hI', _, _⟩ | ⟨out, es', hwin', hiH, hiM⟩
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM, hiF,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact ih out es' sp hI'
          · dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hiH, hiM,
              simulateQ_pure, StateT.run_pure, pure_bind]
            rw [implPRNGBucketAuthGen_frozen_eq prng
              (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep tL (healEpoch tL))
              (hooksPRNGBucketAuthMain cka prng fs Δcka qep tL (healEpoch tL))
              Δcka qep fs.maxSkip tL false false (cont out) es' (some c.1.1) sp (Or.inr hwin')]
            exact le_self_add
      · rcases corr_step_cases cka prng fs Δcka qep tL P hI with
          ⟨_, hcH, hcM, hcF⟩ | ⟨_, stOut, h', hI', hcH, hcM, hlt_imp⟩
        · dsimp only [runPostPBucket]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM, hcF,
            simulateQ_pure, StateT.run_pure, pure_bind]
          exact ih none es sp hI
        · by_cases hlt_max : max (es.g.epoch .A) (es.g.epoch .B) < healEpoch tL
          · obtain ⟨hh', hcF⟩ := hlt_imp hlt_max
            subst hh'
            dsimp only [runPostPBucket]
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM, hcF,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact ih (some stOut) { es with g := es.g.afterCorr P, h := es.h } sp hI'
          · have hge_max : healEpoch tL ≤ max (es.g.epoch .A) (es.g.epoch .B) := by omega
            have hPL' : PostTHLeak tL (es.g.afterCorr P) := PostTHLeak.afterCorr_of_ge_tH P hge_max
            have hle_main := unsplit_le_main_of_post_tH_leak cka prng fs Δcka qep tL
              (cont (some stOut)) { es with g := es.g.afterCorr P, h := h' } sp hI' hPL'
            dsimp only [runPostPBucket] at hle_main ⊢
            simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
              OracleQuery.cont_query, id_map, StateT.run_bind, hcH, hcM,
              simulateQ_pure, StateT.run_pure, pure_bind]
            exact hle_main.trans le_self_add

theorem unsplit_prng_false_le_main_add_forgedHdr
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} ≤
      𝒟[PRFPRNG.branch prng false
          (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} +
        𝒟[PRFPRNG.branch prng false
          (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep tL (healEpoch tL) A)] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng = pImpl prng := rfl
  cases tL with
  | none =>
    have hU : PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep none (healEpoch none) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep none (healEpoch none))
            Δcka qep fs.maxSkip none false A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP_zero prng kr)) := by
      unfold PRFPRNG.branch unsplitRedPRNGAuthBucketHybrid runPRNGAuthBucketHybrid
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_none_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    have hM : PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep none (healEpoch none) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthMain cka prng fs Δcka qep none (healEpoch none))
            Δcka qep fs.maxSkip none false A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP_zero prng kr)) := by
      unfold PRFPRNG.branch redPRNGAuthBucketHybridMain
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_none_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    have hF : PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep none (healEpoch none) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep none (healEpoch none))
            Δcka qep fs.maxSkip none true A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP_zero prng kr)) := by
      unfold PRFPRNG.branch redPRNGAuthBucketHybridForgedHdr
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_none_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    rw [hU, hM, hF]
    refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun kr _ => ?_
    refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun kc _ => ?_
    exact unsplit_le_main_add_forgedHdr_from cka prng fs Δcka qep none A _ _
      (UnsplitInv.init cka prng fs lam Δcka qep (prng.up (prng.init kr) lam).1 kr kc)
  | some l =>
    have hU : PRFPRNG.branch prng false
        (unsplitRedPRNGAuthBucketHybrid cka prng fs lam Δcka qep (some l) (healEpoch (some l)) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthHybrid cka prng fs Δcka qep (some l) (healEpoch (some l)))
            Δcka qep fs.maxSkip (some l) false A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP prng lam (some l) kr)) := by
      unfold PRFPRNG.branch unsplitRedPRNGAuthBucketHybrid runPRNGAuthBucketHybrid
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_some_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_some cka prng fs lam l, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    have hM : PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridMain cka prng fs lam Δcka qep (some l) (healEpoch (some l)) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthMain cka prng fs Δcka qep (some l) (healEpoch (some l)))
            Δcka qep fs.maxSkip (some l) false A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP prng lam (some l) kr)) := by
      unfold PRFPRNG.branch redPRNGAuthBucketHybridMain
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_some_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_some cka prng fs lam l, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    have hF : PRFPRNG.branch prng false
        (redPRNGAuthBucketHybridForgedHdr cka prng fs lam Δcka qep (some l) (healEpoch (some l)) A) =
        ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
          runPostPBucket prng (hooksPRNGBucketAuthForgedHdr cka prng fs Δcka qep (some l) (healEpoch (some l)))
            Δcka qep fs.maxSkip (some l) true A
            (initES_PBucket cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc, none)
            (initSP prng lam (some l) kr)) := by
      unfold PRFPRNG.branch redPRNGAuthBucketHybridForgedHdr
        runPRNGAuthBucketHybridGen initES_PBucket runPostPBucket
      simp only [healEpoch_some_eq, StateT.run'_eq, hpImpl, StateT.run_bind, simulateQ_bind,
        initPRNGBucket_run_some cka prng fs lam l, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
      congr 1; funext kr; congr 1; funext kc; congr 1; funext r
      rcases r with ⟨⟨a, es, winEp⟩, sp'⟩
      cases winEp <;> simp [postPBucket, simulateQ_pure, StateT.run_pure]
    rw [hU, hM, hF]
    refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun kr _ => ?_
    refine evalDist_bind_le_add_of_support_2a _ _ _ _ fun kc _ => ?_
    exact unsplit_le_main_add_forgedHdr_from cka prng fs Δcka qep (some l) A _ _
      (UnsplitInv.init cka prng fs lam Δcka qep (prng.up (prng.init kr) lam).1 kr kc)

end Hop2aProof

end

end Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthHop2aSplit
