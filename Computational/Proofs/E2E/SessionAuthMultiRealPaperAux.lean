/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Proofs.ReductionDsl.SM.RedFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthRouter -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Start -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.E2E.SessionAuthLazy
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Auxiliary Multi-Session Invariant and Eager-Key Helpers for `SessionAuthMultiRealPaper`

Provides `sessTag`, `pubFsSessImpl`, `AllSessLt`, `MultiSessIdxInv`, the `redFSAuthDFPaperMulti`
off-range bound, and eager local key-sampling helpers for `localAuthDFPaper_le_multiSessRealWinProb`.-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthMultiRealPaperAux

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (Config GameState Pos Record RecvResult authLosingConditionsAvoided
  healedBy lastLeakGuessAdmissible)
open _root_.CryptoGames.SM.Engine (EState VP Policy Hooks HM TComp vSend vRecv transmitE challE
  deliverE injectE commitE abortE coinsE authOut liftH)
open _root_.CryptoGames.SM.Construction (FSMultiBook FSMultiSpec FSMultiState Header Mode PartyState
  hooksFSMulti initFSMultiRaw liftFSMulti lookupMultiF mkParties realParty
  regSessMulti regSessOptMulti rootFSMulti sampleT)
open _root_.CryptoGames.SM.Construction.AuthL11 (EStateL LState eraseSt evalDist_bind_eq_zero
  hooksLocal initLocal lImpl localAuthDFPaper lookupFL regSess regSessOf rootL runLocDFPaper)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF specDF corrEPaper deliverForgeE implEDFPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lAead lAeadR lChainPRG lFS lIdeal lPubOf)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (fwd fwd_inl fwd_inr lazyInit multiSessSpec
  sessLift sessLift_inl sessLift_inr sessLiftCore sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsImpl fsInit fsSpec)

/-! ### 1. Multi-Session `pubFsSessImpl` Fusion (`sessLift impl ∘ sessTag`) -/

@[expose] def sessTag {Pt : Type} {ℓ : ℕ} (s : ℕ) :
    QueryImpl
      (unifSpec + fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)))
  | .inl n => liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inl n))
  | .inr q => liftM (OracleSpec.query (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) (.inr ⟨s, q⟩))

theorem simulateQ_sessLift_sessTag {Pt : Type} {ℓ : ℕ} {σ α : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp))
    (s : ℕ)
    (inner : OracleComp (unifSpec + fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) α)
    (tbl : ℕ → σ) :
    (simulateQ (sessLift impl) (simulateQ (sessTag s) inner)).run tbl =
      (fun z => (z.1, Function.update tbl s z.2)) <$> (simulateQ (fwd impl) inner).run (tbl s) := by
  induction inner using OracleComp.inductionOn generalizing tbl with
  | pure a => simp
  | query_bind x k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    rcases x with n | q
    · simp only [add_apply_inl, sessTag, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, sessLift_inl, fwd_inl, QueryImpl.ofLift_eq_id',
        PFunctor.Handler.liftTarget_apply, PFunctor.selfMonomial_B, QueryImpl.id'_apply,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, map_bind, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u tbl
    · simp only [add_apply_inr, sessTag, StateT.run_bind, fwd_inr, map_bind]
      have hstep :
          (simulateQ (sessLift impl) (liftM (OracleSpec.query
            (spec := unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
              (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32))
            (.inr ⟨s, q⟩)))).run tbl =
          (fun r => (r.1, Function.update tbl s r.2)) <$> (impl q).run (tbl s) := by
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          sessLift_inr, sessLiftCore, StateT.run_mk]
        rfl
      erw [hstep]
      simp only [bind_map_left]
      refine bind_congr fun z => ?_
      have hget : Function.update tbl s z.2 s = z.2 := Function.update_self s z.2 tbl
      rw [ih z.1 (Function.update tbl s z.2), hget]
      simp [Function.update_idem]

@[expose] def pubFsSessImpl {Pt : Type} {ℓ : ℕ} {σ : Type}
    (impl : QueryImpl (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (StateT σ ProbComp)) :
    QueryImpl
      (_root_.CryptoGames.FSAEAD.spec
        (_root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (_root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (StateT (Bool × σ) ProbComp) :=
  fun q => StateT.mk fun (ended0, h0) => do
    let ((ans, ended0'), h0') ←
      (simulateQ (fwd impl)
        ((_root_.CryptoGames.FSAEAD.pubRedImpl
          (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
          (AD := Header Pt) (M := Plain ℓ)
          (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf protoSignalCodec c.2)
          (.inr q)).run ended0)).run h0
    return (ans, (ended0', h0'))

/-! ### 2. `AllSessLt` Combinators for `sessOffRange M_sess` -/

inductive AllSessLt (M_sess : ℕ) {SS RS T M E : Type} :
    {α : Type} →
      OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α →
      Prop where
  | pure {α : Type} (a : α) : AllSessLt M_sess (pure a)
  | coin {α : Type} (n : ℕ)
      (k : Fin (n + 1) →
        OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) :
      (∀ u, AllSessLt M_sess (k u)) →
      AllSessLt M_sess
        (liftM (OracleSpec.query
          (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
          (.inl n)) >>= k)
  | sess {α : Type} (s : ℕ) (hs : s < M_sess)
      (q_fs : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
      (k : (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)).Range (.inr ⟨s, q_fs⟩) →
        OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) :
      (∀ u, AllSessLt M_sess (k u)) →
      AllSessLt M_sess
        (liftM (OracleSpec.query
          (spec := unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E))
          (.inr ⟨s, q_fs⟩)) >>= k)

theorem AllSessLt.bind_support {M_sess : ℕ} {SS RS T M E α β : Type}
    {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    {k : α → OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) β}
    (hoa : AllSessLt M_sess oa)
    (hk : ∀ a ∈ support oa, AllSessLt M_sess (k a)) :
    AllSessLt M_sess (oa >>= k) := by
  induction hoa with
  | pure a =>
    rw [pure_bind]
    exact hk a (by simp)
  | coin n r _ ih =>
    rw [bind_assoc]
    refine .coin n _ fun u => ih u fun a ha => hk a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_query _ u, ha⟩
  | sess s hs q_fs r _ ih =>
    rw [bind_assoc]
    refine .sess s hs q_fs _ fun u => ih u fun a ha => hk a ?_
    rw [mem_support_bind_iff]
    exact ⟨u, mem_support_query _ u, ha⟩

theorem AllSessLt.map {M_sess : ℕ} {SS RS T M E α β : Type}
    (f : α → β)
    {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    (hoa : AllSessLt M_sess oa) :
    AllSessLt M_sess (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact hoa.bind_support fun a _ => .pure (f a)

set_option synthInstance.maxHeartbeats 200000 in
theorem AllSessLt.liftProbComp {M_sess : ℕ} {SS RS T M E α : Type}
    (c : ProbComp α) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      (liftM c :
        OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α) := by
  induction c using OracleComp.inductionOn with
  | pure a => simpa using AllSessLt.pure a
  | query_bind n r ih =>
    change AllSessLt M_sess (simulateQ _ (liftM (query n) >>= r))
    simp only [simulateQ_bind, simulateQ_query]
    exact .coin n _ fun u => ih u

set_option synthInstance.maxHeartbeats 200000 in
private theorem AllSessLt.ofSampleT {M_sess : ℕ} {SS RS T M E α : Type} [SampleableType α] :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      (sampleT (tspec := FSMultiSpec SS RS T M E) α) := by
  unfold sampleT FSMultiSpec
  exact AllSessLt.liftProbComp ($ᵗ α : ProbComp α)

private theorem AllSessLt.liftSampleT {M_sess : ℕ} {SS RS T M E HS α : Type}
    [SampleableType α] (h : HS) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      ((StateT.lift (sampleT (tspec := FSMultiSpec SS RS T M E) α)).run h) := by
  unfold StateT.lift
  exact AllSessLt.ofSampleT.bind_support fun _ _ => .pure _

theorem AllSessLt.to_isQueryBoundP {M_sess : ℕ} {SS RS T M E α : Type}
    {oa : OracleComp (unifSpec + multiSessSpec (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)) α}
    (hoa : AllSessLt M_sess oa) :
    oa.IsQueryBoundP (fun t => sessOffRange M_sess t = true) 0 := by
  induction hoa with
  | pure a =>
    exact isQueryBoundP_pure _ _ 0
  | coin n r _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    have hfalse : sessOffRange M_sess
        (.inl n : ℕ ⊕ (_ : ℕ) × (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain) = false := rfl
    refine ⟨Or.inl (by simp [hfalse]), fun u => ?_⟩
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    exact ih u
  | sess s hs q_fs r _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    have hfalse : sessOffRange M_sess (.inr ⟨s, q_fs⟩) = false := by
      simp [sessOffRange]; omega
    refine ⟨Or.inl (by simp [hfalse]), fun u => ?_⟩
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    exact ih u

theorem liftFSMulti_allSessLt {T RSt K I SS RS M E α : Type} {M_sess sIdx : ℕ}
    (hs : sIdx < M_sess) (h : FSMultiState T RSt K I E)
    (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    AllSessLt M_sess ((liftFSMulti (T := T) sIdx x).run h) := by
  unfold liftFSMulti StateT.lift
  refine AllSessLt.bind_support ?_ fun a _ => .pure (a, h)
  induction x using OracleComp.inductionOn with
  | pure a => simpa using AllSessLt.pure a
  | query_bind t r ih =>
    rw [simulateQ_query_bind]
    rcases t with n | qfs
    · exact .coin n _ fun u => ih u
    · exact .sess sIdx hs qfs _ fun u => ih u

private theorem mem_support_liftSampleT {SS RS T M E HS α : Type} [SampleableType α]
    (h : HS) {w : α × HS}
    (hw : w ∈ support ((StateT.lift (sampleT (tspec := FSMultiSpec SS RS T M E) α)).run h)) :
    w.2 = h := by
  change w ∈ support (sampleT (tspec := FSMultiSpec SS RS T M E) α >>= fun a => pure (a, h)) at hw
  rw [mem_support_bind_iff] at hw
  obtain ⟨_, _, hw⟩ := hw
  simp only [support_pure, Set.mem_singleton_iff] at hw
  exact (Prod.ext_iff.mp hw).2

private theorem mem_support_liftFSMulti {T RSt K I SS RS M E α : Type}
    (sIdx : ℕ) (h : FSMultiState T RSt K I E)
    (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α)
    {u : α × FSMultiState T RSt K I E}
    (hu : u ∈ support ((liftFSMulti (T := T) sIdx x).run h)) :
    u.2 = h := by
  unfold liftFSMulti at hu
  change u ∈ support (simulateQ _ x >>= fun a => pure (a, h)) at hu
  rw [mem_support_bind_iff] at hu
  obtain ⟨_, _, hu⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff] at hu
  exact (Prod.ext_iff.mp hu).2

/-! ### 3. Zero-Probability Shortcuts & Lookahead Inject Helper -/

theorem localAuthDFPaper_eq_zero_of_not_validGuess
    {KC Γ CCoins T I KR Sig K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = false)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthDFPaper cka prng fs lam Δcka qep tL t A] {true} = 0 := by
  unfold localAuthDFPaper runLocDFPaper
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  rcases r with ⟨vs, h⟩
  cases vs with
  | none => simp
  | some vp =>
    rcases vp with ⟨vA, vB⟩
    refine evalDist_bind_eq_zero _ _ fun r' _ => ?_
    have hout : authOut (2 + Δcka) (⟨true, tL, t⟩ : Mode).policy r'.2 = false := by
      simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
    simp [hout]

theorem injectL_lookahead_some_accepted {MK CK AD M C : Type}
    [SampleableType MK] [SampleableType CK] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → _root_.PRGScheme CK (CK × MK)) (maxSkip : ℕ)
    {k : CK}
    {stR : _root_.CryptoGames.FSAEAD.State
      (_root_.CryptoGames.FSAEAD.RatchetSenderState CK)
      (_root_.CryptoGames.FSAEAD.RatchetReceiverState CK MK) AD M (ℕ × C)}
    {sM sL : _root_.CryptoGames.FSAEAD.Thm5.HSt CK MK AD M C}
    (hsync : _root_.CryptoGames.FSAEAD.Thm5.Ends.SyncRML ae G k stR sM sL)
    (a : AD) (i : ℕ) (e : C) (msg : M)
    (hend : sM.1.ended = false)
    (hany : (sM.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false)
    (hcont : i ∉ sM.1.skipped)
    (hout : ¬ (i ≤ sM.1.receiverIdx ∨ maxSkip < i - sM.1.receiverIdx - 1))
    (_hlt : sM.1.lastSentIdx < i)
    (hdec : ae.dec (_root_.CryptoGames.FSAEAD.Thm5.Ends.keyAt G k (i - 1)) (i, a) e = some msg) :
    ∃ sL',
      (_root_.CryptoGames.FSAEAD.Thm5.injectH ae G maxSkip
        (_root_.CryptoGames.FSAEAD.Thm5.hp 0 0 true) (_root_.CryptoGames.FSAEAD.Thm5.DG G)
        (none : Option (_root_.CryptoGames.FSAEAD.Thm5.SpecialOps AD M C ProbComp))
        (a, i, e)).run sL = pure (some (.accepted i (some msg)), sL') := by
  have hsL1 : sL.1 = { sM.1 with keys := sL.1.keys } := hsync.sL_eq
  have hendL : sL.1.ended = false := by rw [hsL1]; exact hend
  have hanyL : (sL.1.inTransit.any (fun r => r.ad == a && r.ct == (i, e))) = false := by
    rw [hsL1]; exact hany
  have hcontL : i ∉ sL.1.skipped := by rw [hsL1]; exact hcont
  have houtL : ¬ (i ≤ sL.1.receiverIdx ∨ maxSkip < i - sL.1.receiverIdx - 1) := by
    rw [hsL1]; exact hout
  have hlarejL : ¬ ((true = false ∧ sL.1.lastSentIdx < i) ∧ sL.1.isCompromised i = false) := by simp
  unfold _root_.CryptoGames.FSAEAD.Thm5.injectH
  simp only [StateT.run_bind, _root_.CryptoGames.FSAEAD.Thm5.getH_run, pure_bind,
    hendL, hanyL, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    _root_.CryptoGames.FSAEAD.Thm5.Ends.receiveH_none_run_of_in_window ae G maxSkip true
      hsync.wf_seedL a e hcontL houtL hlarejL,
    hdec, _root_.CryptoGames.FSAEAD.Thm5.modifyH_run, StateT.run_pure]
  exact ⟨_, rfl⟩

/-! ### 4. `MultiSessIdxInv` & `HooksFSMulti` Session-Index Specs -/

structure MultiSessIdxInv {Γ T RSt SS RS K I M E : Type}
    (M_sess rem : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E)) : Prop where
  vS_lt : ∀ P sIdx, (es.g.st P).vS = some (.inr sIdx) → sIdx < es.h.sessions.length
  vR_lt : ∀ P ep sIdx, (es.g.st P).vR ep = some (.inr sIdx) → sIdx < es.h.sessions.length
  cache_lt : ∀ ep Tc σc k sIdx,
    es.h.cache ep = some (Tc, σc, k, some sIdx) → sIdx < es.h.sessions.length
  len_le : es.h.sessions.length + rem ≤ M_sess

theorem lookupMultiF_allSessLt {T RSt K I SS RS M E : Type}
    [DecidableEq I] [SampleableType K] {M_sess : ℕ}
    (Ik : I) (h : FSMultiState T RSt K I E) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      ((lookupMultiF Ik).run h) ∧
    ∀ z ∈ support ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h),
      z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧ z.2.book = h.book ∧ z.2.lfWin = h.lfWin := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some k =>
    simp only [StateT.run_pure]
    exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl, rfl, rfl⟩⟩
  | none =>
    simp only [StateT.run_bind, pure_bind, StateT.run_modify, StateT.run_pure]
    refine ⟨AllSessLt.bind_support (AllSessLt.liftSampleT h) fun _ _ => .pure _, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw2 := mem_support_liftSampleT h hw
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    rw [hw2]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem regSessMulti_spec {T RSt K I SS RS M E : Type}
    [DecidableEq I] {M_sess : ℕ}
    (Ik : I) (h : FSMultiState T RSt K I E) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      ((regSessMulti Ik).run h) ∧
    ∀ z ∈ support ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h),
      z.1 < z.2.sessions.length ∧
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      z.2.cache = h.cache ∧ z.2.book = h.book ∧ z.2.lfWin = h.lfWin := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hmem : Ik ∈ h.sessions
  · simp only [hmem, ↓reduceIte, StateT.run_pure]
    refine ⟨.pure _, fun z hz => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨List.idxOf_lt_length_of_mem hmem, le_rfl, Nat.le_succ _, rfl, rfl, rfl⟩
  · simp only [hmem, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
    refine ⟨.pure _, fun z hz => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    dsimp only
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩ <;> simp [List.length_append]

theorem regSessOptMulti_spec {T RSt K I SS RS M E : Type}
    [DecidableEq I] {M_sess : ℕ}
    (sid : Option I) (h : FSMultiState T RSt K I E) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      ((regSessOptMulti sid).run h) ∧
    ∀ z ∈ support ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h),
      (∀ sIdx, z.1 = some sIdx → sIdx < z.2.sessions.length) ∧
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      z.2.cache = h.cache ∧ z.2.book = h.book ∧ z.2.lfWin = h.lfWin := by
  cases sid with
  | none =>
    unfold regSessOptMulti
    simp only [StateT.run_pure]
    refine ⟨.pure _, fun z hz => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨(by intro _ h; cases h), le_rfl, Nat.le_succ _, rfl, rfl, rfl⟩
  | some Ik =>
    unfold regSessOptMulti
    simp only [StateT.run_map]
    obtain ⟨ha, hsupp⟩ := regSessMulti_spec (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      (M_sess := M_sess) Ik h
    refine ⟨ha.map _, fun z hz => ?_⟩
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨hlt, hle1, hle2, hc, hb, hlf⟩ := hsupp w hw
    exact ⟨by intro sIdx hs; injection hs with hs; subst hs; exact hlt, hle1, hle2, hc, hb, hlf⟩

theorem rootFSMulti_spec {KR RSt I K T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (ep : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess
      ((rootFSMulti prng mo ep Ik σ).run h) ∧
    ∀ z ∈ support ((rootFSMulti (SS := SS) (RS := RS) (M := M) prng mo ep Ik σ).run h),
      z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧ z.2.book = h.book ∧ z.2.lfWin = h.lfWin := by
  unfold rootFSMulti
  split_ifs
  · simp only [StateT.run_pure]
    exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp only [StateT.run_bind, StateT.run_pure]
    refine ⟨AllSessLt.bind_support (AllSessLt.liftSampleT h) fun w _ =>
      AllSessLt.bind_support (AllSessLt.liftSampleT w.2) fun _ _ => .pure _, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz; obtain ⟨w1, hw1, hz⟩ := hz
    have hw1_eq := mem_support_liftSampleT h hw1
    rw [mem_support_bind_iff] at hz; obtain ⟨w2, hw2, hz⟩ := hz
    have hw2_eq := mem_support_liftSampleT w1.2 hw2
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    dsimp only
    rw [hw2_eq, hw1_eq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_pure]
    obtain ⟨ha, hsupp⟩ := lookupMultiF_allSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      (M_sess := M_sess) Ik h
    refine ⟨ha.bind_support fun _ _ => .pure _, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    exact hsupp w hw
  · simp only [StateT.run_bind, StateT.run_pure]
    refine ⟨AllSessLt.bind_support (AllSessLt.liftSampleT h) fun _ _ => .pure _, fun z hz => ?_⟩
    rw [mem_support_bind_iff] at hz; obtain ⟨w1, hw1, hz⟩ := hz
    have hw1_eq := mem_support_liftSampleT h hw1
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    dsimp only
    rw [hw1_eq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [StateT.run_pure]
    exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl, rfl, rfl⟩⟩

theorem startSend_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (r : Option CCoins)
    (h : FSMultiState T RSt K I E)
    (hcache : ∀ ep' Tc σc k sIdx,
      h.cache ep' = some (Tc, σc, k, some sIdx) → sIdx < h.sessions.length) :
    let m := ((hooksFSMulti cka prng fs Δcka mo false la).startSend ctx P ep γ σ r).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess m ∧
    ∀ z ∈ support m,
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ v, z.1 = some v → ∀ sIdx, v.2.2.2 = .inr sIdx → sIdx < z.2.sessions.length) ∧
      (∀ ep' Tc σc k sIdx,
        z.2.cache ep' = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length) := by
  intro m
  dsimp only [m, hooksFSMulti]
  have hbody : ∀ coins : CCoins,
      let tail : HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (Γ × T × RSt × (SS ⊕ ℕ))) := do
        let __x ← rootFSMulti prng mo ep (cka.send γ coins).2.2 σ
        let optIdx ← regSessOptMulti __x.2.2
        modify fun s =>
          { s with cache := Function.update s.cache ep (some ((cka.send γ coins).2.1, __x.1, __x.2.1, optIdx)) }
        pure (some ((cka.send γ coins).1, (cka.send γ coins).2.1, __x.1,
          match optIdx with
          | none => Sum.inl (fs.initSender __x.2.1)
          | some sIdx => Sum.inr sIdx))
      AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess (tail.run h) ∧
      ∀ z ∈ support (tail.run h),
        h.sessions.length ≤ z.2.sessions.length ∧
        z.2.sessions.length ≤ h.sessions.length + 1 ∧
        (∀ v, z.1 = some v → ∀ sIdx, v.2.2.2 = .inr sIdx → sIdx < z.2.sessions.length) ∧
        (∀ ep' Tc σc k sIdx,
          z.2.cache ep' = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length) := by
    intro coins tail
    dsimp only [tail]
    simp only [StateT.run_bind]
    obtain ⟨hroot_a, hroot_s⟩ := rootFSMulti_spec (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      (M_sess := M_sess) prng mo ep (cka.send γ coins).2.2 σ h
    refine ⟨hroot_a.bind_support fun u _ => ?_, fun z hz => ?_⟩
    · obtain ⟨hreg_a, _⟩ := regSessOptMulti_spec (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        (M_sess := M_sess) u.1.2.2 u.2
      exact hreg_a.bind_support fun _ _ => by simp only [StateT.run_modify, pure_bind, StateT.run_pure]; exact .pure _
    · rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
      obtain ⟨husess, hucache, _, _⟩ := hroot_s u hu
      rw [mem_support_bind_iff] at hz; obtain ⟨v, hv, hz⟩ := hz
      obtain ⟨hv_lt, hv_le1, hv_le2, hvcache, _, _⟩ := (regSessOptMulti_spec (SS := SS) (RS := RS) (T := T)
        (M := M) (E := E) (M_sess := M_sess) u.1.2.2 u.2).2 v hv
      simp only [StateT.run_modify, pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      have husess_len : u.2.sessions.length = h.sessions.length := congrArg List.length husess
      dsimp only
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro x hx sIdx hs
        injection hx with hx; subst hx
        cases hopt : v.1 with
        | none => simp [hopt] at hs
        | some idx =>
          simp only [hopt, Sum.inr.injEq] at hs; subst hs
          exact hv_lt idx hopt
      · intro ep' Tc σc k sIdx hce
        by_cases hep : ep' = ep
        · subst hep
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hce
          exact hv_lt sIdx hce.2.2.2
        · simp only [Function.update_of_ne hep, hvcache, hucache] at hce
          exact lt_of_lt_of_le (hcache ep' Tc σc k sIdx hce) (by omega)
  cases r with
  | some c =>
    simp only [StateT.run_bind, StateT.run_pure, pure_bind]
    exact hbody c
  | none =>
    simp only [StateT.run_bind]
    refine ⟨(AllSessLt.liftSampleT h).bind_support fun w hw => ?_, fun z hz => ?_⟩
    · have hw2 := mem_support_liftSampleT h hw
      rw [hw2]
      exact (hbody w.1).1
    · rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
      have hw2 := mem_support_liftSampleT h hw
      rw [hw2] at hz
      exact (hbody w.1).2 z hz

theorem startRecv_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (ep : ℕ) (γ : Γ) (σ : RSt) (Tn : T)
    (h : FSMultiState T RSt K I E)
    (hcache : ∀ ep' Tc σc k sIdx,
      h.cache ep' = some (Tc, σc, k, some sIdx) → sIdx < h.sessions.length) :
    let m := ((hooksFSMulti cka prng fs Δcka mo false la).startRecv ctx P ep γ σ Tn).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess m ∧
    ∀ z ∈ support m,
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ inner, z.1 = some (some inner) → ∀ sIdx, inner.2.2 = .inr sIdx → sIdx < z.2.sessions.length) ∧
      z.2.cache = h.cache := by
  intro m
  dsimp only [m, hooksFSMulti]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hce : h.cache ep with
  | some quad =>
    rcases quad with ⟨Tc, σc, k, optIdx⟩
    by_cases hT : Tc = Tn
    · simp only [hT, ↓reduceIte, StateT.run_pure]
      refine ⟨.pure _, fun z hz => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
      refine ⟨le_rfl, Nat.le_succ _, ?_, rfl⟩
      intro inner hinner sIdx hs
      injection hinner with hinner; injection hinner with hinner; subst hinner
      cases optIdx with
      | none => simp at hs
      | some idx =>
        simp only [Sum.inr.injEq] at hs; subst hs
        exact hcache ep Tc σc k idx hce
    · simp only [hT, ↓reduceIte, Bool.false_eq_true]
      split_ifs
      · simp only [StateT.run_pure]
        exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨le_rfl, Nat.le_succ _, (by intro _ hi; cases hi), rfl⟩⟩
      · simp only [StateT.run_bind, StateT.run_pure]
        obtain ⟨hlk_a, hlk_s⟩ := lookupMultiF_allSessLt (SS := SS) (RS := RS) (T := T) (M := M)
          (E := E) (M_sess := M_sess) (cka.receive γ Tn).2 h
        refine ⟨hlk_a.bind_support fun u _ =>
          (regSessMulti_spec (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
            (M_sess := M_sess) (cka.receive γ Tn).2 u.2).1.bind_support fun _ _ => .pure _, fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
        obtain ⟨husess, hucache, _, _⟩ := hlk_s u hu
        rw [mem_support_bind_iff] at hz; obtain ⟨v, hv, hz⟩ := hz
        obtain ⟨hv_lt, hv_le1, hv_le2, hvcache, _, _⟩ := (regSessMulti_spec (SS := SS) (RS := RS)
          (T := T) (M := M) (E := E) (M_sess := M_sess) (cka.receive γ Tn).2 u.2).2 v hv
        simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
        have husess_len : u.2.sessions.length = h.sessions.length := congrArg List.length husess
        dsimp only
        refine ⟨by omega, by omega, ?_, by rw [hvcache, hucache]⟩
        intro inner hinner sIdx hs
        injection hinner with hinner; injection hinner with hinner; subst hinner
        simp only [Sum.inr.injEq] at hs; subst hs; exact hv_lt
      · simp only [StateT.run_pure]
        exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨le_rfl, Nat.le_succ _, (by intro _ hi; cases hi), rfl⟩⟩
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · simp only [StateT.run_pure]
      exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨le_rfl, Nat.le_succ _, (by intro _ hi; cases hi), rfl⟩⟩
    · simp only [StateT.run_bind, StateT.run_pure]
      obtain ⟨hlk_a, hlk_s⟩ := lookupMultiF_allSessLt (SS := SS) (RS := RS) (T := T) (M := M)
        (E := E) (M_sess := M_sess) (cka.receive γ Tn).2 h
      refine ⟨hlk_a.bind_support fun u _ =>
        (regSessMulti_spec (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
          (M_sess := M_sess) (cka.receive γ Tn).2 u.2).1.bind_support fun _ _ => .pure _, fun z hz => ?_⟩
      rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
      obtain ⟨husess, hucache, _, _⟩ := hlk_s u hu
      rw [mem_support_bind_iff] at hz; obtain ⟨v, hv, hz⟩ := hz
      obtain ⟨hv_lt, hv_le1, hv_le2, hvcache, _, _⟩ := (regSessMulti_spec (SS := SS) (RS := RS)
        (T := T) (M := M) (E := E) (M_sess := M_sess) (cka.receive γ Tn).2 u.2).2 v hv
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
      have husess_len : u.2.sessions.length = h.sessions.length := congrArg List.length husess
      dsimp only
      refine ⟨by omega, by omega, ?_, by rw [hvcache, hucache]⟩
      intro inner hinner sIdx hs
      injection hinner with hinner; injection hinner with hinner; subst hinner
      simp only [Sum.inr.injEq] at hs; subst hs; exact hv_lt
    · simp only [StateT.run_pure]
      exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨le_rfl, Nat.le_succ _, (by intro _ hi; cases hi), rfl⟩⟩

theorem fsSend_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (ep : ℕ) (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T RSt K I E)
    (hssv : ∀ sIdx, ssv = .inr sIdx → sIdx < h.sessions.length)
    (hlen : h.sessions.length ≤ M_sess) :
    let act := ((hooksFSMulti cka prng fs Δcka mo false la).fsSend ctx P ep ssv hdr m pair).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess act ∧
    ∀ z ∈ support act,
      z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
      (∀ p, z.1 = some p → ∀ sIdx, p.1 = .inr sIdx → sIdx < z.2.sessions.length) := by
  intro act; dsimp only [act, hooksFSMulti]
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure]
    exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl, by intro p hp _ hs; injection hp with hp; subst hp; simp at hs⟩⟩
  · have hs_lt : sIdx < h.sessions.length := hssv sIdx rfl
    have hs_M : sIdx < M_sess := lt_of_lt_of_le hs_lt hlen
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    let tail (ok : Bool) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E) (Option ((SS ⊕ ℕ) × E)) :=
      if !ok then pure none
      else
        match pair with
        | some (m₀, m₁) => do
          let e? ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.challengeQuery
            (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          (match e? with
          | none => pure none
          | some e => do
            modify (fun (s : FSMultiState T RSt K I E) =>
              let b : FSMultiBook T E := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with fsCount := b.fsCount + 1, fsTrans := (b.fsCount + 1, hdr, e) :: b.fsTrans }) })
            pure (some (.inr sIdx, e)))
        | none => do
          let e? ← liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
            (SenderState := SS) (ReceiverState := RS) hdr m)
          (match e? with
          | none => pure none
          | some e => do
            modify (fun (s : FSMultiState T RSt K I E) =>
              let b : FSMultiBook T E := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with fsCount := b.fsCount + 1, fsTrans := (b.fsCount + 1, hdr, e) :: b.fsTrans }) })
            pure (some (.inr sIdx, e)))
    have htail : ∀ (ok : Bool) (w2 : FSMultiState T RSt K I E),
        w2.sessions = h.sessions → w2.cache = h.cache →
        AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess ((tail ok).run w2) ∧
        ∀ z ∈ support ((tail ok).run w2),
          z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
          (∀ p, z.1 = some p → ∀ idx, p.1 = .inr idx → idx < z.2.sessions.length) := by
      intro ok w2 hws hwc
      dsimp only [tail]
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
        exact ⟨.pure _, fun z hz => by
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨hws, hwc, by intro _ hp; cases hp⟩⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, fun z hz => ?_⟩
        · cases pair <;> simp only [StateT.run_bind] <;>
            refine (liftFSMulti_allSessLt hs_M w2 _).bind_support fun u _ => ?_ <;>
            (rcases _ : u.1 with _ | e
             · simp only [StateT.run_pure]; exact .pure _
             · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]; exact .pure _)
        · cases pair <;> {
            simp only [StateT.run_bind, mem_support_bind_iff] at hz
            obtain ⟨u, hu, hz⟩ := hz
            have hu2 := mem_support_liftFSMulti sIdx w2 _ hu
            rcases hu1 : u.1 with _ | e
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                (congrArg FSMultiState.cache hu2).trans hwc, by intro _ hp; cases hp⟩
            · simp only [hu1, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz; dsimp only
              refine ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                (congrArg FSMultiState.cache hu2).trans hwc, fun p hp idx hidx => ?_⟩
              injection hp with hp; subst hp; simp only [Sum.inr.injEq] at hidx; subst hidx
              rw [(congrArg FSMultiState.sessions hu2).trans hws]; exact hs_lt
          }
    by_cases hc1 : (!(ctx.safeCh (2 + Δcka) P) && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hc1, ↓reduceIte]
      cases la
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine ⟨(liftFSMulti_allSessLt hs_M h _).bind_support fun u hu => ?_, fun z hz => ?_⟩
        · have hu2 := mem_support_liftFSMulti sIdx h _ hu
          rcases _ : u.1 with _ | val
          · exact (htail false u.2 (congrArg FSMultiState.sessions hu2) (congrArg FSMultiState.cache hu2)).1
          · rw [StateT.run_bind, StateT.run_modify, pure_bind]
            let b' : FSMultiBook T E := { (u.2.book sIdx).getD {} with sCorr := true }
            let u2' : FSMultiState T RSt K I E := { u.2 with book := Function.update u.2.book sIdx (some b') }
            exact (htail true u2' (by dsimp [u2']; exact congrArg FSMultiState.sessions hu2)
              (by dsimp [u2']; exact congrArg FSMultiState.cache hu2)).1
        · rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
          have hu2 := mem_support_liftFSMulti sIdx h _ hu
          rcases hu1 : u.1 with _ | val
          · simp only [hu1] at hz
            exact (htail false u.2 (congrArg FSMultiState.sessions hu2) (congrArg FSMultiState.cache hu2)).2 z hz
          · simp only [hu1] at hz; rw [StateT.run_bind, StateT.run_modify, pure_bind] at hz
            let b' : FSMultiBook T E := { (u.2.book sIdx).getD {} with sCorr := true }
            let u2' : FSMultiState T RSt K I E := { u.2 with book := Function.update u.2.book sIdx (some b') }
            exact (htail true u2' (by dsimp [u2']; exact congrArg FSMultiState.sessions hu2)
              (by dsimp [u2']; exact congrArg FSMultiState.cache hu2)).2 z hz
      · simp only [↓reduceIte]
        exact htail false h rfl rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      exact htail true h rfl rfl

theorem fsRecv_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (ep : ℕ) (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E)
    (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E)
    (hrsv : ∀ sIdx, rsv = .inr sIdx → sIdx < h.sessions.length)
    (hlen : h.sessions.length ≤ M_sess) :
    let act := ((hooksFSMulti cka prng fs Δcka mo false la).fsRecv ctx P ep rsv hdr e rec).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess act ∧
    ∀ z ∈ support act,
      z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
      (∀ tri, z.1 = some (some tri) → ∀ sIdx, tri.1 = .inr sIdx → sIdx < z.2.sessions.length) := by
  intro act; dsimp only [act, hooksFSMulti]
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure]
    refine ⟨.pure _, fun z hz => ?_⟩
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    refine ⟨rfl, rfl, fun tri htri idx hidx => ?_⟩
    cases hrcv : fs.receive rs hdr e with
    | none => simp [hrcv] at htri
    | some o => simp only [hrcv, Option.map_some, Option.some.injEq] at htri; subst htri; simp at hidx
  · have hs_lt : sIdx < h.sessions.length := hrsv sIdx rfl
    have hs_M : sIdx < M_sess := lt_of_lt_of_le hs_lt hlen
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    let recFound := ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
    let tail (la' ok : Bool) :
        HM (FSMultiSpec SS RS T M E) (FSMultiState T RSt K I E)
          (Option (Option ((RS ⊕ ℕ) × ℕ × M))) :=
      if !ok then pure none
      else do
        let res ← if recFound.isSome then
            liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.deliverQuery
              (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMulti sIdx (_root_.CryptoGames.FSAEAD.injectQuery
              (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => pure none
        | some .rejected => pure (some none)
        | some (.accepted i mo') => do
          let s1 ← get
          let b1 := (s1.book sIdx).getD {}
          if la' && recFound.isNone && !b1.sCorr && decide (b1.fsCount < i) then
            modify (fun (s : FSMultiState T RSt K I E) => { s with lfWin := true })
            pure none
          else
            let target := (recFound.map (·.1)).getD i
            modify (fun (s : FSMultiState T RSt K I E) =>
              let b : FSMultiBook T E := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with fsTrans := b.fsTrans.filter (fun x => x.1 != target) }) })
            match mo', rec with
            | some m, _ => pure (some (some (.inr sIdx, i, m)))
            | none, some r => pure (some (some (.inr sIdx, i, r.msg)))
            | none, none => pure none
    have htail : ∀ (la' ok : Bool) (w2 : FSMultiState T RSt K I E),
        w2.sessions = h.sessions → w2.cache = h.cache →
        AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess ((tail la' ok).run w2) ∧
        ∀ z ∈ support ((tail la' ok).run w2),
          z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
          (∀ tri, z.1 = some (some tri) → ∀ idx, tri.1 = .inr idx → idx < z.2.sessions.length) := by
      intro la' ok w2 hws hwc
      dsimp only [tail]
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure]
        exact ⟨.pure _, fun z hz => by
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨hws, hwc, by intro _ hp; cases hp⟩⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, fun z hz => ?_⟩
        · split_ifs <;> simp only [StateT.run_bind] <;>
            refine (liftFSMulti_allSessLt hs_M w2 _).bind_support fun u _ => ?_ <;>
            (rcases _ : u.1 with _ | (_ | ⟨i, mo'⟩)
             · simp only [StateT.run_pure]; exact .pure _
             · simp only [StateT.run_pure]; exact .pure _
             · simp only [StateT.run_bind, StateT.run_get, pure_bind]
               split_ifs <;> simp only [StateT.run_bind, StateT.run_modify, pure_bind]
               · simp only [StateT.run_pure]; exact .pure _
               · cases mo' <;> cases rec <;> simp only [StateT.run_pure] <;> exact .pure _)
        · split_ifs at hz <;> {
            simp only [StateT.run_bind, mem_support_bind_iff] at hz
            obtain ⟨u, hu, hz⟩ := hz
            have hu2 := mem_support_liftFSMulti sIdx w2 _ hu
            rcases hu1 : u.1 with _ | (_ | ⟨i, mo'⟩)
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                (congrArg FSMultiState.cache hu2).trans hwc, by intro _ hp; cases hp⟩
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                (congrArg FSMultiState.cache hu2).trans hwc, by intro _ hp; cases hp⟩
            · simp only [hu1, StateT.run_bind, StateT.run_get, pure_bind] at hz
              split_ifs at hz
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  support_pure, Set.mem_singleton_iff] at hz
                subst hz; dsimp only
                exact ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                  (congrArg FSMultiState.cache hu2).trans hwc, by intro _ hp; cases hp⟩
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hz
                cases mo' <;> cases rec <;>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz <;>
                  subst hz <;> dsimp only
                · exact ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                    (congrArg FSMultiState.cache hu2).trans hwc, by intro _ hp; cases hp⟩
                · refine ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                    (congrArg FSMultiState.cache hu2).trans hwc, fun tri htri idx hidx => ?_⟩
                  injection htri with htri; injection htri with htri; subst htri
                  simp only [Sum.inr.injEq] at hidx; subst hidx
                  rw [(congrArg FSMultiState.sessions hu2).trans hws]; exact hs_lt
                · refine ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                    (congrArg FSMultiState.cache hu2).trans hwc, fun tri htri idx hidx => ?_⟩
                  injection htri with htri; injection htri with htri; subst htri
                  simp only [Sum.inr.injEq] at hidx; subst hidx
                  rw [(congrArg FSMultiState.sessions hu2).trans hws]; exact hs_lt
                · refine ⟨(congrArg FSMultiState.sessions hu2).trans hws,
                    (congrArg FSMultiState.cache hu2).trans hwc, fun tri htri idx hidx => ?_⟩
                  injection htri with htri; injection htri with htri; subst htri
                  simp only [Sum.inr.injEq] at hidx; subst hidx
                  rw [(congrArg FSMultiState.sessions hu2).trans hws]; exact hs_lt
          }
    by_cases hc1 : ((((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isNone &&
        !(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) ep) &&
        !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hc1, ↓reduceIte]
      cases la
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine ⟨(liftFSMulti_allSessLt hs_M h _).bind_support fun u hu => ?_, fun z hz => ?_⟩
        · have hu2 := mem_support_liftFSMulti sIdx h _ hu
          rcases _ : u.1 with _ | val
          · exact (htail false false u.2 (congrArg FSMultiState.sessions hu2) (congrArg FSMultiState.cache hu2)).1
          · rw [StateT.run_bind, StateT.run_modify, pure_bind]
            let b' : FSMultiBook T E := { (u.2.book sIdx).getD {} with sCorr := true }
            let u2' : FSMultiState T RSt K I E := { u.2 with book := Function.update u.2.book sIdx (some b') }
            exact (htail false true u2' (by dsimp [u2']; exact congrArg FSMultiState.sessions hu2)
              (by dsimp [u2']; exact congrArg FSMultiState.cache hu2)).1
        · rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
          have hu2 := mem_support_liftFSMulti sIdx h _ hu
          rcases hu1 : u.1 with _ | val
          · simp only [hu1] at hz
            exact (htail false false u.2 (congrArg FSMultiState.sessions hu2) (congrArg FSMultiState.cache hu2)).2 z hz
          · simp only [hu1] at hz; rw [StateT.run_bind, StateT.run_modify, pure_bind] at hz
            let b' : FSMultiBook T E := { (u.2.book sIdx).getD {} with sCorr := true }
            let u2' : FSMultiState T RSt K I E := { u.2 with book := Function.update u.2.book sIdx (some b') }
            exact (htail false true u2' (by dsimp [u2']; exact congrArg FSMultiState.sessions hu2)
              (by dsimp [u2']; exact congrArg FSMultiState.cache hu2)).2 z hz
      · simp only [↓reduceIte]
        exact htail true false h rfl rfl
    · simp only [hc1, Bool.false_eq_true, ↓reduceIte]
      exact htail la true h rfl rfl

theorem reveal_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiState T RSt K I E)
    (hvp : ∀ sIdx, vp.vS = some (.inr sIdx) → sIdx < h.sessions.length)
    (hlen : h.sessions.length ≤ M_sess) :
    let act := ((hooksFSMulti cka prng fs Δcka mo false la).reveal ctx P vp).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess act ∧
    ∀ z ∈ support act, z.2.sessions = h.sessions ∧ z.2.cache = h.cache := by
  intro act; dsimp only [act, hooksFSMulti]
  cases hvS : vp.vS with
  | none =>
    simp only [pure_bind]
    split_ifs <;> simp only [StateT.run_pure] <;>
      exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩⟩
  | some ssv =>
    rcases ssv with ss | sIdx
    · simp only [pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;>
        exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩⟩
    · have hs_M : sIdx < M_sess := lt_of_lt_of_le (hvp sIdx hvS) hlen
      by_cases hla : la = true
      · simp only [hla, ↓reduceIte, StateT.run_pure, pure_bind]
        exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨rfl, rfl⟩⟩
      · simp only [hla, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine ⟨(liftFSMulti_allSessLt hs_M h _).bind_support fun u _ => ?_, fun z hz => ?_⟩
        · rcases _ : u.1 with _ | ss
          · simp only [StateT.run_pure, pure_bind]; exact .pure _
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            split_ifs <;> simp only [StateT.run_pure] <;> exact .pure _
        · rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
          have hu2 := mem_support_liftFSMulti sIdx h _ hu
          rcases hu1 : u.1 with _ | ss
          · simp only [hu1, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨congrArg FSMultiState.sessions hu2, congrArg FSMultiState.cache hu2⟩
          · simp only [hu1, StateT.run_bind, StateT.run_modify, pure_bind] at hz
            split_ifs at hz <;>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz <;>
              subst hz <;> dsimp only <;>
              exact ⟨congrArg FSMultiState.sessions hu2, congrArg FSMultiState.cache hu2⟩

theorem vSend_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : FSMultiState T RSt K I E)
    (hvpS : ∀ sIdx, vp.vS = some (.inr sIdx) → sIdx < h.sessions.length)
    (hvpR : ∀ ep sIdx, vp.vR ep = some (.inr sIdx) → sIdx < h.sessions.length)
    (hcache : ∀ ep Tc σc k sIdx, h.cache ep = some (Tc, σc, k, some sIdx) → sIdx < h.sessions.length)
    (hlen : h.sessions.length + 1 ≤ M_sess) :
    let act := (vSend (hooksFSMulti cka prng fs Δcka mo false la) ctx P vp m pair r).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess act ∧
    ∀ z ∈ support act,
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      (∀ ep Tc σc k sIdx, z.2.cache ep = some (Tc, σc, k, some sIdx) → sIdx < z.2.sessions.length) ∧
      (∀ vp' c, z.1 = some (vp', c) →
        (∀ sIdx, vp'.vS = some (.inr sIdx) → sIdx < z.2.sessions.length) ∧
        (∀ ep sIdx, vp'.vR ep = some (.inr sIdx) → sIdx < z.2.sessions.length)) := by
  intro act; dsimp only [act, vSend]
  by_cases hsend : vp.id.sendsIn (vp.tcur + 1) = true
  · simp only [hsend, ↓reduceIte]
    rw [StateT.run_bind]
    obtain ⟨ha, hs⟩ := startSend_fsm_spec (SS := SS) (RS := RS) (M := M) (M_sess := M_sess)
      cka prng fs Δcka mo la ctx P (vp.tcur + 1) vp.γ vp.root r h hcache
    refine ⟨ha.bind_support fun w hw => ?_, fun z hz => ?_⟩
    · obtain ⟨hl1, hl2, hss, _⟩ := hs w hw
      rcases hw1 : w.1 with _ | ⟨γ', T', σ', ss⟩
      · dsimp only; rw [pure_bind]; dsimp only; simp only [StateT.run_pure]; exact .pure _
      · dsimp only; rw [pure_bind]; dsimp only; rw [StateT.run_bind]
        have hspec := fsSend_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P (vp.tcur + 1) ss
          (vp.tcur + 1, some T') m pair w.2 (fun sIdx hs' => hss _ hw1 sIdx hs') (hl2.trans hlen)
        exact hspec.1.bind_support fun u _ => by
          rcases _ : u.1 with _ | ⟨_, _⟩ <;> simp only [StateT.run_pure] <;> exact .pure _
    · rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨hl1, hl2, hss, hca⟩ := hs w hw
      rcases hw1 : w.1 with _ | ⟨γ', T', σ', ss⟩
      · simp only [hw1] at hz; rw [pure_bind] at hz; dsimp only at hz
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
        exact ⟨hl1, hl2, hca, by intro _ _ hx; cases hx⟩
      · simp only [hw1] at hz; rw [pure_bind] at hz; dsimp only at hz
        rw [StateT.run_bind, mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
        have hspec := fsSend_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P (vp.tcur + 1) ss
          (vp.tcur + 1, some T') m pair w.2 (fun sIdx hs' => hss _ hw1 sIdx hs') (hl2.trans hlen)
        obtain ⟨hus, huc, hup⟩ := hspec.2 u hu
        rcases hu1 : u.1 with _ | ⟨v', e⟩
        · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨by rw [hus]; exact hl1, by rw [hus]; exact hl2, by simpa [hus, huc] using hca,
            by intro _ _ hx; cases hx⟩
        · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          refine ⟨by rw [hus]; exact hl1, by rw [hus]; exact hl2, by simpa [hus, huc] using hca,
            fun vp' c hx => ?_⟩
          injection hx with hx; injection hx with hv_eq _; subst hv_eq
          exact ⟨fun sIdx hs' => hup (v', e) hu1 sIdx (Option.some.inj hs'),
            fun ep sIdx hr => by rw [hus]; exact lt_of_lt_of_le (hvpR ep sIdx hr) hl1⟩
  · simp only [hsend, Bool.false_eq_true, ↓reduceIte]
    rw [pure_bind]; dsimp only
    cases hvS : vp.vS with
    | none =>
      simp only [StateT.run_pure]
      refine ⟨.pure _, fun z hz => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
      refine ⟨le_rfl, Nat.le_succ _, hcache, fun vp' c hx => ?_⟩
      injection hx with hx; injection hx with hv_eq _; subst hv_eq
      exact ⟨by intro _ h'; simp [hvS] at h', hvpR⟩
    | some v =>
      rw [StateT.run_bind]
      have hspec := fsSend_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P vp.tcur v
        (vp.tcur, vp.curCkaMsg) m pair h
        (fun sIdx hs' => hvpS sIdx (hvS.trans (congrArg some hs'))) (Nat.le_of_succ_le hlen)
      refine ⟨hspec.1.bind_support fun u _ => by
        rcases _ : u.1 with _ | ⟨_, _⟩ <;> simp only [StateT.run_pure] <;> exact .pure _,
        fun z hz => ?_⟩
      rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
      obtain ⟨hus, huc, hup⟩ := hspec.2 u hu
      rcases hu1 : u.1 with _ | ⟨v', e⟩
      · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
        exact ⟨by rw [hus], by rw [hus]; exact Nat.le_succ _, by simpa [hus, huc] using hcache,
          by intro _ _ hx; cases hx⟩
      · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
        refine ⟨by rw [hus], by rw [hus]; exact Nat.le_succ _, by simpa [hus, huc] using hcache,
          fun vp' c hx => ?_⟩
        injection hx with hx; injection hx with hv_eq _; subst hv_eq
        exact ⟨fun sIdx hs' => hup (v', e) hu1 sIdx (Option.some.inj hs'),
          fun ep sIdx hr => by rw [hus]; exact hvpR ep sIdx hr⟩

theorem vRecv_fsm_spec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K] {M_sess : ℕ}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : _root_.CryptoGames.SM.Engine.Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E)
    (P : Party) (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (c : Header T × E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E)
    (hvpS : ∀ sIdx, vp.vS = some (.inr sIdx) → sIdx < h.sessions.length)
    (hvpR : ∀ ep sIdx, vp.vR ep = some (.inr sIdx) → sIdx < h.sessions.length)
    (hcache : ∀ ep Tc σc k sIdx, h.cache ep = some (Tc, σc, k, some sIdx) → sIdx < h.sessions.length)
    (hlen : h.sessions.length + 1 ≤ M_sess) :
    let act := (vRecv (hooksFSMulti cka prng fs Δcka mo false la) ctx P vp c rec).run h
    AllSessLt (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_sess act ∧
    ∀ z ∈ support act,
      h.sessions.length ≤ z.2.sessions.length ∧
      z.2.sessions.length ≤ h.sessions.length + 1 ∧
      z.2.cache = h.cache ∧
      (∀ vp' t' i' m', z.1 = some (some (vp', t', i', m')) →
        (∀ sIdx, vp'.vS = some (.inr sIdx) → sIdx < z.2.sessions.length) ∧
        (∀ ep sIdx, vp'.vR ep = some (.inr sIdx) → sIdx < z.2.sessions.length)) := by
  intro act; dsimp only [act, vRecv]
  by_cases hbad : (vp.id.sendsIn c.1.1 || decide (vp.tcur + 1 < c.1.1)) = true
  · simp only [hbad, ↓reduceIte, StateT.run_pure]
    exact ⟨.pure _, fun z hz => by simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact ⟨le_rfl, Nat.le_succ _, rfl, by intro _ _ _ _ hx; cases hx⟩⟩
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    by_cases hnew : c.1.1 = vp.tcur + 1
    · simp only [hnew, ↓reduceIte]
      cases hc2 : c.1.2 with
      | none =>
        rw [pure_bind]; dsimp only; simp only [StateT.run_pure]
        exact ⟨.pure _, fun z hz => by
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨le_rfl, Nat.le_succ _, rfl, by intro _ _ _ _ hx; cases hx⟩⟩
      | some Tn =>
        rw [StateT.run_bind]
        obtain ⟨ha, hs⟩ := startRecv_fsm_spec (SS := SS) (RS := RS) (M := M) (M_sess := M_sess)
          cka prng fs Δcka mo la ctx P (vp.tcur + 1) vp.γ vp.root Tn h hcache
        refine ⟨ha.bind_support fun w hw => ?_, fun z hz => ?_⟩
        · obtain ⟨_, hl2, hrs, _⟩ := hs w hw
          rcases hw1 : w.1 with _ | (_ | ⟨γ', σ', rs⟩)
          · dsimp only; rw [pure_bind]; dsimp only; simp only [StateT.run_pure]; exact .pure _
          · dsimp only; rw [pure_bind]; dsimp only; simp only [StateT.run_pure]; exact .pure _
          · dsimp only; rw [pure_bind]; dsimp only; simp only [Function.update_self]; rw [StateT.run_bind]
            have hspec := fsRecv_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P
              (vp.tcur + 1) rs c.1 c.2 rec w.2 (fun sIdx hs' => hrs _ hw1 sIdx hs') (hl2.trans hlen)
            exact hspec.1.bind_support fun u _ => by
              rcases _ : u.1 with _ | (_ | ⟨_, _, _⟩) <;> simp only [StateT.run_pure] <;> exact .pure _
        · rw [mem_support_bind_iff] at hz; obtain ⟨w, hw, hz⟩ := hz
          obtain ⟨hl1, hl2, hrs, hca⟩ := hs w hw
          rcases hw1 : w.1 with _ | (_ | ⟨γ', σ', rs⟩)
          · simp only [hw1] at hz; rw [pure_bind] at hz; dsimp only at hz
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨hl1, hl2, hca, by intro _ _ _ _ hx; cases hx⟩
          · simp only [hw1] at hz; rw [pure_bind] at hz; dsimp only at hz
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact ⟨hl1, hl2, hca, by intro _ _ _ _ hx; cases hx⟩
          · simp only [hw1] at hz; rw [pure_bind] at hz; dsimp only at hz
            simp only [Function.update_self] at hz
            rw [StateT.run_bind, mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
            have hspec := fsRecv_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P
              (vp.tcur + 1) rs c.1 c.2 rec w.2 (fun sIdx hs' => hrs _ hw1 sIdx hs') (hl2.trans hlen)
            obtain ⟨hus, huc, hup⟩ := hspec.2 u hu
            rcases hu1 : u.1 with _ | (_ | ⟨v', i', m'⟩)
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨by rw [hus]; exact hl1, by rw [hus]; exact hl2, huc.trans hca, by intro _ _ _ _ hx; cases hx⟩
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              exact ⟨by rw [hus]; exact hl1, by rw [hus]; exact hl2, huc.trans hca, by intro _ _ _ _ hx; cases hx⟩
            · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
              refine ⟨by rw [hus]; exact hl1, by rw [hus]; exact hl2, huc.trans hca, fun vp' t' i'' m'' hx => ?_⟩
              injection hx with hx; injection hx with hx; injection hx with hv_eq _; subst hv_eq
              refine ⟨fun sIdx hs' => by rw [hus]; exact lt_of_lt_of_le (hvpS sIdx hs') hl1,
                fun ep sIdx hr => ?_⟩
              by_cases hep : ep = vp.tcur + 1
              · subst hep; simp only [Function.update_self, Option.some.injEq] at hr
                exact hup (v', i', m') hu1 sIdx hr
              · simp only [Function.update_of_ne hep] at hr
                rw [hus]; exact lt_of_lt_of_le (hvpR ep sIdx hr) hl1
    · simp only [hnew, ↓reduceIte]
      rw [pure_bind]; dsimp only
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [StateT.run_pure]
        exact ⟨.pure _, fun z hz => by
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨le_rfl, Nat.le_succ _, rfl, by intro _ _ _ _ hx; cases hx⟩⟩
      | some v =>
        rw [StateT.run_bind]
        have hspec := fsRecv_fsm_spec (M_sess := M_sess) cka prng fs Δcka mo la ctx P
          c.1.1 v c.1 c.2 rec h
          (fun sIdx hs' => hvpR c.1.1 sIdx (hvR.trans (congrArg some hs'))) (Nat.le_of_succ_le hlen)
        refine ⟨hspec.1.bind_support fun u _ => by
          rcases _ : u.1 with _ | (_ | ⟨_, _, _⟩) <;> simp only [StateT.run_pure] <;> exact .pure _,
          fun z hz => ?_⟩
        rw [mem_support_bind_iff] at hz; obtain ⟨u, hu, hz⟩ := hz
        obtain ⟨hus, huc, hup⟩ := hspec.2 u hu
        rcases hu1 : u.1 with _ | (_ | ⟨v', i', m'⟩)
        · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨by rw [hus], by rw [hus]; exact Nat.le_succ _, huc, by intro _ _ _ _ hx; cases hx⟩
        · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          exact ⟨by rw [hus], by rw [hus]; exact Nat.le_succ _, huc, by intro _ _ _ _ hx; cases hx⟩
        · simp only [hu1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz
          refine ⟨by rw [hus], by rw [hus]; exact Nat.le_succ _, huc, fun vp' t' i'' m'' hx => ?_⟩
          injection hx with hx; injection hx with hx; injection hx with hv_eq _; subst hv_eq
          refine ⟨fun sIdx hs' => by rw [hus]; exact hvpS sIdx hs', fun ep sIdx hr => ?_⟩
          by_cases hep : ep = c.1.1
          · subst hep; simp only [Function.update_self, Option.some.injEq] at hr
            exact hup (v', i', m') hu1 sIdx hr
          · simp only [Function.update_of_ne hep] at hr
            rw [hus]; exact hvpR ep sIdx hr

end

end Computational.Proofs.E2E.SessionAuthMultiRealPaperAux
