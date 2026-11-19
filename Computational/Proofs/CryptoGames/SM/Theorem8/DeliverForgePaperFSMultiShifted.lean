/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperBucketPRNG -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthLazy -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMultiBase -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthPubToAD
import Computational.Proofs.E2E.SessionAuthMultiDec
import Computational.Proofs.E2E.SessionAuthMultiShort

/-!
# Stage-2 Multi-Session Paper `DeliverForge` Hop-3 (`FSMultiSpec`) Bridges (`[B7]` × `[B8]`)

Couples the post-PRNG local games of the Stage-2 `DeliverForgePaper` families
(`localAuthDFShiftedDir2Paper`, `localAuthDFShiftedPaper`, `AuthL11.localAuthDFPaper`,
`localAuthDFPaperBucket`, and `localAuthDFBucket`) to the two-mode (`la = false` + `la = true`)
real multi-session `FSMultiSpec` experiments (`multiSessRealWinProb`), and establishes
per-session query bounds, `TwoModeMultiSessBounds`, and ideal-cutoff zero-output
(`multiSessEndWinProb = 0`) invariants.-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme AEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun dhScheme)
open _root_.CryptoGames.Ratchet (rootPRNG)
open _root_.CryptoGames.SM (authLosingConditionsAvoided)
open _root_.CryptoGames.SM.Construction (Header Mode healEpoch
  inStage2BucketGen redFSAuthDFPaperMulti redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF authOutBucket authOutBucketPaper bucketAuthCfg engRunDFPaperBucket
  hooksLocalBucket initLocalBucket
  localAuthDFPaperBucket localAuthDFShiftedDir2Paper localAuthDFShiftedPaper)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart dummyKey lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (SendMsgsOkDF GuardedSMDFShort)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)
open _root_.CryptoVerification.LibsignalSession (FsAdv fsAuthCompBoundWith fsCostedRedsInst macForgeryTerm)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (lazyInit sessLift multiSessSpec sessOffRange)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsInit fsImpl)
open Computational.Proofs.E2E.SessionAuthBridge (authHopCutoff MultiSessFsAdv multiSessPubToAD
  TwoModeMultiSessBounds RouterAdvCompat)
open Computational.Proofs.SessionCostedFig8.TopAssembly (multiSessRealWinProb multiSessEndWinProb
  multiSess_two_modes_le_sum_fsAuthCompBoundWith_min sum_range_mul_mod_div)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (
  redFSAuthDFShiftedPaperMultiGen redFSAuthDFShiftedPaperMulti redFSAuthDFShiftedDir2PaperMulti)
open _root_.CryptoGames.FSAEAD (
  encBadMsg queryADOutsideClass
  transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB_imp_shortB)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  onAnySess onSess isQueryBoundP_query_bind_pure_zero')
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (
  fsEncBadAD fsOutsideClass shortOk onSess_imp_onAnySess onAnySess_fsOutsideClass_inr_spec)
open Computational.Proofs.E2E.SessionAuthPubToAD (
  fsEncBadPubMsg
  multiSessPubToAD_offRange multiSessPubToAD_decBound multiSessPubToAD_shortAD
  multiSessPubToAD_oneADClass multiSessPubToAD_guardedShort)

section ShiftedTwoModeHelpers

open _root_.CryptoGames.SM (GameState Pos Record RecvResult Config healedBy)
open _root_.CryptoGames.SM.Engine (
  Policy VP Ctx TComp HM Hooks EState EM
  vSend vRecv abortE commitE transmitE challE deliverE injectE coinsE liftH
  injectEGen deliverForgeEGen)
open _root_.CryptoGames.SM.Construction (
  PartyState sampleT mkParties
  FSMultiSpec FSMultiState FSMultiBook
  liftFSMulti lookupMultiF regSessMulti regSessOptMulti rootFSMulti hooksFSMulti initFSMultiRaw)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  afterCorrShifted corrEShiftedPaper injectEB1 deliverForgeE deliverForgeEB1
  implEDFShiftedPaperGen)
open _root_.CryptoVerification.LibsignalSession.HeadlineV1 (badSendMsgDF)
open _root_.CryptoVerification.E2E.Signed.SessionQueries (fsInjQ)
open Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 (runFSMultiDFShiftedPaper)

private def ZeroPost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (P : spec.Domain → Bool) (Post : α → Prop) (oa : OracleComp spec α) : Prop :=
  oa.IsQueryBoundP (fun x => P x = true) 0 ∧ ∀ z ∈ support oa, Post z

private theorem ZeroPost.pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : spec.Domain → Bool} {Post : α → Prop} {a : α} (ha : Post a) :
    ZeroPost P Post (Pure.pure a : OracleComp spec α) :=
  ⟨isQueryBoundP_pure _ _ 0, fun z hz => by
    simp only [support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ ha⟩

private theorem ZeroPost.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : spec.Domain → Bool} {Mid : α → Prop} {Post : β → Prop}
    {mx : OracleComp spec α} {f : α → OracleComp spec β}
    (h : ZeroPost P Mid mx) (hf : ∀ a, Mid a → ZeroPost P Post (f a)) :
    ZeroPost P Post (mx >>= f) := by
  refine ⟨(isQueryBoundP_bind h.1 fun a ha => (hf a (h.2 a ha)).1).mono (by omega), ?_⟩
  intro z hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  exact (hf a (h.2 a ha)).2 z hz

private theorem ZeroPost.map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : spec.Domain → Bool} {Mid : α → Prop} {Post : β → Prop}
    {mx : OracleComp spec α} {g : α → β}
    (h : ZeroPost P Mid mx) (hg : ∀ a, Mid a → Post (g a)) :
    ZeroPost P Post (g <$> mx) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a ha => ZeroPost.pure (hg a ha)

private theorem ZeroPost.query_false {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {P : spec.Domain → Bool} (t : spec.Domain) (ht : P t = false) :
    ZeroPost P (fun _ => True) (query (spec := spec) t) := by
  refine ⟨?_, fun _ _ => trivial⟩
  have hq : (query (spec := spec) t : OracleComp spec (spec.Range t)) =
      (query (spec := spec) t >>= fun r => Pure.pure r) := (bind_pure _).symm
  rw [hq]
  exact isQueryBoundP_query_bind_pure_zero' t (by simp [ht]) id

private theorem ZeroPost.of_probComp {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {P : (unifSpec + spec₀).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    (oa : ProbComp α) :
    ZeroPost P (fun _ => True) (liftM oa : OracleComp (unifSpec + spec₀) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    change ZeroPost P (fun _ => True) (Pure.pure a)
    exact ZeroPost.pure trivial
  | query_bind t k ih =>
    change ZeroPost P (fun _ => True)
      ((query (spec := unifSpec + spec₀) (.inl t)) >>= fun u =>
        (liftM (k u) : OracleComp (unifSpec + spec₀) α))
    exact (ZeroPost.query_false (spec := unifSpec + spec₀) (.inl t) (hInl t)).bind fun u _ => ih u

private theorem zeroPost_simulateQ_run_budget
    {ι₁ ι₂ : Type} {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂}
    {S α : Type}
    (Bad : (unifSpec + s₁).Domain → Bool)
    (P : (unifSpec + s₂).Domain → Bool)
    (M_cap : ℕ)
    (Inv : ℕ → S → Prop)
    (impl : QueryImpl (unifSpec + s₁) (StateT S (OracleComp (unifSpec + s₂))))
    (hInl : ∀ (u : unifSpec.Domain) (k : ℕ) (st : S), k ≤ M_cap → Inv k st →
      ZeroPost P (fun z => Inv k z.2) ((impl (.inl u)).run st))
    (hInr : ∀ (qr : s₁.Domain) (k : ℕ) (st : S),
      k + 1 ≤ M_cap → Bad (.inr qr) = false → Inv k st →
      ZeroPost P (fun z => Inv (k + 1) z.2) ((impl (.inr qr)).run st)) :
    ∀ (rem k : ℕ) (oa : OracleComp (unifSpec + s₁) α),
      k + rem ≤ M_cap →
      oa.IsQueryBoundP (fun x => x.isRight = true) rem →
      oa.IsQueryBoundP (fun x => Bad x = true) 0 →
      ∀ (st : S), Inv k st →
        ZeroPost P (fun _ => True) ((simulateQ impl oa).run st) := by
  intro rem k oa
  induction oa using OracleComp.inductionOn generalizing rem k with
  | pure a =>
    intro _ _ _ _ _
    simp only [simulateQ_pure, StateT.run_pure]
    exact ZeroPost.pure trivial
  | query_bind t r ih =>
    intro hcap hq hbad st hst
    simp only [simulateQ_query_bind, StateT.run_bind]
    rw [isQueryBoundP_query_bind_iff] at hq hbad
    have hnb : ¬ (Bad t = true) := hbad.1.resolve_right (Nat.lt_irrefl 0)
    have hbad_cont : ∀ u, (r u).IsQueryBoundP (fun x => Bad x = true) 0 :=
      fun u => by simpa [hnb] using hbad.2 u
    rcases t with u | qr
    · exact (hInl u k st (by omega) hst).bind fun z hz =>
        ih z.1 rem k hcap (by simpa using hq.2 z.1) (hbad_cont z.1) z.2 hz
    · rcases rem with _ | rem'
      · simp at hq
      · have hnb' : Bad (.inr qr) = false := Bool.eq_false_iff.mpr hnb
        have hq_cont : ∀ u, (r u).IsQueryBoundP (fun x => x.isRight = true) rem' :=
          fun u => by simpa using hq.2 u
        exact (hInr qr k st (by omega) hnb' hst).bind fun z hz =>
          ih z.1 rem' (k + 1) (by omega) (hq_cont z.1) (hbad_cont z.1) z.2 hz

private def badMultiQuery {SS RS T M E : Type} (M_cap tStar : ℕ) (okM : M → Bool) :
    (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨sIdx, q⟩ =>
    decide (M_cap ≤ sIdx) ||
    encBadMsg (SS := SS) (RS := RS) okM (.inr q) ||
    queryADOutsideClass (SS := SS) (RS := RS) (fun h : Header T => h.1) tStar (.inr q)

private theorem badMultiQuery_inl {SS RS T M E : Type} (M_cap tStar : ℕ) (okM : M → Bool)
    (u : unifSpec.Domain) :
    badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM (.inl u) =
      false := rfl

private structure HkInv {T RSt K I E : Type} (tStar k : ℕ)
    (h : FSMultiState T RSt K I E) : Prop where
  len_le : h.sessions.length ≤ k
  cache_ok : ∀ t' e sIdx, h.cache t' = some e → e.2.2.2 = some sIdx →
    sIdx < h.sessions.length ∧ t' = tStar

private theorem HkInv.mono_k {T RSt K I E : Type} {tStar k₁ k₂ : ℕ}
    {h : FSMultiState T RSt K I E} (hinv : HkInv tStar k₁ h) (hle : k₁ ≤ k₂) :
    HkInv tStar k₂ h :=
  ⟨hinv.len_le.trans hle, hinv.cache_ok⟩

private def PartyInv {Γ T RSt SS RS : Type} (tStar len : ℕ)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) : Prop :=
  (∀ sIdx, vp.vS = some (.inr sIdx) →
    sIdx < len ∧ (vp.id.sendsIn (vp.tcur + 1) = false → vp.tcur = tStar)) ∧
  (∀ t' sIdx, vp.vR t' = some (.inr sIdx) → sIdx < len ∧ t' = tStar)

private theorem PartyInv.mono_len {Γ T RSt SS RS : Type} {tStar len₁ len₂ : ℕ}
    {vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hp : PartyInv tStar len₁ vp) (hle : len₁ ≤ len₂) :
    PartyInv tStar len₂ vp :=
  ⟨fun sIdx hs => ⟨Nat.lt_of_lt_of_le (hp.1 sIdx hs).1 hle, (hp.1 sIdx hs).2⟩,
   fun t' sIdx hr => ⟨Nat.lt_of_lt_of_le (hp.2 t' sIdx hr).1 hle, (hp.2 t' sIdx hr).2⟩⟩

private structure MultiInv {Γ T RSt K I SS RS M E : Type} (tStar k : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)) : Prop where
  hk : HkInv tStar k es.h
  st_ok : ∀ P, PartyInv tStar es.h.sessions.length (es.g.st P)

private theorem MultiInv.mono_k {Γ T RSt K I SS RS M E : Type} {tStar k₁ k₂ : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiState T RSt K I E)} (h : MultiInv tStar k₁ es) (hle : k₁ ≤ k₂) :
    MultiInv tStar k₂ es :=
  ⟨h.hk.mono_k hle, h.st_ok⟩

private theorem sendsIn_succ_of_false (p : Party) (t' : ℕ)
    (hf : p.sendsIn t' = false) : p.sendsIn (t' + 1) = true := by
  cases p <;> simp [Party.sendsIn] at hf ⊢ <;> omega

private theorem epMgmt_st_eq {St M C : Type} (g s₁ : GameState St M C)
    (Δ qep : ℕ) (P : Party) (bad : Bool) (h : g.epMgmt Δ qep P bad = some s₁) :
    s₁.st = g.st := by
  unfold GameState.epMgmt GameState.leak at h
  split_ifs at h <;> simp only [Option.some.injEq] at h
  all_goals (subst h; rfl)

private theorem record_st_eq {St M C : Type} [DecidableEq C]
    (s₁ : GameState St M C) (Δ : ℕ) (P : Party) (st' : St) (r : Record M C) (isCh : Bool) :
    (s₁.record Δ P st' r isCh).st = Function.update s₁.st P st' := by
  unfold GameState.record
  rfl

private theorem afterCorrShifted_st_eq {St M C : Type}
    (l : ℕ) (g : GameState St M C) (P : Party) :
    (afterCorrShifted l g P).st = g.st := by
  unfold afterCorrShifted GameState.leak
  rfl

private theorem mkParties_partyInv {Γ T RSt SS RS : Type}
    (γA γB : Γ) (σ : RSt) (ss : SS) (rs : RS) (tStar len : ℕ) (P : Party) :
    PartyInv tStar len
      ((fun | Party.A => (mkParties (T := T) γA γB σ (.inl ss : SS ⊕ ℕ) (.inl rs : RS ⊕ ℕ)).1
            | Party.B => (mkParties (T := T) γA γB σ (.inl ss : SS ⊕ ℕ) (.inl rs : RS ⊕ ℕ)).2) P) := by
  cases P <;> refine ⟨?_, ?_⟩
  · intro sIdx hs; simp [mkParties] at hs
  · intro t' sIdx hr; simp [mkParties] at hr
  · intro sIdx hs; simp [mkParties] at hs
  · intro t' sIdx hr; simp [mkParties] at hr

private theorem partyInv_update {Γ T RSt SS RS : Type} {tStar len₁ len₂ : ℕ}
    {st : Party → VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hst : ∀ Q, PartyInv tStar len₁ (st Q)) (hle : len₁ ≤ len₂)
    (P : Party) {st' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)}
    (hst' : PartyInv tStar len₂ st') (Q : Party) :
    PartyInv tStar len₂ (Function.update st P st' Q) := by
  by_cases hQP : Q = P
  · subst hQP; simpa [Function.update_self] using hst'
  · simpa [Function.update_of_ne hQP] using (hst Q).mono_len hle

private theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

private theorem liftH_zeroPost {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {HS Γv T Sv SSv RSv M E α : Type}
    {P : (unifSpec + tspec).Domain → Bool}
    {Post : α × HS → Prop}
    {x : HM tspec HS α}
    {es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS}
    (hx : ZeroPost P Post (x.run es.h)) :
    ZeroPost P
      (fun z => Post (z.1, z.2.h) ∧ z.2.g = es.g ∧ z.2.abort = es.abort)
      ((liftH x).run es) := by
  unfold liftH
  exact hx.bind fun ⟨a, h'⟩ hpost => ZeroPost.pure ⟨hpost, rfl, rfl⟩

private theorem sampleT_zeroPost {SS RS T M E : Type} (M_cap tStar : ℕ) (okM : M → Bool)
    (α : Type) [SampleableType α] :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun _ => True) (sampleT α) :=
  ZeroPost.of_probComp (badMultiQuery_inl M_cap tStar okM) ($ᵗ α : ProbComp α)

private theorem lift_sampleT_zeroPost {SS RS T M E HS : Type} (M_cap tStar : ℕ) (okM : M → Bool)
    (α : Type) [SampleableType α] (h : HS) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun z => z.2 = h) ((StateT.lift (sampleT α)).run h) := by
  rw [StateT.run_lift]
  exact (sampleT_zeroPost M_cap tStar okM α).bind fun _ _ => ZeroPost.pure rfl

private theorem liftFSMulti_query_zeroPost {SS RS T M E Sig K I : Type}
    (M_cap tStar : ℕ) (okM : M → Bool) (sIdx : ℕ)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    (hq₀ : badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      M_cap tStar okM (.inr ⟨sIdx, q₀⟩) = false)
    (h : FSMultiState T Sig K I E) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun z => z.2 = h)
      ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
        sIdx (liftM (OracleSpec.query q₀))).run h) := by
  have hq : ((liftFSMulti (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E)
        (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => Pure.pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMulti, StateT.run_lift]
  rw [hq]
  exact (ZeroPost.query_false (spec := unifSpec + FSMultiSpec SS RS T M E)
    (.inr ⟨sIdx, q₀⟩) hq₀).bind fun _ _ => ZeroPost.pure rfl

private theorem lookupMultiF_zeroPost {SS RS T M E Sig K I : Type}
    [DecidableEq I] [SampleableType K]
    (M_cap tStar : ℕ) (okM : M → Bool) (Ik : I) (h : FSMultiState T Sig K I E) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      ((lookupMultiF (SS := SS) (RS := RS) (M := M) Ik).run h) := by
  unfold lookupMultiF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h.table.lookup Ik with
  | some _ => exact ZeroPost.pure ⟨rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind]
    exact (lift_sampleT_zeroPost M_cap tStar okM K h).bind fun ⟨_, h1⟩ hh1 => by
      dsimp only at hh1; subst h1
      simp only [StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨rfl, rfl⟩

private theorem regSessMulti_zeroPost {SS RS T M E Sig K I : Type} [DecidableEq I]
    (M_cap tStar : ℕ) (okM : M → Bool) (Ik : I) (h : FSMultiState T Sig K I E) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun z => z.1 < z.2.sessions.length ∧
        h.sessions.length ≤ z.2.sessions.length ∧
        z.2.sessions.length ≤ h.sessions.length + 1 ∧
        z.2.cache = h.cache)
      ((regSessMulti (SS := SS) (RS := RS) (M := M) Ik).run h) := by
  unfold regSessMulti
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hmem
  · simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨List.idxOf_lt_length_of_mem hmem, le_rfl, Nat.le_succ _, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    refine ZeroPost.pure ?_
    dsimp only
    simp only [List.length_append, List.length_singleton]
    exact ⟨Nat.lt_succ_self _, Nat.le_succ _, le_rfl, trivial⟩

private theorem regSessOptMulti_zeroPost {SS RS T M E Sig K I : Type} [DecidableEq I]
    (M_cap tStar : ℕ) (okM : M → Bool) (sid : Option I) (h : FSMultiState T Sig K I E) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap tStar okM)
      (fun z => (∀ sIdx, z.1 = some sIdx → sIdx < z.2.sessions.length ∧ sid.isSome = true) ∧
        h.sessions.length ≤ z.2.sessions.length ∧
        z.2.sessions.length ≤ (if sid.isSome then h.sessions.length + 1 else h.sessions.length) ∧
        z.2.cache = h.cache)
      ((regSessOptMulti (SS := SS) (RS := RS) (M := M) sid).run h) := by
  cases sid with
  | none =>
    simp only [regSessOptMulti, StateT.run_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact ZeroPost.pure ⟨(fun _ hs => by cases hs), le_rfl, le_rfl, rfl⟩
  | some Ik =>
    simp only [regSessOptMulti, StateT.run_map, Option.isSome_some, ↓reduceIte]
    exact (regSessMulti_zeroPost M_cap tStar okM Ik h).map fun z ⟨hlt, hge, hle, hcache⟩ =>
      ⟨fun sIdx hs => by injection hs with hs'; subst hs'; exact ⟨hlt, trivial⟩, hge, hle, hcache⟩

private theorem rootFSMulti_zeroPost {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (M_cap : ℕ) (okM : M → Bool)
    (prng : PRFPRNG KR RSt I K) (mo : Mode) (t' : ℕ) (Ik : I) (σ : RSt)
    (h : FSMultiState T RSt K I E) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => (z.1.2.2.isSome = true → t' = mo.tStar) ∧
        z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      ((rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E) prng mo t' Ik σ).run h) := by
  unfold rootFSMulti
  split_ifs with hlt heq hheal hheal2
  · simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨fun hs => by simp at hs, rfl, rfl⟩
  · simp only [StateT.run_bind]
    refine (lift_sampleT_zeroPost M_cap mo.tStar okM I h).bind fun ⟨_, h1⟩ hh1 => ?_
    dsimp only at hh1; subst h1
    refine (lift_sampleT_zeroPost M_cap mo.tStar okM K h).bind fun ⟨_, h2⟩ hh2 => ?_
    dsimp only at hh2; subst h2
    simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨fun _ => heq, rfl, rfl⟩
  · simp only [StateT.run_bind]
    exact (lookupMultiF_zeroPost M_cap mo.tStar okM Ik h).bind fun ⟨_, h1⟩ ⟨hse, hca⟩ => by
      simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨fun _ => heq, hse, hca⟩
  · simp only [StateT.run_bind]
    exact (lift_sampleT_zeroPost M_cap mo.tStar okM I h).bind fun ⟨_, h1⟩ hh1 => by
      dsimp only at hh1; subst h1
      simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨fun hs => by simp at hs, rfl, rfl⟩
  · simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨fun hs => by simp at hs, rfl, rfl⟩

private theorem startSend_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : RSt)
    (r : Option CCoins) (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => HkInv mo.tStar (k + 1) z.2 ∧ h.sessions.length ≤ z.2.sessions.length ∧
        ∀ γ' T' σ' ssv, z.1 = some (γ', T', σ', ssv) →
          ∀ sIdx, ssv = .inr sIdx → sIdx < z.2.sessions.length ∧ t' = mo.tStar)
      (((hooksFSMulti cka prng fs Δcka mo false la).startSend ctx P t' γ σ r).run h) := by
  dsimp only [hooksFSMulti]
  have hAfter : ∀ (coins : CCoins),
      ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
        (fun z : Option (Γ × T × RSt × (SS ⊕ ℕ)) × FSMultiState T RSt K I E =>
          HkInv mo.tStar (k + 1) z.2 ∧ h.sessions.length ≤ z.2.sessions.length ∧
          ∀ γ' T' σ' ssv, z.1 = some (γ', T', σ', ssv) →
            ∀ sIdx, ssv = Sum.inr sIdx → sIdx < z.2.sessions.length ∧ t' = mo.tStar)
        ((do
          let __x ← rootFSMulti (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
            prng mo t' (cka.send γ coins).2.2 σ
          let optIdx ← regSessOptMulti (SS := SS) (RS := RS) (M := M) __x.2.2
          modify fun (s : FSMultiState T RSt K I E) =>
            { s with cache := Function.update s.cache t' (some ((cka.send γ coins).2.1, __x.1, __x.2.1, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with
            | none => Sum.inl (fs.initSender __x.2.1)
            | some sIdx => Sum.inr sIdx
          return some ((cka.send γ coins).1, (cka.send γ coins).2.1, __x.1, ssv)).run h) := by
    intro coins
    simp only [StateT.run_bind]
    refine (rootFSMulti_zeroPost M_cap okM prng mo t' (cka.send γ coins).2.2 σ h).bind
      fun ⟨⟨σ', k0, sid⟩, h1⟩ ⟨hsid, hse1, hca1⟩ => ?_
    dsimp only at hsid hse1 hca1 ⊢
    refine (regSessOptMulti_zeroPost M_cap mo.tStar okM sid h1).bind
      fun ⟨optIdx, h2⟩ ⟨hopt, hge2, hle2, hca2⟩ => ?_
    dsimp only at hopt hge2 hle2 hca2 ⊢
    refine ZeroPost.pure ?_
    dsimp only
    refine ⟨⟨?_, ?_⟩, hse1 ▸ hge2, ?_⟩
    · change h2.sessions.length ≤ k + 1
      have hlen1 : h1.sessions.length ≤ k := hse1 ▸ hhk.len_le
      cases sid
      · exact Nat.le_trans hle2 (Nat.le_succ_of_le hlen1)
      · exact Nat.le_trans hle2 (Nat.add_le_add_right hlen1 1)
    · intro t'' entry sIdx hent hsIdx
      by_cases ht : t'' = t'
      · subst ht
        simp only [Function.update_self, Option.some.injEq] at hent
        subst hent
        rcases hopt sIdx hsIdx with ⟨hlt, hsome⟩
        exact ⟨hlt, hsid hsome⟩
      · simp only [Function.update_of_ne ht, hca2, hca1] at hent
        rcases hhk.cache_ok t'' entry sIdx hent hsIdx with ⟨hlt, heq⟩
        exact ⟨Nat.lt_of_lt_of_le hlt (hse1 ▸ hge2), heq⟩
    · intro _ _ _ ssv hsome sIdx hssv
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨_, _, _, rfl⟩
      cases optIdx with
      | none => simp at hssv
      | some idx0 =>
        simp only [Sum.inr.injEq] at hssv
        subst hssv
        rcases hopt idx0 rfl with ⟨hlt, hsome_sid⟩
        exact ⟨hlt, hsid hsome_sid⟩
  cases r with
  | some c =>
    dsimp only; simp only [pure_bind]
    exact hAfter c
  | none =>
    dsimp only; simp only [StateT.run_bind]
    refine (lift_sampleT_zeroPost M_cap mo.tStar okM CCoins h).bind fun ⟨coins, h0⟩ hh0 => ?_
    dsimp only at hh0; subst h0
    exact hAfter coins

private theorem startRecv_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : RSt)
    (Tn : T) (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => HkInv mo.tStar (k + 1) z.2 ∧ h.sessions.length ≤ z.2.sessions.length ∧
        ∀ γ' σ' rsv, z.1 = some (some (γ', σ', rsv)) →
          ∀ sIdx, rsv = .inr sIdx → sIdx < z.2.sessions.length ∧ t' = mo.tStar)
      (((hooksFSMulti cka prng fs Δcka mo false la).startRecv ctx P t' γ σ Tn).run h) := by
  dsimp only [hooksFSMulti]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hca : h.cache t' with _ | ⟨Tc, σc, k0, optIdx⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hauth hheal
    · simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ hs => by cases hs⟩
    · simp only [StateT.run_bind]
      have ht_eq : t' = mo.tStar := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hauth
        exact hauth.2
      refine (lookupMultiF_zeroPost M_cap mo.tStar okM (cka.receive γ Tn).2 h).bind
        fun ⟨_, h1⟩ ⟨hse1, hca1⟩ => ?_
      dsimp only at hse1 hca1 ⊢
      refine (regSessMulti_zeroPost M_cap mo.tStar okM (cka.receive γ Tn).2 h1).bind
        fun ⟨sIdx, h2⟩ ⟨hlt2, hge2, hle2, hca2⟩ => ?_
      dsimp only at hlt2 hge2 hle2 hca2 ⊢
      simp only [StateT.run_pure]
      refine ZeroPost.pure ?_
      dsimp only
      refine ⟨⟨?_, ?_⟩, hse1 ▸ hge2, ?_⟩
      · exact Nat.le_trans hle2 (Nat.add_le_add_right (hse1 ▸ hhk.len_le) 1)
      · intro t'' entry idx' hent hidx'
        rw [hca2, hca1] at hent
        rcases hhk.cache_ok t'' entry idx' hent hidx' with ⟨hlt0, heq0⟩
        exact ⟨Nat.lt_of_lt_of_le hlt0 (hse1 ▸ hge2), heq0⟩
      · intro _ _ rsv hs idx' hrsv
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨_, _, rfl⟩
        injection hrsv with h_eq
        subst h_eq
        exact ⟨hlt2, ht_eq⟩
    · simp only [StateT.run_pure]
      exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ hs => by cases hs⟩
  · by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte, StateT.run_pure]
      refine ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, ?_⟩
      intro _ _ rsv hs idx' hrsv
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨_, _, rfl⟩
      cases optIdx with
      | none => simp at hrsv
      | some idx0 =>
        simp only [Sum.inr.injEq] at hrsv
        subst hrsv
        exact hhk.cache_ok t' (Tc, σc, k0, some idx0) idx0 hca rfl
    · simp only [hTc, ↓reduceIte, Bool.false_eq_true]
      split_ifs with hauth hheal
      · simp only [StateT.run_pure]
        exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ hs => by cases hs⟩
      · simp only [StateT.run_bind]
        have ht_eq : t' = mo.tStar := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hauth
          exact hauth.2
        refine (lookupMultiF_zeroPost M_cap mo.tStar okM (cka.receive γ Tn).2 h).bind
          fun ⟨_, h1⟩ ⟨hse1, hca1⟩ => ?_
        dsimp only at hse1 hca1 ⊢
        refine (regSessMulti_zeroPost M_cap mo.tStar okM (cka.receive γ Tn).2 h1).bind
          fun ⟨sIdx, h2⟩ ⟨hlt2, hge2, hle2, hca2⟩ => ?_
        dsimp only at hlt2 hge2 hle2 hca2 ⊢
        simp only [StateT.run_pure]
        refine ZeroPost.pure ?_
        dsimp only
        refine ⟨⟨?_, ?_⟩, hse1 ▸ hge2, ?_⟩
        · exact Nat.le_trans hle2 (Nat.add_le_add_right (hse1 ▸ hhk.len_le) 1)
        · intro t'' entry idx' hent hidx'
          rw [hca2, hca1] at hent
          rcases hhk.cache_ok t'' entry idx' hent hidx' with ⟨hlt0, heq0⟩
          exact ⟨Nat.lt_of_lt_of_le hlt0 (hse1 ▸ hge2), heq0⟩
        · intro _ _ rsv hs idx' hrsv
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨_, _, rfl⟩
          injection hrsv with h_eq
          subst h_eq
          exact ⟨hlt2, ht_eq⟩
      · simp only [StateT.run_pure]
        exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ hs => by cases hs⟩

private theorem fsSend_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ)
    (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) (hcap : k ≤ M_cap)
    (hssv : ∀ sIdx, ssv = .inr sIdx → sIdx < h.sessions.length ∧ hdr.1 = mo.tStar)
    (hm : match pair with
          | none => okM m = true
          | some (m₀, m₁) => okM m₀ = true ∧ okM m₁ = true) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' e, z.1 = some (v', e) → ∀ sIdx, v' = .inr sIdx → ssv = .inr sIdx)
      (((hooksFSMulti cka prng fs Δcka mo false la).fsSend ctx P t' ssv hdr m pair).run h) := by
  dsimp only [hooksFSMulti]
  cases ssv with
  | inl ss =>
    simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, _⟩; simp at hv⟩
  | inr sIdx =>
    rcases hssv sIdx rfl with ⟨hsIdx_lt, hhdr_eq⟩
    have hsIdx_cap : ¬ M_cap ≤ sIdx := by have := hhk.len_le; omega
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : (!(ctx.safeCh (2 + Δcka) P) && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hcond, ↓reduceIte]
      cases la with
      | true =>
        simp only [↓reduceIte, Bool.not_false]
        exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
          fun ⟨res, h1⟩ hh1 => ?_
        dsimp only at hh1; subst h1
        cases res with
        | none =>
          simp only [Bool.not_false, ↓reduceIte]
          exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
        | some _ =>
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases pair with _ | ⟨m₀, m₁⟩
          · simp only [StateT.run_bind]
            refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
              (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hm, hhdr_eq]) _).bind
              fun ⟨e?, h2⟩ hh2 => ?_
            dsimp only at hh2; subst hh2
            rcases e? with _ | e
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                rcases hs with ⟨rfl, _⟩; exact hv⟩
          · simp only [StateT.run_bind]
            refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
              (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hm.1, hm.2, hhdr_eq]) _).bind
              fun ⟨e?, h2⟩ hh2 => ?_
            dsimp only at hh2; subst hh2
            rcases e? with _ | e
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
            · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
              exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                rcases hs with ⟨rfl, _⟩; exact hv⟩
    · simp only [hcond, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      rcases pair with _ | ⟨m₀, m₁⟩
      · simp only [StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hm, hhdr_eq]) _).bind
          fun ⟨e?, h2⟩ hh2 => ?_
        dsimp only at hh2; subst hh2
        rcases e? with _ | e
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
          exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            rcases hs with ⟨rfl, _⟩; exact hv⟩
      · simp only [StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hm.1, hm.2, hhdr_eq]) _).bind
          fun ⟨e?, h2⟩ hh2 => ?_
        dsimp only at hh2; subst hh2
        rcases e? with _ | e
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs => by cases hs⟩
        · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
          exact ZeroPost.pure ⟨rfl, rfl, fun _ _ hs _ hv => by
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            rcases hs with ⟨rfl, _⟩; exact hv⟩

private theorem fsRecv_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t' : ℕ)
    (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) (hcap : k ≤ M_cap)
    (hrsv : ∀ sIdx, rsv = .inr sIdx → sIdx < h.sessions.length ∧ hdr.1 = mo.tStar) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        ∀ v' i m, z.1 = some (some (v', i, m)) → ∀ sIdx, v' = .inr sIdx → rsv = .inr sIdx)
      (((hooksFSMulti cka prng fs Δcka mo false la).fsRecv ctx P t' rsv hdr e rec).run h) := by
  dsimp only [hooksFSMulti]
  cases rsv with
  | inl rs =>
    simp only [StateT.run_pure]
    exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
      cases hfr : fs.receive rs hdr e with
      | none => simp [hfr] at hs
      | some o =>
        simp only [hfr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, _, _⟩; simp at hv⟩
  | inr sIdx =>
    rcases hrsv sIdx rfl with ⟨hsIdx_lt, hhdr_eq⟩
    have hsIdx_cap : ¬ M_cap ≤ sIdx := by have := hhk.len_le; omega
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : ((((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isNone &&
        !(healedBy ctx.tL (2 + Δcka) t') && !((h.book sIdx).getD {}).sCorr) = true
    · simp only [hcond, ↓reduceIte]
      cases la with
      | true =>
        simp only [↓reduceIte, Bool.not_false]
        exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
          fun ⟨res0, h1⟩ hh1 => ?_
        dsimp only at hh1; subst h1
        cases res0 with
        | none =>
          simp only [Bool.not_false, ↓reduceIte]
          exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        | some _ =>
          simp only [StateT.run_bind, StateT.run_modify, pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hm_some : (((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isSome with
          | true =>
            simp only [↓reduceIte, StateT.run_bind]
            refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
              (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]) _).bind
              fun ⟨res, h2⟩ hh2 => ?_
            dsimp only at hh2; subst hh2
            rcases res with _ | (_ | ⟨i, mo'⟩)
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
            · simp only [StateT.run_bind, StateT.run_get, pure_bind]
              split_ifs
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                rcases mo' with _ | m
                · rcases rec with _ | rec0
                  · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
                  · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                      simp only [Option.some.injEq, Prod.mk.injEq] at hs
                      rcases hs with ⟨rfl, _, _⟩; exact hv⟩
                · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                    simp only [Option.some.injEq, Prod.mk.injEq] at hs
                    rcases hs with ⟨rfl, _, _⟩; exact hv⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
            refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
              (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]) _).bind
              fun ⟨res, h2⟩ hh2 => ?_
            dsimp only at hh2; subst hh2
            rcases res with _ | (_ | ⟨i, mo'⟩)
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
            · simp only [StateT.run_bind, StateT.run_get, pure_bind]
              split_ifs
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
                rcases mo' with _ | m
                · rcases rec with _ | rec0
                  · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
                  · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                      simp only [Option.some.injEq, Prod.mk.injEq] at hs
                      rcases hs with ⟨rfl, _, _⟩; exact hv⟩
                · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                    simp only [Option.some.injEq, Prod.mk.injEq] at hs
                    rcases hs with ⟨rfl, _, _⟩; exact hv⟩
    · simp only [hcond, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      cases hm_some : (((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))).isSome with
      | true =>
        simp only [↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]) _).bind
          fun ⟨res, h2⟩ hh2 => ?_
        dsimp only at hh2; subst hh2
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split_ifs
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            rcases mo' with _ | m
            · rcases rec with _ | rec0
              · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
              · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                  simp only [Option.some.injEq, Prod.mk.injEq] at hs
                  rcases hs with ⟨rfl, _, _⟩; exact hv⟩
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                rcases hs with ⟨rfl, _, _⟩; exact hv⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
        refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
          (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass, hhdr_eq]) _).bind
          fun ⟨res, h2⟩ hh2 => ?_
        dsimp only at hh2; subst hh2
        rcases res with _ | (_ | ⟨i, mo'⟩)
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
        · simp only [StateT.run_bind, StateT.run_get, pure_bind]
          split_ifs
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
            rcases mo' with _ | m
            · rcases rec with _ | rec0
              · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs => by cases hs⟩
              · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                  simp only [Option.some.injEq, Prod.mk.injEq] at hs
                  rcases hs with ⟨rfl, _, _⟩; exact hv⟩
            · exact ZeroPost.pure ⟨rfl, rfl, fun _ _ _ hs _ hv => by
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                rcases hs with ⟨rfl, _, _⟩; exact hv⟩

private theorem reveal_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) (hcap : k ≤ M_cap)
    (hvp : PartyInv mo.tStar h.sessions.length vp) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      (((hooksFSMulti cka prng fs Δcka mo false la).reveal ctx P vp).run h) := by
  dsimp only [hooksFSMulti]
  rcases hvs_eq : vp.vS with _ | (ss | sIdx)
  · dsimp only; split_ifs <;> exact ZeroPost.pure ⟨rfl, rfl⟩
  · dsimp only; split_ifs <;> exact ZeroPost.pure ⟨rfl, rfl⟩
  · have hsIdx_lt : sIdx < h.sessions.length := (hvp.1 sIdx hvs_eq).1
    have hsIdx_cap : ¬ M_cap ≤ sIdx := by have := hhk.len_le; omega
    dsimp only
    cases la with
    | true =>
      exact ZeroPost.pure ⟨rfl, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
      refine (liftFSMulti_query_zeroPost M_cap mo.tStar okM sIdx _
        (by simp [badMultiQuery, hsIdx_cap, encBadMsg, queryADOutsideClass]) h).bind
        fun ⟨res, h1⟩ hh1 => ?_
      dsimp only at hh1; subst h1
      cases res with
      | none =>
        dsimp only; exact ZeroPost.pure ⟨rfl, rfl⟩
      | some ss =>
        dsimp only
        split_ifs <;> exact ZeroPost.pure ⟨rfl, rfl⟩

private theorem vSend_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) (hcap : k + 1 ≤ M_cap)
    (hs : PartyInv mo.tStar h.sessions.length s)
    (hm : match pair with
          | none => okM m = true
          | some (m₀, m₁) => okM m₀ = true ∧ okM m₁ = true) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => HkInv mo.tStar (k + 1) z.2 ∧ h.sessions.length ≤ z.2.sessions.length ∧
        ∀ st' c, z.1 = some (st', c) → PartyInv mo.tStar z.2.sessions.length st')
      ((vSend (hooksFSMulti cka prng fs Δcka mo false la) ctx P s m pair r).run h) := by
  unfold vSend
  cases hsend : s.id.sendsIn (s.tcur + 1) with
  | true =>
    simp only [↓reduceIte, StateT.run_bind]
    refine (startSend_zeroPost M_cap k okM cka prng fs Δcka mo la ctx P (s.tcur + 1)
      s.γ s.root r h hhk).bind fun ⟨o, h1⟩ ⟨hhk1, hge1, hss⟩ => ?_
    dsimp only at hhk1 hge1 hss ⊢
    rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]
      exact ZeroPost.pure ⟨hhk1, hge1, fun _ _ hc => by cases hc⟩
    · simp only [pure_bind, StateT.run_bind]
      refine (fsSend_zeroPost M_cap (k + 1) okM cka prng fs Δcka mo la ctx P (s.tcur + 1) ss
        (s.tcur + 1, some T') m pair h1 hhk1 hcap
        (fun sIdx hv_eq => hss γ' T' σ' ss rfl sIdx hv_eq) hm).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      dsimp only at hse2 hca2 hv_eq ⊢
      have hhk2 : HkInv mo.tStar (k + 1) h2 :=
        ⟨hse2 ▸ hhk1.len_le, fun t'' ent idx' hent hidx' => by
          rw [hca2] at hent; rw [hse2]; exact hhk1.cache_ok t'' ent idx' hent hidx'⟩
      rcases res with _ | ⟨v', e⟩
      · exact ZeroPost.pure ⟨hhk2, hse2 ▸ hge1, fun _ _ hc => by cases hc⟩
      · refine ZeroPost.pure ?_
        dsimp only
        refine ⟨hhk2, hse2 ▸ hge1, fun st' _ hc => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, _⟩
        rw [hse2]
        refine ⟨fun sIdx hv' => ?_, (hs.mono_len hge1).2⟩
        simp only [Option.some.injEq] at hv'
        have hex := hss γ' T' σ' ss rfl sIdx (hv_eq v' e rfl sIdx hv')
        exact ⟨hex.1, fun _ => hex.2⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    rcases hv : s.vS with _ | v
    · exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun st' _ hc => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        exact hc.1 ▸ hs⟩
    · simp only [StateT.run_bind]
      refine (fsSend_zeroPost M_cap (k + 1) okM cka prng fs Δcka mo la ctx P s.tcur v
        (s.tcur, s.curCkaMsg) m pair h (hhk.mono_k (Nat.le_succ k)) hcap
        (fun sIdx hv_eq =>
          ⟨(hs.1 sIdx (hv ▸ hv_eq ▸ rfl)).1, (hs.1 sIdx (hv ▸ hv_eq ▸ rfl)).2 hsend⟩) hm).bind
        fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
      dsimp only at hse2 hca2 hv_eq ⊢
      have hhk2 : HkInv mo.tStar (k + 1) h2 :=
        ⟨hse2 ▸ (hhk.mono_k (Nat.le_succ k)).len_le, fun t'' ent idx' hent hidx' => by
          rw [hca2] at hent; rw [hse2]
          exact (hhk.mono_k (Nat.le_succ k)).cache_ok t'' ent idx' hent hidx'⟩
      rcases res with _ | ⟨v', e⟩
      · exact ZeroPost.pure ⟨hhk2, hse2 ▸ le_rfl, fun _ _ hc => by cases hc⟩
      · refine ZeroPost.pure ?_
        dsimp only
        refine ⟨hhk2, hse2 ▸ le_rfl, fun st' _ hc => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, _⟩
        rw [hse2]
        refine ⟨fun sIdx hv' => ?_, hs.2⟩
        simp only [Option.some.injEq] at hv'
        have hv0 : v = .inr sIdx := hv_eq v' e rfl sIdx hv'
        exact hs.1 sIdx (hv ▸ hv0 ▸ rfl)

private theorem vRecv_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (c : Header T × E)
    (rec : Option (Record M (Header T × E)))
    (h : FSMultiState T RSt K I E)
    (hhk : HkInv mo.tStar k h) (hcap : k + 1 ≤ M_cap)
    (hs : PartyInv mo.tStar h.sessions.length s) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => HkInv mo.tStar (k + 1) z.2 ∧ h.sessions.length ≤ z.2.sessions.length ∧
        ∀ st' t' i' m', z.1 = some (some (st', t', i', m')) →
          PartyInv mo.tStar z.2.sessions.length st')
      ((vRecv (hooksFSMulti cka prng fs Δcka mo false la) ctx P s c rec).run h) := by
  rcases c with ⟨⟨t, optTn⟩, e⟩
  unfold vRecv
  dsimp only
  cases hguard : (s.id.sendsIn t || decide (s.tcur + 1 < t)) with
  | true =>
    exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ _ hc => by cases hc⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hsends_false : s.id.sendsIn t = false := by
      simp only [Bool.or_eq_false_iff] at hguard
      exact hguard.1
    by_cases hnew : t = s.tcur + 1
    · subst hnew
      simp only [↓reduceIte]
      rcases optTn with _ | Tn
      · simp only [pure_bind]
        exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ _ hc => by cases hc⟩
      · dsimp only; simp only [StateT.run_bind]
        refine (startRecv_zeroPost M_cap k okM cka prng fs Δcka mo la ctx P (s.tcur + 1)
          s.γ s.root Tn h hhk).bind fun ⟨o, h1⟩ ⟨hhk1, hge1, hrs⟩ => ?_
        dsimp only at hhk1 hge1 hrs ⊢
        rcases o with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind]
          exact ZeroPost.pure ⟨hhk1, hge1, fun _ _ _ _ hc => by cases hc⟩
        · simp only [pure_bind]
          exact ZeroPost.pure ⟨hhk1, hge1, fun _ _ _ _ hc => by cases hc⟩
        · simp only [pure_bind, Function.update_self, StateT.run_bind]
          refine (fsRecv_zeroPost M_cap (k + 1) okM cka prng fs Δcka mo la ctx P (s.tcur + 1) rs
            (s.tcur + 1, some Tn) e rec h1 hhk1 hcap
            (fun sIdx hv_eq => hrs γ' σ' rs rfl sIdx hv_eq)).bind
            fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
          dsimp only at hse2 hca2 hv_eq ⊢
          have hhk2 : HkInv mo.tStar (k + 1) h2 :=
            ⟨hse2 ▸ hhk1.len_le, fun t'' ent idx' hent hidx' => by
              rw [hca2] at hent; rw [hse2]; exact hhk1.cache_ok t'' ent idx' hent hidx'⟩
          rcases res with _ | (_ | ⟨v', i', m'⟩)
          · exact ZeroPost.pure ⟨hhk2, hse2 ▸ hge1, fun _ _ _ _ hc => by cases hc⟩
          · exact ZeroPost.pure ⟨hhk2, hse2 ▸ hge1, fun _ _ _ _ hc => by cases hc⟩
          · refine ZeroPost.pure ?_
            dsimp only
            refine ⟨hhk2, hse2 ▸ hge1, fun st' _ _ _ hc => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, _, _, _⟩
            rw [hse2]
            refine ⟨fun sIdx hv => ?_, fun t'' sIdx hr => ?_⟩
            · refine ⟨((hs.mono_len hge1).1 sIdx hv).1, fun hns => ?_⟩
              exfalso
              rw [sendsIn_succ_of_false s.id (s.tcur + 1) hsends_false] at hns
              cases hns
            · by_cases ht : t'' = s.tcur + 1
              · subst ht
                simp only [Function.update_self, Option.some.injEq] at hr
                exact hrs γ' σ' rs rfl sIdx (hv_eq v' i' m' rfl sIdx hr)
              · simp only [Function.update_of_ne ht] at hr
                exact (hs.mono_len hge1).2 t'' sIdx hr
    · simp only [hnew, ↓reduceIte, pure_bind]
      rcases hv : s.vR t with _ | v
      · exact ZeroPost.pure ⟨hhk.mono_k (Nat.le_succ k), le_rfl, fun _ _ _ _ hc => by cases hc⟩
      · simp only [StateT.run_bind]
        refine (fsRecv_zeroPost M_cap (k + 1) okM cka prng fs Δcka mo la ctx P t v
          (t, optTn) e rec h (hhk.mono_k (Nat.le_succ k)) hcap
          (fun sIdx hv_eq => hs.2 t sIdx (hv ▸ hv_eq ▸ rfl))).bind
          fun ⟨res, h2⟩ ⟨hse2, hca2, hv_eq⟩ => ?_
        dsimp only at hse2 hca2 hv_eq ⊢
        have hhk2 : HkInv mo.tStar (k + 1) h2 :=
          ⟨hse2 ▸ (hhk.mono_k (Nat.le_succ k)).len_le, fun t'' ent idx' hent hidx' => by
            rw [hca2] at hent; rw [hse2]
            exact (hhk.mono_k (Nat.le_succ k)).cache_ok t'' ent idx' hent hidx'⟩
        rcases res with _ | (_ | ⟨v', i', m'⟩)
        · exact ZeroPost.pure ⟨hhk2, hse2 ▸ le_rfl, fun _ _ _ _ hc => by cases hc⟩
        · exact ZeroPost.pure ⟨hhk2, hse2 ▸ le_rfl, fun _ _ _ _ hc => by cases hc⟩
        · refine ZeroPost.pure ?_
          dsimp only
          refine ⟨hhk2, hse2 ▸ le_rfl, fun st' _ _ _ hc => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, _, _, _⟩
          rw [hse2]
          refine ⟨hs.1, fun t'' sIdx hr => ?_⟩
          by_cases ht : t'' = t
          · subst t''
            simp only [Function.update_self, Option.some.injEq] at hr
            exact hs.2 t sIdx (hv ▸ (hv_eq v' i' m' rfl sIdx hr) ▸ rfl)
          · simp only [Function.update_of_ne ht] at hr
            exact hs.2 t'' sIdx hr

private theorem commitE_st_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool)
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hs_st : ∀ Q, PartyInv mo.tStar es.h.sessions.length (s.st Q))
    (hnew : PartyInv mo.tStar es.h.sessions.length new) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => z.2.h = es.h ∧ z.2.g = es.g ∧
        ∀ s₁, z.1 = some s₁ → ∀ Q, PartyInv mo.tStar es.h.sessions.length (s₁.st Q))
      ((commitE (hooksFSMulti cka prng fs Δcka mo false la) s P old new pos).run es) := by
  unfold commitE liftH
  simp only [hooksFSMulti, StateT.run_bind, pure_bind]
  dsimp only [StateT.run_pure]
  refine ZeroPost.pure ⟨rfl, rfl, fun s₁ hs1 Q => ?_⟩
  injection hs1 with hs1'
  subst hs1'
  exact partyInv_update
    (partyInv_update (fun R => by simpa [GameState.delete] using hs_st R) le_rfl P hnew)
    le_rfl P hnew Q

private theorem coinsE_zeroPost
    {Γ T RSt K I SS RS M E : Type}
    (M_cap k : ℕ) (okM : M → Bool) (mo : Mode) (u : unifSpec.Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar k z.2) ((coinsE u).run es) := by
  unfold coinsE
  rw [StateT.run_lift]
  exact (ZeroPost.query_false (spec := unifSpec + FSMultiSpec SS RS T M E)
    (.inl u) (badMultiQuery_inl M_cap mo.tStar okM u)).bind
    fun _ _ => ZeroPost.pure hinv

private theorem initFSMultiRaw_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (M_cap : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (b : Bool)
    (ht0 : 0 < mo.tStar) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun es₀ => MultiInv mo.tStar 0 es₀)
      (initFSMultiRaw cka prng fs lam mo b) := by
  unfold initFSMultiRaw
  refine (sampleT_zeroPost M_cap mo.tStar okM KR).bind fun kr _ => ?_
  refine (sampleT_zeroPost M_cap mo.tStar okM KC).bind fun kc _ => ?_
  refine (rootFSMulti_zeroPost M_cap okM prng mo 0 lam (prng.init kr) {}).bind
    fun ⟨⟨σ, k0, sid⟩, h1⟩ ⟨hsid, hse1, hca1⟩ => ?_
  dsimp only at hsid hse1 hca1 ⊢
  have hsid_none : sid = none := by
    cases h : sid with
    | none => rfl
    | some _ => exfalso; have := hsid (by simp [h]); omega
  subst hsid_none
  refine (regSessOptMulti_zeroPost M_cap mo.tStar okM none h1).bind
    fun ⟨optIdx, h2⟩ ⟨hopt, _, hle2, hca2⟩ => ?_
  dsimp only at hopt hle2 hca2 ⊢
  have hopt_none : optIdx = none := by
    cases h : optIdx with
    | none => rfl
    | some sIdx => exfalso; exact Bool.noConfusion (hopt sIdx h).2
  subst hopt_none
  refine ZeroPost.pure ?_
  dsimp only
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp only at hle2 ⊢
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hle2
    have h1_zero : h1.sessions.length = 0 := by rw [hse1]; rfl
    omega
  · intro t' e sIdx hent _
    rw [hca2, hca1] at hent
    cases hent
  · intro P
    exact mkParties_partyInv (cka.initA kc) (cka.initB kc) σ
      (fs.initSender k0) (fs.initReceiver k0) mo.tStar h2.sessions.length P

private theorem transmitE_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (la : Bool) (π : Policy)
    (q : Party × M × Option CCoins)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hm : okM q.2.1 = true) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((transmitE (hooksFSMulti cka prng fs Δcka mo false la) (2 + Δcka) qep π q).run es) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      dsimp only; simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
    | some s₁ =>
      dsimp only
      have hst1 : s₁.st = es.g.st := epMgmt_st_eq es.g s₁ (2 + Δcka) qep P r.isSome hep
      split_ifs
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroPost.pure ⟨hinv.hk.mono_k (Nat.le_succ k), hinv.st_ok⟩
      · simp only [StateT.run_bind]
        refine (liftH_zeroPost (vSend_zeroPost M_cap k okM cka prng fs Δcka mo la s₁ P
          (s₁.st P) m none r es.h hinv.hk hcap (hst1 ▸ hinv.st_ok P) hm)).bind
          fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
        dsimp only at hhk1 hge1 hst' hg1 ⊢
        rcases res with _ | ⟨st', c⟩
        · dsimp only
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ (hinv.st_ok Q).mono_len hge1⟩
        · dsimp only
          refine ZeroPost.pure ⟨hhk1, fun Q => ?_⟩
          dsimp only
          rw [record_st_eq]
          exact partyInv_update (fun R => hst1 ▸ hinv.st_ok R) hge1 P (hst' st' c rfl) Q

private theorem challE_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (π : Policy)
    (q : Party × M × M × Option CCoins)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hm : okM q.2.1 = true ∧ okM q.2.2.1 = true)
    (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((challE (hooksFSMulti cka prng fs Δcka mo false la) (2 + Δcka) qep cfg π q).run es) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases habort : (es.abort || es.g.win) with
  | true =>
    exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      dsimp only; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
    | some s₁ =>
      dsimp only
      have hst1 : s₁.st = es.g.st := epMgmt_st_eq es.g s₁ (2 + Δcka) qep P r.isSome hep
      cases hch : (!s₁.safeCh (2 + Δcka) P || !cfg.challAllowedIn (s₁.epoch P)) with
      | true =>
        exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hdoom : π.leakDoom es.g s₁ with
        | true =>
          simp only [↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroPost.pure ⟨hinv.hk.mono_k (Nat.le_succ k), hinv.st_ok⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
          let mChosen := (cfg.challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)
          refine (liftH_zeroPost (vSend_zeroPost M_cap k okM cka prng fs Δcka mo la s₁ P
            (s₁.st P) mChosen (some (m₀, m₁)) r es.h hinv.hk hcap (hst1 ▸ hinv.st_ok P) hm)).bind
            fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
          dsimp only at hhk1 hge1 hst' hg1 ⊢
          rcases res with _ | ⟨st', c⟩
          · dsimp only
            simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ (hinv.st_ok Q).mono_len hge1⟩
          · dsimp only
            refine ZeroPost.pure ⟨hhk1, fun Q => ?_⟩
            dsimp only
            rw [record_st_eq]
            exact partyInv_update (fun R => hst1 ▸ hinv.st_ok R) hge1 P (hst' st' c rfl) Q

private theorem deliverE_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka maxSkip : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((deliverE (hooksFSMulti cka prng fs Δcka mo false la) maxSkip cfg q).run es) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · cases es.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
    | some r =>
      simp only [StateT.run_bind]
      refine (liftH_zeroPost (vRecv_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
        (es.g.st P) c (some r) es.h hinv.hk hcap (hinv.st_ok P))).bind
        fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
      have hst_es1 : ∀ Q, PartyInv mo.tStar es1.h.sessions.length (es.g.st Q) :=
        fun Q => (hinv.st_ok Q).mono_len (by dsimp only at hge1; exact hge1)
      dsimp only at hhk1 hge1 hst' hg1 ⊢
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · dsimp only
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
      · dsimp only
        split_ifs <;>
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
      · dsimp only
        simp only [StateT.run_bind]
        refine (commitE_st_zeroPost M_cap okM cka prng fs Δcka mo la es.g P (es.g.st P)
          st' r.pos es1 hst_es1 (hst' st' t' i' m' rfl)).bind
          fun ⟨s₁?, es2⟩ ⟨hh2, hg2, hs1_ok⟩ => ?_
        dsimp only at hh2 hg2 hs1_ok ⊢
        rcases s₁? with _ | s₁
        · dsimp only
          exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hg2 ▸ hg1 ▸ hst_es1 Q⟩
        · dsimp only
          refine ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => ?_⟩
          dsimp only
          split_ifs <;> exact hh2 ▸ hs1_ok s₁ rfl Q

private theorem injectE_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δ qep : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((injectE (hooksFSMulti cka prng fs Δcka mo false la) Δ qep cfg q).run es) := by
  rcases q with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · simp only [StateT.run_bind]
    refine (liftH_zeroPost (vRecv_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
      (es.g.st P) c none es.h hinv.hk hcap (hinv.st_ok P))).bind
      fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
    dsimp only at hhk1 hge1 hst' hg1 ⊢
    have hst_es1 : ∀ Q, PartyInv mo.tStar es1.h.sessions.length (es.g.st Q) :=
      fun Q => (hinv.st_ok Q).mono_len hge1
    rcases res with _ | (_ | ⟨st', t', i', m'⟩)
    · dsimp only
      simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
    · dsimp only
      exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
    · dsimp only
      split_ifs
      · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
      · simp only [StateT.run_bind]
        refine (commitE_st_zeroPost M_cap okM cka prng fs Δcka mo la es.g P (es.g.st P)
          st' ⟨P.other, t', i'⟩ es1 hst_es1 (hst' st' t' i' m' rfl)).bind
          fun ⟨s₁?, es2⟩ ⟨hh2, hg2, hs1_ok⟩ => ?_
        dsimp only at hh2 hg2 hs1_ok ⊢
        rcases s₁? with _ | s₁
        · dsimp only
          exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hg2 ▸ hg1 ▸ hst_es1 Q⟩
        · dsimp only
          exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hs1_ok s₁ rfl Q⟩
      · exact ZeroPost.pure ⟨hhk1, fun Q => by dsimp only; exact hg1 ▸ hst_es1 Q⟩
      · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩

private theorem injectEB1_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep tStar' : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((injectEB1 (hooksFSMulti cka prng fs Δcka mo false la) qep tStar' cfg q).run es) := by
  rcases q with ⟨P, c⟩
  unfold injectEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · simp only [StateT.run_bind]
    refine (liftH_zeroPost (vRecv_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
      (es.g.st P) c none es.h hinv.hk hcap (hinv.st_ok P))).bind
      fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
    dsimp only at hhk1 hge1 hst' hg1 ⊢
    have hst_es1 : ∀ Q, PartyInv mo.tStar es1.h.sessions.length (es.g.st Q) :=
      fun Q => (hinv.st_ok Q).mono_len hge1
    rcases res with _ | (_ | ⟨st', t', i', m'⟩)
    · dsimp only
      simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
    · dsimp only
      exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
    · dsimp only
      split_ifs
      · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
      · simp only [StateT.run_bind]
        refine (commitE_st_zeroPost M_cap okM cka prng fs Δcka mo la es.g P (es.g.st P)
          st' ⟨P.other, t', i'⟩ es1 hst_es1 (hst' st' t' i' m' rfl)).bind
          fun ⟨s₁?, es2⟩ ⟨hh2, hg2, hs1_ok⟩ => ?_
        dsimp only at hh2 hg2 hs1_ok ⊢
        rcases s₁? with _ | s₁
        · dsimp only
          exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hg2 ▸ hg1 ▸ hst_es1 Q⟩
        · dsimp only
          exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hs1_ok s₁ rfl Q⟩
      · exact ZeroPost.pure ⟨hhk1, fun Q => by dsimp only; exact hg1 ▸ hst_es1 Q⟩
      · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩

private theorem injectEGen_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool) (b1 : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δ qep tStar' : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((injectEGen b1 (hooksFSMulti cka prng fs Δcka mo false la) Δ qep tStar' cfg q).run es) := by
  cases b1
  · exact injectE_zeroPost M_cap k okM cka prng fs Δcka Δ qep mo la cfg q es hcap hinv
  · exact injectEB1_zeroPost M_cap k okM cka prng fs Δcka qep tStar' mo la cfg q es hcap hinv

private theorem corrEShiftedPaper_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool) (l : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (la : Bool) (π : Policy)
    (P : Party)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((corrEShiftedPaper l (hooksFSMulti cka prng fs Δcka mo false la) π P).run es) := by
  unfold corrEShiftedPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
    exact ZeroPost.pure ⟨hinv.hk.mono_k (Nat.le_succ k), hinv.st_ok⟩
  · simp only [StateT.run_bind]
    refine (liftH_zeroPost (reveal_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
      (es.g.st P) es.h hinv.hk (by omega) (hinv.st_ok P))).bind
      fun ⟨stOpt, es1⟩ ⟨⟨hse1, hca1⟩, hg1, _⟩ => ?_
    dsimp only at hse1 hca1 hg1 ⊢
    have hhk1 : HkInv mo.tStar (k + 1) es1.h :=
      ⟨hse1 ▸ hinv.hk.len_le.trans (Nat.le_succ k), fun t'' ent idx' hent hidx' => by
        rw [hca1] at hent; rw [hse1]; exact hinv.hk.cache_ok t'' ent idx' hent hidx'⟩
    rcases stOpt with _ | st
    · dsimp only
      simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ZeroPost.pure ⟨hhk1, fun Q => by dsimp only; rw [hg1, hse1]; exact hinv.st_ok Q⟩
    · dsimp only
      exact ZeroPost.pure ⟨hhk1, fun Q => by
        dsimp only; rw [afterCorrShifted_st_eq, hse1]; exact hinv.st_ok Q⟩

private theorem deliverForgeE_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δ qep : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((deliverForgeE (hooksFSMulti cka prng fs Δcka mo false la) Δ qep cfg q).run es) := by
  rcases q with ⟨P, c, c'⟩
  unfold deliverForgeE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · cases es.g.inTransit P.other c with
    | none =>
      dsimp only; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
    | some r =>
      dsimp only
      split_ifs
      · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
      · simp only [StateT.run_bind]
        refine (liftH_zeroPost (vRecv_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
          (es.g.st P) c' none es.h hinv.hk hcap (hinv.st_ok P))).bind
          fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
        dsimp only at hhk1 hge1 hst' hg1 ⊢
        have hst_es1 : ∀ Q, PartyInv mo.tStar es1.h.sessions.length (es.g.st Q) :=
          fun Q => (hinv.st_ok Q).mono_len hge1
        rcases res with _ | (_ | ⟨st', t', i', m'⟩)
        · dsimp only
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
        · dsimp only
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
        · dsimp only
          split_ifs
          · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
          · simp only [StateT.run_bind]
            refine (commitE_st_zeroPost M_cap okM cka prng fs Δcka mo la es.g P (es.g.st P)
              st' ⟨P.other, t', i'⟩ es1 hst_es1 (hst' st' t' i' m' rfl)).bind
              fun ⟨s₁?, es2⟩ ⟨hh2, hg2, hs1_ok⟩ => ?_
            dsimp only at hh2 hg2 hs1_ok ⊢
            rcases s₁? with _ | s₁
            · dsimp only
              exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hg2 ▸ hg1 ▸ hst_es1 Q⟩
            · dsimp only
              exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hs1_ok s₁ rfl Q⟩
          · exact ZeroPost.pure ⟨hhk1, fun Q => by dsimp only; exact hg1 ▸ hst_es1 Q⟩
          · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩

private theorem deliverForgeEB1_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep tStar' : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((deliverForgeEB1 (hooksFSMulti cka prng fs Δcka mo false la) qep tStar' cfg q).run es) := by
  rcases q with ⟨P, c, c'⟩
  unfold deliverForgeEB1
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
  · cases es.g.inTransit P.other c with
    | none =>
      dsimp only; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
    | some r =>
      dsimp only
      split_ifs
      · simp only [StateT.run_pure]; exact ZeroPost.pure (hinv.mono_k (Nat.le_succ k))
      · simp only [StateT.run_bind]
        refine (liftH_zeroPost (vRecv_zeroPost M_cap k okM cka prng fs Δcka mo la es.g P
          (es.g.st P) c' none es.h hinv.hk hcap (hinv.st_ok P))).bind
          fun ⟨res, es1⟩ ⟨⟨hhk1, hge1, hst'⟩, hg1, _⟩ => ?_
        dsimp only at hhk1 hge1 hst' hg1 ⊢
        have hst_es1 : ∀ Q, PartyInv mo.tStar es1.h.sessions.length (es.g.st Q) :=
          fun Q => (hinv.st_ok Q).mono_len hge1
        rcases res with _ | (_ | ⟨st', t', i', m'⟩)
        · dsimp only
          simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
        · dsimp only
          exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
        · dsimp only
          split_ifs
          · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩
          · simp only [StateT.run_bind]
            refine (commitE_st_zeroPost M_cap okM cka prng fs Δcka mo la es.g P (es.g.st P)
              st' ⟨P.other, t', i'⟩ es1 hst_es1 (hst' st' t' i' m' rfl)).bind
              fun ⟨s₁?, es2⟩ ⟨hh2, hg2, hs1_ok⟩ => ?_
            dsimp only at hh2 hg2 hs1_ok ⊢
            rcases s₁? with _ | s₁
            · dsimp only
              exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hg2 ▸ hg1 ▸ hst_es1 Q⟩
            · dsimp only
              exact ZeroPost.pure ⟨hh2 ▸ hhk1, fun Q => hh2 ▸ hs1_ok s₁ rfl Q⟩
          · exact ZeroPost.pure ⟨hhk1, fun Q => by dsimp only; exact hg1 ▸ hst_es1 Q⟩
          · exact ZeroPost.pure ⟨hhk1, fun Q => hg1 ▸ hst_es1 Q⟩

private theorem deliverForgeEGen_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) (okM : M → Bool) (b1 : Bool)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δ qep tStar' : ℕ) (mo : Mode) (la : Bool)
    (cfg : Config M) (q : Party × (Header T × E) × (Header T × E))
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap) (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((deliverForgeEGen b1 (hooksFSMulti cka prng fs Δcka mo false la) Δ qep tStar' cfg q).run es) := by
  cases b1
  · exact deliverForgeE_zeroPost M_cap k okM cka prng fs Δcka Δ qep mo la cfg q es hcap hinv
  · exact deliverForgeEB1_zeroPost M_cap k okM cka prng fs Δcka qep tStar' mo la cfg q es hcap hinv

private theorem implEDFShiftedPaperGen_inr_zeroPost
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (M_cap k : ℕ) {okB okM : M → Bool} (hok : ∀ m, okB m = true → okM m = true)
    (b1 : Bool) (l : ℕ)
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep maxSkip tStar' : ℕ)
    (mo : Mode) (la : Bool) (cfg : Config M) (π : Policy)
    (qr : (_root_.CryptoGames.SM.Construction.DeliverForge.specDF
      (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiState T RSt K I E))
    (hcap : k + 1 ≤ M_cap)
    (hnb : badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins) (C := Header T × E)
      okB (.inr qr) = false)
    (hinv : MultiInv mo.tStar k es) :
    ZeroPost (badMultiQuery (SS := SS) (RS := RS) (T := T) (M := M) (E := E) M_cap mo.tStar okM)
      (fun z => MultiInv mo.tStar (k + 1) z.2)
      ((implEDFShiftedPaperGen b1 l (hooksFSMulti cka prng fs Δcka mo false la)
        (2 + Δcka) qep maxSkip tStar' cfg π (.inr qr)).run es) := by
  rcases qr with ((((q1 | q2) | q3) | q4) | q5) | q6
  · have hm : okM q1.2.1 = true := hok _ (by simpa [badSendMsgDF] using hnb)
    exact transmitE_zeroPost M_cap k okM cka prng fs Δcka qep mo la π q1 es hcap hm hinv
  · have hm01 : okB q2.2.1 = true ∧ okB q2.2.2.1 = true := by
      simpa [badSendMsgDF, Bool.or_eq_false_iff] using hnb
    exact challE_zeroPost M_cap k okM cka prng fs Δcka qep mo la cfg π q2 es hcap
      ⟨hok _ hm01.1, hok _ hm01.2⟩ hinv
  · exact deliverE_zeroPost M_cap k okM cka prng fs Δcka maxSkip mo la cfg q3 es hcap hinv
  · exact injectEGen_zeroPost M_cap k okM b1 cka prng fs Δcka (2 + Δcka) qep tStar' mo la
      cfg q4 es hcap hinv
  · exact corrEShiftedPaper_zeroPost M_cap k okM l cka prng fs Δcka mo la π q5 es hcap hinv
  · exact deliverForgeEGen_zeroPost M_cap k okM b1 cka prng fs Δcka (2 + Δcka) qep tStar' mo la
      cfg q6 es hcap hinv

private theorem redFSAuthDFShiftedPaperMultiGen_badMultiQuery_zero
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    {okB okM : M → Bool} (hok : ∀ m, okB m = true → okM m = true)
    (q Δcka qep l t : ℕ) (ht0 : 0 < t) (authH la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF okB A) :
    (redFSAuthDFShiftedPaperMultiGen cka prng fs lam Δcka qep l t authH la A).IsQueryBoundP
      (fun x => badMultiQuery q t okM x = true) 0 := by
  have hq' : A.IsQueryBoundP (fun x => x.isRight = true) q :=
    hq.of_imp fun x hx => by cases x <;> exact hx
  let mo : Mode := ⟨authH, some (l - 1), t⟩
  let mo' : Mode := ⟨true, some (l - 1), t⟩
  let impl := implEDFShiftedPaperGen (!authH) l (hooksFSMulti cka prng fs Δcka mo false la)
    (2 + Δcka) qep fs.maxSkip t mo'.cfg mo'.policy
  unfold redFSAuthDFShiftedPaperMultiGen runFSMultiDFShiftedPaper
  rw [bind_assoc]
  exact ((initFSMultiRaw_zeroPost q okM cka prng fs lam mo false ht0).bind fun es₀ hes₀ =>
    (zeroPost_simulateQ_run_budget
      (badSendMsgDF (St := PartyState Γ T RSt SS RS) (Coins := CCoins) (C := Header T × E) okB)
      (badMultiQuery q mo.tStar okM) q (MultiInv mo.tStar) impl
      (fun u k st _ hst => coinsE_zeroPost q k okM mo u st hst)
      (fun qr k st hcap hnb hst =>
        implEDFShiftedPaperGen_inr_zeroPost q k hok (!authH) l cka prng fs Δcka qep
          fs.maxSkip t mo la mo'.cfg mo'.policy qr st hcap hnb hst)
      q 0 A (by omega) hq' hsh es₀ hes₀).bind fun _ _ =>
        ZeroPost.pure (Post := fun _ => True) trivial).1

end ShiftedTwoModeHelpers

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


/-- `TwoModeMultiSessBounds` (`M = q`) for `multiSessPubToAD` on `redFSAuthDFShiftedPaperMultiGen`. -/
theorem redFSAuthDFShiftedPaperMultiGen_twoModeMultiSessBounds
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (hℓ : ℓ < 10 ^ 6)
    (q Δcka qep l t : ℕ) (ht0 : 0 < t) (authH : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q)
    (hsh : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) A)
    (hg : GuardedSMDFShort A) :
    TwoModeMultiSessBounds maxForwardJumps (2 * q) q q
      (fun la (_ : Unit) =>
        multiSessPubToAD protoSignalCodec
          (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la A)) := by
  have hComb : ∀ la,
      (redFSAuthDFShiftedPaperMultiGen (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep l t authH la A).IsQueryBoundP
        (fun x => badMultiQuery q t (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) x = true) 0 :=
    fun la => redFSAuthDFShiftedPaperMultiGen_badMultiQuery_zero
      (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
      (fun _ hm => atomicShortPubB_imp_shortB hm) q Δcka qep l t ht0 authH la A hq hsh
  refine
    { offRange := fun la _ =>
        multiSessPubToAD_offRange protoSignalCodec _ q
          ((hComb la).of_imp fun x hx => by
            rcases x with _ | ⟨sIdx, q₀⟩
            · simp [sessOffRange] at hx
            · simp only [sessOffRange] at hx
              simp [badMultiQuery, hx])
      decBound := fun la _ =>
        multiSessPubToAD_decBound protoSignalCodec _ q
          (Computational.Proofs.E2E.SessionAuthMultiDec.redFSAuthDFShiftedPaperMultiGen_dec_onAnySess
            (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
            (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam q Δcka qep l t authH la A hq)
      shortAD := fun la _ =>
        multiSessPubToAD_shortAD protoSignalCodec _
          ((hComb la).of_imp fun x hx => by
            rcases x with _ | ⟨sIdx, q₀⟩
            · simp [onAnySess] at hx
            · have hbad : encBadMsg
                  (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                  (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
                  (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) (.inr q₀) = true := by
                rcases q₀ with (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> exact hx
              simp [badMultiQuery, hbad])
      guardedShort := fun la _ =>
        multiSessPubToAD_guardedShort protoSignalCodec _
          (Computational.Proofs.E2E.SessionAuthMultiShort.redFSAuthDFShiftedPaperMultiGen_guardedMultiInjectShort
            C Dh encPt encT idOf lam hℓ Δcka qep l t authH la A hsh hg)
      oneADClass := fun la j _ =>
        ⟨t, multiSessPubToAD_oneADClass protoSignalCodec _ j t
          ((hComb la).of_imp fun x hx => by
            have hany := onSess_imp_onAnySess (fsOutsideClass (fun h : Header Pt => h.1) t) j x hx
            rcases x with _ | ⟨sIdx, q₀⟩
            · simp [onAnySess] at hany
            · rw [onAnySess_fsOutsideClass_inr_spec
                  (SS := _root_.CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
                  (RS := _root_.CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))] at hany
              simp [badMultiQuery, hany])⟩ }


end LibsignalBridges

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
