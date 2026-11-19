/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthLazy -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthFS -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.TopAssembly -- proof-setup: allow-public-import
import Computational.Proofs.E2E.SessionAuthQueries

/-!
# Stage-2 Multi-Session Paper `DeliverForge` Hop-3 (`FSMultiSpec`) Inactive-Slot Zero-Query Bound

Establishes the inactive-slot `0`-query bound (`IsQueryBoundP ... 0`) on
`redFSAuthDFPaperMultiBucket` when `q = 0`, `idx ≥ ((qep + 2) - healEpoch tL) * q`, or
`inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false` (under `2 ≤ Δbucket`).-/

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
open _root_.CryptoGames.SM.Construction (Header Mode healEpoch
  inStage2BucketGen redFSAuthDFPaperMultiBucket)
open _root_.CryptoGames.SM.Construction.DeliverForge (AdversaryDF SchemeAdversaryDF
  MakesAtMostQueriesDF bucketAuthCfg engRunDFPaperBucket)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart lFS)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)


section InactiveZeroProof

open _root_.CryptoGames.FSAEAD (
  transmitQuery challengeQuery corruptSenderQuery deliverQuery injectQuery)
open _root_.CryptoGames.SM (Config specDF)
open _root_.CryptoGames.SM.Engine (
  Hooks EState VP Ctx HM TComp liftH abortE coinsE vSend vRecv commitE deliverE injectE)
open _root_.CryptoGames.SM.Construction (
  PartyState sampleT mkParties bucketAuthCfgGen
  FSMultiSpec FSMultiBook FSMultiDFBucketState
  liftFSMultiDFBucket lookupMultiDFBucketF regSessMultiDFBucket regSessOptMultiDFBucket
  rootFSMultiDFBucketPaper hooksFSMultiDFBucketPaper initFSMultiDFBucketPaper
  redFSAuthDFPaperMultiBucketGen)
open _root_.CryptoGames.SM.Construction.DeliverForge (
  transmitEBucket challEBucket corrEPaperBucket deliverForgeE
  implEDFPaperBucketRaw implEDFPaperBucket withWinEpDF)

private inductive ZeroBound {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (P : spec.Domain → Bool) (post : α → Prop) : OracleComp spec α → Prop where
  | pure {a : α} (ha : post a) : ZeroBound P post (Pure.pure a)
  | query_bind {t : spec.Domain} {k : spec.Range t → OracleComp spec α}
      (ht : P t = false) (hk : ∀ y, ZeroBound P post (k y)) :
      ZeroBound P post (liftM (OracleSpec.query t) >>= k)

private theorem ZeroBound.mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : spec.Domain → Bool} {post₁ post₂ : α → Prop} {oa : OracleComp spec α}
    (h : ZeroBound P post₁ oa) (himp : ∀ a, post₁ a → post₂ a) : ZeroBound P post₂ oa := by
  induction h with
  | pure ha => exact ZeroBound.pure (himp _ ha)
  | query_bind ht _ ih => exact ZeroBound.query_bind ht ih

private theorem ZeroBound.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : spec.Domain → Bool} {mid : α → Prop} {post : β → Prop}
    {mx : OracleComp spec α} {f : α → OracleComp spec β}
    (h : ZeroBound P mid mx) (hf : ∀ a, mid a → ZeroBound P post (f a)) :
    ZeroBound P post (mx >>= f) := by
  induction h with
  | pure ha => rw [pure_bind]; exact hf _ ha
  | query_bind ht _ ih => rw [bind_assoc]; exact ZeroBound.query_bind ht ih

private theorem ZeroBound.query_false {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {P : spec.Domain → Bool} {t : spec.Domain} (ht : P t = false) :
    ZeroBound P (fun _ => True) (query (spec := spec) t) := by
  have hq : (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) >>= Pure.pure := by
    rw [show (query (spec := spec) t : OracleComp spec _) = liftM (OracleSpec.query t) from rfl, bind_pure]
  rw [hq]; exact ZeroBound.query_bind ht fun _ => ZeroBound.pure trivial

private theorem ZeroBound.to_isQueryBoundP {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : spec.Domain → Bool} {post : α → Prop} {oa : OracleComp spec α} (h : ZeroBound P post oa) :
    oa.IsQueryBoundP (fun x => P x = true) 0 := by
  induction h with
  | pure _ => exact isQueryBoundP_pure _ _ 0
  | query_bind ht _ ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [ht]), fun y => by simpa [ht] using ih y⟩

private theorem ZeroBound.of_probComp {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} {α : Type}
    {P : (unifSpec + spec₀).Domain → Bool} (hInl : ∀ u, P (.inl u) = false) (oa : ProbComp α) :
    ZeroBound P (fun _ => True) (liftM oa : OracleComp (unifSpec + spec₀) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => change ZeroBound P (fun _ => True) (Pure.pure a); exact ZeroBound.pure trivial
  | query_bind t k ih =>
    change ZeroBound P (fun _ => True)
      ((query (spec := unifSpec + spec₀) (.inl t)) >>= fun u => (liftM (k u) : OracleComp (unifSpec + spec₀) α))
    exact (ZeroBound.query_false (hInl t)).bind fun u _ => ih u

private theorem sampleT_zeroBound {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {P : (unifSpec + tspec).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    (α : Type) [SampleableType α] : ZeroBound P (fun _ => True) (sampleT (tspec := tspec) α) :=
  ZeroBound.of_probComp hInl ($ᵗ α : ProbComp α)

private theorem lift_sampleT_zeroBound {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀} {HS : Type}
    {P : (unifSpec + tspec).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    (α : Type) [SampleableType α] {Q : HS → Prop} (h : HS) (hQ : Q h) :
    ZeroBound P (fun z => Q z.2) ((StateT.lift (sampleT (tspec := tspec) α)).run h) := by
  rw [StateT.run_lift]; exact (sampleT_zeroBound hInl α).bind fun _ _ => ZeroBound.pure hQ

private theorem zeroBound_simulateQ_run_of_zero_inr {ι₁ ι₂ : Type}
    {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂} {S α : Type}
    (P : (unifSpec + spec₂).Domain → Bool)
    (impl : QueryImpl (unifSpec + spec₁) (StateT S (OracleComp (unifSpec + spec₂))))
    (hInl : ∀ (u : unifSpec.Domain) (st : S), ZeroBound P (fun _ => True) ((impl (.inl u)).run st))
    (oa : OracleComp (unifSpec + spec₁) α) (hq : oa.IsQueryBoundP (fun x => x.isRight = true) 0) :
    ∀ (st : S), ZeroBound P (fun _ => True) ((simulateQ impl oa).run st) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st; change ZeroBound P (fun _ => True) (Pure.pure (a, st)); exact ZeroBound.pure trivial
  | query_bind t k ih =>
    intro st; simp only [simulateQ_query_bind, StateT.run_bind]; rw [isQueryBoundP_query_bind_iff] at hq
    rcases t with u | _
    · exact (hInl u st).bind fun z _ => ih z.1 (by simpa using hq.2 z.1) z.2
    · simp at hq

private theorem zeroBound_simulateQ_run_fuel {ι₁ ι₂ : Type}
    {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂} {S α : Type}
    (P : (unifSpec + spec₂).Domain → Bool) (Inv : ℕ → S → Prop)
    (impl : QueryImpl (unifSpec + spec₁) (StateT S (OracleComp (unifSpec + spec₂))))
    (hInl : ∀ (u : unifSpec.Domain) (st : S) (rem : ℕ),
      Inv rem st → ZeroBound P (fun z => Inv rem z.2) ((impl (.inl u)).run st))
    (hInr : ∀ (qr : spec₁.Domain) (st : S) (rem : ℕ),
      Inv (rem + 1) st → ZeroBound P (fun z => Inv rem z.2) ((impl (.inr qr)).run st)) :
    ∀ (rem : ℕ) (oa : OracleComp (unifSpec + spec₁) α)
      (_hq : oa.IsQueryBoundP (fun x => x.isRight = true) rem) (st : S),
      Inv rem st → ZeroBound P (fun _ => True) ((simulateQ impl oa).run st) := by
  intro rem oa
  induction oa using OracleComp.inductionOn generalizing rem with
  | pure a => intro _ st _; change ZeroBound P (fun _ => True) (Pure.pure (a, st)); exact ZeroBound.pure trivial
  | query_bind t k ih =>
    intro hq st hst; simp only [simulateQ_query_bind, StateT.run_bind]; rw [isQueryBoundP_query_bind_iff] at hq
    rcases t with u | qr
    · exact (hInl u st rem hst).bind fun z hz => ih z.1 rem (by simpa using hq.2 z.1) z.2 hz
    · rcases rem with _ | rem'
      · simp at hq
      · exact (hInr qr st rem' hst).bind fun z hz => ih z.1 rem' (by simpa using hq.2 z.1) z.2 hz

private def sessPred {SS RS T M E : Type} (idx : ℕ) : (unifSpec + FSMultiSpec SS RS T M E).Domain → Bool
  | .inl _ => false
  | .inr ⟨s', _⟩ => decide (s' = idx)

private theorem query_eq_liftM {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} (t : spec₀.Domain) :
    (query (spec := spec₀) t : OracleComp spec₀ (spec₀.Range t)) = liftM (spec₀.query t) := rfl

private theorem lift_inr_query_eq {ι₁ ι₂ : Type}
    {s₁ : OracleSpec.{0, 0} ι₁} {s₂ : OracleSpec.{0, 0} ι₂} (q₀ : s₂.Domain) :
    (liftM (OracleSpec.query q₀) : OracleComp (s₁ + s₂) (s₂.Range q₀)) =
      liftM (OracleSpec.query (spec := s₁ + s₂) (Sum.inr q₀)) := rfl

private theorem liftFSMultiDFBucket_query_ne_zero {SS RS T M E Sig K I : Type} {idx sIdx : ℕ} (hne : sIdx ≠ idx)
    (q₀ : (_root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E).Domain)
    {Q : FSMultiDFBucketState T Sig K I E → Prop} (h : FSMultiDFBucketState T Sig K I E) (hQ : Q h) :
    ZeroBound (sessPred idx) (fun z => Q z.2)
      ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E) sIdx (liftM (OracleSpec.query q₀))).run h) := by
  have hq : ((liftFSMultiDFBucket (SS := SS) (RS := RS) (T := T) (M := M) (E := E) sIdx (liftM (OracleSpec.query q₀))).run h) =
      (query (spec := unifSpec + FSMultiSpec SS RS T M E) (Sum.inr ⟨sIdx, q₀⟩) >>= fun a => pure (a, h)) := by
    rw [lift_inr_query_eq]; simp [liftFSMultiDFBucket, StateT.run_lift]
  rw [hq]; exact (ZeroBound.query_false (by simp [sessPred, hne])).bind fun _ _ => ZeroBound.pure hQ

private theorem healEpoch_le_of_inStage2BucketGen {Δbucket t0 : ℕ} {tL : Option ℕ} {par : Bool}
    (hΔb : 2 ≤ Δbucket) (hb : inStage2BucketGen Δbucket tL par t0 = true) : healEpoch tL ≤ t0 := by
  rcases tL with _ | l
  · exact Nat.zero_le _
  · unfold inStage2BucketGen at hb; rw [Bool.and_eq_true] at hb
    simp only [_root_.CryptoGames.SM.lastLeakGuessAdmissible, _root_.CryptoGames.SM.healedBy,
      healEpoch, decide_eq_true_eq] at hb ⊢; omega

private theorem slot_ne_inactive {q Δbucket qep t0 r idx : ℕ} {tL : Option ℕ} {par : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket) (ht_hi : t0 ≤ qep + 1)
    (hbuck : inStage2BucketGen Δbucket tL par t0 = true) (hr : r < q)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false) :
    q * (t0 - healEpoch tL) + r ≠ idx := by
  intro hEq
  have ht_lo : healEpoch tL ≤ t0 := healEpoch_le_of_inStage2BucketGen hΔb hbuck
  set d := t0 - healEpoch tL
  have ht0_eq : healEpoch tL + d = t0 := by omega
  have hd_succ : d + 1 ≤ (qep + 2) - healEpoch tL := by omega
  have hlt : idx < ((qep + 2) - healEpoch tL) * q := calc
    idx = q * d + r := hEq.symm
    _ < q * d + q := Nat.add_lt_add_left hr (q * d)
    _ = (d + 1) * q := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm d q]
    _ ≤ ((qep + 2) - healEpoch tL) * q := Nat.mul_le_mul_right q hd_succ
  have hdiv : idx / q = d := by
    rw [← hEq, Nat.add_comm (q * d) r, Nat.add_mul_div_left r d hqpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  rcases hinact with rfl | hge | hfb
  · exact Nat.lt_irrefl 0 hqpos
  · exact Nat.not_le_of_gt hlt hge
  · rw [hdiv, ht0_eq, hbuck] at hfb; exact Bool.noConfusion hfb

private def NoIdxVP {Γ T RSt SS RS : Type} (idx : ℕ)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) : Prop :=
  vp.vS ≠ some (.inr idx) ∧ ∀ t, vp.vR t ≠ some (.inr idx)

private def NoIdxH {T RSt K I E : Type} (q idx rem : ℕ)
    (h : FSMultiDFBucketState T RSt K I E) : Prop :=
  (∀ t, 1 ≤ t → (h.sessions t).length + rem ≤ q) ∧
  (∀ t c, h.cache t = some c → c.2.2.2 ≠ some idx)

private theorem NoIdxH.mono {T RSt K I E : Type} {q idx rem₁ rem₂ : ℕ}
    {h : FSMultiDFBucketState T RSt K I E}
    (hle : rem₁ ≤ rem₂) (hH : NoIdxH q idx rem₂ h) :
    NoIdxH q idx rem₁ h :=
  ⟨fun t ht => by have := hH.1 t ht; omega, hH.2⟩

private def NoIdxES {Γ T RSt SS RS M E K I : Type} (q idx rem : ℕ)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E)) : Prop :=
  (∀ P, NoIdxVP idx (es.g.st P)) ∧ NoIdxH q idx rem es.h

private theorem NoIdxES.mono {Γ T RSt SS RS M E K I : Type} {q idx rem₁ rem₂ : ℕ}
    {es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E)}
    (hle : rem₁ ≤ rem₂) (hes : NoIdxES q idx rem₂ es) :
    NoIdxES q idx rem₁ es :=
  ⟨hes.1, hes.2.mono hle⟩

private theorem regSessMultiDFBucket_step {T RSt K I E : Type} [DecidableEq I]
    {q Δbucket qep t0 rem idx : ℕ} {tL : Option ℕ} {par : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ht1 : 1 ≤ t0) (ht_hi : t0 ≤ qep + 1)
    (hbuck : inStage2BucketGen Δbucket tL par t0 = true)
    (ik : I) (h : FSMultiDFBucketState T RSt K I E)
    (hH : NoIdxH q idx (rem + 1) h) :
    (regSessMultiDFBucket (q + 1) tL t0 ik h).1 ≠ idx ∧
      NoIdxH q idx rem (regSessMultiDFBucket (q + 1) tL t0 ik h).2 := by
  have hlen : (h.sessions t0).length < q := by have := hH.1 t0 ht1; omega
  unfold regSessMultiDFBucket
  simp only [Nat.add_sub_cancel]
  split_ifs with hmem
  · exact ⟨slot_ne_inactive hqpos hΔb ht_hi hbuck
      (Nat.lt_trans (List.idxOf_lt_length_of_mem hmem) hlen) hinact,
      hH.mono (Nat.le_succ rem)⟩
  · refine ⟨slot_ne_inactive hqpos hΔb ht_hi hbuck hlen hinact, ⟨fun t ht => ?_, hH.2⟩⟩
    by_cases hEq : t = t0
    · subst hEq
      have h1 := hH.1 t ht1
      simp only [Function.update_self, List.length_append, List.length_singleton]; omega
    · have h1 := hH.1 t ht
      simp only [Function.update_of_ne hEq]; omega

private theorem regSessOptMultiDFBucket_step {T RSt K I E : Type} [DecidableEq I]
    {q Δbucket qep t0 rem idx : ℕ} {tL : Option ℕ} {par : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ht1 : 1 ≤ t0) (sid : Option I)
    (hsid : ∀ ik, sid = some ik → t0 ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t0 = true)
    (h : FSMultiDFBucketState T RSt K I E)
    (hH : NoIdxH q idx (rem + 1) h) :
    (regSessOptMultiDFBucket (q + 1) tL t0 sid h).1 ≠ some idx ∧
      NoIdxH q idx rem (regSessOptMultiDFBucket (q + 1) tL t0 sid h).2 := by
  cases sid with
  | none => exact ⟨by simp [regSessOptMultiDFBucket], hH.mono (Nat.le_succ rem)⟩
  | some ik =>
    obtain ⟨ht_hi, hbuck⟩ := hsid ik rfl
    obtain ⟨hne, hH'⟩ := regSessMultiDFBucket_step hqpos hΔb hinact ht1 ht_hi hbuck ik h hH
    simpa [regSessOptMultiDFBucket] using And.intro hne hH'

private theorem lookupMultiDFBucketF_zero {SS RS T M E RSt K I : Type}
    [DecidableEq I] [SampleableType K] (idx t0 : ℕ) (ik : I)
    (h : FSMultiDFBucketState T RSt K I E) :
    ZeroBound (sessPred idx)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache)
      ((lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h) := by
  unfold lookupMultiDFBucketF
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (h.fTable t0).lookup ik with
  | some k => simp only [StateT.run_pure]; exact ZeroBound.pure ⟨rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind]
    refine (lift_sampleT_zeroBound (P := sessPred idx)
      (Q := fun s => s.sessions = h.sessions ∧ s.cache = h.cache) (fun _ => rfl) K h ⟨rfl, rfl⟩).bind
      fun ⟨_, h1⟩ ⟨hs1, hc1⟩ => ?_
    simp only [StateT.run_modify, StateT.run_pure, pure_bind]
    exact ZeroBound.pure ⟨hs1, hc1⟩

private theorem rootFSMultiDFBucketPaper_zero {KR RSt K I T SS RS M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl : Bool) (ik0 : I) (σ0 : RSt) (idx : ℕ)
    (h : FSMultiDFBucketState T RSt K I E) :
    ZeroBound (sessPred idx)
      (fun z => z.2.sessions = h.sessions ∧ z.2.cache = h.cache ∧
        (∀ ik, z.1.2.2 = some ik → t0 ≤ qep + 1 ∧ inStage2BucketGen Δbucket tL par t0 = true))
      ((rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
        prng Δbucket qep tL par t0 pl ik0 σ0).run h) := by
  unfold rootFSMultiDFBucketPaper
  dsimp only
  split
  · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨rfl, rfl, fun _ h => by cases h⟩
  · next h1 =>
    have ht_hi : t0 ≤ qep + 1 := by
      by_cases hlt : qep + 1 < t0
      · simp [hlt] at h1
      · omega
    split
    · next hbuck =>
      split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_zeroBound (P := sessPred idx)
          (Q := fun s => s.sessions = h.sessions ∧ s.cache = h.cache) (fun _ => rfl) I h ⟨rfl, rfl⟩).bind
          fun ⟨_, h1'⟩ h1Eq => ?_
        simp only []
        refine (lift_sampleT_zeroBound (P := sessPred idx)
          (Q := fun s => s.sessions = h.sessions ∧ s.cache = h.cache) (fun _ => rfl) K h1' h1Eq).bind
          fun ⟨_, h2'⟩ ⟨hs2, hc2⟩ => ?_
        simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hs2, hc2, fun _ _ => ⟨ht_hi, hbuck⟩⟩
      · simp only [StateT.run_bind]
        refine (lookupMultiDFBucketF_zero idx t0 ik0 h).bind fun ⟨_, h1'⟩ ⟨hs1, hc1⟩ => ?_
        simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hs1, hc1, fun _ _ => ⟨ht_hi, hbuck⟩⟩
    · split
      · simp only [StateT.run_bind]
        refine (lift_sampleT_zeroBound (P := sessPred idx)
          (Q := fun s => s.sessions = h.sessions ∧ s.cache = h.cache) (fun _ => rfl) I h ⟨rfl, rfl⟩).bind
          fun ⟨_, h1'⟩ h1Eq => ?_
        simp only []
        refine (lift_sampleT_zeroBound (P := sessPred idx)
          (Q := fun s => s.sessions = h.sessions ∧ s.cache = h.cache) (fun _ => rfl) K h1' h1Eq).bind
          fun ⟨_, h2'⟩ ⟨hs2, hc2⟩ => ?_
        simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hs2, hc2, fun _ h => by cases h⟩
      · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨rfl, rfl, fun _ h => by cases h⟩

private theorem initFSMultiDFBucketPaper_zero_any {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δbucket qep : ℕ) (tL : Option ℕ) (par : Bool) (idx : ℕ) :
    ZeroBound (sessPred idx) (fun _ => True)
      ((initFSMultiDFBucketPaper L cka prng fs lam Δbucket qep tL par).run
        ({} : FSMultiDFBucketState T RSt K I E)) := by
  unfold initFSMultiDFBucketPaper
  simp only [StateT.run_bind]
  refine (lift_sampleT_zeroBound (P := sessPred idx) (Q := fun _ => True) (fun _ => rfl) KR
    ({} : FSMultiDFBucketState T RSt K I E) trivial).bind fun ⟨kr, h1⟩ _ => ?_
  simp only []
  refine (lift_sampleT_zeroBound (P := sessPred idx) (Q := fun _ => True) (fun _ => rfl) KC h1 trivial).bind
    fun ⟨_, h2⟩ _ => ?_
  simp only []
  refine (rootFSMultiDFBucketPaper_zero (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng Δbucket qep tL par 0 false lam (prng.init kr) idx h2).bind fun ⟨⟨_, _, _⟩, _⟩ _ => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  exact ZeroBound.pure trivial

private theorem initFSMultiDFBucketPaper_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) {q Δbucket qep idx : ℕ} {tL : Option ℕ} {par : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx q z.2 ∧
        ∀ vAB, z.1 = some vAB → NoIdxVP idx vAB.1 ∧ NoIdxVP idx vAB.2)
      ((initFSMultiDFBucketPaper (q + 1) cka prng fs lam Δbucket qep tL par).run
        ({} : FSMultiDFBucketState T RSt K I E)) := by
  unfold initFSMultiDFBucketPaper
  simp only [StateT.run_bind]
  let h0 : FSMultiDFBucketState T RSt K I E := {}
  refine (lift_sampleT_zeroBound (P := sessPred idx)
    (Q := fun s => s.sessions = h0.sessions ∧ s.cache = h0.cache) (fun _ => rfl) KR h0 ⟨rfl, rfl⟩).bind
    fun ⟨kr, h1⟩ h1Eq => ?_
  simp only []
  refine (lift_sampleT_zeroBound (P := sessPred idx)
    (Q := fun s => s.sessions = h0.sessions ∧ s.cache = h0.cache) (fun _ => rfl) KC h1 h1Eq).bind
    fun ⟨kc, h2⟩ ⟨hs2, hc2⟩ => ?_
  simp only []
  refine (rootFSMultiDFBucketPaper_zero (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
    prng Δbucket qep tL par 0 false lam (prng.init kr) idx h2).bind
    fun ⟨⟨σ, kVal, sid⟩, h3⟩ ⟨hs3, hc3, hsid⟩ => ?_
  simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
  have hsess3 : h3.sessions = fun _ => [] := hs3.trans hs2
  have hcache3 : h3.cache = fun _ => none := hc3.trans hc2
  have hReg : (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).1 ≠ some idx ∧
      NoIdxH q idx q (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).2 := by
    cases sid with
    | none =>
      refine ⟨by simp [regSessOptMultiDFBucket], ⟨fun t _ => ?_, fun t c hc => ?_⟩⟩
      · simp [regSessOptMultiDFBucket, hsess3]
      · simp [regSessOptMultiDFBucket, hcache3] at hc
    | some ik =>
      obtain ⟨ht_hi, hbuck⟩ := hsid ik rfl
      have h0 : h3.sessions 0 = [] := congrFun hsess3 0
      dsimp only [regSessOptMultiDFBucket, regSessMultiDFBucket]
      simp only [h0, List.not_mem_nil, ↓reduceIte, List.length_nil, Nat.add_zero,
        Nat.add_sub_cancel, List.nil_append]
      have hne : q * (0 - healEpoch tL) ≠ idx := by
        simpa only [Nat.add_zero] using slot_ne_inactive hqpos hΔb ht_hi hbuck hqpos hinact
      refine ⟨fun hEq => hne (Option.some.inj hEq), ⟨fun t ht => ?_, fun t c hc => ?_⟩⟩
      · have ht0 : t ≠ 0 := by omega
        simp [Function.update_of_ne ht0, hsess3]
      · simp [hcache3] at hc
  refine ZeroBound.pure ⟨hReg.2, fun vAB hvAB => ?_⟩
  simp only [Option.some.injEq] at hvAB; subst hvAB
  obtain ⟨hneOpt, _⟩ := hReg
  cases hopt : (regSessOptMultiDFBucket (q + 1) tL 0 sid h3).1 with
  | none =>
    simp only [mkParties, NoIdxVP]
    refine ⟨⟨by simp, fun t => ?_⟩, ⟨by simp, fun _ => by simp⟩⟩
    split_ifs <;> simp
  | some sIdx =>
    have hne : sIdx ≠ idx := fun hEq => hneOpt (hopt.trans (congrArg some hEq))
    simp only [mkParties, NoIdxVP]
    refine ⟨⟨by simp, fun t => ?_⟩, ⟨by simp [hne], fun _ => by simp⟩⟩
    split_ifs <;> simp [hne]

private theorem startSend_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep t0 rem idx : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ht1 : 1 ≤ t0)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party)
    (γ0 : Γ) (σ0 : RSt) (r0 : Option CCoins)
    (h : FSMultiDFBucketState T RSt K I E)
    (hH : NoIdxH q idx (rem + 1) h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ gTs, z.1 = some gTs → gTs.2.2.2 ≠ .inr idx)
      (((hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la).startSend
        ctx Pt t0 γ0 σ0 r0).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  have hStep : ∀ (coins : CCoins) (h1 : FSMultiDFBucketState T RSt K I E),
      NoIdxH q idx (rem + 1) h1 →
      ZeroBound (sessPred idx)
        (fun (z : Option (Γ × T × RSt × (SS ⊕ ℕ)) × FSMultiDFBucketState T RSt K I E) =>
          NoIdxH q idx rem z.2 ∧ ∀ gTs, z.1 = some gTs → gTs.2.2.2 ≠ Sum.inr idx)
        ((do
          let cOut := cka.send γ0 coins
          let (σ', kVal, sid) ←
            rootFSMultiDFBucketPaper (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
              prng Δbucket qep tL par t0
              (_root_.CryptoGames.SM.Construction.postLeakDFBucket tL ctx) cOut.2.2 σ0
          let s1 ← get
          let (optIdx, s2) := regSessOptMultiDFBucket (q + 1) tL t0 sid s1
          set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
          let ssv : SS ⊕ ℕ := match optIdx with
            | none => .inl (fs.initSender kVal)
            | some sIdx => .inr sIdx
          return some (cOut.1, cOut.2.1, σ', ssv)).run h1) := by
    intro coins h1 hH1
    simp only [StateT.run_bind]
    refine (rootFSMultiDFBucketPaper_zero (T := T) (SS := SS) (RS := RS) (M := M) (E := E)
      prng Δbucket qep tL par t0 _
      (cka.send γ0 coins).2.2 σ0 idx h1).bind fun ⟨⟨σ', kVal, sid⟩, h2⟩ ⟨hs2, hc2, hsid⟩ => ?_
    simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    have hH2 : NoIdxH q idx (rem + 1) h2 := ⟨hs2 ▸ hH1.1, hc2 ▸ hH1.2⟩
    obtain ⟨hneOpt, hHs2⟩ := regSessOptMultiDFBucket_step hqpos hΔb hinact ht1 sid hsid h2 hH2
    refine ZeroBound.pure ⟨⟨hHs2.1, fun t c hc => ?_⟩, fun gTs hgTs => ?_⟩
    · by_cases hEq : t = t0
      · subst hEq; simp only [Function.update_self, Option.some.injEq] at hc; subst hc; exact hneOpt
      · simp only [Function.update_of_ne hEq] at hc; exact hHs2.2 t c hc
    · simp only [Option.some.injEq] at hgTs; subst hgTs
      cases hopt : (regSessOptMultiDFBucket (q + 1) tL t0 sid h2).1 with
      | none => simp
      | some sIdx =>
        simp only [ne_eq, Sum.inr.injEq]
        exact fun hEq => hneOpt (hopt.trans (congrArg some hEq))
  rcases r0 with _ | c
  · simp only [StateT.run_bind]
    exact (lift_sampleT_zeroBound (P := sessPred idx) (fun _ => rfl) CCoins h hH).bind
      fun ⟨coins, h1⟩ hH1 => hStep coins h1 hH1
  · simp only [StateT.run_bind, StateT.run_pure, pure_bind]; exact hStep c h hH

private theorem startRecv_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep t0 rem idx : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ht1 : 1 ≤ t0)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party)
    (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiDFBucketState T RSt K I E)
    (hH : NoIdxH q idx (rem + 1) h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ gTr, z.1 = some (some gTr) → gTr.2.2 ≠ .inr idx)
      (((hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la).startRecv
        ctx Pt t0 γ0 σ0 tn0).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hNoneBranch :
      ZeroBound (sessPred idx)
        (fun (z : Option (Option (Γ × RSt × (RS ⊕ ℕ))) × FSMultiDFBucketState T RSt K I E) =>
          NoIdxH q idx rem z.2 ∧ ∀ gTr, z.1 = some (some gTr) → gTr.2.2 ≠ Sum.inr idx)
        ((if !(qep + 1 < t0) && inStage2BucketGen Δbucket tL par t0 then
            if tL.isSome && (t0 == healEpoch tL) then
              return (none : Option (Option (Γ × RSt × (RS ⊕ ℕ))))
            else if _root_.CryptoGames.SM.Construction.postLeakDFBucket tL ctx then
              let kk := cka.receive γ0 tn0
              let p := prng.up σ0 kk.2
              return some (some (kk.1, p.1, (Sum.inl (fs.initReceiver p.2) : RS ⊕ ℕ)))
            else do
              let kk := cka.receive γ0 tn0
              let _ ← lookupMultiDFBucketF (SS := SS) (RS := RS) (M := M) t0 kk.2
              let s1 ← get
              let (sIdx, s2) := regSessMultiDFBucket (q + 1) tL t0 kk.2 s1
              set s2
              return some (some (kk.1, (prng.up σ0 kk.2).1, (Sum.inr sIdx : RS ⊕ ℕ)))
          else
            return some none : HM (FSMultiSpec SS RS T M E) (FSMultiDFBucketState T RSt K I E)
              (Option (Option (Γ × RSt × (RS ⊕ ℕ))))).run h) := by
    split
    · next hcond =>
      rw [Bool.and_eq_true] at hcond
      have ht_hi : t0 ≤ qep + 1 := by
        by_cases hlt : qep + 1 < t0
        · simp [hlt] at hcond
        · omega
      have hbuck : inStage2BucketGen Δbucket tL par t0 = true := hcond.2
      split
      · simp only [StateT.run_pure]
        exact ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun _ h => by cases h⟩
      · split
        · simp only [StateT.run_pure]
          exact ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun gTr hgTr => by
            simp only [Option.some.injEq] at hgTr; subst hgTr; simp⟩
        · simp only [StateT.run_bind]
          refine (lookupMultiDFBucketF_zero idx t0 (cka.receive γ0 tn0).2 h).bind
            fun ⟨_, h1⟩ ⟨hs1, hc1⟩ => ?_
          simp only [StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
          have hH1 : NoIdxH q idx (rem + 1) h1 := ⟨hs1 ▸ hH.1, hc1 ▸ hH.2⟩
          obtain ⟨hne, hHs2⟩ :=
            regSessMultiDFBucket_step hqpos hΔb hinact ht1 ht_hi hbuck (cka.receive γ0 tn0).2 h1 hH1
          refine ZeroBound.pure ⟨hHs2, fun gTr hgTr => ?_⟩
          simp only [Option.some.injEq] at hgTr; subst hgTr
          simpa only [ne_eq, Sum.inr.injEq] using hne
    · simp only [StateT.run_pure]
      exact ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun _ h => by cases h⟩
  rcases hc : h.cache t0 with _ | ⟨tCached, σc, kVal, optIdx⟩
  · simpa only [hc] using hNoneBranch
  · by_cases ht : tCached = tn0
    · subst ht
      simp only [↓reduceIte, StateT.run_pure]
      have hneOpt : optIdx ≠ some idx := hH.2 t0 (tCached, σc, kVal, optIdx) hc
      refine ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun gTr hgTr => ?_⟩
      simp only [Option.some.injEq] at hgTr; subst hgTr
      cases optIdx with
      | none => simp
      | some sIdx =>
        simp only [ne_eq, Sum.inr.injEq]; exact fun hEq => hneOpt (congrArg some hEq)
    · simpa only [hc, ht, ↓reduceIte] using hNoneBranch

private theorem fsSendTailBucket_zero {SS RS T M E Sig K I : Type}
    {q idx rem sIdx : ℕ} (hne : sIdx ≠ idx) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T Sig K I E) (hH : NoIdxH q idx rem h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ vc, z.1 = some vc → vc.1 ≠ .inr idx)
      ((do
        let e? ← match pair with
          | some (m₀, m₁) =>
            liftFSMultiDFBucket sIdx (challengeQuery (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
          | none =>
            liftFSMultiDFBucket sIdx (transmitQuery (SenderState := SS) (ReceiverState := RS) hdr m)
        match e? with
        | none => return (none : Option ((SS ⊕ ℕ) × E))
        | some e =>
          modify fun (st : FSMultiDFBucketState T Sig K I E) =>
            let b := (st.book sIdx).getD {}
            let cnt' := b.fsCount + 1
            let b' : FSMultiBook T E :=
              { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
            { st with book := Function.update st.book sIdx (some b') }
          return some (.inr sIdx, e)).run h) := by
  rcases pair with _ | ⟨m₀, m₁⟩ <;>
    simp only [StateT.run_bind, challengeQuery, transmitQuery, query_eq_liftM] <;>
    (refine (liftFSMultiDFBucket_query_ne_zero hne _ h hH).bind fun ⟨e?, h2⟩ hH2 => ?_;
     rcases e? with _ | e;
     · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
     · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
       refine ZeroBound.pure ⟨hH2, fun vc hvc => ?_⟩
       simp only [Option.some.injEq] at hvc; subst hvc; simpa only [ne_eq, Sum.inr.injEq] using hne)

private theorem fsSend_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) {q idx rem : ℕ}
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party) (t0 : ℕ)
    (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiDFBucketState T RSt K I E)
    (hssv : ssv ≠ .inr idx) (hH : NoIdxH q idx rem h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ vc, z.1 = some vc → vc.1 ≠ .inr idx)
      (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsSend
        ctx Pt t0 ssv hdr m pair).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure]
    refine ZeroBound.pure ⟨hH, fun vc hvc => ?_⟩
    simp only [Option.some.injEq] at hvc; subst hvc; simp
  · have hne : sIdx ≠ idx := fun hEq => hssv (congrArg Sum.inr hEq)
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
      refine (liftFSMultiDFBucket_query_ne_zero hne _ h hH).bind fun ⟨o, h1⟩ hH1 => ?_
      rcases o with _ | _
      · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
        exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact fsSendTailBucket_zero hne hdr m pair _ hH1
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact fsSendTailBucket_zero hne hdr m pair h hH

private theorem fsRecvTailBucket_zero {SS RS T M E Sig K I : Type} [DecidableEq T] [DecidableEq E]
    {q idx rem sIdx : ℕ} (hne : sIdx ≠ idx) (la : Bool)
    (matched : Option (ℕ × Header T × E))
    (hdr : Header T) (e : E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T Sig K I E) (hH : NoIdxH q idx rem h) :
    ZeroBound (sessPred idx)
      (fun (z : Option (Option ((RS ⊕ ℕ) × ℕ × M)) × FSMultiDFBucketState T Sig K I E) =>
        NoIdxH q idx rem z.2 ∧ ∀ vim, z.1 = some (some vim) → vim.1 ≠ Sum.inr idx)
      ((do
        let res ← if matched.isSome then
            liftFSMultiDFBucket sIdx (deliverQuery (SenderState := SS) (ReceiverState := RS) hdr e)
          else
            liftFSMultiDFBucket sIdx (injectQuery (SenderState := SS) (ReceiverState := RS) hdr e)
        match res with
        | none => return (none : Option (Option ((RS ⊕ ℕ) × ℕ × M)))
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let s1 ← get
          let bk1 := (s1.book sIdx).getD {}
          if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
            modify fun (st : FSMultiDFBucketState T Sig K I E) => { st with lfWin := true }
            return none
          else
            let drop := (matched.map (fun (x : ℕ × Header T × E) => x.1)).getD i
            modify fun (st : FSMultiDFBucketState T Sig K I E) =>
              let b := (st.book sIdx).getD {}
              let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
              { st with book := Function.update st.book sIdx (some b') }
            match mo', rec with
            | some m, _ => return some (some (.inr sIdx, i, m))
            | none, some r => return some (some (.inr sIdx, i, r.msg))
            | none, none => return none).run h) := by
  split_ifs <;>
    simp only [StateT.run_bind, deliverQuery, injectQuery, query_eq_liftM] <;>
    (refine (liftFSMultiDFBucket_query_ne_zero (SS := SS) (RS := RS) (M := M) hne _ h hH).bind
       fun ⟨res, h1⟩ hH1 => ?_;
     rcases res with _ | (_ | ⟨i, mo'⟩);
     · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
     · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
     · simp only [StateT.run_bind, StateT.run_get, pure_bind]
       split_ifs
       · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
         exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
       · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
         rcases mo' with _ | m
         · rcases rec with _ | r
           · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
           · simp only [StateT.run_pure]
             refine ZeroBound.pure ⟨hH1, fun vim hvim => ?_⟩
             simp only [Option.some.injEq] at hvim; subst hvim
             simpa only [ne_eq, Sum.inr.injEq] using hne
         · simp only [StateT.run_pure]
           refine ZeroBound.pure ⟨hH1, fun vim hvim => ?_⟩
           simp only [Option.some.injEq] at hvim; subst hvim
           simpa only [ne_eq, Sum.inr.injEq] using hne)

private theorem fsRecv_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) {q idx rem : ℕ}
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party) (t0 : ℕ)
    (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E)
    (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T RSt K I E)
    (hrsv : rsv ≠ .inr idx) (hH : NoIdxH q idx rem h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ vim, z.1 = some (some vim) → vim.1 ≠ .inr idx)
      (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).fsRecv
        ctx Pt t0 rsv hdr e rec).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure]
    refine ZeroBound.pure ⟨hH, fun vim hvim => ?_⟩
    rcases hrec : fs.receive rs hdr e with _ | o
    · simp [hrec] at hvim
    · simp only [hrec, Option.map_some, Option.some.injEq] at hvim; subst hvim; simp
  · have hne : sIdx ≠ idx := fun hEq => hrsv (congrArg Sum.inr hEq)
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
      refine (liftFSMultiDFBucket_query_ne_zero (SS := SS) (RS := RS) (M := M) hne _ h hH).bind
        fun ⟨o, h1⟩ hH1 => ?_
      rcases o with _ | _
      · simp only [StateT.run_pure, Bool.not_false, ↓reduceIte]
        exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact fsRecvTailBucket_zero (SS := SS) (RS := RS) hne la _ hdr e rec _ hH1
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact fsRecvTailBucket_zero (SS := SS) (RS := RS) hne la _ hdr e rec h hH

private theorem reveal_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) {q idx rem : ℕ}
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiDFBucketState T RSt K I E)
    (hvp : NoIdxVP idx vp) (hH : NoIdxH q idx (rem + 1) h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2)
      (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).reveal
        ctx Pt vp).run h) := by
  dsimp only [hooksFSMultiDFBucketPaper]
  rcases hvs : vp.vS with _ | (ss | sIdx)
  · split_ifs <;> exact ZeroBound.pure (hH.mono (Nat.le_succ rem))
  · split_ifs <;> exact ZeroBound.pure (hH.mono (Nat.le_succ rem))
  · have hne : sIdx ≠ idx := fun hEq =>
      hvp.1 (hvs.trans (congrArg (fun x : ℕ => some (Sum.inr x : SS ⊕ ℕ)) hEq))
    simp only [StateT.run_bind, corruptSenderQuery, query_eq_liftM]
    refine (liftFSMultiDFBucket_query_ne_zero hne _ h (hH.mono (Nat.le_succ rem))).bind
      fun ⟨o, h1⟩ hH1 => ?_
    rcases o with _ | ss
    · simp only [StateT.run_pure, pure_bind]; exact ZeroBound.pure hH1
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
      split_ifs <;> simp only [StateT.run_pure] <;> exact ZeroBound.pure hH1

private theorem liftH_zero {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {P : (unifSpec + tspec).Domain → Bool} {Γv T Sv SSv RSv M E HS α : Type} {Q : α × HS → Prop}
    {x : HM tspec HS α} {es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS}
    (hx : ZeroBound P Q (x.run es.h)) :
    ZeroBound P (fun z => Q (z.1, z.2.h) ∧ z.2.g = es.g) ((liftH x).run es) := by
  unfold liftH; exact hx.bind fun ⟨_, _⟩ hQ => ZeroBound.pure ⟨hQ, rfl⟩

private theorem coinsE_zero {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {P : (unifSpec + tspec).Domain → Bool} (hInl : ∀ u, P (.inl u) = false)
    {Γv T Sv SSv RSv M E HS : Type} {Q : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS → Prop}
    (u : unifSpec.Domain) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) (hes : Q es) :
    ZeroBound P (fun z => Q z.2) ((coinsE u).run es) := by
  unfold coinsE; rw [StateT.run_lift]
  exact (ZeroBound.query_false (hInl u)).bind fun _ _ => ZeroBound.pure hes

private theorem epMgmt_st {St Msg C : Type} {g s₁ : _root_.CryptoGames.SM.GameState St Msg C}
    {Δ qep : ℕ} {P : Party} {bad : Bool} (h : g.epMgmt Δ qep P bad = some s₁) : s₁.st = g.st := by
  unfold _root_.CryptoGames.SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; dsimp only; split <;> rfl
  · split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; rfl

private theorem noIdxVP_update {Γ T RSt SS RS : Type} {idx : ℕ}
    {st : Party → VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hst : ∀ Q, NoIdxVP idx (st Q)) (P : Party)
    {vp' : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)} (hvp' : NoIdxVP idx vp') :
    ∀ Q, NoIdxVP idx (Function.update st P vp' Q) := by
  intro Q
  by_cases hQP : Q = P
  · subst hQP; simpa only [Function.update_self] using hvp'
  · simpa only [Function.update_of_ne hQP] using hst Q

private theorem vSend_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {q Δcka Δbucket qep rem idx : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party) (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (h : FSMultiDFBucketState T RSt K I E)
    (hs : NoIdxVP idx s) (hH : NoIdxH q idx (rem + 1) h) :
    ZeroBound (sessPred idx) (fun z => NoIdxH q idx rem z.2 ∧ ∀ sc, z.1 = some sc → NoIdxVP idx sc.1)
      ((vSend (hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la) ctx Pt s m pair r).run h) := by
  unfold vSend; dsimp only; split
  · simp only [StateT.run_bind, pure_bind]
    refine (startSend_zero cka prng fs hqpos hΔb hinact (Nat.succ_pos _) ctx Pt s.γ s.root r h hH).bind
      fun ⟨o, h1⟩ ⟨hH1, ho⟩ => ?_
    rcases o with _ | ⟨γ', T', σ', ss⟩
    · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
    · simp only [StateT.run_bind]
      refine (fsSend_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la ctx Pt (s.tcur + 1) ss
        (s.tcur + 1, some T') m pair h1 (ho (γ', T', σ', ss) rfl) hH1).bind fun ⟨o2, h2⟩ ⟨hH2, ho2⟩ => ?_
      rcases o2 with _ | ⟨v', e⟩
      · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
      · simp only [StateT.run_pure]; refine ZeroBound.pure ⟨hH2, fun sc hsc => ?_⟩
        simp only [Option.some.injEq] at hsc; subst hsc
        exact ⟨by simpa only [ne_eq, Option.some.injEq] using ho2 (v', e) rfl, hs.2⟩
  · simp only [pure_bind]
    have hH0 : NoIdxH q idx rem h := hH.mono (Nat.le_succ rem)
    rcases hvs : s.vS with _ | v
    · refine ZeroBound.pure ⟨hH0, fun sc hsc => ?_⟩
      simp only [Option.some.injEq] at hsc; subst hsc; exact ⟨by simp [hvs], hs.2⟩
    · simp only [StateT.run_bind]
      refine (fsSend_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la ctx Pt s.tcur v
        (s.tcur, s.curCkaMsg) m pair h (fun hEq => hs.1 (hvs.trans (congrArg some hEq))) hH0).bind
        fun ⟨o2, h2⟩ ⟨hH2, ho2⟩ => ?_
      rcases o2 with _ | ⟨v', e⟩
      · exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
      · refine ZeroBound.pure ⟨hH2, fun sc hsc => ?_⟩
        simp only [Option.some.injEq] at hsc; subst hsc
        exact ⟨by simpa only [ne_eq, Option.some.injEq] using ho2 (v', e) rfl, hs.2⟩

private theorem vRecv_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep rem idx : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party) (s : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (c : Header T × E) (rec : Option (_root_.CryptoGames.SM.Record M (Header T × E)))
    (h : FSMultiDFBucketState T RSt K I E) (hs : NoIdxVP idx s) (hH : NoIdxH q idx (rem + 1) h) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxH q idx rem z.2 ∧ ∀ stim, z.1 = some (some stim) → NoIdxVP idx stim.1)
      ((vRecv (hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la)
        ctx Pt s c rec).run h) := by
  have hvRUpd : ∀ {v' : RS ⊕ ℕ} (hv' : v' ≠ .inr idx) (vR0 : ℕ → Option (RS ⊕ ℕ))
      (hvR0 : ∀ t, vR0 t ≠ some (.inr idx)) (t : ℕ), Function.update vR0 c.1.1 (some v') t ≠ some (.inr idx) := by
    intro v' hv' vR0 hvR0 t
    by_cases ht : t = c.1.1
    · subst ht; simpa only [Function.update_self, ne_eq, Option.some.injEq] using hv'
    · simpa only [Function.update_of_ne ht] using hvR0 t
  unfold vRecv; dsimp only
  split
  · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun _ h => by cases h⟩
  · split
    · next hEqEp =>
      have ht1 : 1 ≤ c.1.1 := by omega
      cases c.1.2 with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact ZeroBound.pure ⟨hH.mono (Nat.le_succ rem), fun _ h => by cases h⟩
      | some Tn =>
        simp only [StateT.run_bind, pure_bind]
        refine (startRecv_zero cka prng fs hqpos hΔb hinact ht1
          ctx Pt s.γ s.root Tn h hH).bind fun ⟨o, h1⟩ ⟨hH1, ho⟩ => ?_
        rcases o with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
        · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨hH1, fun _ h => by cases h⟩
        · simp only [Function.update_self]
          refine (fsRecv_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
            ctx Pt c.1.1 rs c.1 c.2 rec h1 (ho (γ', σ', rs) rfl) hH1).bind fun ⟨o2, h2⟩ ⟨hH2, ho2⟩ => ?_
          rcases o2 with _ | (_ | ⟨v', i, m⟩)
          · exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
          · exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
          · refine ZeroBound.pure ⟨hH2, fun stim hstim => ?_⟩
            simp only [Option.some.injEq] at hstim; subst hstim
            exact ⟨hs.1, hvRUpd (ho2 (v', i, m) rfl) _ (hvRUpd (ho (γ', σ', rs) rfl) _ hs.2)⟩
    · simp only [pure_bind]
      have hH0 : NoIdxH q idx rem h := hH.mono (Nat.le_succ rem)
      rcases hvr : s.vR c.1.1 with _ | v
      · exact ZeroBound.pure ⟨hH0, fun _ h => by cases h⟩
      · simp only [StateT.run_bind]
        have hv : v ≠ .inr idx := fun hEq => hs.2 c.1.1 (hvr.trans (congrArg some hEq))
        refine (fsRecv_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
          ctx Pt c.1.1 v c.1 c.2 rec h hv hH0).bind fun ⟨o2, h2⟩ ⟨hH2, ho2⟩ => ?_
        rcases o2 with _ | (_ | ⟨v', i, m⟩)
        · exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
        · exact ZeroBound.pure ⟨hH2, fun _ h => by cases h⟩
        · refine ZeroBound.pure ⟨hH2, fun stim hstim => ?_⟩
          simp only [Option.some.injEq] at hstim; subst hstim
          exact ⟨hs.1, hvRUpd (ho2 (v', i, m) rfl) _ hs.2⟩

private theorem commitE_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka Δbucket qep : ℕ)
    (tL : Option ℕ) (par la : Bool) {q idx rem : ℕ}
    (s : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (Pt : Party)
    (old new : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) (pos : _root_.CryptoGames.SM.Pos)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (hs : ∀ Q, NoIdxVP idx (s.st Q)) (hnew : NoIdxVP idx new)
    (hes : NoIdxES q idx rem es) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxES q idx rem z.2 ∧ ∀ s1, z.1 = some s1 → ∀ Q, NoIdxVP idx (s1.st Q))
      ((commitE (hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la)
        s Pt old new pos).run es) := by
  unfold commitE
  rw [StateT.run_bind]
  have hc : ZeroBound (sessPred idx)
      (fun z => z.1 = some new ∧ z.2 = es.h)
      (((hooksFSMultiDFBucketPaper L cka prng fs Δcka Δbucket qep tL par la).commit
        (s.accept Pt new pos) Pt old new).run es.h) := by
    dsimp only [hooksFSMultiDFBucketPaper]; simp only [StateT.run_pure]; exact ZeroBound.pure ⟨rfl, rfl⟩
  refine (liftH_zero hc).bind fun ⟨o, es1⟩ ⟨⟨ho, hh1⟩, hg1⟩ => ?_
  dsimp only at ho hh1
  subst ho
  simp only [StateT.run_pure]
  refine ZeroBound.pure ⟨⟨fun Q => hg1 ▸ hes.1 Q, hh1 ▸ hes.2⟩, fun s1 hs1 Q => ?_⟩
  simp only [Option.some.injEq] at hs1; subst hs1
  exact noIdxVP_update (noIdxVP_update hs Pt hnew) Pt hnew Q

private theorem implEDFPaperBucketRaw_inr_zero {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    {q Δcka Δbucket qep rem idx : ℕ} {tL : Option ℕ} {par la : Bool}
    (hqpos : 0 < q) (hΔb : 2 ≤ Δbucket)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (Δ maxSkip : ℕ) (cfg : Config M)
    (qr : (specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain)
    (es : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
      (FSMultiDFBucketState T RSt K I E))
    (hes : NoIdxES q idx (rem + 1) es) :
    ZeroBound (sessPred idx)
      (fun z => NoIdxES q idx rem z.2)
      ((implEDFPaperBucketRaw
        (hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la)
        Δ qep maxSkip cfg (.inr qr)).run es) := by
  rcases qr with ((((q1 | q2) | q3) | q4) | q5) | q6
  · rcases q1 with ⟨Pt, m, r⟩
    change ZeroBound _ _ ((transmitEBucket _ Δ qep (Pt, m, r)).run es)
    unfold transmitEBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
    · cases hep : es.g.epMgmt Δ qep Pt r.isSome with
      | none => simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
      | some s1 =>
        have hst1 : s1.st = es.g.st := epMgmt_st hep
        dsimp only; rw [StateT.run_bind]
        refine (liftH_zero (vSend_zero cka prng fs hqpos hΔb hinact
          s1 Pt (s1.st Pt) m none r es.h (hst1 ▸ hes.1 Pt) hes.2)).bind fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1⟩ => ?_
        rcases o with _ | p
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · dsimp only at ho
          simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroBound.pure ⟨noIdxVP_update (fun Q => hst1 ▸ hes.1 Q) Pt (ho p rfl), hH1⟩
  · change ZeroBound _ _ ((challEBucket q2).run es)
    unfold challEBucket; simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
  · rcases q3 with ⟨Pt, c⟩
    change ZeroBound _ _ ((deliverE _ maxSkip cfg (Pt, c)).run es)
    unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
    · cases es.g.inTransit Pt.other c with
      | none => simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
      | some r =>
        dsimp only; rw [StateT.run_bind]
        refine (liftH_zero (vRecv_zero cka prng fs hqpos hΔb hinact
          es.g Pt (es.g.st Pt) c (some r) es.h (hes.1 Pt) hes.2)).bind fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1⟩ => ?_
        rcases o with _ | (_ | ⟨st', t', i', m'⟩)
        · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · dsimp only
          split <;> simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
            exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · dsimp only; rw [StateT.run_bind]
          refine (commitE_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
            es.g Pt (es.g.st Pt) st' r.pos es1 hes.1 (ho (st', t', i', m') rfl)
            ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
          cases s1? with
          | none => simp only [StateT.run_pure]; exact ZeroBound.pure hes2
          | some s1 =>
            simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            refine ZeroBound.pure ⟨fun Q => ?_, hes2.2⟩
            dsimp only; split <;> exact hs1? s1 rfl Q
  · rcases q4 with ⟨Pt, c⟩
    change ZeroBound _ _ ((injectE _ Δ qep cfg (Pt, c)).run es)
    unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
    · rw [StateT.run_bind]
      refine (liftH_zero (vRecv_zero cka prng fs hqpos hΔb hinact
        es.g Pt (es.g.st Pt) c none es.h (hes.1 Pt) hes.2)).bind fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1⟩ => ?_
      rcases o with _ | (_ | ⟨st', t', i', m'⟩)
      · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      · dsimp only; split
        · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
        · split
          · rw [StateT.run_bind]
            refine (commitE_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
              es.g Pt (es.g.st Pt) st' ⟨Pt.other, t', i'⟩ es1 hes.1 (ho (st', t', i', m') rfl)
              ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
            cases s1? with
            | none => simp only [StateT.run_pure]; exact ZeroBound.pure hes2
            | some s1 =>
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
              exact ZeroBound.pure ⟨hs1? s1 rfl, hes2.2⟩
          · split <;>
              simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
              exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
  · change ZeroBound _ _ ((corrEPaperBucket _ q5).run es)
    unfold corrEPaperBucket; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
    · rw [StateT.run_bind]
      refine (liftH_zero (reveal_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
        es.g q5 (es.g.st q5) es.h (hes.1 q5) hes.2)).bind fun ⟨o, es1⟩ ⟨hH1, hg1⟩ => ?_
      cases o with
      | none =>
        simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
      | some _ =>
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
        exact ZeroBound.pure ⟨hes.1, hH1⟩
  · rcases q6 with ⟨Pt, c, c'⟩
    change ZeroBound _ _ ((deliverForgeE _ Δ qep cfg (Pt, c, c')).run es)
    unfold deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
    · cases es.g.inTransit Pt.other c with
      | none => simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
      | some r =>
        dsimp only; split
        · simp only [StateT.run_pure]; exact ZeroBound.pure (hes.mono (Nat.le_succ rem))
        · rw [StateT.run_bind]
          refine (liftH_zero (vRecv_zero cka prng fs hqpos hΔb hinact
            es.g Pt (es.g.st Pt) c' none es.h (hes.1 Pt) hes.2)).bind fun ⟨o, es1⟩ ⟨⟨hH1, ho⟩, hg1⟩ => ?_
          rcases o with _ | (_ | ⟨st', t', i', m'⟩)
          · simp only [abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
            exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
          · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
          · dsimp only; split
            · simp only [StateT.run_pure]; exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩
            · split
              · rw [StateT.run_bind]
                refine (commitE_zero (q + 1) cka prng fs Δcka Δbucket qep tL par la
                  es.g Pt (es.g.st Pt) st' ⟨Pt.other, t', i'⟩ es1 hes.1 (ho (st', t', i', m') rfl)
                  ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩).bind fun ⟨s1?, es2⟩ ⟨hes2, hs1?⟩ => ?_
                cases s1? with
                | none => simp only [StateT.run_pure]; exact ZeroBound.pure hes2
                | some s1 =>
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
                  exact ZeroBound.pure ⟨hs1? s1 rfl, hes2.2⟩
              · split <;>
                  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] <;>
                  exact ZeroBound.pure ⟨fun Q => hg1 ▸ hes.1 Q, hH1⟩

private theorem withWinEpDF_zero {ι₀ : Type} {tspec : OracleSpec.{0, 0} ι₀}
    {St Msg Coins C S' : Type}
    {P : (unifSpec + tspec).Domain → Bool} {Q : S' → Prop}
    (ctEpoch : C → ℕ) (hasWin : S' → Bool)
    (impl : QueryImpl (unifSpec + specDF St Msg Coins C) (StateT S' (TComp tspec)))
    (t : (unifSpec + specDF St Msg Coins C).Domain)
    (st : S' × Option ℕ)
    (h : ZeroBound P (fun z => Q z.2) ((impl t).run st.1)) :
    ZeroBound P (fun z => Q z.2.1) ((withWinEpDF ctEpoch hasWin impl t).run st) := by
  unfold withWinEpDF
  dsimp only [StateT.run_mk]
  exact h.bind fun ⟨_, _⟩ hs' => ZeroBound.pure hs'

private theorem hq_to_isInrQuery {Γ T RSt SS RS M CCoins E : Type} {q : ℕ}
    {A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E} (hq : MakesAtMostQueriesDF A q) :
    A.IsQueryBoundP (fun x => x.isRight = true) q := by
  unfold MakesAtMostQueriesDF at hq
  convert hq using 1; funext x; rcases x with _ | _ <;> rfl

private theorem redFSAuthDFPaperMultiBucket_inactive_isQueryBoundP_zero_gen
    {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (q Δcka Δbucket qep : ℕ) (tL : Option ℕ) (par la : Bool)
    (A : SchemeAdversaryDF Γ T RSt SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) (idx : ℕ)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false)
    (hΔb : 2 ≤ Δbucket) :
    (redFSAuthDFPaperMultiBucket (q + 1) cka prng fs lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0 := by
  suffices h :
      ZeroBound (sessPred idx) (fun _ => True)
        (redFSAuthDFPaperMultiBucket (q + 1) cka prng fs lam Δcka Δbucket qep la tL par A) by
    convert h.to_isQueryBoundP using 1
    funext x; rcases x with _ | ⟨_, _⟩ <;> rfl
  have hq' := hq_to_isInrQuery hq
  unfold redFSAuthDFPaperMultiBucket redFSAuthDFPaperMultiBucketGen engRunDFPaperBucket
    implEDFPaperBucket
  rw [bind_assoc]
  let hk := hooksFSMultiDFBucketPaper (q + 1) cka prng fs Δcka Δbucket qep tL par la
  let rawImpl := implEDFPaperBucketRaw hk (2 + Δcka) qep fs.maxSkip (bucketAuthCfgGen Δbucket tL par)
  let impl := withWinEpDF (fun c => c.1.1) (fun es => es.g.win) rawImpl
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · refine (initFSMultiDFBucketPaper_zero_any 1 cka prng fs lam Δbucket qep tL par idx).bind
      fun ⟨vs, h⟩ _ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroBound.pure trivial
    · simp only [bind_assoc]
      refine (zeroBound_simulateQ_run_of_zero_inr (sessPred idx) impl
        (fun u st => withWinEpDF_zero (Q := fun _ => True) _ _ rawImpl (.inl u) st
          (coinsE_zero (P := sessPred idx) (Q := fun _ => True) (fun _ => rfl) u st.1 trivial))
        A hq' _).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroBound.pure trivial
  · refine (initFSMultiDFBucketPaper_zero cka prng fs lam hqpos hΔb hinact).bind
      fun ⟨vs, h⟩ ⟨hH, hvs⟩ => ?_
    rcases vs with _ | ⟨vA, vB⟩
    · simp only [pure_bind]; exact ZeroBound.pure trivial
    · simp only [bind_assoc]
      obtain ⟨hvA, hvB⟩ := hvs (vA, vB) rfl
      let es₀ : EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E)
          (FSMultiDFBucketState T RSt K I E) :=
        { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h }
      have hes₀ : NoIdxES q idx q es₀ :=
        ⟨fun P => by cases P with | A => exact hvA | B => exact hvB, hH⟩
      refine (zeroBound_simulateQ_run_fuel (sessPred idx)
        (fun rem st => NoIdxES q idx rem st.1) impl
        (fun u st rem hst => withWinEpDF_zero (Q := NoIdxES q idx rem) _ _ rawImpl (.inl u) st
          (coinsE_zero (P := sessPred idx) (Q := NoIdxES q idx rem) (fun _ => rfl) u st.1 hst))
        (fun qr st rem hst => withWinEpDF_zero (Q := NoIdxES q idx rem) _ _ rawImpl (.inr qr) st
          (implEDFPaperBucketRaw_inr_zero cka prng fs hqpos hΔb hinact
            (2 + Δcka) fs.maxSkip (bucketAuthCfgGen Δbucket tL par) qr st.1 hst))
        q A hq' (es₀, none) hes₀).bind fun _ _ => ?_
      simp only [pure_bind]; exact ZeroBound.pure trivial

end InactiveZeroProof

section LibsignalBridges

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt)


/-- Inactive-slot `0`-query bound on `redFSAuthDFPaperMultiBucket`: if `q = 0`, or
`idx ≥ ((qep + 2) - healEpoch tL) * q`, or epoch `healEpoch tL + idx / q` is outside the `(tL, par)`
bucket (`inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false`), session `idx`
receives `0` queries. -/
theorem redFSAuthDFPaperMultiBucket_inactive_isQueryBoundP_zero
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (q Δcka Δbucket qep : ℕ) (hΔb : 2 ≤ Δbucket := by omega) (tL : Option ℕ) (par la : Bool)
    (A : AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (hq : MakesAtMostQueriesDF A q) (idx : ℕ)
    (hinact : q = 0 ∨ idx ≥ ((qep + 2) - healEpoch tL) * q ∨
      inStage2BucketGen Δbucket tL par (healEpoch tL + idx / q) = false) :
    (redFSAuthDFPaperMultiBucket (q + 1) (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
      (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka Δbucket qep la tL par A).IsQueryBoundP
      (fun x => (match x with | .inl _ => false | .inr ⟨s', _⟩ => decide (s' = idx)) = true) 0 := by
  convert redFSAuthDFPaperMultiBucket_inactive_isQueryBoundP_zero_gen
    (dhScheme Dh) (CryptoGames.Ratchet.rootPRNG C.F encPt)
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam
    q Δcka Δbucket qep tL par la A hq idx hinact hΔb using 1
  funext x; rcases x with _ | ⟨_, _⟩ <;> rfl

end LibsignalBridges

end

end Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperFSMulti
