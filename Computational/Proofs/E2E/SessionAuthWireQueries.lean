/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthWire
public import Computational.Proofs.E2E.SessionAuthQueries
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound

/-!
# Wire query bounds and wrapper AD/shortness transport

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

Discharges the wire-side and MAC-wrapper side conditions consumed by
`SessionWire.sessionHybrid_fs_real_to_ideal_mix_le` and
`SessionWire.sessionHybrid_fs_real_to_honestIdeal_mix_le` from hypotheses stated directly on the
multi-session FS-AEAD adversary `Adv`:

* `multiSlotOtccaReductionOut_of_red`: transfers any `IsQueryBoundP` bound from
  `multiSlotOtccaReduction` to the output-mode `multiSlotOtccaReductionOut` (for any `F`), yielding
  `multiSlotOtccaReductionOut_otADClassConst` and `multiSlotOtccaReductionOut_otEncADsOk`.
* `fsEncBadAD`, `fsOutsideClass`, and the `onInr` / `onSess` / `onAnySess` bridges: read single-session
  `FSAEAD.encBadAD` and `FSAEAD.queryADOutsideClass` on `FsIdx` without mentioning session state types.
* `lWireE_dec`, `lWireE_enc`, `lWireE_encADsOk`, `lWireE_encADsOk_of_any`,
  `lWireE_allQueriesInOneADClass`: per-session query, short-AD, and single-epoch-class bounds on the
  wire-side reductions `lWireE … P j o` for an arbitrary target `P : Params`.
* `sessSlotAdv_otEncADsOk`, `lMacAdv_encADsOk`: zero-query transport of `OTEncADsOk` through the
  multi-session re-tagging wrapper `sessSlotAdv` / `lMacAdv`.
* `GuardedMultiInjectShort`, `guardedSafePost_retagImpl`, `multiOraclesWith_guardedSafeStep`,
  `lMacAdv_guardedOTDecShort`: transport of `GuardedOTDecShort` through `sessSlotAdv` / `lMacAdv`.
* `sessionHybrid_fs_real_to_ideal_mix_le_of_adv` and
  `sessionHybrid_fs_real_to_honestIdeal_mix_le_of_adv`: the combined libsignal real-to-ideal
  session-hybrid bounds with all wrapper side conditions reduced to `Adv`.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed.SessionWireQueries

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5
open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSession CryptoGames.LibsignalSM.Proofs
open CryptoGames.LibsignalSM.Proofs.SaltHopKeyed CryptoGames.LibsignalSM.Proofs.WireHop CryptoGames.LibsignalSM.Proofs.WireHop
open CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound
open CryptoVerification.E2E.Signed.FSMix
open CryptoVerification.E2E.Signed.SessionRouter
open CryptoVerification.E2E.Signed.SessionFS
open CryptoVerification.E2E.Signed.SessionFSMix
open CryptoVerification.E2E.Signed.SessionMac
open CryptoVerification.E2E.Signed.SessionWire
open CryptoVerification.E2E.Signed.SessionQueries
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. Session-level AD predicates, bridges, and output-mode reduction transfer -/

section Predicates

/-- Single-session `FSAEAD.encBadAD` on `FsIdx` (independent of sender/receiver state types). -/
@[expose] def fsEncBadAD {AD M C : Type} (ok : AD → Bool) : FsIdx AD M C → Bool :=
  fun q => FSAEAD.encBadAD (SS := Unit) (RS := Unit) ok (.inr q)

/-- Single-session `FSAEAD.queryADOutsideClass` on `FsIdx` (independent of state types). -/
@[expose] def fsOutsideClass {AD M C κ : Type} [DecidableEq κ] (cls : AD → κ) (k₀ : κ) :
    FsIdx AD M C → Bool :=
  fun q => FSAEAD.queryADOutsideClass (SS := Unit) (RS := Unit) cls k₀ (.inr q)

/-- `onInr (fsEncBadAD ok)` agrees with `FSAEAD.encBadAD ok` at any state types `SS`, `RS`. -/
theorem onInr_fsEncBadAD {SS RS AD M C : Type} (ok : AD → Bool)
    (t : (unifSpec + FSAEAD.spec SS RS AD M C).Domain) :
    onInr (fsEncBadAD ok) t = FSAEAD.encBadAD (SS := SS) (RS := RS) ok t := by
  rcases t with _ | (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> rfl

/-- `onInr (fsOutsideClass cls k₀)` agrees with `FSAEAD.queryADOutsideClass cls k₀` at any `SS`, `RS`. -/
theorem onInr_fsOutsideClass {SS RS AD M C κ : Type} [DecidableEq κ] (cls : AD → κ) (k₀ : κ)
    (t : (unifSpec + FSAEAD.spec SS RS AD M C).Domain) :
    onInr (fsOutsideClass cls k₀) t =
      FSAEAD.queryADOutsideClass (SS := SS) (RS := RS) cls k₀ t := by
  rcases t with _ | (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> rfl

/-- Definitional bridge on `.inr ⟨s, q⟩` for concrete multi-session adversaries. -/
@[simp] theorem onAnySess_fsEncBadAD_inr {AD M C : Type} (ok : AD → Bool)
    (s : ℕ) (q : FsIdx AD M C) :
    onAnySess (fsEncBadAD ok) (.inr ⟨s, q⟩) =
      FSAEAD.encBadAD (SS := Unit) (RS := Unit) ok (.inr q) := rfl

@[simp] theorem onAnySess_fsEncBadAD_inl {AD M C : Type} (ok : AD → Bool) (n : ℕ) :
    onAnySess (fsEncBadAD (AD := AD) (M := M) (C := C) ok) (.inl n) = false := rfl

theorem onAnySess_fsEncBadAD_inr_spec {SS RS AD M C : Type} (ok : AD → Bool)
    (s : ℕ) (q : (FSAEAD.spec SS RS AD M C).Domain) :
    onAnySess (fsEncBadAD ok) (.inr ⟨s, q⟩) =
      FSAEAD.encBadAD (SS := SS) (RS := RS) ok (.inr q) := by
  rcases q with (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> rfl

@[simp] theorem onAnySess_fsOutsideClass_inr {AD M C κ : Type} [DecidableEq κ]
    (cls : AD → κ) (k₀ : κ) (s : ℕ) (q : FsIdx AD M C) :
    onAnySess (fsOutsideClass cls k₀) (.inr ⟨s, q⟩) =
      FSAEAD.queryADOutsideClass (SS := Unit) (RS := Unit) cls k₀ (.inr q) := rfl

@[simp] theorem onAnySess_fsOutsideClass_inl {AD M C κ : Type} [DecidableEq κ]
    (cls : AD → κ) (k₀ : κ) (n : ℕ) :
    onAnySess (fsOutsideClass (AD := AD) (M := M) (C := C) cls k₀) (.inl n) = false := rfl

theorem onAnySess_fsOutsideClass_inr_spec {SS RS AD M C κ : Type} [DecidableEq κ]
    (cls : AD → κ) (k₀ : κ) (s : ℕ) (q : (FSAEAD.spec SS RS AD M C).Domain) :
    onAnySess (fsOutsideClass cls k₀) (.inr ⟨s, q⟩) =
      FSAEAD.queryADOutsideClass (SS := SS) (RS := RS) cls k₀ (.inr q) := by
  rcases q with (((((⟨_, _⟩ | ⟨_, _, _⟩) | _) | _) | _) | _) <;> rfl

/-- A query satisfying `onSess Q j` also satisfies `onAnySess Q`. -/
theorem onSess_imp_onAnySess {ι : Type} (Q : ι → Bool) (j : ℕ)
    (t : ℕ ⊕ ((_ : ℕ) × ι)) (h : onSess Q j t = true) :
    onAnySess Q t = true := by
  rcases t with _ | ⟨_, _⟩
  · simp [onSess] at h
  · simp only [onSess, Bool.and_eq_true] at h
    exact h.2

end Predicates

section OutTransfer

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Output-mode query-bound transfer. `multiSlotOtccaReductionOut` maps an output function over
the same oracle run as `multiSlotOtccaReduction`, so every `IsQueryBoundP` bound transfers. -/
theorem multiSlotOtccaReductionOut_of_red (N : ℕ) (la : Bool)
    (F : Bool → HState CK MK AD M C → Bool) (A : RatchetAdversary CK MK AD M C)
    {Q : (IndexedOtccaSpec AD M C).Domain → Prop} [DecidablePred Q] {n : ℕ}
    (h : (multiSlotOtccaReduction ideal ae G maxSkip N la A).IsQueryBoundP Q n) :
    (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A).IsQueryBoundP Q n := by
  unfold multiSlotOtccaReduction multiRunWith at h
  unfold multiSlotOtccaReductionOut multiRunOut
  simp only [bind_pure_comp, ← map_bind, isQueryBoundP_map_iff] at h ⊢
  exact h

/-- `OTAllQueriesInOneADClass` for the output-mode multi-slot reduction. -/
theorem multiSlotOtccaReductionOut_otADClassConst {κ : Type} [DecidableEq κ] (cls : AD → κ)
    (N : ℕ) (la : Bool) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (hcls : FSAEAD.AllQueriesInOneADClass cls A) :
    AEADScheme.OTAllQueriesInOneADClass (fun ia : ℕ × AD => cls ia.2)
      (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A) := by
  rcases multiRedWith_otADClassConst cls ideal ae G maxSkip N la A hcls with ⟨k₀, hk₀⟩
  exact ⟨k₀, multiSlotOtccaReductionOut_of_red ideal ae G maxSkip N la F A hk₀⟩

/-- `OTEncADsOk` for the output-mode multi-slot reduction. -/
theorem multiSlotOtccaReductionOut_otEncADsOk (ok : AD → Bool)
    (N : ℕ) (la : Bool) (F : Bool → HState CK MK AD M C → Bool)
    (A : RatchetAdversary CK MK AD M C) (hA : FSAEAD.EncADsOk ok A) :
    AEADScheme.OTEncADsOk (fun ia : ℕ × AD => ok ia.2)
      (multiSlotOtccaReductionOut ideal ae G maxSkip N la F A) :=
  multiSlotOtccaReductionOut_of_red ideal ae G maxSkip N la F A
    (multiRedWith_otEncADsOk ok ideal ae G maxSkip N la A hA)

end OutTransfer

/-! ## 2. Zero-bound transport through `sessSlotAdv` (`OTEncADsOk`) -/

section ZeroSlot

/-- Zero-query simulation lemma: if `oa` never triggers `P` and every non-`P` query's implementation
issues zero `Q`-queries, then `(simulateQ impl oa).run s` issues zero `Q`-queries. -/
theorem isQueryBoundP_simulateQ_run_zero {ι κ σ α : Type}
    {spec₁ : OracleSpec ι} {spec₂ : OracleSpec κ}
    {P : ι → Prop} [DecidablePred P] {Q : κ → Prop} [DecidablePred Q]
    {impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂))}
    {oa : OracleComp spec₁ α} (hoa : oa.IsQueryBoundP P 0)
    (hstep : ∀ t, ¬ P t → ∀ s, ((impl t).run s).IsQueryBoundP Q 0) (s : σ) :
    ((simulateQ impl oa).run s).IsQueryBoundP Q 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure _ => simp
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have hnp : ¬ P t := hoa.1.resolve_right (Nat.lt_irrefl 0)
    have hcont : ∀ u, (r u).IsQueryBoundP P 0 := fun u => by simpa [hnp] using hoa.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    exact isQueryBoundP_bind_zero_left (hstep t hnp s) fun z => ih z.1 (hcont z.1) z.2

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- One FS-AEAD oracle step of `multiOraclesWith` issues zero `Q`-queries when the query's AD is
outside `B` and every in-range OT-CCA query for that AD avoids `Q`. -/
theorem qb_multiOraclesWith_zero {Q : (RSpec AD M C).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u)) (N : ℕ) (la : Bool)
    (B : FsIdx AD M (ℕ × C) → Bool)
    (hQe_tx : ∀ a m, B (.inl (.inl (.inl (.inl (.inl (a, m)))))) = false →
      ∀ i, 1 ≤ i → i ≤ N → ¬ Q (.inr (.inl ((i, a), m))))
    (hQe_ch : ∀ a m₀ m₁, B (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁)))))) = false →
      ∀ i, 1 ≤ i → i ≤ N → ∀ m, ¬ Q (.inr (.inl ((i, a), m))))
    (hQd_inj : ∀ a i e, B (.inr (a, (i, e))) = false →
      1 ≤ i → i ≤ N → ¬ Q (.inr (.inr ((i, a), e))))
    (t : (fsSpec CK MK AD M C).Domain) (ht : B t = false) :
    QB Q (multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t) 0 := by
  set P := hp N 0 la
  intro s
  rcases t with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩)
  · change IsQueryBoundP
      ((multiTransmitHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m)).run s) Q 0
    unfold multiTransmitHWith
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    · refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
      refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a m (hQe_tx a m ht _)) fun _ => ?_
      exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · change IsQueryBoundP
      ((multiChallengeHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m₀, m₁)).run s) Q 0
    unfold multiChallengeHWith
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    all_goals
      refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
      refine qb_bind0 (qb_multiEncIdx_at ideal ae hQu N _ a _
        (fun h1 hN => hQe_ch a m₀ m₁ ht _ h1 hN _)) fun _ => ?_
      exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · exact qb_corruptSenderH hQu G P u s
  · exact qb_corruptReceiverH hQu G P u s
  · change IsQueryBoundP
      ((multiDeliverH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, c)).run s) Q 0
    unfold multiDeliverH
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    · split
      · exact qb_pure _ _
      · refine qb_bind_r (qb_multiReceiveH_at ideal ae G maxSkip hQu P N rfl (DG G) _ a c
          (fun h => nomatch h)) fun r => ?_
        cases r <;> exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · change IsQueryBoundP
      ((multiInjectH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, (i, e))).run s) Q 0
    unfold multiInjectH
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    · refine qb_bind_r (qb_multiReceiveH_at ideal ae G maxSkip hQu P N rfl (DG G) none a (i, e)
        (fun _ => hQd_inj a i e ht)) fun r => ?_
      cases r
      · exact qb_pure _ _
      · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

/-- `OTEncADsOk` through `sessSlotAdv`. If `Adv` makes no `transmit`/`challenge` query failing
`ok` on any session and `tag` preserves `ok`, then `sessSlotAdv` makes no OT-CCA encryption query
failing `ok ∘ Prod.snd`. -/
theorem sessSlotAdv_otEncADsOk (N : ℕ) (la : Bool) (ok : AD → Bool) (tag : ℕ → AD → AD)
    (htag : ∀ s a, ok (tag s a) = ok a)
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)
    (hAdv : Adv.IsQueryBoundP (fun t => onAnySess (fsEncBadAD ok) t = true) 0) :
    AEADScheme.OTEncADsOk (fun ia : ℕ × AD => ok ia.2)
      (sessSlotAdv ideal ae G maxSkip N la tag Adv) := by
  let Q : (RSpec AD M C).Domain → Prop :=
    fun q => AEADScheme.otEncBad (M := M) (C := C) (fun ia : ℕ × AD => ok ia.2) q = true
  have hQu : ∀ u, ¬ Q (.inl u) := fun _ => by simp [Q, AEADScheme.otEncBad]
  have hstep : ∀ (t : (fsSpec CK MK AD M C).Domain) (ht : fsEncBadAD ok t = false)
      (h : HSt CK MK AD M C),
      IsQueryBoundP ((multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G)
        (some (otOpsWith ideal)) t).run h) Q 0 := by
    intro t ht h
    exact qb_multiOraclesWith_zero ideal ae G maxSkip hQu N la (fsEncBadAD ok)
      (fun a m htx _ _ _ => by simpa [Q, AEADScheme.otEncBad, fsEncBadAD, FSAEAD.encBadAD] using htx)
      (fun a m₀ m₁ hch _ _ _ _ => by
        simpa [Q, AEADScheme.otEncBad, fsEncBadAD, FSAEAD.encBadAD] using hch)
      (fun _ _ _ _ _ _ => by simp [Q, AEADScheme.otEncBad]) t ht h
  have hretag : ∀ (s : ℕ) (t : (fsSpec CK MK AD M C).Domain) (ht : fsEncBadAD ok t = false)
      (h : HSt CK MK AD M C),
      IsQueryBoundP (simulateQ (retagImpl (tag s)) ((multiOraclesWith ideal ae G maxSkip
        (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t).run h)) Q 0 :=
    fun s t ht h => retagImpl_isQueryBoundP (tag s)
      (fun i a m => by simp [Q, AEADScheme.otEncBad, htag s a])
      (fun i a e => by simp [Q, AEADScheme.otEncBad])
      _ (hstep t ht h)
  have hsess : ∀ (s : ℕ) (t : (fsSpec CK MK AD M C).Domain) (ht : fsEncBadAD ok t = false)
      (st : ℕ → Option (HSt CK MK AD M C)),
      IsQueryBoundP ((sessSlotRedImpl ideal ae G maxSkip N la tag (.inr ⟨s, t⟩)).run st) Q 0 := by
    intro s t ht st
    have hrest : ∀ h : HSt CK MK AD M C,
        IsQueryBoundP (do
          let r ← simulateQ (retagImpl (tag s)) ((multiOraclesWith ideal ae G maxSkip
            (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t).run h)
          pure (r.1, Function.update st s (some r.2))) Q 0 :=
      fun h => isQueryBoundP_bind_zero_right (hretag s t ht h) fun _ => isQueryBoundP_pure _ _ _
    simp only [sessSlotRedImpl_inr, StateT.run_mk]
    split
    · exact isQueryBoundP_bind_zero_left (isQueryBoundP_pure _ _ _) hrest
    · exact isQueryBoundP_bind_zero_left (isQueryBoundP_liftProb hQu _)
        fun _ => isQueryBoundP_bind_zero_left (isQueryBoundP_pure _ _ _) hrest
  unfold AEADScheme.OTEncADsOk sessSlotAdv
  rw [isQueryBoundP_map_iff]
  refine isQueryBoundP_simulateQ_run_zero hAdv (fun t hnt st => ?_) _
  rcases t with u | ⟨s, t⟩
  · simp only [sessSlotRedImpl_inl, StateT.run_lift]
    exact isQueryBoundP_query_bind_pure_zero' _ (hQu u) _
  · simp only [onAnySess, Bool.not_eq_true] at hnt
    exact hsess s t hnt st

end ZeroSlot

/-! ## 3. Multi-session guarded-shortness definitions and transport -/

section GuardedShort

/-- Multi-session response-shortness predicate on `(unifSpec + multiSessSpec (fsSpec …))`: every
session's `transmit` and `challenge` responses satisfy `fsRespShort`. -/
@[expose] def multiRespShort {CK MK AD Msg : Type} :
    (q : (unifSpec + multiSessSpec (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32)).Domain) →
      (unifSpec + multiSessSpec (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32)).Range q → Prop
  | .inl _, _ => True
  | .inr ⟨_, o⟩, r =>
      fsRespShort (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK) (.inr o) r

@[simp] theorem multiRespShort_inl {CK MK AD Msg : Type} (n : ℕ) (r : Fin (n + 1)) :
    multiRespShort (CK := CK) (MK := MK) (AD := AD) (Msg := Msg) (.inl n) r = True := rfl

@[simp] theorem multiRespShort_inr {CK MK AD Msg : Type} (s : ℕ)
    (o : (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32).Domain)
    (r : (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32).Range o) :
    multiRespShort (CK := CK) (MK := MK) (AD := AD) (Msg := Msg) (.inr ⟨s, o⟩) r =
      fsRespShort (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK) (.inr o) r := rfl

/-- Multi-session bad `inject` predicate: some session receives an `inject` query whose serialized
wire has length `≥ 2^32`. -/
@[expose] def multiInjectLong {CK MK AD Msg : Type} :
    (unifSpec + multiSessSpec (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32)).Domain → Prop
  | .inl _ => False
  | .inr ⟨_, o⟩ =>
      fsInjectLong (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (Msg := Msg) (.inr o)

@[simp] theorem multiInjectLong_inl {CK MK AD Msg : Type} (n : ℕ) :
    multiInjectLong (CK := CK) (MK := MK) (AD := AD) (Msg := Msg) (.inl n) = False := rfl

@[simp] theorem multiInjectLong_inr {CK MK AD Msg : Type} (s : ℕ)
    (o : (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32).Domain) :
    multiInjectLong (CK := CK) (MK := MK) (AD := AD) (Msg := Msg) (.inr ⟨s, o⟩) =
      fsInjectLong (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (Msg := Msg) (.inr o) := rfl

/-- Guarded multi-session short-inject invariant: assuming `multiRespShort` on every session's
`transmit` and `challenge` responses, `Adv` never issues `multiInjectLong` on any session. -/
@[expose] def GuardedMultiInjectShort {CK MK AD Msg β : Type}
    (Adv : OracleComp
      (unifSpec + multiSessSpec (fsSpec CK MK AD Msg LibsignalCiphertextWithSalt32)) β) : Prop :=
  GuardedSafe.GuardedSafePost multiRespShort multiInjectLong (fun _ => True) Adv

/-- AD re-tagging preserves `GuardedSafePost otRespShort otDecLong`. Neither `otRespShort` nor
`otDecLong` inspects the associated data, so `simulateQ (retagImpl f)` preserves any postcondition
`P` verbatim. -/
theorem guardedSafePost_retagImpl {AD M β : Type} (f : AD → AD) {P : β → Prop}
    {mx : OracleComp (IndexedOtccaSpec AD M LibsignalCiphertextWithSalt32) β}
    (hmx : GuardedSafe.GuardedSafePost otRespShort otDecLong P mx) :
    GuardedSafe.GuardedSafePost otRespShort otDecLong P (simulateQ (retagImpl f) mx) := by
  induction hmx with
  | pure h =>
    simp only [simulateQ_pure]
    exact GuardedSafe.GuardedSafePost.pure h
  | @query_bind t k hQt _ ih =>
    rw [simulateQ_query_bind]
    rcases t with n | ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, e⟩
    · dsimp only [retagImpl]
      exact GuardedSafe.GuardedSafePost.query_bind (by simp [otDecLong]) fun u _ => ih u trivial
    · dsimp only [retagImpl]
      exact GuardedSafe.GuardedSafePost.query_bind (by simp [otDecLong]) fun u hu => ih u hu
    · dsimp only [retagImpl]
      exact GuardedSafe.GuardedSafePost.query_bind (by simpa [otDecLong] using hQt)
        fun u _ => ih u trivial

/-- Per-step guarded-shortness for `multiOraclesWith` on the libsignal instance. Under a non-long
`inject` and a short encryption AD, one step of `multiOraclesWith … (hp N 0 la)` never issues
`otDecLong` and returns responses satisfying `fsRespShort`. -/
theorem multiOraclesWith_guardedSafeStep {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16) (encT : Pt → PublicKey) (idO : Party → IdentityKey)
    (maxSkip N : ℕ) (la : Bool)
    (q : (fsSpec (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32).Domain)
    (ht1 : ¬ fsInjectLong (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ) (.inr q))
    (ht2 : ¬ FSAEAD.encBadAD (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ)
      (C := ℕ × LibsignalCiphertextWithSalt32)
      (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB) (.inr q) = true)
    (s : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32) :
    GuardedSafe.GuardedSafePost otRespShort otDecLong
      (fun r => fsRespShort (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (.inr q) r.1)
      ((multiOraclesWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO)
        (lChainPRG C.F) maxSkip (hp N 0 la) N (DG (lChainPRG C.F))
        (some (otOpsWith (lIdeal C codec ℓ encT))) q).run s) := by
  classical
  have hQu : ∀ u, ¬ otDecLong (AD := ℕ × (Header Pt × LibsignalMsgPublicPart)) (M := Plain ℓ) (.inl u) :=
    fun _ => by simp [otDecLong]
  set P := hp N 0 la
  rcases q with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩)
  · have ha : a.2.shortB = true := by simpa [FSAEAD.encBadAD] using ht2
    change GuardedSafe.GuardedSafePost otRespShort otDecLong _
      ((multiTransmitHWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO)
        (lChainPRG C.F) P N (DG (lChainPRG C.F))
        (some (otOpsWith (lIdeal C codec ℓ encT))) (a, m)).run s)
    unfold multiTransmitHWith
    rw [StateT.run_bind]
    refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP (qb_getH (Q := otDecLong) s)).bind
      fun st _ => ?_
    split_ifs
    · rw [StateT.run_pure]
      exact GuardedSafe.GuardedSafePost.pure (by rintro _ ⟨⟩)
    · rw [StateT.run_bind]
      refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (qb_genUpTo hQu (lChainPRG C.F) P (DG (lChainPRG C.F)) _ st.2)).bind fun u1 _ => ?_
      rw [StateT.run_bind]
      refine (multiEncIdx_guardedSafePost C codec hfit ℓ hℓ encT idO N _ a m ha u1.2).bind
        fun ec hec => ?_
      rw [StateT.run_bind]
      exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (qb_modifyH (Q := otDecLong) _ ec.2)).bind fun _ _ => by
          rw [StateT.run_pure]
          exact GuardedSafe.GuardedSafePost.pure (by rintro _ ⟨rfl⟩; exact hec)
  · have ha : a.2.shortB = true := by simpa [FSAEAD.encBadAD] using ht2
    change GuardedSafe.GuardedSafePost otRespShort otDecLong _
      ((multiChallengeHWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO)
        (lChainPRG C.F) P N (DG (lChainPRG C.F))
        (some (otOpsWith (lIdeal C codec ℓ encT))) (a, m₀, m₁)).run s)
    unfold multiChallengeHWith
    rw [StateT.run_bind]
    refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP (qb_getH (Q := otDecLong) s)).bind
      fun st _ => ?_
    split_ifs
    · rw [StateT.run_pure]
      exact GuardedSafe.GuardedSafePost.pure (by rintro _ ⟨⟩)
    all_goals
      rw [StateT.run_bind]
      refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (qb_genUpTo hQu (lChainPRG C.F) P (DG (lChainPRG C.F)) _ st.2)).bind fun u1 _ => ?_
      rw [StateT.run_bind]
      refine (multiEncIdx_guardedSafePost C codec hfit ℓ hℓ encT idO N _ a _ ha u1.2).bind
        fun ec hec => ?_
      rw [StateT.run_bind]
      exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (qb_modifyH (Q := otDecLong) _ ec.2)).bind fun _ _ => by
          rw [StateT.run_pure]
          exact GuardedSafe.GuardedSafePost.pure (by rintro _ ⟨rfl⟩; exact hec)
  · exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
      (qb_corruptSenderH hQu (lChainPRG C.F) P u s)).mono fun _ _ => trivial
  · exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
      (qb_corruptReceiverH hQu (lChainPRG C.F) P u s)).mono fun _ _ => trivial
  · have hqb : IsQueryBoundP
        ((multiDeliverH (lAeadR C codec ℓ encT idO) (lChainPRG C.F) maxSkip P N
          (DG (lChainPRG C.F)) (some (otOpsWith (lIdeal C codec ℓ encT))) (a, c)).run s)
        otDecLong 0 := by
      unfold multiDeliverH
      refine (qb_bind0 (qb_getH (Q := otDecLong)) fun st => ?_) s
      split_ifs
      · exact fun _ => by simp
      · split
        · exact fun _ => by simp
        · refine qb_bind_r (qb_multiReceiveH_at (lIdeal C codec ℓ encT)
            (lAeadR C codec ℓ encT idO) (lChainPRG C.F) maxSkip hQu P N rfl
            (DG (lChainPRG C.F)) _ a c (fun h => nomatch h)) fun r => ?_
          cases r <;>
            exact qb_bind0 (qb_modifyH (Q := otDecLong) _) fun _ => fun _ => by simp
    exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP hqb).mono fun _ _ => trivial
  · have hqb : IsQueryBoundP
        ((multiInjectH (lAeadR C codec ℓ encT idO) (lChainPRG C.F) maxSkip P N
          (DG (lChainPRG C.F)) (some (otOpsWith (lIdeal C codec ℓ encT))) (a, (i, e))).run s)
        otDecLong 0 := by
      unfold multiInjectH
      refine (qb_bind0 (qb_getH (Q := otDecLong)) fun st => ?_) s
      split_ifs
      · exact fun _ => by simp
      · refine qb_bind_r (qb_multiReceiveH_at (lIdeal C codec ℓ encT)
          (lAeadR C codec ℓ encT idO) (lChainPRG C.F) maxSkip hQu P N rfl
          (DG (lChainPRG C.F)) none a (i, e)
          (fun _ _ _ => by simpa [otDecLong, fsInjectLong] using ht1)) fun r => ?_
        cases r with
        | none => exact fun _ => by simp
        | some _ =>
          exact qb_bind0 (qb_modifyH (Q := otDecLong) _) fun _ => fun _ => by simp
    exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP hqb).mono fun _ _ => trivial

end GuardedShort

/-! ## 4. The libsignal instance: `lWireE`, `lMacAdv`, and combined corollaries -/

section Libsignal

/-- Shortness predicate on libsignal FS-AEAD associated data `(hdr, pub)`: `pub.shortB`. -/
abbrev shortOk {Pt : Type} (ap : Header Pt × LibsignalMsgPublicPart) : Bool := ap.2.shortB

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
  (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool)

/-- Wire side, per session `j`: short encryption ADs (`hshortE`). -/
theorem lWireE_encADsOk (P : Params) (j : ℕ) (o : α)
    (h : (Adv o).IsQueryBoundP (fun t => onSess (fsEncBadAD shortOk) j t = true) 0) :
    AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lWireE C codec ℓ encT idOf maxSkip N la Adv P j o) := by
  have hsess : FSAEAD.EncADsOk shortOk
      (lWireSessAdv C codec ℓ encT idOf maxSkip N la Adv P o j) :=
    (sessAdv_isQueryBoundP _ _ (Adv o) _ _ j (fsEncBadAD shortOk) h).of_imp fun t ht => by
      rwa [onInr_fsEncBadAD (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))]
  exact multiSlotOtccaReductionOut_otEncADsOk _ _ _ _ shortOk N la advBit _ hsess

/-- `lWireE_encADsOk` from a single multi-session `onAnySess` hypothesis across all sessions. -/
theorem lWireE_encADsOk_of_any (P : Params) (j : ℕ) (o : α)
    (h : (Adv o).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0) :
    AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lWireE C codec ℓ encT idOf maxSkip N la Adv P j o) :=
  lWireE_encADsOk C codec ℓ encT idOf maxSkip N la Adv P j o
    (h.of_imp fun t ht => onSess_imp_onAnySess _ j t ht)

/-- Wire side, per session `j`: single AD class (`hclsE`). -/
theorem lWireE_allQueriesInOneADClass (P : Params) (j : ℕ) (o : α)
    (h : ∃ k₀, (Adv o).IsQueryBoundP
      (fun t => onSess (fsOutsideClass
        (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0) :
    AEADScheme.OTAllQueriesInOneADClass lCls
      (lWireE C codec ℓ encT idOf maxSkip N la Adv P j o) := by
  rcases h with ⟨k₀, hk₀⟩
  have hsess : FSAEAD.AllQueriesInOneADClass
      (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1)
      (lWireSessAdv C codec ℓ encT idOf maxSkip N la Adv P o j) :=
    ⟨k₀, (sessAdv_isQueryBoundP _ _ (Adv o) _ _ j _ hk₀).of_imp fun t ht => by
      rwa [onInr_fsOutsideClass (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))]⟩
  exact multiSlotOtccaReductionOut_otADClassConst _ _ _ _
    (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) N la advBit _ hsess

/-- MAC hop: short encryption ADs (`hshortA`). -/
theorem lMacAdv_encADsOk (o : α)
    (h : (Adv o).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0) :
    AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o) :=
  sessSlotAdv_otEncADsOk _ _ _ _ N la shortOk lTagAD (fun _ _ => rfl) (Adv o) h

/-- MAC hop: guarded short decryptions (`hdecA`). -/
theorem lMacAdv_guardedOTDecShort (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (o : α)
    (hA : (Adv o).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0)
    (hdec : GuardedMultiInjectShort (Adv o)) :
    GuardedOTDecShort (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o) := by
  classical
  have hQu : ∀ u, ¬ otDecLong (AD := ℕ × (Header Pt × LibsignalMsgPublicPart)) (M := Plain ℓ) (.inl u) :=
    fun _ => by simp [otDecLong]
  have hcomb := hdec.and_isQueryBoundP hA
  unfold GuardedOTDecShort lMacAdv sessSlotAdv
  refine GuardedSafe.GuardedSafePost.map (P := fun _ => True) Prod.fst ?_ (fun _ _ => trivial)
  refine GuardedSafe.GuardedSafePost.simulateQ_run (I := fun _ => True) hcomb ?_ trivial
  intro t ht st _
  rcases t with u | ⟨s, q⟩
  · simp only [sessSlotRedImpl_inl, StateT.run_lift]
    exact (GuardedSafe.GuardedSafePost.query (hQu u)).bind fun _ _ =>
      GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
  · have ht1 : ¬ fsInjectLong (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ) (.inr q) :=
      fun h => ht (Or.inl h)
    have ht2 : ¬ FSAEAD.encBadAD (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ)
        (C := ℕ × LibsignalCiphertextWithSalt32) shortOk (.inr q) = true := by
      intro h
      apply ht
      right
      rwa [onAnySess_fsEncBadAD_inr_spec]
    have hrest : ∀ h : HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
        (Plain ℓ) LibsignalCiphertextWithSalt32,
        GuardedSafe.GuardedSafePost otRespShort otDecLong
          (fun r => multiRespShort (.inr ⟨s, q⟩) r.1 ∧ True)
          (do
            let r ← simulateQ (retagImpl (lTagAD s))
              ((multiOraclesWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
                (lChainPRG C.F) maxSkip (hp N 0 la) N (DG (lChainPRG C.F))
                (some (otOpsWith (lIdeal C codec ℓ encT))) q).run h)
            pure (r.1, Function.update st s (some r.2))) := fun h =>
      (guardedSafePost_retagImpl (lTagAD s)
        (multiOraclesWith_guardedSafeStep C codec hfit ℓ hℓ encT (idOf o) maxSkip N la q
          ht1 ht2 h)).bind fun _ hr => GuardedSafe.GuardedSafePost.pure ⟨hr, trivial⟩
    simp only [sessSlotRedImpl_inr, StateT.run_mk]
    split
    · rw [pure_bind]
      exact hrest _
    · exact (GuardedSafe.GuardedSafePost.liftComp_unif hQu ($ᵗ Bool)).bind fun b _ => by
        rw [pure_bind]
        exact hrest _

/-- Combined libsignal FS-AEAD session hybrid (`hp 0 0 la` → `hp N N la`), from `Adv` bounds.
Discharges `hqdA`, `hshortA`, `hdecA`, `hclsE`, and `hshortE` of
`SessionWire.sessionHybrid_fs_real_to_ideal_mix_le` directly from hypotheses on `Adv`. -/
theorem sessionHybrid_fs_real_to_ideal_mix_le_of_adv (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hN : N ≤ 2 ^ 32) (q : ℕ)
    (hoffAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    {qd : ℕ}
    (hqdAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd)
    (hshortAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0)
    (hdecAdv : ∀ o, GuardedMultiInjectShort (Adv o))
    (hclsAdv : ∀ j o, ∃ k₀, (Adv o).IsQueryBoundP
      (fun t => onSess (fsOutsideClass
        (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp 0 0 la)))) (Adv o)).run (fun _ => none)].boolDist
      𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp N N la)))) (Adv o)).run (fun _ => none)] ≤
      (∑ j ∈ Finset.range q,
        (lSaltPre C codec ℓ encT oa idOf maxSkip N la Adv j +
          ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) N k
                (lSaltD C codec ℓ encT idOf maxSkip N la Adv j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range N, (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k
              (lWireE C codec ℓ encT idOf maxSkip N la Adv (hp N N la) j o))) :=
  sessionHybrid_fs_real_to_ideal_mix_le C codec ℓ encT oa idOf maxSkip N la Adv
    hrt hfit hℓ hinj hdum hN q hoffAdv
    (fun o => lMacAdv_dec C codec ℓ encT idOf maxSkip N la Adv hqdAdv o)
    (fun o => lMacAdv_encADsOk C codec ℓ encT idOf maxSkip N la Adv o (hshortAdv o))
    (fun o => lMacAdv_guardedOTDecShort C codec ℓ encT idOf maxSkip N la Adv hfit hℓ o
      (hshortAdv o) (hdecAdv o))
    (fun j o => lWireE_allQueriesInOneADClass C codec ℓ encT idOf maxSkip N la Adv (hp N N la)
      j o (hclsAdv j o))
    (fun j o => lWireE_encADsOk_of_any C codec ℓ encT idOf maxSkip N la Adv (hp N N la)
      j o (hshortAdv o))

end Libsignal

end CryptoVerification.E2E.Signed.SessionWireQueries
