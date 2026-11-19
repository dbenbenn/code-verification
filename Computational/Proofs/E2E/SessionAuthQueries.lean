/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthMac
public import Computational.Proofs.GameHop.StateSim
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Query accounting for the session router

**Checked by Lean. Not trusted.** Query accounting bounds for the session router and the
single global MAC-hop adversary.

* `sessAdv_isQueryBoundP`: the session adversary `sessAdv … M k` asks at most as many
  `Q`-queries of its external single-session oracle as `M` asks of session `k`.
* `qb_multiOraclesWith_step`: one FS-AEAD oracle step of the multi-slot OT-CCA reduction asks at
  most `e` `encrypt` queries for `transmit`/`challenge`, at most `d` `decrypt` queries for
  `inject`, and none otherwise (`deliver` decrypts with the stored message as hint).
* `fsSessRed_dec`, `fsSessRed_enc`: the per-session salt-side reductions `D_j` ask at most as
  many `decrypt` (resp. `encrypt`) queries as the multi-session adversary asks `inject`
  (resp. `transmit`/`challenge`) queries of session `j`. Libsignal instances: `lSaltD_dec`,
  `lSaltD_enc`.
* `sessSlotAdv_dec`: the multi-session MAC adversary asks at most `qd` `decrypt` queries when the
  multi-session adversary asks at most `qd` `inject` queries summed over all sessions. Libsignal
  instance (`hqdA` of `SessionMac`): `lMacAdv_dec`, `lMacAdv_dec_of_fsDec`.
* `onSess_zero_of_offRange`: the off-range hypothesis `hoffAdv` (no query to sessions `≥ q`)
  gives zero per-session counts for every session `j ≥ q`. `hoffAdv` is supplied as a hypothesis
  for the concrete multi-session adversary.-/

public section

open OracleComp OracleSpec

namespace CryptoVerification.E2E.Signed.SessionRouter

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ι : Type} {spec : OracleSpec ι}

/-! ## Predicates on the two interfaces -/

/-- A predicate on single-session queries, read on the `spec` side of `unifSpec + spec`. -/
@[expose] def onInr (Q : ι → Bool) : ℕ ⊕ ι → Bool
  | .inl _ => false
  | .inr i => Q i

/-- A predicate on single-session queries, read on session `k` of the multi-session interface. -/
@[expose] def onSess (Q : ι → Bool) (k : ℕ) : ℕ ⊕ ((_ : ℕ) × ι) → Bool
  | .inl _ => false
  | .inr t => decide (t.1 = k) && Q t.2

/-- A predicate on single-session queries, read on every session of the multi-session interface. -/
@[expose] def onAnySess (Q : ι → Bool) : ℕ ⊕ ((_ : ℕ) × ι) → Bool
  | .inl _ => false
  | .inr t => Q t.2

/-- One forwarded query followed by `pure` counts once. -/
theorem isQueryBoundP_query_bind_pure_le_one {κ : Type} {spec' : OracleSpec κ} {α : Type}
    {P : κ → Prop} [DecidablePred P] (t : κ) (f : spec'.Range t → α) :
    IsQueryBoundP ((query (spec := spec') t : OracleComp spec' _) >>= fun r => pure (f r)) P 1 := by
  rw [show (query (spec := spec') t : OracleComp spec' _) = liftM (spec'.query t) from rfl,
    isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩

/-- One forwarded query outside `P`, followed by `pure`, does not count. -/
theorem isQueryBoundP_query_bind_pure_zero' {κ : Type} {spec' : OracleSpec κ} {α : Type}
    {P : κ → Prop} [DecidablePred P] (t : κ) (ht : ¬ P t) (f : spec'.Range t → α) :
    IsQueryBoundP ((query (spec := spec') t : OracleComp spec' _) >>= fun r => pure (f r)) P 0 := by
  rw [show (query (spec := spec') t : OracleComp spec' _) = liftM (spec'.query t) from rfl,
    isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl ht, fun _ => by simp⟩

/-- A lifted coin computation asks no query of `unifSpec + spec` satisfying `onInr Q`. -/
theorem isQueryBoundP_liftM_onInr (Q : ι → Bool) {β : Type} (p : ProbComp β) :
    (liftM p : OracleComp (unifSpec + spec) β).IsQueryBoundP (fun t => onInr Q t = true) 0 :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => False)
    (fun t => ⟨False.elim, fun h => by simp [onInr] at h⟩)
    (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false p 0)

section Router

variable {σL σR : Type}

/-- Per-session query bound through the router. If `M` asks at most `n` queries of session `k`
satisfying `Q`, then the session adversary `sessAdv … M k` asks at most `n` queries satisfying `Q`
of its external single-session oracle. -/
theorem sessAdv_isQueryBoundP (implL : QueryImpl spec (StateT σL ProbComp))
    (implR : QueryImpl spec (StateT σR ProbComp)) {α : Type}
    (M : OracleComp (unifSpec + multiSessSpec spec) α) (sL : ℕ → σL) (sR : ℕ → σR) (k : ℕ)
    (Q : ι → Bool) {n : ℕ} (hM : M.IsQueryBoundP (fun t => onSess Q k t = true) n) :
    (sessAdv implL implR M sL sR k).IsQueryBoundP (fun t => onInr Q t = true) n := by
  unfold sessAdv
  rw [isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hM (fun t ht s => ?_) (fun t ht s => ?_) (sL, sR)
  · rcases t with m | t
    · simp [onSess] at ht
    · simp only [onSess, Bool.and_eq_true, decide_eq_true_eq] at ht
      simp only [sessRedImpl, ht.1, ↓reduceIte, StateT.run_lift]
      exact isQueryBoundP_query_bind_pure_le_one _ _
  · rcases t with m | t
    · simp only [sessRedImpl, StateT.run_lift]
      exact isQueryBoundP_query_bind_pure_zero' _ (by simp [onInr]) _
    · by_cases hk : t.1 = k
      · have hQ : Q t.2 = false := by
          simpa [onSess, hk] using ht
        simp only [sessRedImpl, hk, ↓reduceIte, StateT.run_lift]
        exact isQueryBoundP_query_bind_pure_zero' _ (by simp [onInr, hQ]) _
      · simp only [sessRedImpl, hk, ↓reduceIte]
        split_ifs
        · exact isQueryBoundP_liftM_onInr Q _
        · exact isQueryBoundP_liftM_onInr Q _

end Router

end CryptoVerification.E2E.Signed.SessionRouter

namespace CryptoVerification.E2E.Signed.SessionQueries

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5
open CryptoVerification.E2E.Signed.SessionRouter CryptoVerification.E2E.Signed.SessionFS
open CryptoVerification.E2E.Signed.SessionMac

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Query classes of one FS-AEAD session and of the OT-CCA interface -/

section Classes

variable {AD M C : Type}

/-- The query index of one FS-AEAD session (Fig. 5): `transmit`, `challenge`, `corruptSender`,
`corruptReceiver`, `deliver`, `inject`. This is `(FSAEAD.spec SS RS AD M C).Domain` spelled out:
it does not mention the state types `SS` and `RS`, so they could not be inferred from it. -/
abbrev FsIdx (AD M C : Type) : Type :=
  (((((AD × M) ⊕ (AD × M × M)) ⊕ Unit) ⊕ Unit) ⊕ (AD × C)) ⊕ (AD × C)

/-- `inject` queries of one FS-AEAD session. -/
@[expose] def fsInjQ : FsIdx AD M C → Bool
  | .inr _ => true
  | .inl _ => false

/-- Decryption queries (`deliver` or `inject`) of one FS-AEAD session. -/
@[expose] def fsDecQ : FsIdx AD M C → Bool
  | .inl (.inr _) => true
  | .inr _ => true
  | _ => false

/-- Encryption queries (`transmit` or `challenge`) of one FS-AEAD session. -/
@[expose] def fsEncQ : FsIdx AD M C → Bool
  | .inl (.inl (.inl (.inl _))) => true
  | _ => false

theorem fsDecQ_of_fsInjQ (t : FsIdx AD M C) (h : fsInjQ t = true) : fsDecQ t = true := by
  rcases t with t | t
  · simp [fsInjQ] at h
  · rfl

/-- `encrypt` queries of the OT-CCA interface. -/
@[expose] def otEncQ : (unifSpec + AEADScheme.otccaSpec AD M C).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

end Classes

/-! ## Two bind rules -/

section Bind

variable {ι : Type} {spec : OracleSpec ι} {α β : Type} {p : ι → Prop} [DecidablePred p]

/-- A first step asking nothing in `p`, then a continuation asking at most `n`. -/
theorem isQueryBoundP_bind_zero_left {oa : OracleComp spec α} {f : α → OracleComp spec β} {n : ℕ}
    (h : oa.IsQueryBoundP p 0) (hf : ∀ a, (f a).IsQueryBoundP p n) :
    (oa >>= f).IsQueryBoundP p n :=
  (isQueryBoundP_bind h fun a _ => hf a).mono (Nat.zero_add n).le

/-- A first step asking at most `n` in `p`, then a continuation asking nothing. -/
theorem isQueryBoundP_bind_zero_right {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {n : ℕ} (h : oa.IsQueryBoundP p n) (hf : ∀ a, (f a).IsQueryBoundP p 0) :
    (oa >>= f).IsQueryBoundP p n :=
  (isQueryBoundP_bind h fun a _ => hf a).mono (Nat.add_zero n).le

end Bind

/-! ## One FS-AEAD oracle step in the multi-slot world -/

section Step

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  {Q : (RSpec AD M C).Domain → Prop} [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
include hQu

/-- Multi-slot encryption at index `i` asks at most `e` queries in `Q`, if every in-range
`encrypt` query in `Q` is allowed (`0 < e`). -/
theorem qb_multiEncIdx_le (N : ℕ) (e : ℕ)
    (hQe : ∀ i a m, 1 ≤ i → i ≤ N → Q (.inr (.inl ((i, a), m))) → 0 < e)
    (i : ℕ) (a : AD) (msg : M) :
    QB Q (multiEncIdxWith ideal ae 0 N (some (otOpsWith ideal)) i a msg :
      RM CK MK AD M C C) e := by
  unfold multiEncIdxWith
  refine qb_bind0 qb_getH fun st => ?_
  split
  · exact fun s => (qb_sampleH hQu _ s).mono (Nat.zero_le _)
  · rename_i heq hops
    obtain rfl := Option.some.inj hops
    obtain ⟨hi1, hiN⟩ := multiKind_special heq
    refine qb_liftOM _ ?_
    simp only [otOpsWith]
    refine (isQueryBoundP_query_bind_iff Q _ _ _).2
      ⟨by_cases (fun hq => Or.inr (hQe i a msg hi1 hiN hq)) Or.inl, fun r => ?_⟩
    cases r
    · exact (isQueryBoundP_liftProb hQu _).mono (Nat.zero_le _)
    · exact isQueryBoundP_pure Q _ _
  · split
    · exact qb_pure _ _
    · exact fun s => (qb_sampleH hQu _ s).mono (Nat.zero_le _)

/-- One FS-AEAD oracle step in the multi-slot world. A `transmit` or `challenge` step asks at
most `e` queries in `Q`, an `inject` step at most `d`, and every other step none, provided every
in-range `encrypt` query in `Q` is allowed by `e` and every in-range `decrypt` query in `Q` by `d`.
`deliver` asks none: it decrypts with the stored message as hint, so it never reaches the external
`decrypt` oracle. -/
theorem qb_multiOraclesWith_step (N : ℕ) (la : Bool) (e d : ℕ)
    (hQe : ∀ i a m, 1 ≤ i → i ≤ N → Q (.inr (.inl ((i, a), m))) → 0 < e)
    (hQd : ∀ i a c, 1 ≤ i → i ≤ N → Q (.inr (.inr ((i, a), c))) → 0 < d)
    (t : (fsSpec CK MK AD M C).Domain) :
    QB Q (multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t)
      (if fsEncQ t then e else if fsInjQ t then d else 0) := by
  set P := hp N 0 la
  intro s
  rcases t with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩)
  · change IsQueryBoundP
      ((multiTransmitHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m)).run s) Q e
    unfold multiTransmitHWith
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    · refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
      refine qb_bind_r (qb_multiEncIdx_le ideal ae hQu N e hQe _ a m) fun _ => ?_
      exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _
  · change IsQueryBoundP
      ((multiChallengeHWith ideal ae G P N (DG G) (some (otOpsWith ideal)) (a, m₀, m₁)).run s) Q e
    unfold multiChallengeHWith
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    all_goals
      refine qb_bind0 (qb_genUpTo hQu G P (DG G) _) fun _ => ?_
      refine qb_bind_r (qb_multiEncIdx_le ideal ae hQu N e hQe _ a _) fun _ => ?_
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
      ((multiInjectH ae G maxSkip P N (DG G) (some (otOpsWith ideal)) (a, c)).run s) Q d
    unfold multiInjectH
    refine (qb_bind0 qb_getH fun st => ?_) s
    split_ifs
    · exact qb_pure _ _
    · refine qb_bind_r (qb_multiReceiveH ideal ae G maxSkip hQu P N rfl (DG G) d hQd none a c)
        fun r => ?_
      cases r
      · exact qb_pure _ _
      · exact qb_bind0 (qb_modifyH _) fun _ => qb_pure _ _

end Step

/-! ## Per-session reductions: decryption and encryption counts -/

section PerSession

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

variable (P : Params) (N : ℕ) (la : Bool) {S : Type}
  (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) (initS : ProbComp (ℕ → S))
  (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool)

end PerSession

/-! ## The multi-session MAC adversary: total decryption count -/

section Total

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)

/-- Re-tagging the AD keeps the count of any query class that ignores the AD. -/
theorem retagImpl_isQueryBoundP (f : AD → AD)
    {Q : (IndexedOtccaSpec AD M C).Domain → Prop} [DecidablePred Q]
    (hQenc : ∀ i a m, Q (.inr (.inl ((i, f a), m))) ↔ Q (.inr (.inl ((i, a), m))))
    (hQdec : ∀ i a e, Q (.inr (.inr ((i, f a), e))) ↔ Q (.inr (.inr ((i, a), e))))
    {β : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) β) {n : ℕ}
    (h : oa.IsQueryBoundP Q n) :
    (simulateQ (retagImpl f) oa).IsQueryBoundP Q n := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t _ => ?_) (fun t ht => ?_)
  · rcases t with u | ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, e⟩ <;>
      exact (isQueryBoundP_query_iff Q _ 1).2 fun _ => Nat.zero_lt_one
  · rcases t with u | ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, e⟩
    · exact (isQueryBoundP_query_iff Q _ 0).2 fun hq => absurd hq ht
    · exact (isQueryBoundP_query_iff Q _ 0).2 fun hq => absurd ((hQenc i a m).1 hq) ht
    · exact (isQueryBoundP_query_iff Q _ 0).2 fun hq => absurd ((hQdec i a e).1 hq) ht

/-- Total decryption count of the multi-session MAC adversary. If the multi-session adversary
asks at most `qd` `inject` queries summed over all sessions, then `sessSlotAdv` asks at most `qd`
`decrypt` queries. -/
theorem sessSlotAdv_dec (tag : ℕ → AD → AD) {β : Type}
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β) {qd : ℕ}
    (hAdv : Adv.IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd) :
    (sessSlotAdv ideal ae G maxSkip N la tag Adv).IsQueryBoundP
      (fun q => AEADScheme.isDecQuery q = true) qd := by
  have hQu : ∀ u, ¬ (fun q : (RSpec AD M C).Domain => AEADScheme.isDecQuery q = true) (.inl u) :=
    fun u => by simp [AEADScheme.isDecQuery]
  -- one session step, before re-tagging
  have hstep : ∀ (t : (fsSpec CK MK AD M C).Domain) (h : HSt CK MK AD M C),
      IsQueryBoundP ((multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G)
        (some (otOpsWith ideal)) t).run h) (fun q => AEADScheme.isDecQuery q = true)
        (if fsInjQ t then 1 else 0) := by
    intro t h
    have h' := qb_multiOraclesWith_step ideal ae G maxSkip
      (Q := fun q => AEADScheme.isDecQuery q = true) hQu N la 0 1
      (fun _ _ _ _ _ h => by simp [AEADScheme.isDecQuery] at h)
      (fun _ _ _ _ _ _ => Nat.zero_lt_one) t h
    rwa [show (if fsEncQ t then 0 else if fsInjQ t then 1 else 0) = if fsInjQ t then 1 else 0 by
      rcases t with (((((_ | _) | _) | _) | _) | _) <;> rfl] at h'
  -- the same step after re-tagging session `s`
  have hretag : ∀ (s : ℕ) (t : (fsSpec CK MK AD M C).Domain) (h : HSt CK MK AD M C),
      IsQueryBoundP (simulateQ (retagImpl (tag s)) ((multiOraclesWith ideal ae G maxSkip
        (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t).run h))
        (fun q => AEADScheme.isDecQuery q = true) (if fsInjQ t then 1 else 0) :=
    fun s t h => retagImpl_isQueryBoundP (tag s) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) _
      (hstep t h)
  -- one router step on session `s`: the lazy start asks nothing, the re-tagged step as above
  have hsess : ∀ (s : ℕ) (t : (fsSpec CK MK AD M C).Domain) (st : ℕ → Option (HSt CK MK AD M C)),
      IsQueryBoundP ((sessSlotRedImpl ideal ae G maxSkip N la tag (.inr ⟨s, t⟩)).run st)
        (fun q => AEADScheme.isDecQuery q = true) (if fsInjQ t then 1 else 0) := by
    intro s t st
    -- after the (possibly lazy) start: the re-tagged step, then a `pure` that asks nothing
    have hrest : ∀ h : HSt CK MK AD M C,
        IsQueryBoundP (do
          let r ← simulateQ (retagImpl (tag s)) ((multiOraclesWith ideal ae G maxSkip
            (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t).run h)
          pure (r.1, Function.update st s (some r.2)))
          (fun q => AEADScheme.isDecQuery q = true) (if fsInjQ t then 1 else 0) :=
      fun h => isQueryBoundP_bind_zero_right (hretag s t h) fun _ => isQueryBoundP_pure _ _ _
    simp only [sessSlotRedImpl_inr, StateT.run_mk]
    split
    · exact isQueryBoundP_bind_zero_left (isQueryBoundP_pure _ _ _) hrest
    · exact isQueryBoundP_bind_zero_left
        (isQueryBoundP_liftProb (Q := fun q => AEADScheme.isDecQuery q = true) hQu _)
        fun _ => isQueryBoundP_bind_zero_left (isQueryBoundP_pure _ _ _) hrest
  unfold sessSlotAdv
  rw [isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hAdv (fun t ht st => ?_) (fun t hnt st => ?_) _
  · rcases t with u | ⟨s, t⟩
    · simp [onAnySess] at ht
    · simp only [onAnySess] at ht
      have h := hsess s t st
      rw [ite_eq_left ht] at h
      exact h
  · rcases t with u | ⟨s, t⟩
    · simp only [sessSlotRedImpl_inl, StateT.run_lift]
      exact isQueryBoundP_query_bind_pure_zero' _ (by simp [AEADScheme.isDecQuery]) _
    · simp only [onAnySess, Bool.not_eq_true] at hnt
      have h := hsess s t st
      rw [ite_eq_right (by simp [hnt])] at h
      exact h

end Total

/-! ## Off-range sessions -/

section OffRange

variable {ι : Type} {spec : OracleSpec ι}

end OffRange

/-! ## The libsignal instance -/

section Libsignal

open CryptoGames.LibsignalSM.Proofs CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSession CryptoGames.LibsignalSM.Proofs.SaltHopKeyed CryptoGames.LibsignalSM.Proofs.WireHop
open CryptoGames.LibsignalSM.Proofs.WireHop CryptoVerification.E2E.Signed.FSMix
open CryptoVerification.E2E.Signed.SessionHybrid CryptoVerification.E2E.Signed.SessionFSMix
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
  (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool)

/-- MAC hop: total decryption count (`hqdA`). If `Adv o` asks at most `qd` `inject` queries
summed over all sessions, the MAC-hop adversary `lMacAdv o` asks at most `qd` `decrypt` queries. -/
theorem lMacAdv_dec {qd : ℕ}
    (hAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd) (o : α) :
    AEADScheme.MakesAtMostDecQueries (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o) qd :=
  sessSlotAdv_dec _ _ _ _ _ _ _ (Adv o) (hAdv o)

end Libsignal

end CryptoVerification.E2E.Signed.SessionQueries
