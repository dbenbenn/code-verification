/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltHop
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.FSAEAD.CellForgery
import Computational.Proofs.CryptoGames.FSAEAD.HybridOT
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Keyed Multi-Slot Lift (`slotLiftK`) and Global Multi-Slot MAC Forgery Hop

Standalone keyed generalization of the multi-slot MAC forgery hop from `SaltHop.lean` (`κ`-indexed
slots via `slotLiftK sk`), enabling a single global MAC hop across multiple FS-AEAD sessions.-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.SaltHopKeyed

open CryptoGames.LibsignalSM.Proofs.SaltHop (AD AState ChalState Ct PState aImpl aImpl_query_bind aImpl_step_inl boolDist_bind_coin_false evalDist_aImpl_true_eq_saltRun_true evalDist_aImpl_true_eq_slotSaltImpl_true evalDist_multiOtBranch_true_eq_slotLift_slotSaltImpl_true evalDist_otccaGameWith_eq_branch_false evalDist_saltHyb_self evalDist_saltHyb_step_left evalDist_slotLift_otImpl_true_eq_slotLift_slotSaltImpl_true multiOtBranch_false_boolDist_multiSalt_false otImpl_eq_aImpl otccaBranch_false_boolDist_saltRun_false pImpl runSaltRed runSaltRed_eq runSaltRed_pure runSaltRed_query_bind saltHyb saltHyb_step_right saltHyb_zero saltRedImpl simulateQ_pImpl_evalQuery_false simulateQ_pImpl_liftM_run slotSaltImplNF_fst_eq_saltRunNF slotSaltImplNF_run_map slotSaltImpl_fst_eq_saltRun slotSaltImpl_run_map step_dec step_enc_none_false step_enc_none_true step_enc_some step_inl)
open CryptoGames.LibsignalSM.Proofs.WireHop
open FSAEAD.Thm5 CryptoGames.Lazy
open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type} [DecidableEq Pt]

/-! ## Keyed slot lift (`slotLiftK`)

`slotLift` dispatches each OT-CCA query on its slot index `h.1 : ℕ`. `slotLiftK sk` dispatches on
an arbitrary slot key `sk h : κ` instead, so one multi-slot game can host slots of several sessions
(for example `sk a = (a.1, a.2.1.2)`: message index and ratchet public key). `slotLiftK_fst` shows
that `sk = Prod.fst` recovers `slotLift`. -/

section Keyed

variable {A M C' S κ : Type} [DecidableEq κ]

/-- Keyed variant of `slotLiftOtcca`: dispatches each encryption/decryption query on the slot key
`sk h : κ` instead of the slot index `h.1 : ℕ`. -/
@[expose] def slotLiftOtccaK (sk : ℕ × A → κ)
    (impl : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT S ProbComp)) :
    QueryImpl (AEADScheme.otccaSpec (ℕ × A) M C') (StateT (κ → S) ProbComp)
  | .inl (h, msg) => StateT.mk fun σ => do
      let (r, s') ← (impl (.inr (.inl (h, msg)))).run (σ (sk h))
      pure (r, Function.update σ (sk h) s')
  | .inr (h, e) => StateT.mk fun σ => do
      let (r, s') ← (impl (.inr (.inr (h, e)))).run (σ (sk h))
      pure (r, Function.update σ (sk h) s')

/-- Keyed variant of `slotLift`: lifts a single-slot implementation on state `S` to the multi-slot
state `κ → S`, dispatching each OT-CCA query on its slot key `sk h`. -/
@[expose] def slotLiftK (sk : ℕ × A → κ)
    (impl : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT S ProbComp)) :
    QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT (κ → S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (κ → S) ProbComp)
    + slotLiftOtccaK sk impl

@[simp] theorem slotLiftK_inl (sk : ℕ × A → κ)
    (impl : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT S ProbComp)) (n : ℕ) :
    slotLiftK sk impl (.inl n) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (κ → S) ProbComp) n :=
  rfl

@[simp] theorem slotLiftK_inr (sk : ℕ × A → κ)
    (impl : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT S ProbComp))
    (q : (AEADScheme.otccaSpec (ℕ × A) M C').Domain) :
    slotLiftK sk impl (.inr q) = slotLiftOtccaK sk impl q :=
  rfl

/-- Keying by the slot index recovers `slotLift`. -/
theorem slotLiftK_fst
    (impl : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec A M C') (StateT S ProbComp)) :
    slotLiftK Prod.fst impl = FSAEAD.Thm5.slotLift impl := by
  funext q
  rcases q with n | ⟨h, msg⟩ | ⟨h, e⟩ <;> rfl

end Keyed

/-! ## Global multi-slot MAC forgery hop (`multiSalt_false_boolDist_multiSaltNF_false`) -/

variable {κ : Type} [DecidableEq κ]

abbrev MSaltSt (κ Pt : Type) := κ → SaltSlotSt Pt

/-- `ProbComp` key lookup at slot `i` and salt `salt` on `MSaltSt κ Pt × Bool`. -/
@[expose] def mKeyOfF (i : κ) (salt : Salt32) : StateT (MSaltSt κ Pt × Bool) ProbComp DerivedMessageKeys :=
  StateT.mk fun (st, f) =>
    (fun p : DerivedMessageKeys × SaltSlotSt Pt => (p.1, (Function.update st i p.2, f))) <$>
      (slotKeyOf salt).run (st i)

/-- Multi-slot flag game `multiSaltFlagNF`: identical to `slotLiftK sk (slotSaltImpl false)` on
challenge-salt decryptions within each slot `(sk a)`, while non-challenge-salt decryptions
(`!isChalSalt (s.1 (sk a)).chal a.2.2.salt`, including all pre-challenge decryptions at slot `(sk a)`)
return `none` and raise the global `Bool` flag when the HMAC (Hash-based Message Authentication
Code) tag check accepts. -/
@[expose] def multiSaltFlagNF (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) :
    QueryImpl (QSpecS Pt ℓ) (StateT (MSaltSt κ Pt × Bool) ProbComp)
  | .inl n => EtMProof.coin n
  | .inr (.inl ⟨a, m⟩) => do
    let s ← get
    if (s.1 (sk a)).chal.isSome then return none
    let mk ← mKeyOfF (sk a) a.2.2.salt
    let e := (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m
    modify fun (st, f) =>
      (Function.update st (sk a) { (st (sk a)) with chal := some (a, e) }, f)
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    let s ← get
    if (s.1 (sk a)).chal == some (a, e) then return none
    let mk ← mKeyOfF (sk a) a.2.2.salt
    if isChalSalt (s.1 (sk a)).chal a.2.2.salt then
      return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e
    else
      modify fun (st, f) =>
        (st, f || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2))
      return none

theorem multiSaltFlagNF_flag (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt κ Pt) (fl : Bool) :
    (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl) =
      Prod.map id (fun z : MSaltSt κ Pt × Bool => (z.1, fl || z.2)) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false) := by
  have := EtMProof.run_map (multiSaltFlagNF C codec ℓ encT idOf sk)
    (multiSaltFlagNF C codec ℓ encT idOf sk)
    (fun z : MSaltSt κ Pt × Bool => (z.1, fl || z.2)) (fun _ => True)
    (fun t z _ => ?_) oa (st, false) trivial
  · simpa using this
  refine ⟨?_, fun _ _ => trivial⟩
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · simp [multiSaltFlagNF, EtMProof.coin]
  · by_cases hc : (z.1 (sk a)).chal.isSome = true
    · simp only [multiSaltFlagNF, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
        StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    · simp only [multiSaltFlagNF, mKeyOfF, StateT.run_bind, StateT.run_get, pure_bind, hc,
        Bool.false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_modify, StateT.run_pure,
        bind_map_left, map_bind, map_pure, Prod.map_apply, id_eq]
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp only [multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
        map_pure, Prod.map_apply, id_eq]
    · by_cases hch : ((z.1 (sk a)).chal == some (a, e)) = true
      · simp only [multiSaltFlagNF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
          hch, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
      · by_cases hcs : isChalSalt (z.1 (sk a)).chal a.2.2.salt = true
        · simp only [multiSaltFlagNF, mKeyOfF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get,
            pure_bind, hch, Bool.false_eq_true, StateT.run_mk, hcs, StateT.run_pure,
            bind_map_left, map_bind, map_pure, Prod.map_apply, id_eq]
        · simp only [multiSaltFlagNF, mKeyOfF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get,
            pure_bind, hch, Bool.false_eq_true, StateT.run_mk, hcs, StateT.run_modify,
            StateT.run_pure, bind_map_left, map_bind, map_pure,
            Prod.map_apply, id_eq, Bool.or_assoc]

theorem multiSaltFlagNF_flag_or (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt κ Pt) (fl : Bool) :
    (fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl) =
      (fl || ·) <$> ((fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false)) := by
  rw [multiSaltFlagNF_flag C codec ℓ encT idOf sk oa st fl, Functor.map_map, Functor.map_map]
  rfl

theorem multiSaltFlagNF_out_fl (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt κ Pt) (fl : Bool) :
    (fun z : α × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl) =
      (fun z : α × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false) := by
  rw [multiSaltFlagNF_flag C codec ℓ encT idOf sk oa st fl, Functor.map_map]
  rfl

theorem slotLift_slotSaltImpl_false_le_multiSaltFlagNF (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (post : α → ProbComp Bool) (x : Bool) :
    ∀ (st : MSaltSt κ Pt),
      𝒟[(simulateQ (slotLiftK sk (slotSaltImpl C codec ℓ encT idOf false)) oa).run st >>=
        fun z => post z.1] {x} ≤
        𝒟[(simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false) >>=
          fun z => post z.1] {x} +
        𝒟[(fun z => z.2.2) <$>
          (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false)] {true} := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st; simp
  | query_bind q k ih =>
    intro st
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [slotLiftK_inl, multiSaltFlagNF, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact WireHop.bind_apply_le_add_true _ _ _ _ x fun u => ih u st
    · by_cases hc : (st (sk a)).chal.isSome = true
      · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, StateT.run_mk,
          StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte, StateT.run_pure,
          Function.update_eq_self]
        exact ih none st
      · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, mKeyOfF, slotKeyOf,
          StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hc, Bool.false_eq_true,
          ↓reduceIte, StateT.run_modify, StateT.run_pure, bind_map_left, bind_assoc,
          Function.update_self, Function.update_idem]
        cases hlk : (st (sk a)).table.lookup a.2.2.salt with
        | some mk =>
          simp only [pure_bind]
          exact ih _ _
        | none =>
          simp only [bind_map_left]
          exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => ih _ _
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, hs, ne_eq,
          not_false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_pure, pure_bind,
          Function.update_eq_self]
        exact ih none st
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases hch : ((st (sk a)).chal == some (a, e)) = true
        · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, hs, ne_eq,
            not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get,
            pure_bind, Bool.false_or, hch, StateT.run_pure, Function.update_eq_self]
          exact ih none st
        · by_cases hcs : isChalSalt (st (sk a)).chal a.2.2.salt = true
          · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk,
              StateT.run_bind, StateT.run_get, pure_bind, Bool.false_or, hch, Bool.false_eq_true,
              hcs, StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st (sk a)).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind]
              exact ih _ _
            | none =>
              simp only [bind_map_left]
              exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => ih _ _
          · simp only [slotLiftK_inr, slotLiftOtccaK, slotSaltImpl, multiSaltFlagNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk,
              StateT.run_bind, StateT.run_get, pure_bind, Bool.false_or, hch, Bool.false_eq_true,
              hcs, StateT.run_modify, StateT.run_pure, bind_map_left, bind_assoc]
            have hstep : ∀ (mk : DerivedMessageKeys) (st' : MSaltSt κ Pt),
                𝒟[(simulateQ (slotLiftK sk (slotSaltImpl C codec ℓ encT idOf false))
                    (k ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e))).run st' >>=
                  fun z => post z.1] {x} ≤
                𝒟[(simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                    (st', (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2) >>=
                  fun z => post z.1] {x} +
                𝒟[(fun z => z.2.2) <$>
                  (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                    (st', (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)]
                  {true} := by
              intro mk st'
              rcases htag :
                ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)
              · rw [lAeadK_dec_eq_none_of_tag_false C codec ℓ encT idOf mk a e htag]
                exact ih none st'
              · refine le_trans (EtMProof.apply_le_one _ _) (le_trans (le_of_eq ?_) le_add_self)
                have hf := multiSaltFlagNF_flag_or C codec ℓ encT idOf sk (k none) st' true
                rw [hf, Functor.map_map, map_eq_bind_pure_comp]
                exact (EtMProof.const_true_eq_one _).symm
            cases hlk : (st (sk a)).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind]
              exact hstep mk _
            | none =>
              simp only [bind_map_left]
              exact WireHop.bind_apply_le_add_true _ _ _ _ x fun mk => hstep mk _

/-- Lazy key lookup for `multiSaltLazy i₀ s₀`: uses `getSlotKey` when `i = i₀ ∧ salt = s₀` and
`mKeyOfF i salt` otherwise. -/
@[expose] def mKeyOfLazy (i₀ : κ) (s₀ : Salt32) (i : κ) (salt : Salt32) :
    StateT ((MSaltSt κ Pt × Bool) × Option DerivedMessageKeys) ProbComp DerivedMessageKeys :=
  if i = i₀ ∧ salt = s₀ then getSlotKey else WireHop.onH (mKeyOfF i salt)

omit [DecidableEq Pt] in
theorem rc_mKeyOfLazy (i₀ : κ) (s₀ : Salt32) (i : κ) (salt : Salt32) :
    RC (fillKey (H := MSaltSt κ Pt × Bool))
      (mKeyOfLazy i₀ s₀ i salt) (mKeyOfLazy i₀ s₀ i salt) := by
  unfold mKeyOfLazy
  split_ifs
  · exact rc_getSlotKey_self
  · exact rc_onH _

/-- Variant of `multiSaltFlagNF` that stores the key for a distinguished `(i₀, s₀)` in a separate
lazy slot `Option DerivedMessageKeys`, while keeping all other `(i, s) ≠ (i₀, s₀)` in `(st i).table`. -/
@[expose] def multiSaltLazy (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) (i₀ : κ) (s₀ : Salt32) :
    QueryImpl (QSpecS Pt ℓ) (StateT ((MSaltSt κ Pt × Bool) × Option DerivedMessageKeys) ProbComp)
  | .inl n => WireHop.onH (EtMProof.coin n)
  | .inr (.inl ⟨a, m⟩) => do
    let s ← WireHop.onH get
    if (s.1 (sk a)).chal.isSome then return none
    let mk ← mKeyOfLazy i₀ s₀ (sk a) a.2.2.salt
    let e := (lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m
    WireHop.onH (modify fun (st, f) =>
      (Function.update st (sk a) { (st (sk a)) with chal := some (a, e) }, f))
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if e.2 ≠ a.2.2.salt then return none
    let s ← WireHop.onH get
    if (s.1 (sk a)).chal == some (a, e) then return none
    let mk ← mKeyOfLazy i₀ s₀ (sk a) a.2.2.salt
    if isChalSalt (s.1 (sk a)).chal a.2.2.salt then
      return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e
    else
      WireHop.onH (modify fun (st, f) =>
        (st, f || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)))
      return none

theorem multiSaltLazy_rc (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) (i₀ : κ) (s₀ : Salt32)
    (t : (QSpecS Pt ℓ).Domain) :
    RC (fillKey (H := MSaltSt κ Pt × Bool))
      (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ t)
      (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ t) := by
  rcases t with n | ⟨a, m⟩ | ⟨a, e⟩
  · exact rc_onH _
  · refine (rc_onH _).bind fun s => ?_
    by_cases hc : (s.1 (sk a)).chal.isSome = true
    · simp only [hc, ↓reduceIte]
      exact RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) none
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact (rc_mKeyOfLazy i₀ s₀ (sk a) a.2.2.salt).bind fun _ =>
        (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) _
  · by_cases hs : e.2 ≠ a.2.2.salt
    · simp only [multiSaltLazy, hs, ne_eq, not_false_eq_true, ↓reduceIte]
      exact RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) none
    · simp only [multiSaltLazy, hs, ↓reduceIte]
      refine (rc_onH _).bind fun s => ?_
      by_cases hch : ((s.1 (sk a)).chal == some (a, e)) = true
      · simp only [hch, ↓reduceIte]
        exact RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) none
      · simp only [hch, Bool.false_eq_true, ↓reduceIte]
        refine (rc_mKeyOfLazy i₀ s₀ (sk a) a.2.2.salt).bind fun _ => ?_
        by_cases hcs : isChalSalt (s.1 (sk a)).chal a.2.2.salt = true
        · simp only [hcs, ↓reduceIte]
          exact RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) _
        · simp only [hcs, Bool.false_eq_true, ↓reduceIte]
          exact (rc_onH _).bind fun _ => RC.pure (idem_fillKey (H := MSaltSt κ Pt × Bool)) none

/-- Synchronization invariant between `multiSaltFlagNF` and `multiSaltLazy i₀ s₀`. -/
structure MSaltLazySync (i₀ : κ) (s₀ : Salt32) (st₁ st₂ : MSaltSt κ Pt) (sl : Option DerivedMessageKeys) :
    Prop where
  other_slot : ∀ i, i ≠ i₀ → st₁ i = st₂ i
  chal_self : (st₁ i₀).chal = (st₂ i₀).chal
  lk_self : (st₁ i₀).table.lookup s₀ = sl
  lk_other : ∀ s, s ≠ s₀ → (st₁ i₀).table.lookup s = (st₂ i₀).table.lookup s

omit [DecidableEq Pt] in
theorem MSaltLazySync.chal_eq {i₀ : κ} {s₀ : Salt32} {st₁ st₂ : MSaltSt κ Pt} {sl : Option DerivedMessageKeys}
    (h : MSaltLazySync i₀ s₀ st₁ st₂ sl) (i : κ) :
    (st₁ i).chal = (st₂ i).chal := by
  by_cases hi : i = i₀
  · subst hi; exact h.chal_self
  · rw [h.other_slot i hi]

omit [DecidableEq Pt] in
theorem MSaltLazySync.upd_chal {i₀ : κ} {s₀ : Salt32} {st₁ st₂ : MSaltSt κ Pt} {sl : Option DerivedMessageKeys}
    (h : MSaltLazySync i₀ s₀ st₁ st₂ sl) (i : κ) (ch : ChalState Pt) :
    MSaltLazySync i₀ s₀
      (Function.update st₁ i { (st₁ i) with chal := ch })
      (Function.update st₂ i { (st₂ i) with chal := ch }) sl := by
  refine ⟨fun j hj => ?_, ?_, ?_, fun s hs => ?_⟩
  · by_cases hij : j = i
    · subst hij; simp [h.other_slot j hj]
    · simp [Function.update_of_ne hij, h.other_slot j hj]
  · by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne (Ne.symm hi), h.chal_self]
  · by_cases hi : i = i₀
    · subst hi; simp [h.lk_self]
    · simp [Function.update_of_ne (Ne.symm hi), h.lk_self]
  · by_cases hi : i = i₀
    · subst hi; simp [h.lk_other s hs]
    · simp [Function.update_of_ne (Ne.symm hi), h.lk_other s hs]

omit [DecidableEq Pt] in
theorem mKeyOfF_run_bind_eq (i₀ : κ) (s₀ : Salt32) (i : κ) (salt : Salt32) {β : Type}
    (st₁ st₂ : MSaltSt κ Pt) (fl : Bool) (sl : Option DerivedMessageKeys)
    (hsync : MSaltLazySync i₀ s₀ st₁ st₂ sl)
    (k₁ : DerivedMessageKeys × (MSaltSt κ Pt × Bool) → ProbComp β)
    (k₂ : DerivedMessageKeys × ((MSaltSt κ Pt × Bool) × Option DerivedMessageKeys) → ProbComp β)
    (hk : ∀ mk st₁' st₂' sl',
      MSaltLazySync i₀ s₀ st₁' st₂' sl' →
      k₁ (mk, (st₁', fl)) = k₂ (mk, ((st₂', fl), sl'))) :
    ((mKeyOfF i salt).run (st₁, fl) >>= k₁) =
      ((mKeyOfLazy i₀ s₀ i salt).run ((st₂, fl), sl) >>= k₂) := by
  unfold mKeyOfLazy mKeyOfF slotKeyOf
  by_cases hi : i = i₀
  · subst hi
    by_cases hs : salt = s₀
    · subst hs
      simp only [and_self, ↓reduceIte, getSlotKey, StateT.run_mk, hsync.lk_self, bind_map_left]
      cases sl with
      | some mk =>
        simp only [pure_bind, Function.update_eq_self]
        exact hk mk st₁ st₂ (some mk) hsync
      | none =>
        simp only [bind_map_left]
        refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
        refine hk mk
          (Function.update st₁ i { (st₁ i) with table := (salt, mk) :: (st₁ i).table })
          st₂ (some mk) ⟨fun j hj => ?_, by simp [hsync.chal_self], by simp, fun s hs_ne => ?_⟩
        · simp [Function.update_of_ne hj, hsync.other_slot j hj]
        · simp [List.lookup, beq_eq_false_iff_ne.mpr hs_ne, hsync.lk_other s hs_ne]
    · have hlk_eq : (st₁ i).table.lookup salt = (st₂ i).table.lookup salt := hsync.lk_other salt hs
      simp only [hs, and_false, ↓reduceIte, WireHop.onH, StateT.run_mk, hlk_eq, bind_map_left]
      cases hlk : (st₂ i).table.lookup salt with
      | some mk =>
        simp only [pure_bind, Function.update_eq_self]
        exact hk mk st₁ st₂ sl hsync
      | none =>
        simp only [bind_map_left]
        refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
        refine hk mk
          (Function.update st₁ i { (st₁ i) with table := (salt, mk) :: (st₁ i).table })
          (Function.update st₂ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
          sl ⟨fun j hj => ?_, by simp [hsync.chal_self], ?_, fun s hs_ne => ?_⟩
        · simp [Function.update_of_ne hj, hsync.other_slot j hj]
        · simp [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm hs), hsync.lk_self]
        · simp only [Function.update_self, List.lookup]
          by_cases hs' : (s == salt) = true
          · simp [hs']
          · simp [hs', hsync.lk_other s hs_ne]
  · have hst_i : st₁ i = st₂ i := hsync.other_slot i hi
    simp only [hi, false_and, ↓reduceIte, WireHop.onH, StateT.run_mk, hst_i, bind_map_left]
    cases hlk : (st₂ i).table.lookup salt with
    | some mk =>
      simp only [pure_bind, Function.update_eq_self]
      rw [← hst_i, Function.update_eq_self]
      exact hk mk st₁ st₂ sl hsync
    | none =>
      simp only [bind_map_left]
      refine congrArg (Bind.bind (m := ProbComp) _) (funext fun mk => ?_)
      refine hk mk
        (Function.update st₁ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
        (Function.update st₂ i { (st₂ i) with table := (salt, mk) :: (st₂ i).table })
        sl ⟨fun j hj => ?_, ?_, ?_, fun s hs_ne => ?_⟩
      · by_cases hij : j = i
        · subst hij; simp
        · simp [Function.update_of_ne hij, hsync.other_slot j hj]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.chal_self]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.lk_self]
      · simp [Function.update_of_ne (Ne.symm hi), hsync.lk_other s hs_ne]

theorem multiSaltFlagNF_eq_multiSaltLazy (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) (i₀ : κ) (s₀ : Salt32)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α) :
    ∀ (st₁ st₂ : MSaltSt κ Pt) (fl : Bool) (sl : Option DerivedMessageKeys),
      MSaltLazySync i₀ s₀ st₁ st₂ sl →
      (fun z : α × MSaltSt κ Pt × Bool => (z.1, z.2.2)) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st₁, fl) =
      (fun z : α × (MSaltSt κ Pt × Bool) × Option DerivedMessageKeys => (z.1, z.2.1.2)) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀) oa).run ((st₂, fl), sl) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st₁ st₂ fl sl _; simp
  | query_bind q k ih =>
    intro st₁ st₂ fl sl hsync
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, EtMProof.coin,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_mk, StateT.run_monadLift,
        bind_map_left, bind_assoc, pure_bind]
      exact congrArg (Bind.bind (m := ProbComp) _) (funext fun u => ih u st₁ st₂ fl sl hsync)
    · by_cases hc : (st₂ (sk a)).chal.isSome = true
      · have hc₁ : (st₁ (sk a)).chal.isSome = true := hsync.chal_eq (sk a) ▸ hc
        simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, StateT.run_mk, StateT.run_bind,
          StateT.run_get, pure_bind, hc, hc₁, ↓reduceIte, StateT.run_pure, map_pure]
        exact ih none st₁ st₂ fl sl hsync
      · have hc₁ : (st₁ (sk a)).chal.isSome = false :=
          hsync.chal_eq (sk a) ▸ Bool.eq_false_iff.mpr hc
        simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, StateT.run_mk, StateT.run_bind,
          StateT.run_get, pure_bind, hc, hc₁, Bool.false_eq_true, ↓reduceIte, StateT.run_modify,
          StateT.run_pure, map_pure, bind_assoc]
        refine mKeyOfF_run_bind_eq i₀ s₀ (sk a) a.2.2.salt st₁ st₂ fl sl hsync _ _
          fun mk st₁' st₂' sl' hsync' => ?_
        exact ih _ _ _ fl sl' (hsync'.upd_chal (sk a) _)
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltLazy, multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind]
        exact ih none st₁ st₂ fl sl hsync
      · by_cases hch : ((st₂ (sk a)).chal == some (a, e)) = true
        · have hch₁ : ((st₁ (sk a)).chal == some (a, e)) = true := hsync.chal_eq (sk a) ▸ hch
          simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, hs, ↓reduceIte, StateT.run_mk,
            StateT.run_bind, StateT.run_get, pure_bind, hch, hch₁, StateT.run_pure, map_pure]
          exact ih none st₁ st₂ fl sl hsync
        · have hch₁ : ((st₁ (sk a)).chal == some (a, e)) = false :=
            hsync.chal_eq (sk a) ▸ Bool.eq_false_iff.mpr hch
          simp only [multiSaltLazy, WireHop.onH, multiSaltFlagNF, hs, ↓reduceIte, StateT.run_mk,
            StateT.run_bind, StateT.run_get, map_pure, pure_bind, hch, hch₁, Bool.false_eq_true,
            bind_assoc]
          refine mKeyOfF_run_bind_eq i₀ s₀ (sk a) a.2.2.salt st₁ st₂ fl sl hsync _ _
            fun mk st₁' st₂' sl' hsync' => ?_
          by_cases hcs : isChalSalt (st₂ (sk a)).chal a.2.2.salt = true
          · have hcs₁ : isChalSalt (st₁ (sk a)).chal a.2.2.salt = true := hsync.chal_eq (sk a) ▸ hcs
            simp only [hcs, hcs₁, ↓reduceIte, StateT.run_pure, pure_bind]
            exact ih _ st₁' st₂' fl sl' hsync'
          · have hcs₁ : isChalSalt (st₁ (sk a)).chal a.2.2.salt = false :=
              hsync.chal_eq (sk a) ▸ Bool.eq_false_iff.mpr hcs
            simp only [hcs, hcs₁, Bool.false_eq_true, ↓reduceIte, StateT.run_modify, map_pure]
            exact ih none st₁' st₂' _ sl' hsync'

theorem multiSaltFlagNF_prepopulate_flag (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) (i₀ : κ) (s₀ : Salt32)
    {α : Type} (oa : OracleComp (QSpecS Pt ℓ) α)
    (st : MSaltSt κ Pt) (fl : Bool) (hlk : (st i₀).table.lookup s₀ = none) :
    𝒟[do
      let k₀ ← $ᵗ DerivedMessageKeys
      (fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl)] =
    𝒟[(fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl)] := by
  have h1 : ∀ k₀ : DerivedMessageKeys,
      (fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl) =
      (fun z : α × (MSaltSt κ Pt × Bool) × Option DerivedMessageKeys => z.2.1.2) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀) oa).run ((st, fl), some k₀) := by
    intro k₀
    have h := congrArg (Prod.snd <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ oa
        (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table })
        st fl (some k₀)
        ⟨fun i hi => by simp [Function.update_of_ne hi], by simp, by simp,
          fun s hs => by simp [List.lookup, beq_eq_false_iff_ne.mpr hs]⟩)
    simpa only [Functor.map_map] using h
  have h2 :
      (fun z : α × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl) =
      (fun z : α × (MSaltSt κ Pt × Bool) × Option DerivedMessageKeys => z.2.1.2) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀) oa).run ((st, fl), none) := by
    have h := congrArg (Prod.snd <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ oa st st fl none
        ⟨fun _ _ => rfl, rfl, hlk, fun _ _ => rfl⟩)
    simpa only [Functor.map_map] using h
  simp only [h1, h2]
  have hlz := evalDist_eager_eq_lazy
    (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀)
    (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀)
    (multiSaltLazy_rc C codec ℓ encT idOf sk i₀ s₀) oa (st, fl) (fun _ h => pure h.2)
  simpa [map_eq_bind_pure_comp] using hlz

theorem multiSaltFlagNF_prepopulate_out (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ) (i₀ : κ) (s₀ : Salt32)
    (oa : OracleComp (QSpecS Pt ℓ) Bool)
    (st : MSaltSt κ Pt) (fl : Bool) (hlk : (st i₀).table.lookup s₀ = none) :
    𝒟[do
      let k₀ ← $ᵗ DerivedMessageKeys
      (fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl)] =
    𝒟[(fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl)] := by
  have h1 : ∀ k₀ : DerivedMessageKeys,
      (fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run
          (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table }, fl) =
      (fun z : Bool × (MSaltSt κ Pt × Bool) × Option DerivedMessageKeys => z.1) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀) oa).run ((st, fl), some k₀) := by
    intro k₀
    have h := congrArg (Prod.fst <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ oa
        (Function.update st i₀ { (st i₀) with table := (s₀, k₀) :: (st i₀).table })
        st fl (some k₀)
        ⟨fun i hi => by simp [Function.update_of_ne hi], by simp, by simp,
          fun s hs => by simp [List.lookup, beq_eq_false_iff_ne.mpr hs]⟩)
    simpa only [Functor.map_map] using h
  have h2 :
      (fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl) =
      (fun z : Bool × (MSaltSt κ Pt × Bool) × Option DerivedMessageKeys => z.1) <$>
        (simulateQ (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀) oa).run ((st, fl), none) := by
    have h := congrArg (Prod.fst <$> ·)
      (multiSaltFlagNF_eq_multiSaltLazy C codec ℓ encT idOf sk i₀ s₀ oa st st fl none
        ⟨fun _ _ => rfl, rfl, hlk, fun _ _ => rfl⟩)
    simpa only [Functor.map_map] using h
  rw [h2]
  simp only [h1]
  have hlz := evalDist_eager_eq_lazy
    (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀)
    (multiSaltLazy C codec ℓ encT idOf sk i₀ s₀)
    (multiSaltLazy_rc C codec ℓ encT idOf sk i₀ s₀) oa (st, fl) (fun b' _ => pure b')
  simpa [map_eq_bind_pure_comp] using hlz

/-- Invariant on `SaltSlotSt`: before the challenge encryption query (`chal = none`), `table = []`;
after (`chal = some (a₀, e₀)`), `table` has an entry only at `a₀.2.2.salt`. -/
@[expose] def SaltSlotTableInv (sst : SaltSlotSt Pt) : Prop :=
  match sst.chal with
  | none => sst.table = []
  | some (a₀, _) => ∀ s, s ≠ a₀.2.2.salt → sst.table.lookup s = none

/-- Pointwise `SaltSlotTableInv` across all slot keys `i : κ`. -/
@[expose] def MSaltTableInv (st : MSaltSt κ Pt) : Prop :=
  ∀ i, SaltSlotTableInv (st i)

omit [DecidableEq Pt] [DecidableEq κ] in
theorem MSaltTableInv.init : MSaltTableInv (fun _ : κ => ({} : SaltSlotSt Pt)) :=
  fun _ => rfl

omit [DecidableEq Pt] [DecidableEq κ] in
theorem MSaltTableInv.lookup_eq_none_of_isChalSalt_false {st : MSaltSt κ Pt}
    (hinv : MSaltTableInv st) (i : κ) {s : Salt32}
    (hcs : isChalSalt (st i).chal s = false) :
    (st i).table.lookup s = none := by
  have hi := hinv i
  unfold SaltSlotTableInv at hi
  unfold isChalSalt at hcs
  cases hch : (st i).chal with
  | none => rw [hch] at hi; simp [hi]
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    rw [hch] at hi hcs
    exact hi s (beq_eq_false_iff_ne.mp hcs)

omit [DecidableEq Pt] [DecidableEq κ] in
theorem MSaltTableInv.lookup_eq_none_of_isSome_false {st : MSaltSt κ Pt}
    (hinv : MSaltTableInv st) {i : κ} (hc : (st i).chal.isSome = false) (s : Salt32) :
    (st i).table.lookup s = none := by
  have hi := hinv i
  unfold SaltSlotTableInv at hi
  cases hch : (st i).chal with
  | none => rw [hch] at hi; simp [hi]
  | some _ => rw [hch] at hc; cases hc

omit [DecidableEq Pt] in
theorem MSaltTableInv.enc_step {st : MSaltSt κ Pt} (sk : AD Pt → κ) (a : AD Pt) (e : Ct) (mk : DerivedMessageKeys)
    (hinv : MSaltTableInv st) (hc : (st (sk a)).chal.isSome = false) :
    MSaltTableInv (Function.update st (sk a)
      { chal := some (a, e), table := (a.2.2.salt, mk) :: (st (sk a)).table }) := by
  intro i
  by_cases hi : i = (sk a)
  · subst hi
    have ha := hinv (sk a)
    unfold SaltSlotTableInv at ha ⊢
    simp only [Function.update_self]
    cases hch : (st (sk a)).chal with
    | none =>
      rw [hch] at ha
      intro s hs
      simp [ha, List.lookup, beq_eq_false_iff_ne.mpr hs]
    | some _ => rw [hch] at hc; cases hc
  · simpa [Function.update_of_ne hi] using hinv i

omit [DecidableEq Pt] in
theorem MSaltTableInv.dec_chal_step {st : MSaltSt κ Pt} (i : κ) {salt : Salt32} (mk : DerivedMessageKeys)
    (hinv : MSaltTableInv st) (hcs : isChalSalt (st i).chal salt = true) :
    MSaltTableInv (Function.update st i { (st i) with table := (salt, mk) :: (st i).table }) := by
  intro j
  by_cases hj : j = i
  · subst hj
    have hi := hinv j
    unfold SaltSlotTableInv at hi ⊢
    unfold isChalSalt at hcs
    simp only [Function.update_self]
    cases hch : (st j).chal with
    | none => rw [hch] at hcs; cases hcs
    | some p =>
      rcases p with ⟨a₀, e₀⟩
      rw [hch] at hi hcs
      have hsalt : salt = a₀.2.2.salt := beq_iff_eq.mp hcs
      subst hsalt
      intro s hs
      simp [List.lookup, beq_eq_false_iff_ne.mpr hs, hi s hs]
  · simpa [Function.update_of_ne hj] using hinv j

theorem multiSaltFlagNF_flag_le_aux (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    {oa : OracleComp (QSpecS Pt ℓ) Bool}
    (hdec : GuardedSafe.GuardedSafePost otRespShort otDecLong (fun _ => True) oa) :
    ∀ (qd : ℕ) (st : MSaltSt κ Pt),
      MSaltTableInv st →
      AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) oa →
      oa.IsQueryBoundP (fun q => isDecQuery q = true) qd →
      𝒟[(fun z : Bool × MSaltSt κ Pt × Bool => z.2.2) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, false)] {true} ≤
        (qd : ℝ≥0∞) * macForgeryProb C.F := by
  induction hdec with
  | pure _ =>
    intro qd st _ _ _
    simp
  | @query_bind q k hnotlong _ ih =>
    intro qd st hinv hshort hq
    rw [AEADScheme.OTEncADsOk, isQueryBoundP_query_bind_iff] at hshort
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltFlagNF, EtMProof.coin, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        StateT.run_monadLift, bind_assoc, pure_bind]
      refine EtMProof.bind_le_of_support ($ᵗ (Fin (n + 1))) _ (measurableSet_singleton true)
        fun u _ => ?_
      have hk := hq.2 u
      simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inl n) = true) := by
        simp [AEADScheme.otEncBad]
      have hsh_u : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k u) := by
        simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 u
      exact ih u trivial qd st hinv hsh_u hk
    · have ha_ok : a.2.2.shortB = true := by
        have := hshort.1.resolve_right (Nat.not_lt_zero 0)
        simpa [AEADScheme.otEncBad] using this
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inr (.inl ⟨a, m⟩)) = true) := by
        simp [AEADScheme.otEncBad, ha_ok]
      by_cases hc : (st (sk a)).chal.isSome = true
      · have hk_none := hq.2 none
        simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk_none
        have hsh_none : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k none) := by
          simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 none
        simp only [multiSaltFlagNF, StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte,
          StateT.run_pure]
        exact ih none (by rintro _ ⟨⟩) qd st hinv hsh_none hk_none
      · have hcf : (st (sk a)).chal.isSome = false := Bool.eq_false_iff.mpr hc
        have hlk : (st (sk a)).table.lookup a.2.2.salt = none :=
          hinv.lookup_eq_none_of_isSome_false hcf a.2.2.salt
        simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, StateT.run_bind, StateT.run_get,
          StateT.run_mk, pure_bind, hcf, Bool.false_eq_true, ↓reduceIte, hlk, StateT.run_modify,
          StateT.run_pure, Functor.map_map, bind_map_left, bind_assoc,
          Function.update_self, Function.update_idem]
        refine EtMProof.bind_le_of_support ($ᵗ DerivedMessageKeys) _ (measurableSet_singleton true)
          fun mk _ => ?_
        have hk_some := hq.2 (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))
        simp only [isDecQuery, Bool.false_eq_true, ↓reduceIte] at hk_some
        have hsh_some : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB)
            (k (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))) := by
          simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using
            hshort.2 (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m))
        have hresp : otRespShort (AD := AD Pt) (M := Plain ℓ) (.inr (.inl ⟨a, m⟩))
            (some ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)) := by
          rintro _ ⟨rfl⟩
          exact ProstMsgAeadCorrect.lAeadK_enc_length_lt C codec hfit ℓ hℓ encT idOf mk
            ((a.1, a.2.1), a.2.2) m ha_ok
        exact ih _ hresp qd _ (hinv.enc_step sk a _ mk hcf) hsh_some hk_some
    · have he_lt : e.1.1.length < 2 ^ 32 := Classical.not_not.mp hnotlong
      have hpos : 0 < qd := hq.1.resolve_left (by simp [isDecQuery])
      have hk_none := hq.2 none
      simp only [isDecQuery, ↓reduceIte] at hk_none
      have hnb : ¬ (AEADScheme.otEncBad (M := Plain ℓ) (C := Ct) (fun a : AD Pt => a.2.2.shortB) (.inr (.inr ⟨a, e⟩)) = true) := by
        simp [AEADScheme.otEncBad]
      have hsh_r : ∀ r, AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) (k r) := fun r => by
        simpa only [AEADScheme.OTEncADsOk, hnb, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using hshort.2 r
      have hle_cast : ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F ≤
          (qd : ℝ≥0∞) * macForgeryProb C.F := by
        gcongr
        exact Nat.sub_le qd 1
      by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltFlagNF, hs, ne_eq, not_false_eq_true, ↓reduceIte, StateT.run_pure,
          pure_bind]
        exact (ih none trivial (qd - 1) st hinv (hsh_r none) hk_none).trans hle_cast
      · by_cases hch : ((st (sk a)).chal == some (a, e)) = true
        · simp only [multiSaltFlagNF, hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
            hch, StateT.run_pure]
          exact (ih none trivial (qd - 1) st hinv (hsh_r none) hk_none).trans hle_cast
        · by_cases hcs : isChalSalt (st (sk a)).chal a.2.2.salt = true
          · simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, hs, ↓reduceIte, StateT.run_bind,
              StateT.run_get, StateT.run_mk, pure_bind, hch, Bool.false_eq_true, hcs,
              StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st (sk a)).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind, Function.update_eq_self]
              have hk_dec := hq.2 ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e)
              simp only [isDecQuery, ↓reduceIte] at hk_dec
              exact (ih _ trivial (qd - 1) st hinv (hsh_r _) hk_dec).trans hle_cast
            | none =>
              simp only [bind_map_left]
              refine (EtMProof.bind_le_of_support ($ᵗ DerivedMessageKeys) _ (measurableSet_singleton true)
                fun mk _ => ?_).trans hle_cast
              have hk_dec := hq.2 ((lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e)
              simp only [isDecQuery, ↓reduceIte] at hk_dec
              exact ih _ trivial (qd - 1) _ (hinv.dec_chal_step (sk a) mk hcs) (hsh_r _) hk_dec
          · have hcsf : isChalSalt (st (sk a)).chal a.2.2.salt = false := Bool.eq_false_iff.mpr hcs
            have hlk : (st (sk a)).table.lookup a.2.2.salt = none :=
              hinv.lookup_eq_none_of_isChalSalt_false (sk a) hcsf
            simp only [multiSaltFlagNF, mKeyOfF, slotKeyOf, hs, ↓reduceIte, StateT.run_bind,
              StateT.run_get, StateT.run_mk, pure_bind, hch, Bool.false_eq_true, hcsf, hlk,
              StateT.run_modify, StateT.run_pure, Functor.map_map, bind_map_left, bind_assoc,
              Bool.false_or]
            have hstep : 𝒟[do
                let mk ← $ᵗ DerivedMessageKeys
                (fun z : Bool × MSaltSt κ Pt × Bool => z.2.2) <$>
                  (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                    (Function.update st (sk a) { (st (sk a)) with table := (a.2.2.salt, mk) :: (st (sk a)).table },
                      (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)]
                {true} ≤
                macForgeryProb C.F + ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F := by
              have hor : (do
                  let mk ← $ᵗ DerivedMessageKeys
                  (fun z : Bool × MSaltSt κ Pt × Bool => z.2.2) <$>
                    (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                      (Function.update st (sk a) { (st (sk a)) with table := (a.2.2.salt, mk) :: (st (sk a)).table },
                        (hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2)) =
                (do
                  let mk ← $ᵗ DerivedMessageKeys
                  (((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2) || ·) <$>
                    ((fun z : Bool × MSaltSt κ Pt × Bool => z.2.2) <$>
                      (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                        (Function.update st (sk a) { (st (sk a)) with table := (a.2.2.salt, mk) :: (st (sk a)).table },
                          false))) :=
                congrArg (Bind.bind (m := ProbComp) _) (funext fun mk =>
                  multiSaltFlagNF_flag_or C codec ℓ encT idOf sk (k none) _ _)
              rw [hor]
              refine (EtMProof.union_step ($ᵗ DerivedMessageKeys) _ _).trans (add_le_add
                (lForge_step_le C.F (lIds idOf a.2.1.1) e.1.1 he_lt e.1.2) ?_)
              have hprep := congrArg (fun μ => μ {true})
                (multiSaltFlagNF_prepopulate_flag C codec ℓ encT idOf sk (sk a) a.2.2.salt (k none)
                  st false hlk)
              rw [hprep]
              exact ih none trivial (qd - 1) st hinv (hsh_r none) hk_none
            have hqd_eq : (qd : ℝ≥0∞) * macForgeryProb C.F =
                macForgeryProb C.F + ((qd - 1 : ℕ) : ℝ≥0∞) * macForgeryProb C.F := by
              have : qd = 1 + (qd - 1) := by omega
              conv_lhs => rw [this, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            exact hqd_eq ▸ hstep

theorem evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (st : MSaltSt κ Pt) (fl : Bool),
      MSaltTableInv st →
      𝒟[(fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
        (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) oa).run (st, fl)] =
      𝒟[Prod.fst <$>
        (simulateQ (slotLiftK sk (slotSaltImplNF C codec ℓ encT idOf false)) oa).run st] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro st fl _; simp
  | query_bind q k ih =>
    intro st fl hinv
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [multiSaltFlagNF, slotLiftK_inl, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u => ih u st fl hinv
    · by_cases hc : (st (sk a)).chal.isSome = true
      · simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, StateT.run_mk,
          StateT.run_bind, StateT.run_get, pure_bind, hc, ↓reduceIte, StateT.run_pure,
          Function.update_eq_self]
        exact ih none st fl hinv
      · have hcf : (st (sk a)).chal.isSome = false := Bool.eq_false_iff.mpr hc
        have hlk : (st (sk a)).table.lookup a.2.2.salt = none :=
          hinv.lookup_eq_none_of_isSome_false hcf a.2.2.salt
        simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, mKeyOfF,
          slotKeyOf, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind, hcf,
          Bool.false_eq_true, ↓reduceIte, hlk, StateT.run_modify, StateT.run_pure,
          Functor.map_map, bind_map_left, bind_assoc, Function.update_self, Function.update_idem]
        exact evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun mk =>
          ih _ _ fl (hinv.enc_step sk a _ mk hcf)
    · by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, hs, ne_eq,
          not_false_eq_true, ↓reduceIte, StateT.run_mk, StateT.run_pure, pure_bind,
          Function.update_eq_self]
        exact ih none st fl hinv
      · simp only [ne_eq, Decidable.not_not] at hs
        have his : isSlotChalSalt (st (sk a)).chal a.2.2.salt =
            isChalSalt (st (sk a)).chal a.2.2.salt := rfl
        by_cases hcs : isChalSalt (st (sk a)).chal a.2.2.salt = true
        · by_cases hch : ((st (sk a)).chal == some (a, e)) = true
          · simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, hs, ne_eq,
              not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind, StateT.run_get,
              pure_bind, his, hcs, Bool.not_true, Bool.false_or, hch, StateT.run_pure,
              Function.update_eq_self]
            exact ih none st fl hinv
          · simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, mKeyOfF,
              slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind,
              StateT.run_get, pure_bind, his, hcs, Bool.not_true, Bool.false_or, hch,
              Bool.false_eq_true, StateT.run_pure, bind_map_left, bind_assoc]
            cases hlk : (st (sk a)).table.lookup a.2.2.salt with
            | some mk =>
              simp only [pure_bind, Function.update_eq_self]
              exact ih _ st fl hinv
            | none =>
              simp only [bind_map_left]
              exact evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun mk =>
                ih _ _ fl (hinv.dec_chal_step (sk a) mk hcs)
        · have hcsf : isChalSalt (st (sk a)).chal a.2.2.salt = false := Bool.eq_false_iff.mpr hcs
          have hchf : ((st (sk a)).chal == some (a, e)) = false :=
            chal_beq_false_of_isChalSalt_false hcsf
          have hlk : (st (sk a)).table.lookup a.2.2.salt = none :=
            hinv.lookup_eq_none_of_isChalSalt_false (sk a) hcsf
          simp only [multiSaltFlagNF, slotLiftK_inr, slotLiftOtccaK, slotSaltImplNF, mKeyOfF,
            slotKeyOf, hs, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_mk, StateT.run_bind,
            StateT.run_get, pure_bind, his, hcsf, Bool.not_false, Bool.false_or, Bool.true_or,
            hchf, Bool.false_eq_true, hlk, StateT.run_modify, StateT.run_pure, Functor.map_map,
            bind_map_left, bind_assoc, Function.update_eq_self]
          have hfl : (do
              let mk ← $ᵗ DerivedMessageKeys
              (fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
                (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                  (Function.update st (sk a) { (st (sk a)) with table := (a.2.2.salt, mk) :: (st (sk a)).table },
                    fl || ((hmacScheme C.F).tag mk.2 ((lIds idOf a.2.1.1).toList ++ e.1.1) == e.1.2))) =
            (do
              let mk ← $ᵗ DerivedMessageKeys
              (fun z : Bool × MSaltSt κ Pt × Bool => z.1) <$>
                (simulateQ (multiSaltFlagNF C codec ℓ encT idOf sk) (k none)).run
                  (Function.update st (sk a) { (st (sk a)) with table := (a.2.2.salt, mk) :: (st (sk a)).table },
                    fl)) :=
            congrArg (Bind.bind (m := ProbComp) _) (funext fun mk =>
              (multiSaltFlagNF_out_fl C codec ℓ encT idOf sk (k none) _ _).trans
                (multiSaltFlagNF_out_fl C codec ℓ encT idOf sk (k none) _ fl).symm)
          rw [hfl, multiSaltFlagNF_prepopulate_out C codec ℓ encT idOf sk (sk a) a.2.2.salt (k none)
            st fl hlk]
          exact ih none st fl hinv

/-- Global multi-slot no-forgery bad-event bound.
Replacing `slotLiftK sk (slotSaltImpl false)` with `slotLiftK sk (slotSaltImplNF false)` across all
slot keys
simultaneously changes the adversary's output distribution by at most `qd * macForgeryProb C.F`
in `boolDist`, where `qd` bounds the total number of decryption queries made by `B`. -/
theorem multiSalt_false_boolDist_multiSaltNF_false_keyed (C : Crypto)
    (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (sk : AD Pt → κ)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) {qd : ℕ}
    (hB : MakesAtMostDecQueries B qd)
    (hshort : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) B)
    (hdec : GuardedOTDecShort B) :
    𝒟[Prod.fst <$> (simulateQ (slotLiftK sk (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {})].boolDist
      𝒟[Prod.fst <$> (simulateQ (slotLiftK sk (slotSaltImplNF C codec ℓ encT idOf false)) B).run
        (fun _ => {})] ≤
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  rw [← evalDist_multiSaltFlagNF_out_eq_slotLift_slotSaltImplNF_aux C codec ℓ encT idOf sk B
    (fun _ => {}) false MSaltTableInv.init]
  refine Measure.boolDist_le_of_apply_le _ _ fun x => ?_
  simp only [map_eq_bind_pure_comp]
  exact (slotLift_slotSaltImpl_false_le_multiSaltFlagNF C codec ℓ encT idOf sk B pure x
    (fun _ => {})).trans
    (add_le_add le_rfl
      (multiSaltFlagNF_flag_le_aux C codec hfit ℓ hℓ encT idOf sk hdec qd (fun _ => {})
        MSaltTableInv.init hshort hB))

/-- Global multi-slot no-forgery bad-event bound, slots keyed by the message index `a.1`
(`multiSalt_false_boolDist_multiSaltNF_false_keyed` at `sk = Prod.fst`). -/
theorem multiSalt_false_boolDist_multiSaltNF_false (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (AD Pt) (Plain ℓ) Ct) {qd : ℕ}
    (hB : MakesAtMostDecQueries B qd)
    (hshort : AEADScheme.OTEncADsOk (fun a : AD Pt => a.2.2.shortB) B)
    (hdec : GuardedOTDecShort B) :
    𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
        (fun _ => {})].boolDist
      𝒟[Prod.fst <$> (simulateQ (slotLift (slotSaltImplNF C codec ℓ encT idOf false)) B).run
        (fun _ => {})] ≤
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  simpa only [slotLiftK_fst] using
    multiSalt_false_boolDist_multiSaltNF_false_keyed C codec hfit ℓ hℓ encT idOf Prod.fst B hB
      hshort hdec

end CryptoGames.LibsignalSM.Proofs.SaltHopKeyed
