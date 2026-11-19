/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SessionAuthWireQueries -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.PubToAD

/-!
# Multi-Session `multiSessPubToAD` Query, Shortness, and AD-Class Preservation Lemmas

Lifts single-session `FSAEAD.pubRed` query-bound, `shortAD`, `oneADClass`, and
`GuardedMultiInjectShort` preservation properties across `SessionAuthBridge.multiSessPubToAD`.-/

set_option autoImplicit false

namespace Computational.Proofs.E2E.SessionAuthPubToAD

public section

open OracleSpec OracleComp
open _root_.CryptoGames.FSAEAD (
  RatchetSenderState RatchetReceiverState pubRedImpl encBadMsg encBadAD queryADOutsideClass
  transmitQuery challengeQuery corruptSenderQuery corruptReceiverQuery deliverQuery injectQuery)
open _root_.CryptoGames.GuardedSafe (GuardedSafePost)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.SM.Construction (Header)
open _root_.CryptoGames.LibsignalSession (SignalMessageProtoCodec)
open _root_.CryptoGames.Ratchet.LibsignalInst (
  LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lPubOf fsRespShort fsInjectLong)
open _root_.CryptoGames.LibsignalSM.Proofs.IndexRestrictions (stateT_lift_run query_eq_liftM)
open _root_.CryptoVerification.E2E.Signed.SessionRouter (
  multiSessSpec sessOffRange onInr onAnySess onSess isQueryBoundP_query_bind_pure_zero')
open _root_.CryptoVerification.E2E.Signed.SessionQueries (
  FsIdx fsInjQ isQueryBoundP_bind_zero_right)
open _root_.CryptoVerification.E2E.Signed.SessionFS (fsSpec)
open _root_.CryptoVerification.E2E.Signed.SessionWire (sessQueryAt)
open _root_.CryptoVerification.E2E.Signed.SessionWireQueries (
  fsEncBadAD fsOutsideClass shortOk multiRespShort multiInjectLong GuardedMultiInjectShort)
open Computational.Proofs.E2E.SessionAuthBridge (MultiSessPubFsAdv MultiSessFsAdv multiSessPubToAD)

section PubToADQueries

variable {Pt : Type} {ℓ : ℕ} (codec : SignalMessageProtoCodec)

/-- Public-part encryption bad-message predicate on `FsIdx` (`transmit` or `challenge` with
`!ok m.1`). -/
@[expose] def fsEncBadPubMsg {AD Pub M C : Type} (ok : Pub → Bool) :
    FsIdx AD (Pub × M) C → Bool :=
  fun q => encBadMsg (SS := Unit) (RS := Unit) (fun m : Pub × M => ok m.1) (.inr q)

private abbrev SingleAdSpec (Pt : Type) (ℓ : ℕ) :=
  unifSpec + fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32

private abbrev MultiAdSpec (Pt : Type) (ℓ : ℕ) :=
  unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)

/-- Session-tag query implementation inside `multiSessPubToAD`. -/
private def msTag (s : ℕ) : QueryImpl (SingleAdSpec Pt ℓ) (OracleComp (MultiAdSpec Pt ℓ))
  | .inl n => query (spec := MultiAdSpec Pt ℓ) (.inl n)
  | .inr q => query (spec := MultiAdSpec Pt ℓ) (.inr ⟨s, q⟩)

private theorem msTag_isQueryBoundP (s : ℕ)
    {Q₁ : (SingleAdSpec Pt ℓ).Domain → Prop}
    {Q₂ : (MultiAdSpec Pt ℓ).Domain → Prop}
    [DecidablePred Q₁] [DecidablePred Q₂]
    (hInl : ∀ n, Q₂ (.inl n) → Q₁ (.inl n))
    (hInr : ∀ q, Q₂ (.inr ⟨s, q⟩) → Q₁ (.inr q))
    {β : Type} (oa : OracleComp (SingleAdSpec Pt ℓ) β) {k : ℕ}
    (h : oa.IsQueryBoundP Q₁ k) :
    (simulateQ (msTag (Pt := Pt) (ℓ := ℓ) s) oa).IsQueryBoundP Q₂ k := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t _ => ?_) (fun t ht => ?_)
  · rcases t with n | q <;>
      exact (isQueryBoundP_query_iff Q₂ _ 1).2 fun _ => Nat.zero_lt_one
  · rcases t with n | q
    · exact (isQueryBoundP_query_iff Q₂ _ 0).2 fun hq => absurd (hInl n hq) ht
    · exact (isQueryBoundP_query_iff Q₂ _ 0).2 fun hq => absurd (hInr q hq) ht

private theorem guardedSafePost_msTag (s : ℕ) {β : Type} {P : β → Prop}
    {oa : OracleComp (SingleAdSpec Pt ℓ) β}
    (hoa : GuardedSafePost
      (fsRespShort (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)))
      (fsInjectLong (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ))
      P oa) :
    GuardedSafePost multiRespShort multiInjectLong P
      (simulateQ (msTag (Pt := Pt) (ℓ := ℓ) s) oa) := by
  induction hoa with
  | pure hp =>
    simp only [simulateQ_pure]
    exact GuardedSafePost.pure hp
  | @query_bind t k hQt _ ih =>
    rw [simulateQ_query_bind]
    rcases t with n | q
    · dsimp only [msTag]
      exact GuardedSafePost.query_bind (by simp [multiInjectLong]) fun u _ =>
        ih u trivial
    · dsimp only [msTag]
      exact GuardedSafePost.query_bind
        (by simpa [multiInjectLong] using hQt) fun u hu => ih u hu

/-- Single-session `pubRedImpl` step run at receiver-corrupted flag `b`. -/
private abbrev pubStep
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (b : Bool) :=
  (pubRedImpl
    (SS := RatchetSenderState (BitVec 256))
    (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
    (AD := Header Pt) (M := Plain ℓ)
    (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2) (.inr o)).run b

private theorem pubStep_le_one
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (b : Bool) :
    (pubStep codec o b).IsQueryBoundP (fun _ => True) 1 := by
  rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [StateT.run_bind, stateT_lift_run, corruptReceiverQuery, query_eq_liftM,
      bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr Nat.zero_lt_one, fun r => ?_⟩
    cases r <;> simp [StateT.run_set, map_eq_bind_pure_comp]
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp
    | some p =>
      rw [stateT_lift_run, deliverQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp [StateT.run_map, StateT.run_get]
    | some p =>
      rw [stateT_lift_run, injectQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩

private theorem pubStep_not_inj
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ho : ¬ fsInjQ o = true) (b : Bool) :
    (pubStep codec o b).IsQueryBoundP (fun q => onInr fsInjQ q = true) 0 := by
  rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [onInr, fsInjQ]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [onInr, fsInjQ]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [onInr, fsInjQ]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [StateT.run_bind, stateT_lift_run, corruptReceiverQuery, query_eq_liftM,
      bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [onInr, fsInjQ]), fun r => ?_⟩
    cases r <;> simp [StateT.run_set, map_eq_bind_pure_comp]
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp
    | some p =>
      rw [stateT_lift_run, deliverQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [onInr, fsInjQ]), fun _ => by simp⟩
  · exact False.elim (ho rfl)

private theorem pubStep_shortAD
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ho : ¬ fsEncBadPubMsg (fun p : LibsignalMsgPublicPart => p.shortB) o = true) (b : Bool) :
    (pubStep codec o b).IsQueryBoundP (fun q => onInr (fsEncBadAD shortOk) q = true) 0 := by
  rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun _ => by simp⟩
    simpa [onInr, fsEncBadAD, fsEncBadPubMsg, encBadAD, encBadMsg, shortOk] using ho
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun _ => by simp⟩
    simp only [fsEncBadPubMsg, encBadMsg, Bool.or_eq_true, not_or] at ho
    simpa [onInr, fsEncBadAD, encBadAD, shortOk] using ho.1
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [onInr, fsEncBadAD, encBadAD]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [StateT.run_bind, stateT_lift_run, corruptReceiverQuery, query_eq_liftM,
      bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [onInr, fsEncBadAD, encBadAD]), fun r => ?_⟩
    cases r <;> simp [StateT.run_set, map_eq_bind_pure_comp]
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp
    | some p =>
      rw [stateT_lift_run, deliverQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [onInr, fsEncBadAD, encBadAD]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp [StateT.run_map, StateT.run_get]
    | some p =>
      rw [stateT_lift_run, injectQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [onInr, fsEncBadAD, encBadAD]), fun _ => by simp⟩

private theorem pubStep_oneADClass (k₀ : ℕ)
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ho : ¬ fsOutsideClass (fun h : Header Pt => h.1) k₀ o = true) (b : Bool) :
    (pubStep codec o b).IsQueryBoundP
      (fun q => onInr (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) q = true) 0 := by
  rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun _ => by simp⟩
    simpa [onInr, fsOutsideClass, queryADOutsideClass] using ho
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun _ => by simp⟩
    simpa [onInr, fsOutsideClass, queryADOutsideClass] using ho
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [onInr, fsOutsideClass, queryADOutsideClass]), fun _ => by simp⟩
  · unfold pubStep pubRedImpl
    rw [StateT.run_bind, stateT_lift_run, corruptReceiverQuery, query_eq_liftM,
      bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [onInr, fsOutsideClass, queryADOutsideClass]), fun r => ?_⟩
    cases r <;> simp [StateT.run_set, map_eq_bind_pure_comp]
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp
    | some p =>
      rw [stateT_lift_run, deliverQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl ?_, fun _ => by simp⟩
      simpa [onInr, fsOutsideClass, queryADOutsideClass] using ho
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none => simp [StateT.run_map, StateT.run_get]
    | some p =>
      rw [stateT_lift_run, injectQuery, query_eq_liftM,
        bind_assoc, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl ?_, fun _ => by simp⟩
      simpa [onInr, fsOutsideClass, queryADOutsideClass] using ho

private theorem pubStep_guardedShort
    (o : FsIdx (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (ho : ¬ fsInjectLong (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (.inr o))
    (b : Bool) :
    GuardedSafePost
      (fsRespShort (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)))
      (fsInjectLong (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256)) (Msg := Plain ℓ))
      (fun r => fsRespShort (SS := RatchetSenderState (BitVec 256))
        (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (.inr o) r.1)
      (pubStep codec o b) := by
  rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, transmitQuery]
    exact (GuardedSafePost.query (by simp [fsInjectLong])).bind fun r hr =>
      GuardedSafePost.pure (by simpa [fsRespShort] using hr)
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, challengeQuery]
    exact (GuardedSafePost.query (by simp [fsInjectLong])).bind fun r hr =>
      GuardedSafePost.pure (by simpa [fsRespShort] using hr)
  · unfold pubStep pubRedImpl
    rw [stateT_lift_run, corruptSenderQuery]
    exact (GuardedSafePost.query (by simp [fsInjectLong])).bind fun _ _ =>
      GuardedSafePost.pure trivial
  · unfold pubStep pubRedImpl
    rw [StateT.run_bind, stateT_lift_run, corruptReceiverQuery, bind_assoc]
    refine (GuardedSafePost.query (by simp [fsInjectLong])).bind fun r _ => ?_
    cases r
    · simp only [pure_bind, Option.isSome, Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
      exact GuardedSafePost.pure trivial
    · simp only [pure_bind, Option.isSome, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure]
      exact GuardedSafePost.pure trivial
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec c.2 with
    | none =>
      simp only [StateT.run_pure]
      exact GuardedSafePost.pure trivial
    | some p =>
      rw [stateT_lift_run, deliverQuery, bind_assoc]
      exact (GuardedSafePost.query (by simp [fsInjectLong])).bind fun _ _ => by
        simp only [pure_bind]
        exact GuardedSafePost.pure trivial
  · unfold pubStep pubRedImpl
    dsimp only
    cases lPubOf codec e with
    | none =>
      exact GuardedSafePost.pure trivial
    | some p =>
      rw [stateT_lift_run, injectQuery, bind_assoc]
      have ho' : ¬ fsInjectLong (SS := RatchetSenderState (BitVec 256))
          (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
          (Msg := Plain ℓ) (.inr (.inr ((a, p), i, e))) := by
        simpa [fsInjectLong] using ho
      exact (GuardedSafePost.query ho').bind fun _ _ => by
        simp only [pure_bind]
        exact GuardedSafePost.pure trivial

/-- Per-session query bound `sessQueryAt s` is preserved by `multiSessPubToAD`. -/
theorem multiSessPubToAD_isQueryBoundP_sessQueryAt
    (AdvPub : MultiSessPubFsAdv Pt ℓ) (s q : ℕ)
    (hq : AdvPub.IsQueryBoundP (fun t => sessQueryAt s t = true) q) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => sessQueryAt s t = true) q := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hq (fun t hs st => ?_) (fun t hns st => ?_)
    (fun _ => false)
  · rcases t with n | ⟨s', o⟩
    · simp [sessQueryAt] at hs
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP s' (fun _ _ => trivial) (fun _ _ => trivial) _
          (pubStep_le_one codec o (st s')))
        fun _ => isQueryBoundP_pure _ _ 0
  · rcases t with n | ⟨s', o⟩
    · exact isQueryBoundP_query_bind_pure_zero' _ (by simp [sessQueryAt]) _
    · have hne : s' ≠ s := by simpa [sessQueryAt] using hns
      exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP (Q₁ := fun _ => False) s'
          (fun _ h => by simp [sessQueryAt] at h)
          (fun _ h => by simp [sessQueryAt, hne] at h) _
          (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false _ 0))
        fun _ => isQueryBoundP_pure _ _ 0

/-- `sessOffRange M` zero-query bound is preserved by `multiSessPubToAD`. -/
theorem multiSessPubToAD_offRange
    (AdvPub : MultiSessPubFsAdv Pt ℓ) (M : ℕ)
    (hoff : AdvPub.IsQueryBoundP (fun t => sessOffRange M t = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => sessOffRange M t = true) 0 := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hoff (fun t hp st => ?_) (fun t hnp st => ?_)
    (fun _ => false)
  · rcases t with n | ⟨s', o⟩
    · simp [sessOffRange] at hp
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP s' (fun _ _ => trivial) (fun _ _ => trivial) _
          (pubStep_le_one codec o (st s')))
        fun _ => isQueryBoundP_pure _ _ 0
  · rcases t with n | ⟨s', o⟩
    · exact isQueryBoundP_query_bind_pure_zero' _ (by simp [sessOffRange]) _
    · have hs' : ¬ M ≤ s' := by simpa [sessOffRange] using hnp
      exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP (Q₁ := fun _ => False) s'
          (fun _ h => by simp [sessOffRange] at h)
          (fun _ h => hs' (by simpa [sessOffRange] using h)) _
          (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false _ 0))
        fun _ => isQueryBoundP_pure _ _ 0

/-- `onAnySess fsInjQ` decryption-query bound is preserved by `multiSessPubToAD`. -/
theorem multiSessPubToAD_decBound
    (AdvPub : MultiSessPubFsAdv Pt ℓ) (qd : ℕ)
    (hdec : AdvPub.IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP (fun t => onAnySess fsInjQ t = true) qd := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hdec (fun t hp st => ?_) (fun t hnp st => ?_)
    (fun _ => false)
  · rcases t with n | ⟨s', o⟩
    · simp [onAnySess] at hp
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP s' (fun _ _ => trivial) (fun _ _ => trivial) _
          (pubStep_le_one codec o (st s')))
        fun _ => isQueryBoundP_pure _ _ 0
  · rcases t with n | ⟨s', o⟩
    · exact isQueryBoundP_query_bind_pure_zero' _ (by simp [onAnySess]) _
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP (Q₁ := fun q => onInr fsInjQ q = true) s'
          (fun _ h => by simp [onAnySess] at h)
          (fun q h => by simpa [onInr, onAnySess] using h) _
          (pubStep_not_inj codec o (by simpa [onAnySess] using hnp) (st s')))
        fun _ => isQueryBoundP_pure _ _ 0

/-- `multiSessPubToAD` maps `fsEncBadPubMsg (fun p => p.shortB)` zero-query bound to
`onAnySess (fsEncBadAD shortOk)` zero-query bound. -/
theorem multiSessPubToAD_shortAD
    (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (hsh : AdvPub.IsQueryBoundP
      (fun t => onAnySess (fsEncBadPubMsg (fun p : LibsignalMsgPublicPart => p.shortB)) t = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP
      (fun t => onAnySess (fsEncBadAD shortOk) t = true) 0 := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hsh (fun t hp st => ?_) (fun t hnp st => ?_)
    (fun _ => false)
  · rcases t with n | ⟨s', o⟩
    · simp [onAnySess] at hp
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP s' (fun _ _ => trivial) (fun _ _ => trivial) _
          (pubStep_le_one codec o (st s')))
        fun _ => isQueryBoundP_pure _ _ 0
  · rcases t with n | ⟨s', o⟩
    · exact isQueryBoundP_query_bind_pure_zero' _ (by simp [onAnySess]) _
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP (Q₁ := fun q => onInr (fsEncBadAD shortOk) q = true) s'
          (fun _ h => by simp [onAnySess] at h)
          (fun q h => by simpa [onInr, onAnySess] using h) _
          (pubStep_shortAD codec o (by simpa [onAnySess] using hnp) (st s')))
        fun _ => isQueryBoundP_pure _ _ 0

/-- `multiSessPubToAD` preserves per-session single-epoch AD class `h.1 = k₀`. -/
theorem multiSessPubToAD_oneADClass
    (AdvPub : MultiSessPubFsAdv Pt ℓ) (j k₀ : ℕ)
    (hcls : AdvPub.IsQueryBoundP
      (fun t => onSess (fsOutsideClass (fun h : Header Pt => h.1) k₀) j t = true) 0) :
    (multiSessPubToAD codec AdvPub).IsQueryBoundP
      (fun t => onSess (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) j t = true) 0 := by
  unfold multiSessPubToAD
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step hcls (fun t hp st => ?_) (fun t hnp st => ?_)
    (fun _ => false)
  · rcases t with n | ⟨s', o⟩
    · simp [onSess] at hp
    · exact isQueryBoundP_bind_zero_right
        (msTag_isQueryBoundP s' (fun _ _ => trivial) (fun _ _ => trivial) _
          (pubStep_le_one codec o (st s')))
        fun _ => isQueryBoundP_pure _ _ 0
  · rcases t with n | ⟨s', o⟩
    · exact isQueryBoundP_query_bind_pure_zero' _ (by simp [onSess]) _
    · by_cases hsj : s' = j
      · subst hsj
        have ho : ¬ fsOutsideClass (fun h : Header Pt => h.1) k₀ o = true := by
          simpa [onSess] using hnp
        exact isQueryBoundP_bind_zero_right
          (msTag_isQueryBoundP
            (Q₁ := fun q => onInr (fsOutsideClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) k₀) q = true)
            s'
            (fun _ h => by simp [onSess] at h)
            (fun q h => by simpa [onInr, onSess] using h) _
            (pubStep_oneADClass codec k₀ o ho (st s')))
          fun _ => isQueryBoundP_pure _ _ 0
      · exact isQueryBoundP_bind_zero_right
          (msTag_isQueryBoundP (Q₁ := fun _ => False) s'
            (fun _ h => by simp [onSess] at h)
            (fun _ h => by simp [onSess, hsj] at h) _
            (Computational.Proofs.GameHop.StateSim.isQueryBoundP_false _ 0))
          fun _ => isQueryBoundP_pure _ _ 0

/-- `GuardedMultiInjectShort` is preserved by `multiSessPubToAD`. -/
theorem multiSessPubToAD_guardedShort
    (AdvPub : MultiSessPubFsAdv Pt ℓ)
    (hg : GuardedMultiInjectShort AdvPub) :
    GuardedMultiInjectShort (multiSessPubToAD codec AdvPub) := by
  unfold multiSessPubToAD GuardedMultiInjectShort
  rw [StateT.run'_eq]
  refine GuardedSafePost.map (P := fun _ => True) Prod.fst ?_ (fun _ _ => trivial)
  refine GuardedSafePost.simulateQ_run (I := fun _ : ℕ → Bool => True) hg ?_ trivial
  intro t ht st _
  rcases t with n | ⟨s', o⟩
  · dsimp only
    rw [StateT.run_lift]
    exact (GuardedSafePost.query (by simp [multiInjectLong])).bind fun a ha =>
      GuardedSafePost.pure ⟨ha, trivial⟩
  · exact (guardedSafePost_msTag s'
      (pubStep_guardedShort codec o (by simpa [multiInjectLong] using ht) (st s'))).bind
      fun r hr => GuardedSafePost.pure ⟨by simpa [multiRespShort] using hr, trivial⟩

end PubToADQueries

end

end Computational.Proofs.E2E.SessionAuthPubToAD
