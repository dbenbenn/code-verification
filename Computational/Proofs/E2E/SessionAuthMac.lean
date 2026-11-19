/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthFSMix
public import Mathlib.Data.Nat.Pairing

/-!
# The MAC-hop endpoints: all sessions in the slot world as one keyed MAC adversary

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

In `SessionFSMix.sessionHybrid_fs_mix_le`, the salt-side session hybrid ends at the all-slot world:
every session runs `fsSlotImpl` over its own lazily initialised `SaltSlotSt` table
(`slotSaltImpl … false`). To apply the single global MAC hop (`SessionHybrid.mac_mix_keyed`) for
the linear multi-session MAC bound, that multi-session game must equal one OT-CCA adversary
attacking a keyed multi-slot oracle `slotLiftK sk …` with slot key `κ = ℕ × ℕ` (`(session, index)`),
and symmetrically on the post-MAC side (`slotSaltImplNF … false`).

## Why epoch re-tagging is needed, and why the boundary holds

`slotLiftK sk` selects a slot from the OT-CCA query's `(i, a) : ℕ × AD` alone, without seeing which
session issued the query:

* Merging two sessions into the same slot is unsound because each OT-CCA slot permits at most one
  encryption query.
* Packing `(session, i)` into the message index `i` via `Nat.pair` would change the wire ciphertext,
  because `lHeader` encodes `i - 1` into the 32-bit counter of `SignalHeader`.

Instead, for queries from session `s`, we re-tag the epoch `t` inside `Header Pt = ℕ × Option Pt`:
`retagEpoch s t = 2 * Nat.pair s (t / 2) + t % 2`, paired with `lSessionSlotKey (i, ((t, T), p)) =
((t / 2).unpair.1, i)`. This works across the entire MAC chain without touching `SaltHop.lean`:

1. **Primitive invariance.** The trusted libsignal AEAD reads `t` only through `Party.senderOf t`
   (`t % 2 == 1`) in `lIds`; `lHeader` reads only the ratchet key `h.2` and `i`. Because
   `retagEpoch s t` preserves `t % 2` and leaves `h.2`, `i`, and `p` untouched, `lAeadK.enc`,
   `lAeadK.dec`, `lIdeal`, and `p.shortB` are unchanged.
2. **Slot-oracle equivariance (`SlotRetagEquiv`).** `slotSaltImpl`, `slotSaltImplNF`, and
   `multiSaltFlagNF` inspect the AD's header only through `lIds`, `lHeader`, salt lookup (`p.salt`),
   and equality with the recorded challenge (`st.chal == some (a, e)`). Since `retagEpoch s` is
   injective for each fixed `s`, mapping the stored challenge AD by `lTagAD s` makes both
   `slotSaltImpl` and `slotSaltImplNF` commute with re-tagging.
3. **Strict oracle boundary.** Epoch arithmetic (successor, epoch gaps, `maxSkip`, and skipped-key
   bookkeeping) lives inside the FS-AEAD hybrid (`multiOraclesWith`), which runs on **un-tagged**
   state inside the reduction `sessSlotAdv`. Queries are re-tagged by `retagImpl` strictly on the
   way into `IndexedOtccaSpec`, and responses (`Option C`, `Option M`) carry no AD, so nothing
   needs un-tagging on the way back.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal
open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5
open CryptoGames.LibsignalSM.Proofs.SaltHopKeyed CryptoGames.LibsignalSM.Proofs.WireHop
open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

namespace CryptoVerification.E2E.Signed.SessionMac

open CryptoVerification.E2E.Signed.SessionRouter
open CryptoVerification.E2E.Signed.SessionFS
open CryptoVerification.E2E.Signed.SessionFSMix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Single-slot re-tagging and single-session stacking -/

section Retag

variable {AD M C S : Type}

/-- Re-tag the AD of every OT-CCA query by `f`, passing uniform coin queries through unchanged. -/
@[expose] def retagImpl (f : AD → AD) :
    QueryImpl (IndexedOtccaSpec AD M C) (OracleComp (IndexedOtccaSpec AD M C))
  | .inl n => liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inl n))
  | .inr (.inl (h, m)) =>
    liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inr (.inl ((h.1, f h.2), m))))
  | .inr (.inr (h, e)) =>
    liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inr (.inr ((h.1, f h.2), e))))

/-- Oracle equivariance under AD re-tagging. A single-slot oracle `O` commutes with `f : AD → AD`
along a slot-state map `mapS : S → S` if re-tagging the query AD and mapping the input state yields
the same response and mapped output state on both `encrypt` and `decrypt`. -/
structure SlotRetagEquiv (f : AD → AD) (mapS : S → S)
    (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) : Prop where
  enc : ∀ (i : ℕ) (a : AD) (m : M) (st : S),
    (O (.inr (.inl ((i, f a), m)))).run (mapS st) =
      (fun r => (r.1, mapS r.2)) <$> (O (.inr (.inl ((i, a), m)))).run st
  dec : ∀ (i : ℕ) (a : AD) (e : C) (st : S),
    (O (.inr (.inr ((i, f a), e)))).run (mapS st) =
      (fun r => (r.1, mapS r.2)) <$> (O (.inr (.inr ((i, a), e)))).run st

/-- Splice session `s`'s slot states `σ` (mapped by `mapS`) into a global `(session, index)` table
`τ : ℕ × ℕ → S`, leaving all other sessions unchanged. -/
@[expose] def putSession (s : ℕ) (mapS : S → S) (σ : ℕ → S) (τ : ℕ × ℕ → S) : ℕ × ℕ → S :=
  fun k => if k.1 = s then mapS (σ k.2) else τ k

@[simp] theorem putSession_self (s i : ℕ) (mapS : S → S) (σ : ℕ → S) (τ : ℕ × ℕ → S) :
    putSession s mapS σ τ (s, i) = mapS (σ i) := by
  simp [putSession]

theorem putSession_update (s i : ℕ) (mapS : S → S) (σ : ℕ → S) (τ : ℕ × ℕ → S) (x : S) :
    Function.update (putSession s mapS σ τ) (s, i) (mapS x) =
      putSession s mapS (Function.update σ i x) τ := by
  funext ⟨s', j⟩
  by_cases hs : s' = s
  · subst hs
    by_cases hj : j = i
    · subst hj; simp [putSession]
    · have hne : (s', j) ≠ (s', i) := fun h => hj (Prod.mk.inj h).2
      simp [putSession, hj, hne]
  · have hne : (s', j) ≠ (s, i) := fun h => hs (Prod.mk.inj h).1
    simp [putSession, hs, hne]

/-- Single-session re-tag stacking. If `O` is equivariant under `(f, mapS)` and `sk` maps every
re-tagged query `(i, f a)` to `(s, i)`, then running `oa` through `retagImpl f` against `slotLiftK sk O`
updates only session `s`'s slice of the global table and matches `slotLift O` on `σ`. -/
theorem retag_slotLift_eq (f : AD → AD) (mapS : S → S) (s : ℕ) (sk : ℕ × AD → ℕ × ℕ)
    (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (heq : SlotRetagEquiv f mapS O) (hsk : ∀ i a, sk (i, f a) = (s, i))
    {β : Type} (oa : OracleComp (IndexedOtccaSpec AD M C) β) (σ : ℕ → S) (τ : ℕ × ℕ → S) :
    (simulateQ (slotLiftK sk O) (simulateQ (retagImpl f) oa)).run (putSession s mapS σ τ) =
      (fun r => (r.1, putSession s mapS r.2 τ)) <$> (simulateQ (slotLift O) oa).run σ := by
  induction oa using OracleComp.inductionOn generalizing σ τ with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, e⟩
    · simp only [retagImpl, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, slotLiftK_inl, slotLift, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u σ τ
    · simp only [retagImpl, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, slotLiftK_inr, slotLiftOtccaK, slotLift, QueryImpl.add_apply_inr, slotLiftOtcca,
        StateT.run_mk, hsk, putSession_self, heq.enc, bind_map_left, bind_assoc, pure_bind,
        putSession_update]
      exact bind_congr fun z => ih z.1 (Function.update σ i z.2) τ
    · simp only [retagImpl, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, slotLiftK_inr, slotLiftOtccaK, slotLift, QueryImpl.add_apply_inr, slotLiftOtcca,
        StateT.run_mk, hsk, putSession_self, heq.dec, bind_map_left, bind_assoc, pure_bind,
        putSession_update]
      exact bind_congr fun z => ih z.1 (Function.update σ i z.2) τ

end Retag

/-! ## All sessions in the slot world equal one re-tagged OT-CCA adversary -/

section MultiSession

variable {CK MK AD M C S : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)

/-- A coin computation lifted into `IndexedOtccaSpec` leaves every keyed slot state unchanged. -/
theorem slotLiftK_liftM_run {κ : Type} [DecidableEq κ] (sk : ℕ × AD → κ)
    (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    {β : Type} (p : ProbComp β) (τ : κ → S) :
    (simulateQ (slotLiftK sk O) (liftM p : OracleComp (IndexedOtccaSpec AD M C) β)).run τ =
      (fun a => (a, τ)) <$> p := by
  simp [slotLiftK, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

/-- Query implementation of the multi-session slot reduction: keeps each session's un-tagged
FS-AEAD hybrid state lazily on `ℕ → Option HSt`, forwarding its OT-CCA queries to the external
`IndexedOtccaSpec` oracle after re-tagging session `s`'s ADs with `tag s`. -/
@[expose] def sessSlotRedImpl (tag : ℕ → AD → AD) :
    QueryImpl (unifSpec + multiSessSpec (fsSpec CK MK AD M C))
      (StateT (ℕ → Option (HSt CK MK AD M C)) (OracleComp (IndexedOtccaSpec AD M C)))
  | .inl n => StateT.lift (liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inl n)))
  | .inr ⟨s, t⟩ => StateT.mk fun st => do
      let h ← match st s with
        | some h => pure h
        | none => do
          let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (IndexedOtccaSpec AD M C) Bool)
          pure (hInit b .unknown)
      let r ← simulateQ (retagImpl (tag s))
        ((multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G)
          (some (otOpsWith ideal)) t).run h)
      return (r.1, Function.update st s (some r.2))

@[simp] theorem sessSlotRedImpl_inl (tag : ℕ → AD → AD) (n : ℕ) :
    sessSlotRedImpl ideal ae G maxSkip N la tag (.inl n) =
      StateT.lift (liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inl n))) := rfl

@[simp] theorem sessSlotRedImpl_inr (tag : ℕ → AD → AD)
    (q : (_ : ℕ) × (fsSpec CK MK AD M C).Domain) :
    sessSlotRedImpl ideal ae G maxSkip N la tag (.inr q) =
      StateT.mk fun st => do
        let h ← match st q.1 with
          | some h => pure h
          | none => do
            let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (IndexedOtccaSpec AD M C) Bool)
            pure (hInit b .unknown)
        let r ← simulateQ (retagImpl (tag q.1))
          ((multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G)
            (some (otOpsWith ideal)) q.2).run h)
        return (r.1, Function.update st q.1 (some r.2)) := rfl

theorem fsSlotInit_pure (s₀ : S) :
    fsSlotInit (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C) (pure fun _ => s₀) = do
      let b ← $ᵗ Bool
      return (hInit b .unknown, fun _ => s₀) := by
  simp [fsSlotInit]

/-- Multi-session slot adversary: runs the multi-session FS-AEAD adversary `Adv`, simulating
every session's post-PRG hybrid (`hp N 0 la`) internally on un-tagged state and re-tagging its
OT-CCA queries by session via `tag`. -/
@[expose] def sessSlotAdv (tag : ℕ → AD → AD) {β : Type}
    (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β) :
    OracleComp (IndexedOtccaSpec AD M C) β :=
  Prod.fst <$> (simulateQ (sessSlotRedImpl ideal ae G maxSkip N la tag) Adv).run (fun _ => none)

/-- Extract the per-session `Option HSt` table from the all-slot world's joint state. -/
@[expose] def packHSt (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) :
    ℕ → Option (HSt CK MK AD M C) :=
  fun s => (stL s).map Prod.fst

/-- Extract the global `(session, index)` slot-state table from the all-slot world's joint state,
mapping initialised sessions by `mapS` and sending uninitialised sessions to `s₀`. -/
@[expose] def packSlotSt (s₀ : S) (mapS : ℕ → S → S)
    (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) : ℕ × ℕ → S :=
  fun k => match stL k.1 with
    | none => s₀
    | some (_, σ) => mapS k.1 (σ k.2)

theorem packHSt_update (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) (s : ℕ)
    (h : HSt CK MK AD M C) (σ : ℕ → S) :
    Function.update (packHSt stL) s (some h) =
      packHSt (Function.update stL s (some (h, σ))) := by
  funext s'
  by_cases hs : s' = s <;> simp [packHSt, hs]

theorem packSlotSt_of_none (s₀ : S) (mapS : ℕ → S → S)
    (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) (s : ℕ)
    (hnone : stL s = none) (hinit : mapS s s₀ = s₀) :
    packSlotSt s₀ mapS stL =
      putSession s (mapS s) (fun _ => s₀) (packSlotSt s₀ mapS stL) := by
  funext ⟨s', i⟩
  by_cases hs : s' = s
  · subst hs; simp [packSlotSt, putSession, hnone, hinit]
  · simp [putSession, hs]

theorem packSlotSt_of_some (s₀ : S) (mapS : ℕ → S → S)
    (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) (s : ℕ)
    (h : HSt CK MK AD M C) (σ : ℕ → S) (hsome : stL s = some (h, σ)) :
    packSlotSt s₀ mapS stL =
      putSession s (mapS s) σ (packSlotSt s₀ mapS stL) := by
  funext ⟨s', i⟩
  by_cases hs : s' = s
  · subst hs; simp [packSlotSt, putSession, hsome]
  · simp [putSession, hs]

theorem putSession_packSlotSt (s₀ : S) (mapS : ℕ → S → S)
    (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) (s : ℕ)
    (h : HSt CK MK AD M C) (σ : ℕ → S) :
    putSession s (mapS s) σ (packSlotSt s₀ mapS stL) =
      packSlotSt s₀ mapS (Function.update stL s (some (h, σ))) := by
  funext ⟨s', i⟩
  by_cases hs : s' = s
  · subst hs; simp [packSlotSt, putSession]
  · simp [packSlotSt, putSession, hs]

/-- Multi-session stacking with AD re-tagging. Under per-session `SlotRetagEquiv`, slot-key
routing `sk (i, tag s a) = (s, i)`, and preservation of the empty slot state `mapS s s₀ = s₀`,
running `sessSlotRedImpl` inside `slotLiftK sk O` is state-for-state equivalent to the all-slot
world `sessLift (lazyInit … (fsSlotImpl … O))`. -/
theorem sessSlot_stack (tag : ℕ → AD → AD) (mapS : ℕ → S → S) (s₀ : S)
    (sk : ℕ × AD → ℕ × ℕ) (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (heq : ∀ s, SlotRetagEquiv (tag s) (mapS s) O)
    (hsk : ∀ s i a, sk (i, tag s a) = (s, i))
    (hinit : ∀ s, mapS s s₀ = s₀)
    {β : Type} (oa : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β)
    (stL : ℕ → Option (HSt CK MK AD M C × (ℕ → S))) :
    (simulateQ (slotLiftK sk O)
        ((simulateQ (sessSlotRedImpl ideal ae G maxSkip N la tag) oa).run (packHSt stL))).run
        (packSlotSt s₀ mapS stL) =
      (fun z => ((z.1, packHSt z.2), packSlotSt s₀ mapS z.2)) <$>
        (simulateQ (sessLift (lazyInit (fsSlotInit (pure fun _ => s₀))
          (fsSlotImpl ideal ae G maxSkip N la O))) oa).run stL := by
  induction oa using OracleComp.inductionOn generalizing stL with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases q with n | ⟨s, t⟩
    · simp only [sessSlotRedImpl_inl, StateT.run_lift, bind_pure_comp, simulateQ_map,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, slotLiftK_inl,
        sessLift_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, id_map, StateT.run_map,
        StateT.run_monadLift, monadLift_self, Functor.map_map, bind_map_left, bind_assoc,
        pure_bind]
      exact bind_congr fun u => ih u stL
    · simp only [sessSlotRedImpl_inr, sessLift_inr, sessLiftCore, StateT.run_mk, bind_map_left]
      cases hst : stL s with
      | none =>
        have hp : packHSt stL s = none := by simp [packHSt, hst]
        simp only [hp, lazyInit_run_none', StateT.run_mk, simulateQ_bind, StateT.run_bind,
          slotLiftK_liftM_run, bind_map_left, bind_assoc, pure_bind, simulateQ_pure,
          StateT.run_pure]
        conv_rhs => arg 1; rw [fsSlotInit_pure]
        simp only [bind_assoc]
        refine bind_congr fun b => ?_
        simp only [pure_bind, fsSlotImpl, StateT.run_mk, bind_assoc]
        conv_lhs =>
          arg 1; arg 2
          rw [packSlotSt_of_none s₀ mapS stL s hst (hinit s)]
        rw [retag_slotLift_eq (tag s) (mapS s) s sk O (heq s) (hsk s)]
        simp only [bind_map_left]
        refine bind_congr fun w => ?_
        rw [packHSt_update stL s w.1.2 w.2, putSession_packSlotSt s₀ mapS stL s w.1.2 w.2]
        exact ih w.1.1 (Function.update stL s (some (w.1.2, w.2)))
      | some hσ =>
        rcases hσ with ⟨h, σ⟩
        have hp : packHSt stL s = some h := by simp [packHSt, hst]
        simp only [hp, lazyInit_run_some', fsSlotImpl, StateT.run_mk, pure_bind, simulateQ_bind,
          StateT.run_bind, bind_assoc, bind_map_left, simulateQ_pure, StateT.run_pure]
        conv_lhs =>
          arg 1; arg 2
          rw [packSlotSt_of_some s₀ mapS stL s h σ hst]
        rw [retag_slotLift_eq (tag s) (mapS s) s sk O (heq s) (hsk s)]
        simp only [bind_map_left]
        refine bind_congr fun w => ?_
        rw [packHSt_update stL s w.1.2 w.2, putSession_packSlotSt s₀ mapS stL s w.1.2 w.2]
        exact ih w.1.1 (Function.update stL s (some (w.1.2, w.2)))

/-- All-slot world equals one keyed multi-session adversary (generic form). Starting every
session uninitialised on the left and every `(session, index)` slot at `s₀` on the right produces
the exact same output `ProbComp`. -/
theorem allSlot_eq_slotLiftK (tag : ℕ → AD → AD) (mapS : ℕ → S → S) (s₀ : S)
    (sk : ℕ × AD → ℕ × ℕ) (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))
    (heq : ∀ s, SlotRetagEquiv (tag s) (mapS s) O)
    (hsk : ∀ s i a, sk (i, tag s a) = (s, i))
    (hinit : ∀ s, mapS s s₀ = s₀)
    {β : Type} (Adv : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) β) :
    Prod.fst <$> (simulateQ (sessLift (lazyInit (fsSlotInit (pure fun _ => s₀))
        (fsSlotImpl ideal ae G maxSkip N la O))) Adv).run (fun _ => none) =
      Prod.fst <$> (simulateQ (slotLiftK sk O)
        (sessSlotAdv ideal ae G maxSkip N la tag Adv)).run (fun _ => s₀) := by
  have h := congrArg (fun p => (fun z => z.1.1) <$> p)
    (sessSlot_stack ideal ae G maxSkip N la tag mapS s₀ sk O heq hsk hinit Adv (fun _ => none))
  simp only [Functor.map_map] at h
  rw [← h, sessSlotAdv, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end MultiSession

/-! ## Epoch re-tagging and `SlotRetagEquiv` for libsignal (`slotSaltImpl`, `slotSaltImplNF`) -/

section EpochRetag

open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

/-- Pack `(session, epoch / 2)` into the upper bits of the epoch while preserving `epoch % 2`. -/
@[expose] def retagEpoch (s t : ℕ) : ℕ :=
  2 * Nat.pair s (t / 2) + t % 2

/-- Recover the session index from a re-tagged epoch. -/
@[expose] def epochSession (t : ℕ) : ℕ :=
  (t / 2).unpair.1

theorem retagEpoch_mod_two (s t : ℕ) : retagEpoch s t % 2 = t % 2 := by
  unfold retagEpoch; omega

theorem retagEpoch_div_two (s t : ℕ) : retagEpoch s t / 2 = Nat.pair s (t / 2) := by
  unfold retagEpoch; omega

@[simp] theorem epochSession_retagEpoch (s t : ℕ) : epochSession (retagEpoch s t) = s := by
  simp [epochSession, retagEpoch_div_two]

theorem retagEpoch_injective (s : ℕ) : Function.Injective (retagEpoch s) := by
  intro t₁ t₂ h
  have hm : t₁ % 2 = t₂ % 2 := by
    have := congrArg (· % 2) h
    simpa [retagEpoch_mod_two] using this
  have hd : t₁ / 2 = t₂ / 2 := by
    have := congrArg (· / 2) h
    simp only [retagEpoch_div_two, Nat.pair_eq_pair, true_and] at this
    exact this
  omega

/-- Re-tag the epoch of a libsignal FS-AEAD associated-data pair `((t, T), pub)` with session `s`. -/
@[expose] def lTagAD {Pt : Type} (s : ℕ) (a : Header Pt × LibsignalMsgPublicPart) :
    Header Pt × LibsignalMsgPublicPart :=
  ((retagEpoch s a.1.1, a.1.2), a.2)

/-- Slot selector `(session, index)` for a re-tagged OT-CCA query `(i, ((t, T), pub))`. -/
@[expose] def lSessionSlotKey {Pt : Type} (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) : ℕ × ℕ :=
  (epochSession a.2.1.1, a.1)

/-- Map the recorded challenge AD of a `SaltSlotSt` by `lTagAD s`, leaving the key table intact. -/
@[expose] def lMapSaltSlotSt {Pt : Type} (s : ℕ) (st : SaltSlotSt Pt) : SaltSlotSt Pt :=
  { chal := st.chal.map fun p => ((p.1.1, lTagAD s p.1.2), p.2)
    table := st.table }

theorem lTagAD_injective {Pt : Type} (s : ℕ) : Function.Injective (lTagAD (Pt := Pt) s) := by
  rintro ⟨⟨t₁, T₁⟩, p₁⟩ ⟨⟨t₂, T₂⟩, p₂⟩ h
  simp only [lTagAD, Prod.mk.injEq] at h
  rcases h with ⟨⟨ht, rfl⟩, rfl⟩
  rw [retagEpoch_injective s ht]

@[simp] theorem lSessionSlotKey_lTagAD {Pt : Type} (s i : ℕ)
    (a : Header Pt × LibsignalMsgPublicPart) :
    lSessionSlotKey (i, lTagAD s a) = (s, i) := by
  simp [lSessionSlotKey, lTagAD]

@[simp] theorem lMapSaltSlotSt_empty {Pt : Type} (s : ℕ) :
    lMapSaltSlotSt s ({} : SaltSlotSt Pt) = {} := rfl

theorem lIds_retagEpoch (idO : Party → IdentityKey) (s t : ℕ) :
    lIds idO (retagEpoch s t) = lIds idO t := by
  simp [lIds, Party.senderOf, retagEpoch_mod_two]

theorem lAeadK_enc_lTagAD {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idO : Party → IdentityKey) (mk : DerivedMessageKeys)
    (s i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (m : Plain ℓ) :
    (lAeadK C codec ℓ encT idO).enc mk ((i, (lTagAD s a).1), (lTagAD s a).2) m =
      (lAeadK C codec ℓ encT idO).enc mk ((i, a.1), a.2) m := by
  simp [lAeadK, lTagAD, lIds_retagEpoch, lHeader]

theorem lAeadK_dec_lTagAD {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idO : Party → IdentityKey) (mk : DerivedMessageKeys)
    (s i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (e : LibsignalCiphertextWithSalt32) :
    (lAeadK C codec ℓ encT idO).dec mk ((i, (lTagAD s a).1), (lTagAD s a).2) e =
      (lAeadK C codec ℓ encT idO).dec mk ((i, a.1), a.2) e := by
  dsimp only [lAeadK, lTagAD, lHeader]
  rw [lIds_retagEpoch]
  cases (lWire C codec ℓ).dec mk (lIds idO a.1.1) e.1 <;> rfl

theorem lMapSaltSlotSt_chal_isSome {Pt : Type} (s : ℕ) (st : SaltSlotSt Pt) :
    (lMapSaltSlotSt s st).chal.isSome = st.chal.isSome := by
  simp [lMapSaltSlotSt]

theorem lMapSaltSlotSt_chal_beq {Pt : Type} [DecidableEq Pt] (s i : ℕ)
    (a : Header Pt × LibsignalMsgPublicPart) (e : LibsignalCiphertextWithSalt32)
    (st : SaltSlotSt Pt) :
    ((lMapSaltSlotSt s st).chal == some ((i, lTagAD s a), e)) =
      (st.chal == some ((i, a), e)) := by
  rw [Bool.eq_iff_iff]
  rcases st with ⟨_ | ⟨⟨i₀, a₀⟩, e₀⟩, tbl⟩
  · simp [lMapSaltSlotSt]
  · simp [lMapSaltSlotSt, (lTagAD_injective s).eq_iff]

theorem isSlotChalSalt_lMapSaltSlotSt {Pt : Type} (s : ℕ) (st : SaltSlotSt Pt) (salt : Salt32) :
    isSlotChalSalt (lMapSaltSlotSt s st).chal salt = isSlotChalSalt st.chal salt := by
  rcases st with ⟨_ | ⟨⟨i₀, a₀⟩, e₀⟩, tbl⟩ <;> rfl

theorem slotKeyOf_lMapSaltSlotSt {Pt : Type} (s : ℕ) (salt : Salt32) (st : SaltSlotSt Pt) :
    (slotKeyOf salt).run (lMapSaltSlotSt s st) =
      (fun r => (r.1, lMapSaltSlotSt s r.2)) <$> (slotKeyOf salt).run st := by
  simp only [slotKeyOf, lMapSaltSlotSt, StateT.run_mk]
  cases st.table.lookup salt <;> simp [Functor.map_map]

/-- `slotSaltImpl` commutes with epoch re-tagging. -/
theorem slotRetagEquiv_slotSaltImpl {Pt : Type} [DecidableEq Pt] (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idO : Party → IdentityKey)
    (b : Bool) (s : ℕ) :
    SlotRetagEquiv (lTagAD s) (lMapSaltSlotSt s) (slotSaltImpl C codec ℓ encT idO b) where
  enc i a m st := by
    have hsalt : (lTagAD s a).2.salt = a.2.salt := rfl
    have hideal : lIdeal C codec ℓ encT (i, lTagAD s a) = lIdeal C codec ℓ encT (i, a) := rfl
    simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind,
      lMapSaltSlotSt_chal_isSome, map_bind]
    by_cases hc : st.chal.isSome = true
    · simp [hc]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hsalt,
        slotKeyOf_lMapSaltSlotSt, bind_map_left, map_bind]
      refine bind_congr fun r => ?_
      cases b
      · simp [lAeadK_enc_lTagAD, lMapSaltSlotSt, StateT.run_modify]
      · simp only [↓reduceIte, hideal, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure,
          lMapSaltSlotSt, Option.map_some]
        simp [StateT.lift, StateT.run]
  dec i a e st := by
    have hsalt : (lTagAD s a).2.salt = a.2.salt := rfl
    simp only [slotSaltImpl, hsalt]
    by_cases hs : e.2 ≠ a.2.salt
    · simp [hs]
    · simp only [hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
        lMapSaltSlotSt_chal_beq, map_bind]
      by_cases hch : (b || (st.chal == some ((i, a), e))) = true
      · simp [hch]
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, lAeadK_dec_lTagAD,
          slotKeyOf_lMapSaltSlotSt, bind_map_left, map_bind, StateT.run_pure, map_pure]

/-- `slotSaltImplNF` commutes with epoch re-tagging. -/
theorem slotRetagEquiv_slotSaltImplNF {Pt : Type} [DecidableEq Pt] (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idO : Party → IdentityKey)
    (b : Bool) (s : ℕ) :
    SlotRetagEquiv (lTagAD s) (lMapSaltSlotSt s) (slotSaltImplNF C codec ℓ encT idO b) where
  enc i a m st := (slotRetagEquiv_slotSaltImpl C codec ℓ encT idO b s).enc i a m st
  dec i a e st := by
    have hsalt : (lTagAD s a).2.salt = a.2.salt := rfl
    simp only [slotSaltImplNF, hsalt]
    by_cases hs : e.2 ≠ a.2.salt
    · simp [hs]
    · simp only [hs, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
        isSlotChalSalt_lMapSaltSlotSt, lMapSaltSlotSt_chal_beq, map_bind]
      by_cases hch :
          (b || !isSlotChalSalt st.chal a.2.salt || (st.chal == some ((i, a), e))) = true
      · simp [hch]
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, lAeadK_dec_lTagAD,
          slotKeyOf_lMapSaltSlotSt, bind_map_left, map_bind, StateT.run_pure, map_pure]

end EpochRetag

/-! ## Libsignal multi-session MAC-hop endpoints and hybrid specialization -/

section Libsignal

open CryptoGames.LibsignalSM.Proofs CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoGames.LibsignalSession CryptoGames.LibsignalSM.Proofs.SaltHop
open CryptoGames.LibsignalSM.Proofs.WireHop CryptoVerification.E2E.Signed.FSMix
open CryptoVerification.E2E.Signed.SessionHybrid CryptoVerification.E2E.Signed.SessionFSMix
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD

variable {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
  (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (oa : ProbComp α)
  (idOf : α → Party → IdentityKey) (maxSkip N : ℕ) (la : Bool)
  (Adv : α → OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) Bool)

/-- The single keyed multi-session MAC adversary for draw `o : α`: runs every session of `Adv o`
in `hp N 0 la` on un-tagged state and re-tags OT-CCA queries by session via `lTagAD`. -/
abbrev lMacAdv (o : α) :
    OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32 :=
  sessSlotAdv (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F)
    maxSkip N la lTagAD (Adv o)

/-- Pre-MAC (`slotSaltImpl`) all-slot world equals `slotLiftK lSessionSlotKey` against
`sessSlotAdv`. -/
theorem lAllSlot_slotSaltImpl_eq (idO : Party → IdentityKey) (b : Bool) {β : Type}
    (Adv₀ : OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) β) :
    Prod.fst <$> (simulateQ (sessLift (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
        (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
          maxSkip N la (slotSaltImpl C codec ℓ encT idO b)))) Adv₀).run (fun _ => none) =
      Prod.fst <$> (simulateQ (slotLiftK lSessionSlotKey (slotSaltImpl C codec ℓ encT idO b))
        (sessSlotAdv (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
          maxSkip N la lTagAD Adv₀)).run (fun _ => {}) :=
  allSlot_eq_slotLiftK (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
    maxSkip N la lTagAD lMapSaltSlotSt {} lSessionSlotKey (slotSaltImpl C codec ℓ encT idO b)
    (slotRetagEquiv_slotSaltImpl C codec ℓ encT idO b)
    (fun s i a => lSessionSlotKey_lTagAD s i a)
    lMapSaltSlotSt_empty Adv₀

/-- Post-MAC (`slotSaltImplNF`) all-slot world equals `slotLiftK lSessionSlotKey` against
`sessSlotAdv`. -/
theorem lAllSlot_slotSaltImplNF_eq (idO : Party → IdentityKey) (b : Bool) {β : Type}
    (Adv₀ : OracleComp (unifSpec + multiSessSpec (fsSpec (BitVec 256) (BitVec 256)
      (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)) β) :
    Prod.fst <$> (simulateQ (sessLift (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
        (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
          maxSkip N la (slotSaltImplNF C codec ℓ encT idO b)))) Adv₀).run (fun _ => none) =
      Prod.fst <$> (simulateQ (slotLiftK lSessionSlotKey (slotSaltImplNF C codec ℓ encT idO b))
        (sessSlotAdv (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
          maxSkip N la lTagAD Adv₀)).run (fun _ => {}) :=
  allSlot_eq_slotLiftK (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F)
    maxSkip N la lTagAD lMapSaltSlotSt {} lSessionSlotKey (slotSaltImplNF C codec ℓ encT idO b)
    (slotRetagEquiv_slotSaltImplNF C codec ℓ encT idO b)
    (fun s i a => lSessionSlotKey_lTagAD s i a)
    lMapSaltSlotSt_empty Adv₀

/-- Mixture form of `lAllSlot_slotSaltImpl_eq` (discharges `hAL` in `sessionHybrid_fs_mix_le` at
`b = false`). -/
theorem lAllSlot_slotSaltImpl_mix_eq (b : Bool) :
    (oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
          (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F)
            maxSkip N la (slotSaltImpl C codec ℓ encT (idOf o) b)))) (Adv o)).run
          (fun _ => none)) =
      (oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK lSessionSlotKey
        (slotSaltImpl C codec ℓ encT (idOf o) b))
        (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o)).run (fun _ => {})) :=
  bind_congr fun o => lAllSlot_slotSaltImpl_eq C codec ℓ encT maxSkip N la (idOf o) b (Adv o)

/-- Mixture form of `lAllSlot_slotSaltImplNF_eq`. -/
theorem lAllSlot_slotSaltImplNF_mix_eq (b : Bool) :
    (oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
          (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F)
            maxSkip N la (slotSaltImplNF C codec ℓ encT (idOf o) b)))) (Adv o)).run
          (fun _ => none)) =
      (oa >>= fun o => Prod.fst <$> (simulateQ (slotLiftK lSessionSlotKey
        (slotSaltImplNF C codec ℓ encT (idOf o) b))
        (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o)).run (fun _ => {})) :=
  bind_congr fun o => lAllSlot_slotSaltImplNF_eq C codec ℓ encT maxSkip N la (idOf o) b (Adv o)

/-- The libsignal FS-AEAD session hybrid with salt side and MAC-hop endpoints discharged.
Specialises `sessionHybrid_fs_mix_le` to `κ = ℕ × ℕ`, `sk = fun _ => lSessionSlotKey`, and
`A = lMacAdv`: `hAL` is discharged automatically, and `hAR` compares `Hw 0` directly against the
`slotSaltImplNF` all-slot mixture. -/
theorem sessionHybrid_fs_mac_mix_le (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (q : ℕ) (Hw : ℕ → ProbComp Bool)
    (hoffAdv : ∀ o, (Adv o).IsQueryBoundP (fun t => sessOffRange q t = true) 0)
    {qd : ℕ}
    (hqdA : ∀ o, MakesAtMostDecQueries (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o) qd)
    (hshortA : ∀ o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o))
    (hdecA : ∀ o, GuardedOTDecShort (lMacAdv C codec ℓ encT idOf maxSkip N la Adv o))
    (hAR : 𝒟[Hw 0] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit (fsSlotInit (pure fun _ => ({} : SaltSlotSt Pt)))
          (fsSlotImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F)
            maxSkip N la (slotSaltImplNF C codec ℓ encT (idOf o) false)))) (Adv o)).run
          (fun _ => none)])
    -- wire side
    (Nw : ℕ → ℕ) (hNw : ∀ j, Nw j ≤ 2 ^ 32)
    (E : ℕ → α → OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ)
      LibsignalCiphertextWithSalt32)
    (hoffE : ∀ j o, (E j o).IsQueryBoundP (fun t => multiOffRange (Nw j) t = true) 0)
    (hclsE : ∀ j o, AEADScheme.OTAllQueriesInOneADClass lCls (E j o))
    (hshortE : ∀ j o, AEADScheme.OTEncADsOk
      (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) (E j o))
    (post : ℕ → ℝ≥0∞)
    (hEL : ∀ j < q, 𝒟[Hw j] = 𝒟[oa >>= fun o => Prod.fst <$> (simulateQ
      (slotLift (slotSaltImplNF C codec ℓ encT (idOf o) false)) (E j o)).run (fun _ => {})])
    (hER : ∀ j < q, 𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT (idOf o)) true (Nw j) (E j o)].boolDist 𝒟[Hw (j + 1)] ≤ post j) :
    𝒟[oa >>= fun o => Prod.fst <$> (simulateQ (sessLift
        (lazyInit fsInit (fsImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          (lChainPRG C.F) maxSkip (hp 0 0 la)))) (Adv o)).run (fun _ => none)].boolDist
        𝒟[Hw q] ≤
      (∑ j ∈ Finset.range q,
        (lSaltPre C codec ℓ encT oa idOf maxSkip N la Adv j +
          ∑ k ∈ Finset.range N, 2 * (lSaltPRF32 C.F).prfAdvantage
            (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
              (slotSaltRed C codec ℓ encT (idOf o) N k
                (lSaltD C codec ℓ encT idOf maxSkip N la Adv j o))))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F +
      ∑ j ∈ Finset.range q,
        ((∑ k ∈ Finset.range (Nw j), (lWire C codec ℓ).wireOtccaAdvantage
          (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
            (slotWireRed C codec ℓ encT (idOf o) k (E j o)))) + post j) :=
  sessionHybrid_fs_mix_le C codec ℓ encT oa idOf maxSkip N la Adv hrt hfit hℓ hinj hdum q Hw
    hoffAdv (fun _ => lSessionSlotKey) (lMacAdv C codec ℓ encT idOf maxSkip N la Adv)
    hqdA hshortA hdecA
    (congrArg evalDist (lAllSlot_slotSaltImpl_mix_eq C codec ℓ encT oa idOf maxSkip N la Adv false))
    (hAR.trans (congrArg evalDist
      (lAllSlot_slotSaltImplNF_mix_eq C codec ℓ encT oa idOf maxSkip N la Adv false)))
    Nw hNw E hoffE hclsE hshortE post hEL hER

end Libsignal

end CryptoVerification.E2E.Signed.SessionMac
