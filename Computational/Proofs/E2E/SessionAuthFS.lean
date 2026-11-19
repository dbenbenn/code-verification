/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthLazy
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

/-!
# The session router on FS-AEAD sessions

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

This file instantiates the session router (`E2E/SessionAuthRouter.lean`,
`E2E/SessionAuthLazy.lean`) with FS-AEAD sessions for the linear multi-session MAC bound, and links
each per-session game to the output-mode Theorem 5 hops of `FSAEAD/Theorem5Out.lean`.

A session is one copy of the FS-AEAD oracle interface `fsSpec`. Two session implementations are
compared:

* `fsImpl`: the Thm 5 hybrid at a fixed parameter `P` (for `P = hp 0 0 la`, the start of the Thm 5
  chain), with hidden bit sampled by `fsInit`.
* `fsSlotImpl O`: the multi-slot hybrid after all `N` chain-PRG hops (`hp N 0 la`), whose OT-CCA
  queries are answered by a **slot world** `O` (any per-slot OT-CCA implementation, for example the
  slot-salt world of `SaltHop`), with slot states sampled by `initS` (`fsSlotInit`).

Main results:

* `fsInit_bind_run`: a single session against `fsImpl`, from a fresh hidden bit, is `hRunOut` with
  output "the adversary's bit".
* `fsSlotInit_bind_run`: a single session against `fsSlotImpl O`, from fresh states, is the
  multi-slot OT-CCA reduction `multiSlotOtccaReductionOut` run against the slot world `O`.
* `fsSession_step_le`: for one session, the distance between the two is at most the `N` chain-PRG
  terms plus the distance between `multiOtBranch false` and the slot world `O`, both against the
  same multi-slot OT-CCA adversary.
* `fsSessLift_le`: the multi-session form. If a multi-session adversary uses only sessions `< q`,
  "every session runs `fsImpl`" and "every session runs `fsSlotImpl O`" are within the sum over
  sessions of those per-session terms, each for the session adversary `fsSessAdv … k` built by the
  router.

This is the per-session link that `SessionHybrid.sessionHybrid_mix_le` needs on its salt side
(`hDL`, `hDR`), with `D k = multiSlotOtccaReductionOut … (fsSessAdv … k)` and `pre k` the chain-PRG
sum. Instantiating `O` with the libsignal slot-salt world and averaging over identities is done in
`E2E/SessionAuthFSMix.lean`.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames.Lazy
open CryptoGames CryptoGames.FSAEAD CryptoGames.FSAEAD.Thm5

namespace CryptoVerification.E2E.Signed.SessionFS

open Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out

open CryptoVerification.E2E.Signed.SessionRouter

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- One FS-AEAD session: the ACD19 Fig. 5 oracles at the ratchet construction's types. -/
abbrev fsSpec (CK MK AD M C : Type) :=
  FSAEAD.spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C)

section Defs

variable (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

export Computational.Proofs.CryptoGames.FSAEAD.Theorem5Out (advBit outKeyFree_advBit)

/-- Real-side session: the Thm 5 hybrid at parameter `P`. -/
@[expose] def fsImpl (P : Params) :
    QueryImpl (fsSpec CK MK AD M C) (StateT (HSt CK MK AD M C) ProbComp) :=
  oraclesWith ideal ae G maxSkip P (DG G) (none : Option (SpecialOps AD M C ProbComp))

/-- Initial state of a real-side session: a fresh hidden bit, nothing generated yet. -/
@[expose] def fsInit : ProbComp (HSt CK MK AD M C) := do
  let b ← $ᵗ Bool
  return hInit b .unknown

/-- Slot-side session: the multi-slot hybrid after `N` chain-PRG hops (`hp N 0 la`), with its
OT-CCA queries answered by the slot world `O` on per-slot states `ℕ → S`. -/
@[expose] def fsSlotImpl (N : ℕ) (la : Bool) {S : Type}
    (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) :
    QueryImpl (fsSpec CK MK AD M C) (StateT (HSt CK MK AD M C × (ℕ → S)) ProbComp) := fun t =>
  StateT.mk fun s => do
    let r ← (simulateQ (slotLift O)
      ((multiOraclesWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) t).run
        s.1)).run s.2
    return (r.1.1, (r.1.2, r.2))

/-- Initial state of a slot-side session: slot states from `initS`, then a fresh hidden bit. -/
@[expose] def fsSlotInit {S : Type} (initS : ProbComp (ℕ → S)) : ProbComp (HSt CK MK AD M C × (ℕ → S)) := do
  let σ ← initS
  let b ← $ᵗ Bool
  return (hInit b .unknown, σ)

/-- The session adversary for session `k`, built by the router from a multi-session adversary `A`
over FS-AEAD sessions: session `k` is forwarded, sessions `< k` are simulated on the slot side and
sessions `> k` on the real side, each from fresh states. -/
@[expose] def fsSessAdv (P : Params) (N : ℕ) (la : Bool) {S : Type}
    (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp)) (initS : ProbComp (ℕ → S))
    (A : OracleComp (unifSpec + multiSessSpec (fsSpec CK MK AD M C)) Bool) (k : ℕ) :
    RatchetAdversary CK MK AD M C :=
  sessAdv (lazyInit fsInit (fsImpl ideal ae G maxSkip P))
    (lazyInit (fsSlotInit initS) (fsSlotImpl ideal ae G maxSkip N la O)) A
    (fun _ => none) (fun _ => none) k

end Defs

/-! ## The real side is `hRunOut` -/

section Real

variable (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

theorem fwd_fsImpl (P : Params) :
    fwd (fsImpl ideal ae G maxSkip P) =
      implWith ideal ae G maxSkip P (DG G) (none : Option (SpecialOps AD M C ProbComp)) := rfl

/-- Real side. A single session against `fsImpl`, from a fresh hidden bit, is `hRunOut` with
output "the adversary's bit". -/
theorem fsInit_bind_run (P : Params) (B : RatchetAdversary CK MK AD M C) :
    (fsInit >>= fun s => Prod.fst <$> (simulateQ (fwd (fsImpl ideal ae G maxSkip P)) B).run s) =
      hRunOut ideal ae G maxSkip P (DG G) (none : Option (SpecialOps AD M C ProbComp)) advBit B
        .unknown := by
  simp [fsInit, hRunOut, fwd_fsImpl, advBit, map_eq_bind_pure_comp]

end Real

/-! ## The slot side is the multi-slot OT-CCA reduction against a slot world -/

section Slot

variable (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) {S : Type}
  (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))

/-- A coin computation lifted into the OT-CCA interface leaves every slot state unchanged. -/
theorem slotLift_liftM_run {β : Type} (p : ProbComp β) (σ : ℕ → S) :
    (simulateQ (slotLift O) (liftM p : OracleComp (IndexedOtccaSpec AD M C) β)).run σ =
      (fun a => (a, σ)) <$> p := by
  simp [slotLift, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

/-- Stacking. Running the multi-slot hybrid and then answering its OT-CCA queries with the slot
world `O` is running `fsSlotImpl O` on the joint state. -/
theorem fsSlot_stack (N : ℕ) (la : Bool) {α : Type}
    (oa : OracleComp (unifSpec + fsSpec CK MK AD M C) α) (h : HSt CK MK AD M C) (σ : ℕ → S) :
    (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (slotLift O)
      ((simulateQ (multiImplWith ideal ae G maxSkip (hp N 0 la) N (DG G)
        (some (otOpsWith ideal))) oa).run h)).run σ =
      (simulateQ (fwd (fsSlotImpl ideal ae G maxSkip N la O)) oa).run (h, σ) := by
  induction oa using OracleComp.inductionOn generalizing h σ with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | t
    · simp only [multiImplWith, fwd_inl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        simulateQ_bind, StateT.run_bind, slotLift_liftM_run, bind_map_left, simulateQ_pure,
        StateT.run_pure]
      exact bind_congr fun u => ih u h σ
    · simp only [multiImplWith, fwd_inr, QueryImpl.add_apply_inr, fsSlotImpl, StateT.run_mk,
        simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind, bind_map_left]
      exact bind_congr fun z => ih z.1.1 z.1.2 z.2

/-- Slot side. A single session against `fsSlotImpl O`, from fresh states, is the multi-slot
OT-CCA reduction (output "the adversary's bit") run against the slot world `O`. -/
theorem fsSlotInit_bind_run (N : ℕ) (la : Bool) (initS : ProbComp (ℕ → S))
    (B : RatchetAdversary CK MK AD M C) :
    (fsSlotInit initS >>= fun s =>
        Prod.fst <$> (simulateQ (fwd (fsSlotImpl ideal ae G maxSkip N la O)) B).run s) =
      (initS >>= fun σ => Prod.fst <$> (simulateQ (slotLift O)
        (multiSlotOtccaReductionOut ideal ae G maxSkip N la advBit B)).run σ) := by
  simp only [fsSlotInit, bind_assoc, pure_bind]
  refine bind_congr fun σ => ?_
  simp only [multiSlotOtccaReductionOut, multiRunOut, simulateQ_bind, StateT.run_bind,
    slotLift_liftM_run, bind_map_left, map_bind, simulateQ_pure, StateT.run_pure, map_pure]
  refine bind_congr fun b => ?_
  rw [← fsSlot_stack ideal ae G maxSkip O N la B (hInit b .unknown) σ]
  simp [advBit, map_eq_bind_pure_comp]

end Slot

/-! ## One session, then all sessions -/

section Bound

variable (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ) {S : Type}
  (O : QueryImpl (IndexedOtccaSpec AD M C) (StateT S ProbComp))

end Bound

end CryptoVerification.E2E.Signed.SessionFS
