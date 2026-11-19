/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SessionAuthRouter
public import Computational.Proofs.CryptoGames.FSAEAD.Lazy -- proof-setup: allow-public-import

/-!
# Session router with randomly initialised sessions

**Checked by Lean. Not trusted.** No theorem of `Computational/Theorems/` unfolds a definition of
this file, and Lean's kernel checks every proof in it.

The router of `E2E/SessionAuthRouter.lean` starts every session from a fixed state `s k`. A real
per-session game samples its initial state instead (the FS-AEAD game samples its hidden bit; a slot
world samples its keys). This file adds that sampling for the multi-session linear MAC bound.

* `lazyInit init impl` runs `impl` on state `Option σ`. On the first query it samples the initial
  state from `init`; later queries reuse the stored state.
* `lazyInit_run_some`: once initialised, `lazyInit init impl` is `impl`.
* `lazyInit_run_none`: started uninitialised, `lazyInit init impl` has the same output distribution
  as "sample `s ← init`, then run `impl` from `s`". Only the output is compared (`CryptoGames.Lazy.DEq`),
  because sampling early or late changes the order of the random choices, not their distribution.
* `sessLift_lazy_boolDist_le`: the session hybrid of `sessLift_boolDist_le` where every session
  samples its own initial state, with each summand a single-session game that samples its initial
  state up front.-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal CryptoGames.Lazy

namespace CryptoVerification.E2E.Signed.SessionRouter

variable {ι : Type} {spec : OracleSpec ι}

/-! ## Lazily initialised state -/

section Lazy

variable {σ : Type}

/-- Lazily initialised implementation. On state `none`, sample the initial state from `init`,
then answer with `impl`; on state `some s`, answer with `impl` from `s`. -/
@[expose] def lazyInit (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (Option σ) ProbComp) := fun t =>
  StateT.mk fun os => do
    let s ← match os with
      | some s => pure s
      | none => init
    let r ← (impl t).run s
    return (r.1, some r.2)

@[simp] theorem lazyInit_run_some' (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (t : ι) (s : σ) :
    (lazyInit init impl t).run (some s) = (fun r => (r.1, some r.2)) <$> (impl t).run s := by
  simp [lazyInit, StateT.run_mk]

@[simp] theorem lazyInit_run_none' (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (t : ι) :
    (lazyInit init impl t).run none = do
      let s ← init
      let r ← (impl t).run s
      return (r.1, some r.2) := by
  simp [lazyInit, StateT.run_mk]

/-- Once initialised, `lazyInit init impl` is `impl`. -/
theorem lazyInit_run_some (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp (unifSpec + spec) α) (s : σ) :
    (simulateQ (fwd (lazyInit init impl)) oa).run (some s) =
      (fun z => (z.1, some z.2)) <$> (simulateQ (fwd impl) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | t
    · simp only [fwd_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u s
    · simp only [fwd_inr, lazyInit_run_some', bind_map_left]
      exact bind_congr fun z => ih z.1 z.2

/-- Started uninitialised, `lazyInit init impl` is "sample, then run `impl`", up to the order of
the random choices. -/
theorem lazyInit_run_none (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp (unifSpec + spec) α) :
    DEq (Prod.fst <$> (simulateQ (fwd (lazyInit init impl)) oa).run none)
      (init >>= fun s => Prod.fst <$> (simulateQ (fwd impl) oa).run s) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (DEq.bind_const init (pure a)).symm
  | query_bind t r ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with n | t
    · -- a coin: sample it before or after the initial state
      simp only [fwd_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
      refine (DEq.bind_right _ fun u => ih u).trans ?_
      exact DEq.swap _ init _
    · -- a session query: the first one samples the initial state
      simp only [fwd_inr, lazyInit_run_none', bind_assoc, pure_bind, lazyInit_run_some,
        Functor.map_map]
      rfl

end Lazy

/-! ## The session hybrid with randomly initialised sessions -/

section Telescope

variable {σL σR : Type}

/-- Session hybrid with randomly initialised sessions. Every session of the multi-session game
samples its own initial state on first use (from `initL` on the left, `initR` on the right). If the
multi-session adversary `M` only uses sessions `< q`, the two multi-session games are within the
sum, over `k < q`, of the distance between the single-session adversaries `sessAdv … k` against a
fresh `implL` game (state sampled from `initL`) and a fresh `implR` game (state sampled from
`initR`). -/
theorem sessLift_lazy_boolDist_le (initL : ProbComp σL) (implL : QueryImpl spec (StateT σL ProbComp))
    (initR : ProbComp σR) (implR : QueryImpl spec (StateT σR ProbComp)) (q : ℕ)
    (M : OracleComp (unifSpec + multiSessSpec spec) Bool)
    (hoff : M.IsQueryBoundP (fun t => sessOffRange q t = true) 0) :
    𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit initL implL)) M).run (fun _ => none)].boolDist
        𝒟[Prod.fst <$> (simulateQ (sessLift (lazyInit initR implR)) M).run (fun _ => none)] ≤
      ∑ k ∈ Finset.range q,
        𝒟[initL >>= fun s => Prod.fst <$> (simulateQ (fwd implL)
            (sessAdv (lazyInit initL implL) (lazyInit initR implR) M
              (fun _ => none) (fun _ => none) k)).run s].boolDist
          𝒟[initR >>= fun s => Prod.fst <$> (simulateQ (fwd implR)
            (sessAdv (lazyInit initL implL) (lazyInit initR implR) M
              (fun _ => none) (fun _ => none) k)).run s] := by
  refine (sessLift_boolDist_le (lazyInit initL implL) (lazyInit initR implR) q M hoff
    (fun _ => none) (fun _ => none)).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [(lazyInit_run_none initL implL _).evalDist_eq, (lazyInit_run_none initR implR _).evalDist_eq]

end Telescope

end CryptoVerification.E2E.Signed.SessionRouter
