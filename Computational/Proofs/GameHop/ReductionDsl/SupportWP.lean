/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.StateSim -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.Core
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Support-Invariant Rules and Potential-Based Query Bounds for `ReductionDsl`

Propagates unary `AllSupport` invariants across `ReductionDsl` evaluators and runners, and tracks
state-potential query bounds (`PotOK`) across `handlerImpl` simulations.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.GameHop.ReductionDsl.SupportWP

open OracleSpec OracleComp
open Computational.Proofs.GameHop.StateSim (AllSupport)
open _root_.ReductionDsl (Sig Ty Env Ops Iface Expr Comp GameCodec Mid TwoStageCostedReduction
  iterM findML anyML mapML consumeFirstML foldML handlerImpl runFuel)

section LoopSupport

variable {ι : Type} {T : OracleSpec.{0, 0} ι}

end LoopSupport

section CompSupport

variable {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι} {O : Ops S} {I : Iface S T}

end CompSupport

section PotOK

variable {S : Sig} {ι : Type} {T : OracleSpec.{0, 0} ι} {O : Ops S} {I : Iface S T}

/-- Continuation-passing potential bound requiring `oa >>= k` to satisfy `IsQueryBoundP P n`
whenever each continuation `k a` has query bound `B a`. -/
@[expose] def PotOK {α : Type} (P : ι → Prop) [DecidablePred P]
    (B : α → ℕ) (oa : OracleComp T α) (n : ℕ) : Prop :=
  ∀ {β : Type} (k : α → OracleComp T β),
    (∀ a, (k a).IsQueryBoundP P (B a)) → (oa >>= k).IsQueryBoundP P n

theorem PotOK.pure' {α : Type} {P : ι → Prop} [DecidablePred P]
    {B : α → ℕ} {a : α} {n : ℕ} (h : B a ≤ n) :
    PotOK P B (pure a : OracleComp T α) n := by
  intro β k hk
  simpa using (hk a).mono h

theorem PotOK.bind' {α γ : Type} {P : ι → Prop} [DecidablePred P]
    {B : γ → ℕ} {oa : OracleComp T α} {f : α → OracleComp T γ} {m n r : ℕ}
    (hoa : oa.IsQueryBoundP P m)
    (hf : ∀ a, PotOK P B (f a) r) (hmn : m + r ≤ n) :
    PotOK P B (oa >>= f) n := by
  intro β k hk
  rw [bind_assoc]
  exact (isQueryBoundP_bind hoa (fun a _ => hf a k hk)).mono hmn

theorem PotOK.bindPot {α γ : Type} {P : ι → Prop} [DecidablePred P]
    {B₁ : α → ℕ} {B₂ : γ → ℕ} {oa : OracleComp T α}
    {f : α → OracleComp T γ} {n : ℕ}
    (hoa : PotOK P B₁ oa n) (hf : ∀ a, PotOK P B₂ (f a) (B₁ a)) :
    PotOK P B₂ (oa >>= f) n := by
  intro β k hk
  rw [bind_assoc]
  exact hoa (fun a => f a >>= k) (fun a => hf a k hk)

theorem PotOK.toQueryBound {α : Type} {P : ι → Prop} [DecidablePred P]
    {B : α → ℕ} {oa : OracleComp T α} {n : ℕ}
    (h : PotOK P B oa n) (hB : ∀ a, B a = 0) :
    oa.IsQueryBoundP P n := by
  have := h (fun a => (pure a : OracleComp T α))
    (fun a => by rw [hB a]; exact isQueryBoundP_pure P a 0)
  simpa using this

theorem potC_bind {P : ι → Prop} [DecidablePred P]
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {Γ : List (Ty S)} {τ₁ τ₂ : Ty S} {B : τ₂.denote → ℕ}
    (m : Comp O I Γ τ₁) (k : Comp O I (τ₁ :: Γ) τ₂) (env : Env Γ) {r n : ℕ}
    (hk : ∀ x, PotOK P B (k.eval (.cons x env)) r)
    (hmn : m.queries w ws + r ≤ n) :
    PotOK P B ((Comp.bind m k).eval env) n := by
  simp only [Comp.eval]
  exact PotOK.bind' (Comp.queryBound_eval P w ws hw hU m env) hk hmn

theorem potC_caseSum {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ₁ τ₂ τ : Ty S} {B : τ.denote → ℕ}
    (s : Expr O Γ (.sum τ₁ τ₂))
    (kl : Comp O I (τ₁ :: Γ) τ) (kr : Comp O I (τ₂ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hl : ∀ a, s.eval env = .inl a → PotOK P B (kl.eval (.cons a env)) n)
    (hr : ∀ b, s.eval env = .inr b → PotOK P B (kr.eval (.cons b env)) n) :
    PotOK P B ((Comp.caseSum s kl kr).eval env) n := by
  simp only [Comp.eval]
  split
  · next a h => exact hl a h
  · next b h => exact hr b h

theorem potC_caseOpt {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ₁ τ : Ty S} {B : τ.denote → ℕ}
    (o : Expr O Γ (.opt τ₁))
    (kn : Comp O I Γ τ) (ks : Comp O I (τ₁ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hn : o.eval env = none → PotOK P B (kn.eval env) n)
    (hs : ∀ a, o.eval env = some a → PotOK P B (ks.eval (.cons a env)) n) :
    PotOK P B ((Comp.caseOpt o kn ks).eval env) n := by
  simp only [Comp.eval]
  split
  · next h => exact hn h
  · next a h => exact hs a h

theorem potC_ite {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ : Ty S} {B : τ.denote → ℕ}
    (c : Expr O Γ .bool) (t e : Comp O I Γ τ) (env : Env Γ) {n : ℕ}
    (ht : c.eval env = true → PotOK P B (t.eval env) n)
    (he : c.eval env = false → PotOK P B (e.eval env) n) :
    PotOK P B ((Comp.ite c t e).eval env) n := by
  simp only [Comp.eval]
  cases h : c.eval env
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact he h
  · simp only [↓reduceIte]; exact ht h

theorem potC_ret {P : ι → Prop} [DecidablePred P]
    {Γ : List (Ty S)} {τ : Ty S} {B : τ.denote → ℕ}
    (e : Expr O Γ τ) (env : Env Γ) {n : ℕ} (h : B (e.eval env) ≤ n) :
    PotOK P B ((Comp.ret e : Comp O I Γ τ).eval env) n := by
  simp only [Comp.eval]
  exact PotOK.pure' h

/-- Potential-based query bound for `simulateQ (handlerImpl h)`: if every step respects the state
potential `B`, the whole simulation respects `B`. -/
theorem potOK_simulateQ_handlerImpl {κ : Type} {G : OracleSpec.{0, 0} κ}
    {C : GameCodec S G} {σ : Ty S} {α : Type}
    {P : ι → Prop} [DecidablePred P]
    (B : σ.denote → ℕ)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hStep : ∀ q s, PotOK P (fun x : C.R.denote × σ.denote => B x.2)
      (h.eval (.cons s (.cons q .nil))) (B s))
    (mx : OracleComp (unifSpec + G) α) (st : σ.denote) :
    PotOK P (fun x : α × σ.denote => B x.2)
      ((simulateQ (handlerImpl (C := C) h) mx).run st) (B st) := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact PotOK.pure' le_rfl
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change PotOK P _
        ((do let u ← I.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (B st)
      rw [bind_assoc]
      refine PotOK.bind' (m := 0) (r := B st) (hU uq) (fun u => ?_) (by omega)
      rw [pure_bind]
      exact ih u st
    · change PotOK P _
        ((do
            let p ← h.eval (.cons st (.cons (C.qenc gq) .nil))
            return (C.rdec gq p.1, p.2)) >>=
          fun x => (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2)
        (B st)
      rw [bind_assoc]
      refine PotOK.bindPot (hStep (C.qenc gq) st) (fun p => ?_)
      rw [pure_bind]
      exact ih (C.rdec gq p.1) p.2

end PotOK

end Computational.Proofs.GameHop.ReductionDsl.SupportWP
