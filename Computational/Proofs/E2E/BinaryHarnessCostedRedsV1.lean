/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
import Computational.Proofs.GameHop.StateSim
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SM.GameCosted

/-!
# Query-bound transfer for the binary-harness adapter

Proves `IsQueryBoundP` preservation across `cliGameAdversaryReassoc`, `L_bh.eval`, `runFuel`,
`bhShallowRunFuel`, and two-stage `run1`/`eval1` continuations.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal
open OracleComp OracleSpec

namespace CryptoVerification.E2E

open ReductionDsl CryptoVerification.E2E.Costed
open CryptoVerification.SignalSession (stdinCapBytes)
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim

section QueryBounds

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC Pt : Type}

@[expose] def bhClassifyComposed (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (cliGameSpec S ℓ PQC).Domain → Bool
  | .inl (.inl (.inl _)) => false
  | .inl (.inl (.inr kq)) => pKi kq
  | .inl (.inr cq) => pCtl cq
  | .inr ⟨i, _⟩ => pInst i

@[expose] def bhClassifyGameOnly (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (bhGameSpec S ℓ PQC).Domain → Bool
  | .inl (.inl kq) => pKi kq
  | .inl (.inr cq) => pCtl cq
  | .inr ⟨i, _⟩ => pInst i

abbrev bhClassifyGame (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (unifSpec + bhGameSpec S ℓ PQC).Domain → Bool :=
  fun x => match x with
    | .inl _ => false
    | .inr t => bhClassifyGameOnly pKi pCtl pInst t

@[expose] def bhClassifyTargetOnly (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (bhTargetGameSpec S ℓ PQC).Domain → Bool
  | .inl (.inl kq) => pKi kq
  | .inl (.inr cq) => pCtl cq
  | .inr ⟨i, _⟩ => pInst i

abbrev bhClassifyTarget (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool) :
    (unifSpec + bhTargetGameSpec S ℓ PQC).Domain → Bool :=
  fun x => match x with
    | .inl _ => false
    | .inr t => bhClassifyTargetOnly pKi pCtl pInst t

@[expose] def bhAdvToGameImpl (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :
    QueryImpl (cliGameSpec S ℓ PQC) (OracleComp (unifSpec + bhGameSpec S ℓ PQC)) :=
  fun q => match q with
    | .inl (.inl (.inl m)) =>
      query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inl m)
    | .inl (.inl (.inr kq)) =>
      query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inl (.inl kq)))
    | .inl (.inr cq) =>
      query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inl (.inr cq)))
    | .inr dq =>
      query (spec := unifSpec + bhGameSpec S ℓ PQC) (.inr (.inr dq))

theorem isQueryBoundP_bhAdvRun_aux
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    {α : Type} (oa : OracleComp (cliGameSpec S ℓ PQC) α) (n : ℕ)
    (h : oa.IsQueryBoundP (fun q => bhClassifyComposed pKi pCtl pInst q = true) n) :
    (simulateQ (bhAdvToGameImpl S ℓ PQC) oa).IsQueryBoundP
      (fun q => bhClassifyGame pKi pCtl pInst q = true) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind]
    rcases q with ((m | kq) | cq) | ⟨i, sq⟩ <;>
      simpa [bhAdvToGameImpl, bhClassifyComposed, bhClassifyGame, bhClassifyGameOnly,
        isQueryBoundP_query_bind_iff] using ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem isQueryBoundP_bhAdvRun
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    (A : CliGameAdversary S ℓ PQC) (n : ℕ)
    (h : A.run.IsQueryBoundP (fun q => bhClassifyComposed pKi pCtl pInst q = true) n) :
    (cliGameAdversaryReassoc A).IsQueryBoundP (fun q => bhClassifyGame pKi pCtl pInst q = true) n :=
  isQueryBoundP_bhAdvRun_aux pKi pCtl pInst A.run n h

section PrefixQueryBound

abbrev isSmTargetQuery (ℓ : ℕ) :
    (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain → Prop :=
  fun q => (q matches .inr _) = true

theorem runFuel_queryBound_of_step_le
    {Sig0 : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
    {G : OracleSpec κ} {C_codec : GameCodec Sig0 G} {σ : Ty Sig0}
    (h : Comp O I [σ, C_codec.Q] (.prod C_codec.R σ))
    {p : κ → Bool} {P_tgt : ι → Prop} [DecidablePred P_tgt]
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P_tgt 0)
    (hstep : ∀ t s,
      (h.eval (.cons s (.cons (C_codec.qenc t) .nil))).IsQueryBoundP P_tgt (if p t then 1 else 0))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP
        (fun x => (match x with | .inl _ => false | .inr t => p t) = true) q →
      ∀ (fuel : ℕ) (s : σ.denote),
        (runFuel h dflt oa fuel s).IsQueryBoundP P_tgt q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s; simp [runFuel]
  | query_bind t mx ih =>
    intro q hq fuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl n =>
      simpa [runFuel] using isQueryBoundP_bind (hU n)
        (fun u _ => ih u (q := q) ((hq.2 u).mono (by simp)) fuel s)
    | inr g =>
      cases fuel with
      | zero => simp [runFuel]
      | succ f =>
        simp only [runFuel, construct_query_bind]
        by_cases hpg : p g = true
        · have hpos : 0 < q := hq.1.resolve_left (by simp [hpg])
          have hh : (h.eval (.cons s (.cons (C_codec.qenc g) .nil))).IsQueryBoundP P_tgt 1 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (C_codec.rdec g res.1) (q := q - 1)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)
        · have hh : (h.eval (.cons s (.cons (C_codec.qenc g) .nil))).IsQueryBoundP P_tgt 0 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (C_codec.rdec g res.1) (q := q)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)

theorem bhShallowRunFuel_queryBound_of_step_le
    {ι κ Q R St : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    {p : κ → Bool} {P_tgt : (unifSpec + T).Domain → Prop} [DecidablePred P_tgt]
    (hU : ∀ n, (bhFwdU (G := T) n).IsQueryBoundP P_tgt 0)
    (hstep : ∀ t s, (h s (qenc t)).IsQueryBoundP P_tgt (if p t then 1 else 0))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP
        (fun x => (match x with | .inl _ => false | .inr t => p t) = true) q →
      ∀ (fuel : ℕ) (s : St),
        (bhShallowRunFuel qenc rdec h dflt oa fuel s).IsQueryBoundP P_tgt q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s; simp [bhShallowRunFuel]
  | query_bind t mx ih =>
    intro q hq fuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases t with
    | inl n =>
      simpa [bhShallowRunFuel] using isQueryBoundP_bind (hU n)
        (fun u _ => ih u (q := q) ((hq.2 u).mono (by simp)) fuel s)
    | inr g =>
      cases fuel with
      | zero => simp [bhShallowRunFuel]
      | succ f =>
        simp only [bhShallowRunFuel_query_inr_succ]
        by_cases hpg : p g = true
        · have hpos : 0 < q := hq.1.resolve_left (by simp [hpg])
          have hh : (h s (qenc g)).IsQueryBoundP P_tgt 1 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (rdec g res.1) (q := q - 1)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)
        · have hh : (h s (qenc g)).IsQueryBoundP P_tgt 0 := by
            simpa [hpg] using hstep g s
          exact (isQueryBoundP_bind hh
            (fun res _ => ih (rdec g res.1) (q := q)
              ((hq.2 _).mono (by simp [hpg])) f res.2)).mono
            (by omega)

theorem isQueryBoundP_paused_of_mem_support_simulateQ_run1
    {Sig0 : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
    {G : OracleSpec κ} {C_codec : GameCodec Sig0 G}
    {rIn aIn aOut ch rIn2 out : Ty Sig0}
    (R : TwoStageCostedReduction O I G C_codec rIn aIn aOut ch rIn2 out)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl T ProbComp)
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP P_src q →
      ∀ (fuel : ℕ) (s : R.σ.denote) (t : κ) (c : ch.denote) (p : R.π.denote)
        (s' : R.σ.denote) (cont : G t → OracleComp (unifSpec + G) α),
        Mid.paused t c p s' cont ∈ support (simulateQ impl (R.run1 dflt oa fuel s)) →
        ∀ v, (cont v).IsQueryBoundP P_src q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s t c p s' cont hmem
    simp [TwoStageCostedReduction.run1, construct_pure, simulateQ_pure] at hmem
  | query_bind q_oa mx ih =>
    intro q hq fuel s t c p s' cont hmem
    rw [isQueryBoundP_query_bind_iff] at hq
    have hmx : ∀ u, (mx u).IsQueryBoundP P_src q := fun u =>
      (hq.2 u).mono (by split_ifs <;> omega)
    cases q_oa with
    | inl n =>
      simp only [TwoStageCostedReduction.run1, construct_query_bind, simulateQ_bind, support_bind,
        Set.mem_iUnion] at hmem
      rcases hmem with ⟨u, _, hmem⟩
      exact ih u (hmx u) fuel s t c p s' cont hmem
    | inr g =>
      cases fuel with
      | zero =>
        simp [TwoStageCostedReduction.run1, construct_query_bind, simulateQ_pure] at hmem
      | succ f =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, simulateQ_bind, support_bind,
          Set.mem_iUnion] at hmem
        rcases hmem with ⟨res, _, hmem⟩
        rcases res with ⟨v, s₁⟩ | ⟨c₁, p₁, s₁⟩
        · exact ih (C_codec.rdec g v) (hmx _) f s₁ t c p s' cont hmem
        · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Mid.paused.injEq] at hmem
          rcases hmem with ⟨rfl, _, _, _, hcont⟩
          cases hcont
          exact hmx

/-- Any `Mid.paused` continuation in the support of `simulateQ impl (R.eval1 A x fuel dflt)`
inherits `IsQueryBoundP` from `A`. -/
theorem isQueryBoundP_paused_of_mem_support_simulateQ_eval1
    {Sig0 : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
    {G : OracleSpec κ} {C_codec : GameCodec Sig0 G}
    {rIn aIn aOut ch rIn2 out : Ty Sig0}
    (R : TwoStageCostedReduction O I G C_codec rIn aIn aOut ch rIn2 out)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl T ProbComp)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (x : rIn.denote) (fuel : ℕ) (dflt : aOut.denote) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP P_src q)
    (c0 : ch.denote) (t : κ) (c : ch.denote) (p : R.π.denote)
    (s' : R.σ.denote) (cont : G t → OracleComp (unifSpec + G) aOut.denote)
    (hmem : (c0, Mid.paused t c p s' cont) ∈ support (simulateQ impl (R.eval1 A x fuel dflt))) :
    ∀ v, (cont v).IsQueryBoundP P_src q := by
  unfold TwoStageCostedReduction.eval1 at hmem
  simp only [simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
  rcases hmem with ⟨⟨a, s⟩, _, m, hm, hfin⟩
  cases m with
  | done b s₁ =>
    simp only [simulateQ_bind, simulateQ_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false] at hfin
    rcases hfin with ⟨_, _, hfalse⟩
    exact False.elim hfalse
  | paused t₁ c₁ p₁ s₁ cont₁ =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
    rcases hfin with ⟨_, hmid⟩
    rw [← hmid] at hm
    exact isQueryBoundP_paused_of_mem_support_simulateQ_run1 R impl dflt (hA a)
      fuel s t c p s' cont hm

theorem isQueryBoundP_paused_of_mem_support_simulateQ_shallow_run1
    {ι κ Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {T : OracleSpec ι} {G : OracleSpec κ}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl (unifSpec + T) ProbComp)
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP P_src q →
      ∀ (fuel : ℕ) (s : σ) (t : κ) (c : ch) (p : π)
        (s' : σ) (cont : G t → OracleComp (unifSpec + G) α),
        Mid.paused t c p s' cont ∈ support (simulateQ impl (Red.run1 dflt oa fuel s)) →
        ∀ v, (cont v).IsQueryBoundP P_src q := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel s t c p s' cont hmem
    simp [BhShallowTwoStageRed.run1_pure, simulateQ_pure] at hmem
  | query_bind q_oa mx ih =>
    intro q hq fuel s t c p s' cont hmem
    rw [isQueryBoundP_query_bind_iff] at hq
    have hmx : ∀ u, (mx u).IsQueryBoundP P_src q := fun u =>
      (hq.2 u).mono (by split_ifs <;> omega)
    cases q_oa with
    | inl n =>
      simp only [BhShallowTwoStageRed.run1_query_inl, simulateQ_bind, support_bind,
        Set.mem_iUnion] at hmem
      rcases hmem with ⟨u, _, hmem⟩
      exact ih u (hmx u) fuel s t c p s' cont hmem
    | inr g =>
      cases fuel with
      | zero =>
        simp [BhShallowTwoStageRed.run1, construct_query_bind, simulateQ_pure] at hmem
      | succ f =>
        simp only [BhShallowTwoStageRed.run1_query_inr_succ, simulateQ_bind, support_bind,
          Set.mem_iUnion] at hmem
        rcases hmem with ⟨res, _, hmem⟩
        rcases res with ⟨v, s₁⟩ | ⟨c₁, p₁, s₁⟩
        · exact ih (Red.rdec g v) (hmx _) f s₁ t c p s' cont hmem
        · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff,
            Mid.paused.injEq] at hmem
          rcases hmem with ⟨rfl, _, _, _, hcont⟩
          cases hcont
          exact hmx

/-- Shallow counterpart of `isQueryBoundP_paused_of_mem_support_simulateQ_eval1` for
`BhShallowTwoStageRed.eval1`. -/
theorem isQueryBoundP_paused_of_mem_support_simulateQ_shallow_eval1
    {ι κ Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {T : OracleSpec ι} {G : OracleSpec κ}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    {P_src : (unifSpec + G).Domain → Prop} [DecidablePred P_src]
    (impl : QueryImpl (unifSpec + T) ProbComp)
    (A : aIn → OracleComp (unifSpec + G) aOut)
    (x : rIn) (fuel : ℕ) (dflt : aOut) (q : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP P_src q)
    (c0 : ch) (t : κ) (c : ch) (p : π)
    (s' : σ) (cont : G t → OracleComp (unifSpec + G) aOut)
    (hmem : (c0, Mid.paused t c p s' cont) ∈ support (simulateQ impl (Red.eval1 A x fuel dflt))) :
    ∀ v, (cont v).IsQueryBoundP P_src q := by
  unfold BhShallowTwoStageRed.eval1 at hmem
  simp only [simulateQ_bind, support_bind, Set.mem_iUnion] at hmem
  rcases hmem with ⟨⟨a, s⟩, _, m, hm, hfin⟩
  cases m with
  | done b s₁ =>
    simp only [simulateQ_bind, simulateQ_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, and_false] at hfin
    rcases hfin with ⟨_, _, hfalse⟩
    exact False.elim hfalse
  | paused t₁ c₁ p₁ s₁ cont₁ =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hfin
    rcases hfin with ⟨_, hmid⟩
    rw [← hmid] at hm
    exact isQueryBoundP_paused_of_mem_support_simulateQ_shallow_run1 Red impl dflt (hA a)
      fuel s t c p s' cont hm

end PrefixQueryBound

end QueryBounds

end CryptoVerification.E2E
