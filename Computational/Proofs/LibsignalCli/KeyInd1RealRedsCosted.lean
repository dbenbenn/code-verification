/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.ModelIface
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
import Computational.Proofs.E2E.BhKindCouplingV1
import Computational.Proofs.ReductionDsl.Bridge
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames -- proof-setup: allow-public-import

/-!
# Polymorphic `KeyInd` Shallow Reference Reduction Query Bounds

Specializes `compositionLocalStart`, `pqxdhKeyIndExpForHandshake`, and
`KeyIndAdvantageForHandshake` to `SignalPqxdh.pqxdhKeyIndImpl true S P`, and relates tightened
`2 * qTot` reduction query budgets to `2 * qTot + 2`. Establishes structural `Comp` query-bound
helpers and proves `bhKindRedWith_queryBounded_of_B` for an arbitrary `KeyInd` oracle handler `ki`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open ReductionDsl CryptoVerification.E2E.Costed
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

@[simp]
theorem bhE2ELocalStartWith_pqxdhKeyIndImpl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) :
    compositionLocalStart (ℓ := ℓ) (SignalPqxdh.pqxdhKeyIndImpl true S P) =
      bhE2ELocalStart (S := S) (ℓ := ℓ) P := rfl

@[simp]
theorem pqxdhKeyIndExpWith_pqxdhKeyIndImpl (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (A : SignalPqxdh.KeyIndAdversary S) :
    pqxdhKeyIndExpForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl true S P) A =
      SignalPqxdh.pqxdhKeyIndExp S P A := rfl

@[simp]
theorem KeyIndAdvantageWith_pqxdhKeyIndImpl (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (A : SignalPqxdh.KeyIndAdversary S) :
    (KeyIndAdvantageForHandshake S P (SignalPqxdh.pqxdhKeyIndImpl true S P) A).toReal =
      SignalPqxdh.KeyIndAdvantage S P A := rfl

namespace KeyInd1RealRedsAux

theorem isQueryBoundP_congr_pred_with {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨by rw [← hpq t]; exact h.1, fun u => ih u ?_⟩
    have hu := h.2 u
    by_cases hpt : p t
    · have hqt : q t := (hpq t).mp hpt
      simpa [hpt, hqt] using hu
    · have hqt : ¬ q t := fun hq => hpt ((hpq t).mpr hq)
      simpa [hpt, hqt] using hu

section CompQueryHelpersWith

variable {Sig0 : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
variable (P : ι → Prop) [DecidablePred P]

theorem wqb_ret {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {e : Expr O Γ t} {ρ : Env Γ} (m : ℕ) :
    ((Comp.ret e : Comp O I Γ t).eval ρ).IsQueryBoundP P m :=
  isQueryBoundP_pure P (e.eval ρ) m

theorem wqb0_ret {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {e : Expr O Γ t} {ρ : Env Γ} :
    ((Comp.ret e : Comp O I Γ t).eval ρ).IsQueryBoundP P 0 :=
  isQueryBoundP_pure P (e.eval ρ) 0

theorem wqb_ite {Γ : List (Ty Sig0)} {t : Ty Sig0} {m : ℕ}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P m) (hd : (d.eval ρ).IsQueryBoundP P m) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval]
  split_ifs
  · exact hc
  · exact hd

theorem wqb0_ite {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0) (hd : (d.eval ρ).IsQueryBoundP P 0) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P 0 :=
  wqb_ite P hc hd

theorem wqb_caseOpt {Γ : List (Ty Sig0)} {a t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ t} {s : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hn : (n.eval ρ).IsQueryBoundP P m)
    (hs : ∀ x, (s.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.caseOpt e n s).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval]
  cases e.eval ρ with
  | none => exact hn
  | some x => exact hs x

theorem wqb0_caseOpt {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ t} {s : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hn : (n.eval ρ).IsQueryBoundP P 0)
    (hs : ∀ x, (s.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseOpt e n s).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseOpt P hn hs

theorem wqb_caseSum_inl {Γ : List (Ty Sig0)} {a b t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {x : a.denote} (he : e.eval ρ = .inl x)
    (hl : (l.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval, he]
  exact hl

theorem wqb0_caseSum_inl {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {x : a.denote} (he : e.eval ρ = .inl x)
    (hl : (l.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseSum_inl P he hl

theorem wqb_caseSum_inr {Γ : List (Ty Sig0)} {a b t : Ty Sig0} {m : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {y : b.denote} (he : e.eval ρ = .inr y)
    (hr : (r.eval (.cons y ρ)).IsQueryBoundP P m) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P m := by
  simp only [Comp.eval, he]
  exact hr

theorem wqb0_caseSum_inr {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {y : b.denote} (he : e.eval ρ = .inr y)
    (hr : (r.eval (.cons y ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 :=
  wqb_caseSum_inr P he hr

theorem wqb_bind {Γ : List (Ty Sig0)} {a t : Ty Sig0} {n m : ℕ}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P n)
    (hk : ∀ x, (k.eval (.cons x ρ)).IsQueryBoundP P m) :
    ((Comp.bind c k).eval ρ).IsQueryBoundP P (n + m) := by
  simpa [Comp.eval] using isQueryBoundP_bind hc (fun x _ => hk x)

theorem wqb0_bind {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0)
    (hk : ∀ x, (k.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.bind c k).eval ρ).IsQueryBoundP P 0 := by
  simpa [Comp.eval] using isQueryBoundP_bind hc (fun x _ => hk x)

theorem wqb0_sample {Γ : List (Ty Sig0)}
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {s : I.smp.Samp} {e : Expr O Γ (I.smp.sDom s)} {ρ : Env Γ} :
    ((Comp.sample s e : Comp O I Γ (I.smp.sTy s)).eval ρ).IsQueryBoundP P 0 :=
  liftP_queryBound P hU _

theorem wqb0_query {Γ : List (Ty Sig0)}
    {g : I.Tag} {e : Expr O Γ (I.dom g)} {ρ : Env Γ}
    (hg : ¬ P (I.enc g (e.eval ρ))) :
    ((Comp.query g e : Comp O I Γ (I.cod g)).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro h
  exact False.elim (hg h)

theorem wqb1_query {Γ : List (Ty Sig0)}
    {g : I.Tag} {e : Expr O Γ (I.dom g)} {ρ : Env Γ} :
    ((Comp.query g e : Comp O I Γ (I.cod g)).eval ρ).IsQueryBoundP P 1 := by
  simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro _
  exact Nat.zero_lt_one

end CompQueryHelpersWith

end KeyInd1RealRedsAux

section KindQueryBoundWith

open KeyInd1RealRedsAux

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
variable (P : SignalPqxdh.Primitives)
variable (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
variable (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
variable (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

private theorem isQueryBoundP_bhFwdU_ki
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (n : ℕ) :
    (bhFwdU (G := SignalPqxdh.keyIndSpec S) n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem isQueryBoundP_bhLiftP_ki {α : Type}
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (p : ProbComp α) :
    (bhLiftP (G := SignalPqxdh.keyIndSpec S) p).IsQueryBoundP P_ki 0 := by
  unfold bhLiftP
  induction p using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n mx ih =>
    rw [simulateQ_query_bind]
    exact (isQueryBoundP_bind (isQueryBoundP_bhFwdU_ki hInl n)
      (fun u _ => ih u)).mono (by omega)

private theorem isQueryBoundP_ki_query_zero
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    {kq : SignalPqxdh.KeyIndQuery S} (hnot : ¬ P_ki (.inr kq)) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 0).2 (fun h => False.elim (hnot h))

private theorem isQueryBoundP_ki_query_one
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (kq : SignalPqxdh.KeyIndQuery S) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 1 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 1).2 (fun _ => Nat.zero_lt_one)

private theorem simulateQ_run_StateT_of_step_le
    {ι κ : Type} {G : OracleSpec κ} {T : OracleSpec ι} {σ α : Type}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {so : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((so q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ} (hB : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ so oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure _ => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hB
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hB.1.resolve_left (not_not.mpr hp)
      have hq : ((so q).run s).IsQueryBoundP P_tgt 1 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)
    · have hq : ((so q).run s).IsQueryBoundP P_tgt 0 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)

end KindQueryBoundWith

end CryptoVerification.E2E
