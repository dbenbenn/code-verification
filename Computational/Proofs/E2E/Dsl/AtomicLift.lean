/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.AtomicLiftDefs
public import Computational.Proofs.E2E.Dsl.CliAdapterCosted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CliAdapterTblByKind -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Atomic Binary-Harness Adapter Lifted via `AtomicLiftDefs`

Specializes the covariant `ReductionDsl` homomorphism in `AtomicLiftDefs` to lift the `Ty.tbl`
binary-harness adapter `cliToModelAdapterProgTblRo` onto `atomicAdapterOps`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.AtomicLift

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface GameCodec Expr Comp
  handlerImpl CostedReduction atomicSig atomicBaseSamplers atomicAdapterOps)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey)
open CryptoVerification.LibsignalSession (GRedBounded GRedCostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BinState BHDRCtlQuery bhCtlUnStart bhGameSpec bhTargetGameSpec
  e2eBhAdapterIface e2eBhAdapterCodec CliToModelAdapterProg CliAdapterCostBounded
  bhQueryKind bhKindCounts bhAdapterCostBudget bhAdapterCostBudgetByKind CliAdapterForwardsKinds
  CliGameAdversary CliGameAdversaryPerInstanceBounded cliGameAdversaryReassoc
  bhIsInstQueryWithSpqr bhClassifyComposed bhClassifyGame bhClassifyGameOnly
  bhClassifyTarget bhClassifyTargetOnly isQueryBoundP_bhAdvRun
  cliE2EExpWithKi L_bh stageOneAsProbComp)
open CryptoVerification.E2E.Costed (E2EAdapterTag e2eSig e2eAdapterOps
  e2eAdapterIface e2eAdapterCodec sidV keyIndQenc keyIndQdec smQenc gRedBounded_of_bounds)
open _root_.ReductionDsl (atomicBaseSamplers_sizeHonest atomicAdapterOps_sizeHonest)
open Computational.Proofs.E2E.Dsl.TablesHonest (adapterCrArm keyIndQdec_keyIndQenc)
open Computational.Proofs.E2E.Dsl.AtomicLiftDefs (
  mapEnv mapCostedReduction mapCostedReduction_totalCost mapCostedReduction_size
  mapCostedReduction_totalQueries mapCostedReduction_eval mapCostedReduction_gRedCostByKind
  ιSort toDen toAtomicVal toAtomicVal_surjective ιAdapterTag
  adapterOpsHom adapterIfaceHom adapterCodecHom)
open Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs (
  cliQuery cliAdapterTblStateTy
  cliAdapterKiOrCtlArmTbl cliAdapterTrArmTbl cliAdapterChArmTbl
  cliAdapterDlArmTbl cliAdapterIjArmTbl cliAdapterHandleTbl
  cliToModelAdapterProgTbl)
open Computational.Proofs.E2E.Dsl.CliAdapterCosted (
  cliE2EExpWithKiCoinLogged
  totalCost_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
  size_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
  totalQueries_cliToModelAdapterProgTbl_le
  cliToModelAdapterProgTbl_perInstanceQueryBounds
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh
  boolBias_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh)
open Computational.Proofs.E2E.Dsl.CliAdapterTblByKind (cliToModelAdapterProgTblRo
  cliToModelAdapterProgTblRo_eval_eq
  totalCost_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
  size_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
  totalQueries_cliToModelAdapterProgTblRo_le
  costBoundedByKind_cliToModelAdapterProgTblRo_bhAdapterCostBudgetByKind)

/-- `Ty.tbl`-backed binary-harness `CostedReduction` adapter lifted onto `atomicAdapterOps`. -/
@[expose] def cliToModelAdapterProgTblAtomic {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProg S ℓ decT encT :=
  mapCostedReduction
    (adapterOpsHom ℓ decT encT)
    (adapterIfaceHom S ℓ Pt)
    (adapterCodecHom S ℓ Pt)
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)

theorem cliToModelAdapterProgTblAtomic_totalCost_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).totalCost q =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalCost q :=
  mapCostedReduction_totalCost _ _ _ _ q

theorem cliToModelAdapterProgTblAtomic_size_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).size =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).size :=
  mapCostedReduction_size _ _ _ _

theorem cliToModelAdapterProgTblAtomic_totalQueries_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q :=
  mapCostedReduction_totalQueries _ _ _ (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) _ q

theorem cliToModelAdapterProgTblAtomic_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval =
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval :=
  (mapCostedReduction_eval
    (adapterOpsHom ℓ decT encT) (adapterIfaceHom S ℓ Pt) (adapterCodecHom S ℓ Pt)
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)).trans
    (cliToModelAdapterProgTblRo_eval_eq decT encT)

private def wKiOnly : E2EAdapterTag → ℕ
  | .ki => 1
  | _ => 0

private theorem isQueryBoundP_congr_pred_atomic {ι α : Type} {spec : OracleSpec ι}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨h.1.imp (mt (hpq t).mpr) id, fun u => ?_⟩
    by_cases ht : p t
    · have hqt : q t := (hpq t).mp ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)
    · have hqt : ¬ q t := mt (hpq t).mpr ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)

private theorem simulateQ_run_stateT_of_step_le_atomic
    {ι κ σ α : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {impl : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((impl q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ}
    (hoa : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ impl oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a => simp [simulateQ_pure]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hoa.1.resolve_left (not_not.mpr hp)
      have hcont : ∀ u, (cont u).IsQueryBoundP P_src (n - 1) := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega
    · have hcont : ∀ u, (cont u).IsQueryBoundP P_src n := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega

private theorem cliAdapterHandleTbl_queries_wKiOnly
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterHandleTbl decT encT S ℓ).queries wKiOnly (fun _ => 0) = 1 := by
  simp [cliAdapterHandleTbl, cliAdapterKiOrCtlArmTbl, cliAdapterTrArmTbl,
    cliAdapterChArmTbl, cliAdapterDlArmTbl, cliAdapterIjArmTbl, adapterCrArm,
    cliQuery, wKiOnly, Comp.queries]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandleTbl_kiPred
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (s : (cliAdapterTblStateTy S ℓ).denote) (t : (bhGameSpec S ℓ (BitVec 512)).Domain) :
    ((cliAdapterHandleTbl decT encT S ℓ).eval
      (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true)
      (if bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true
  have hU0 : ∀ n, ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ).fwdU n).IsQueryBoundP P_tgt 0 := fun n =>
    (isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      P_tgt (Sum.inl n) 0).2 (by simp [P_tgt, bhClassifyTarget])
  have hwKi : ∀ g x, P_tgt ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ).enc g x) → 1 ≤ wKiOnly g := by
    intro g x hx
    cases g <;> simp [P_tgt, wKiOnly, Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface,
      e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly] at hx ⊢
  by_cases hp : bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t = true
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
    rw [← cliAdapterHandleTbl_queries_wKiOnly (S := S) (ℓ := ℓ) decT encT]
    exact _root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0
      (cliAdapterHandleTbl decT encT S ℓ)
      (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
    have hpFalse : bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t = false :=
      Bool.eq_false_iff.mpr hp
    rcases t with (kq | cq) | ⟨i, sq⟩
    · simp only [bhClassifyGameOnly] at hpFalse
      change ((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
          (.cons (.inl (keyIndQenc kq))
            (.cons s (.cons (.inl (.inl (keyIndQenc kq))) .nil)))).IsQueryBoundP P_tgt 0
      simp only [cliAdapterKiOrCtlArmTbl, cliQuery, Comp.eval, Expr.eval, Expr.v0]
      refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun x _ => isQueryBoundP_pure P_tgt _ 0))
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro hq
      change pKi (keyIndQdec (keyIndQenc kq)) = true at hq
      rw [keyIndQdec_keyIndQenc, hpFalse] at hq
      exact False.elim (Bool.false_ne_true hq)
    · rcases cq with ⟨sid⟩
      let cCtl : Comp (e2eAdapterOps ℓ decT encT)
          (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ)
          [CryptoVerification.E2E.Costed.sidT S,
           .sum (CryptoVerification.E2E.Costed.keyIndQT S) (CryptoVerification.E2E.Costed.sidT S),
           cliAdapterTblStateTy S ℓ,
           (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).Q]
          (.prod (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
        .bind (cliQuery E2EAdapterTag.ctl .v0)
          (.caseOpt .v0
            (.ret (.pair (.inl (.inr .none)) .v3))
            (.caseOpt (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.guardPromoteTblExpr (.snd (.snd .v4)) .v2)
              (.ret (.pair (.inl (.inr (.some .v0))) .v4))
              (.ret (.pair (.inl (.inr (.some .v1)))
                (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5))))))
      have hc0 : cCtl.queries wKiOnly (fun _ => 0) = 0 := by
        simp [cCtl, cliQuery, wKiOnly, Comp.queries]
      change (cCtl.eval (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s (.cons (.inl (.inr (sidV sid))) .nil))))).IsQueryBoundP P_tgt 0
      exact (_root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0 cCtl
        (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s (.cons (.inl (.inr (sidV sid))) .nil))))).mono (by rw [hc0])
    · let cSm : Comp (e2eAdapterOps ℓ decT encT)
          (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ)
          [.prod .nat CryptoVerification.E2E.Costed.smQT, cliAdapterTblStateTy S ℓ,
           (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).Q]
          (.prod (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
        .caseSum (.snd .v0)
          (cliAdapterTrArmTbl S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterChArmTbl S ℓ decT encT)
            (.caseSum .v0
              (cliAdapterDlArmTbl S ℓ decT encT)
              (.caseSum .v0
                (cliAdapterIjArmTbl S ℓ decT encT)
                (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
                  (Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.drvMirrorTblTy S ℓ)))))
      have hc0 : cSm.queries wKiOnly (fun _ => 0) = 0 := by
        simp [cSm, cliAdapterTrArmTbl, cliAdapterChArmTbl, cliAdapterDlArmTbl,
          cliAdapterIjArmTbl, adapterCrArm, cliQuery, wKiOnly, Comp.queries]
      change (cSm.eval (.cons (i, smQenc sq)
          (.cons s (.cons (.inr (i, smQenc sq)) .nil)))).IsQueryBoundP P_tgt 0
      exact (_root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0 cSm
        (.cons (i, smQenc sq) (.cons s (.cons (.inr (i, smQenc sq)) .nil)))).mono (by rw [hc0])

theorem cliAdapterForwardsKinds_cliToModelAdapterProgTblAtomic
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qKind : Fin 2 → ℕ) :
    CliAdapterForwardsKinds
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT) qKind := by
  intro A hA i
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  let P_src (k : Fin 2) : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => SignalPqxdh.isGameQueryOfKind bhQueryKind k q = true
  let P_tgt (k : Fin 2) : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q' => SignalPqxdh.isGameQueryOfKind bhQueryKind k q' = true
  have hstep : ∀ (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain)
      (s : (cliAdapterTblStateTy S ℓ).denote),
      (((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).impl q).run s).IsQueryBoundP
        (P_tgt i) (if P_src i q then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      have hnc : ¬ P_src i (.inl m) := by simp [P_src, SignalPqxdh.isGameQueryOfKind]
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnc h))]
      show ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ).fwdU m >>=
          fun a => pure (a, s)).IsQueryBoundP (P_tgt i) 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        ((isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
          (P_tgt i) (Sum.inl m) 0).2 (by simp [P_tgt, SignalPqxdh.isGameQueryOfKind]))
        (fun a _ => isQueryBoundP_pure (P_tgt i) (a, s) 0)
    | inr t =>
      show ((cliAdapterHandleTbl decT encT S ℓ).eval
          (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        (P_tgt i) (if P_src i (.inr t) then 1 else 0)
      suffices hh :
          ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt i) (if P_src i (.inr t) then 1 else 0) by
        simpa only [Nat.add_zero] using isQueryBoundP_bind hh
          (fun p _ => isQueryBoundP_pure (P_tgt i) _ 0)
      rcases i with ⟨_ | _ | n, hn⟩
      ·
        change ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt 0) (if P_src 0 (.inr t) then 1 else 0)
        by_cases hp : P_src 0 (.inr t)
        · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
          have hq1 : (cliAdapterHandleTbl decT encT S ℓ).queries (fun _ => 1) (fun _ => 0) = 1 := by
            simp [cliAdapterHandleTbl, cliAdapterKiOrCtlArmTbl, cliAdapterTrArmTbl,
              cliAdapterChArmTbl, cliAdapterDlArmTbl, cliAdapterIjArmTbl, adapterCrArm,
              cliQuery, Comp.queries]
          have hU0 : ∀ n, ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterIface S ℓ).fwdU n).IsQueryBoundP (P_tgt 0) 0 := fun n =>
            (isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
              (P_tgt 0) (Sum.inl n) 0).2 (by simp [P_tgt, SignalPqxdh.isGameQueryOfKind])
          exact (_root_.ReductionDsl.Comp.queryBound_eval (P_tgt 0) (fun _ => 1) (fun _ => 0)
            (fun _ _ _ => le_rfl) hU0 (cliAdapterHandleTbl decT encT S ℓ)
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))).mono
            (by rw [hq1])
        · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
          rcases t with (kq | cq) | ⟨idx, sq⟩
          · cases kq with
            | roQuery sec =>
              change ((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
                  (.cons (.inl (keyIndQenc (.roQuery sec)))
                    (.cons s (.cons (.inl (.inl (keyIndQenc (.roQuery sec)))) .nil)))).IsQueryBoundP (P_tgt 0) 0
              simp only [cliAdapterKiOrCtlArmTbl, cliQuery, Comp.eval, Expr.eval, Expr.v0]
              refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure (P_tgt 0) _ 0)
              rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
              intro hq
              change P_tgt 0 (.inr (.inl (.inl (keyIndQdec (ℓ := ℓ)
                (keyIndQenc (ℓ := ℓ) (SignalPqxdh.KeyIndQuery.roQuery (S := S) sec)))))) at hq
              rw [keyIndQdec_keyIndQenc] at hq
              simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind] at hq
            | _ =>
              exfalso; apply hp
              simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
          · exfalso; apply hp
            simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
          · exfalso; apply hp
            simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
      ·
        change ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCostedDefs.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt 1) (if P_src 1 (.inr t) then 1 else 0)
        let isRoKi : SignalPqxdh.KeyIndQuery S → Bool
          | .roQuery _ => true
          | _ => false
        have hSrcEq : P_src 1 (.inr t) ↔
            bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true := by
          rcases t with (kq | cq) | ⟨idx, sq⟩
          · cases kq <;> simp [P_src, isRoKi, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
          · simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
          · simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
        have hTgtEq :
            ∀ q' : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain,
              (bhClassifyTarget isRoKi (fun _ => false) (fun _ => false) q' = true) ↔ P_tgt 1 q' := by
          intro q'
          cases q' with
          | inl _ => simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhClassifyTarget]
          | inr t' =>
            rcases t' with (kq | cq) | ⟨idx, sq⟩
            · cases kq <;> simp [P_tgt, isRoKi, SignalPqxdh.isGameQueryOfKind, bhQueryKind,
                bhClassifyTarget, bhClassifyTargetOnly]
            · simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyTarget, bhClassifyTargetOnly]
            · simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyTarget, bhClassifyTargetOnly]
        have h1 := isQueryBoundP_congr_pred_atomic hTgtEq
          (isQueryBoundP_cliAdapterHandleTbl_kiPred decT encT isRoKi s t)
        by_cases hs : P_src 1 (.inr t)
        · have hs' : bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true := hSrcEq.mp hs
          simpa [hs, hs'] using h1
        · have hs' : ¬ (bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true) := mt hSrcEq.mpr hs
          simpa [hs, hs'] using h1
      · omega
  have hsim := simulateQ_run_stateT_of_step_le_atomic hstep (hA () i)
  have hinit :
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).init.eval
        (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP (P_tgt i) 0 :=
    isQueryBoundP_pure (P_tgt i) _ 0
  have hfin : ∀ s' b,
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).finish.eval
        (Env.cons s' (Env.cons b Env.nil))).IsQueryBoundP (P_tgt i) 0 :=
    fun _ _ => isQueryBoundP_pure (P_tgt i) _ 0
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

/-- Unconditional `CliAdapterCostBounded` witness for `cliToModelAdapterProgTblAtomic`. -/
theorem gRedBounded_cliToModelAdapterProgTblAtomic_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CliAdapterCostBounded decT encT b qStart qDR
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT) := by
  unfold CliAdapterCostBounded
  refine ⟨?_, ?_, cliAdapterForwardsKinds_cliToModelAdapterProgTblAtomic decT encT _⟩
  · refine gRedBounded_of_bounds
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (bhAdapterCostBudget S b qStart qDR ℓ) ?_ ?_ ?_
      (atomicAdapterOps_sizeHonest ℓ decT encT)
      (atomicBaseSamplers_sizeHonest ℓ Pt)
    · rw [cliToModelAdapterProgTblAtomic_totalCost_eq]
      exact totalCost_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget decT encT b qStart qDR
    · rw [cliToModelAdapterProgTblAtomic_size_eq]
      exact size_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget decT encT b qStart qDR
    · rw [cliToModelAdapterProgTblAtomic_totalQueries_eq]
      exact totalQueries_cliToModelAdapterProgTblRo_le decT encT (b.q_total + qStart + qDR)
  · exact mapCostedReduction_gRedCostByKind
      (adapterOpsHom ℓ decT encT) (adapterIfaceHom S ℓ Pt) (adapterCodecHom S ℓ Pt)
      (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
      (fun _ => rfl) (fun _ => rfl)
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)
      (toAtomicVal_surjective ℓ Pt _)
      ⟨costBoundedByKind_cliToModelAdapterProgTblRo_bhAdapterCostBudgetByKind decT encT b qStart qDR,
       totalQueries_cliToModelAdapterProgTblRo_le decT encT _⟩

/-- Per-instance `IsQueryBoundP` transfer for `cliToModelAdapterProgTblAtomic`. -/
theorem cliToModelAdapterProgTblAtomic_perInstanceQueryBounds
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let B_A :=
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
      (∑ k ∈ Finset.range qStart, qs k) ∧
    (∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) := by
  dsimp only
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  exact cliToModelAdapterProgTbl_perInstanceQueryBounds decT encT A b qStart qs hA

/-- Exact `ProbComp (Bool × List (BitVec 512))` equivalence between
`cliToModelAdapterProgTblAtomic` and `L_bh` inside `cliE2EExpWithKiCoinLogged` under
`WellFormedPrimitivesδ P`. -/
theorem cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTblAtomic_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) := by
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  exact cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A


end Computational.Proofs.E2E.Dsl.AtomicLift

-- AUTO-BRIDGE BEGIN
namespace Computational.Proofs.E2E.Dsl.AtomicLift
export Computational.Proofs.E2E.Dsl.AtomicLiftDefs (
  mapTy toVal mapVar mapEnv get_mapEnv castDen
  castDen_self castDen_symm_castDen castExpr castExpr_cost castExpr_size castExpr_eval
  castComp castComp_cost castComp_size castComp_queries castComp_eval castCompCtx
  castCompCtx_cost castCompCtx_size castCompCtx_queries OpsHom mapExpr mapExpr_cost
  mapExpr_size mapExpr_eval IfaceHom mapComp mapComp_cost mapComp_size
  mapComp_queries mapComp_eval GameCodecHom mapCostedReduction mapCostedReduction_totalCost mapCostedReduction_size
  mapCostedReduction_totalQueries simulateQ_handlerImpl_map mapCostedReduction_eval mapMid mapTwoStageCostedReduction mapTwoStageCostedReduction_totalCost
  mapTwoStageCostedReduction_size mapTwoStageCostedReduction_totalQueries mapTwoStageCostedReduction_stage1Queries run1_mapTwoStage runFuel_mapOps mapTwoStageCostedReduction_eval1
  mapTwoStageCostedReduction_eval2 castExpr_costAt castComp_pureEval? castComp_costAt mapExpr_costAt mapComp_pureEval?
  mapComp_costAt mapCostedReduction_validKindCosts mapCostedReduction_totalCostByKind mapCostedReduction_costBoundedByKind mapCostedReduction_gRedCostByKind mapTwoStageCostedReduction_validKindCosts
  mapTwoStageCostedReduction_totalCostByKind mapTwoStageCostedReduction_costBoundedByKind mapTwoStageCostedReduction_gRed2CostByKind ιSort toDen atomic_e2eReadProstVarint_eq atomic_e2eDecodePreKeyMsg_eq
  atomic_splitSpqrPrev_eq atomic_e2eRecordExtras_eq toAtomicVal mapTy_ιSort_denote cast_option_map cast_prod_mk
  cast_sum_map cast_list_map cast_tbl_map cast_toVal_ιSort toAtomicVal_surjective castDen_toVal_ιSort_heq castDen_toVal_ιSort_eq_cast
  ιUnifBase ιPureOp atomic_spqrDirToV_eq atomic_spqrChainToV_eq pureOp_dom_eq pureOp_cod_eq pureOp_cost_eq pureOp_opSize_eq
  pureOp_eval_eq ιCurveCheckOp curveCheckOp_dom_eq curveCheckOp_cod_eq curveCheckOp_eval_eq ιAdapterOp adapterOpsHom ιE2EOp e2eOp_dom_eq
  e2eOp_cod_eq e2eOp_cost_eq e2eOp_opSize_eq e2eOpsHom ιAdapterTag ιKeyIndTag ιSessionTag atomic_sidV_eq atomic_sidOfV_eq
  atomic_keyIndQenc_eq atomic_keyIndQdec_eq atomic_keyIndRenc_eq atomic_keyIndRdec_eq atomic_recvResultEnc_eq atomic_recvResultDec_eq
  atomic_smQenc_eq ιSamp samp_hom_eq adapterIfaceHom keyIndTargetIfaceHom sessionTargetIfaceHom adapterCodecHom
  targetGameCodecHom
)
end Computational.Proofs.E2E.Dsl.AtomicLift
-- AUTO-BRIDGE END
