/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.DFProgBucketBounds -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperBucketFS -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedStage2 -- proof-setup: allow-public-import
import Computational.Proofs.SessionCostedFig8.BundlesAuxSize
import Computational.Proofs.SessionCostedFig8.DFProgBoundsBase
import Computational.Proofs.SessionCostedFig8.DFProgSizeBounds
import Computational.Proofs.ReductionDsl.SM.DeliverForge
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds
import Computational.Proofs.ReductionDsl.Fig8WeightedParts
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.GameHop.ReductionDsl.CostUB
import Computational.Proofs.ReductionDsl.Notation
import Mathlib.Data.Nat.Log

/-!
# `N10b`: Tight `compCostW` bounds on `deliverForgeEC` / `deliverForgeECGen`-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Computational.Proofs.SessionCostedFig8.DFProgFsStage2DeliverCost

public section

open OracleSpec OracleComp
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM.Construction (Header healEpoch)
open _root_.ReductionDsl (Sig Ops Ty Expr Comp Iface bits)
open scoped Computational.Proofs.ReductionDsl.Notation
open _root_.CryptoGames.LibsignalSession (maxForwardJumps)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded authOutE_cost_le
  bits_le_bits_qep_add bits_succ_le cCompContainsE_cost_le cGsEpoch_cost cGsSetWin_cost
  cGsSt_cost cInTransitE_cost_le cRecPos_cost cTrivialE_cost_le commitEC_cost_le esAbort_cost
  esG_cost esH_cost esSetG_cost esSetH_cost implEC_cost_le isSomeE_cost
  modeCfgEC_injectFullE_cost_le otherE_cost pGet_cost v0_cost v1_cost v2_cost v3_cost v4_cost
  v5_cost v6_cost vRecvC_cost_le)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (HooksExcessBounded ckaOpC ckaSampC
  cInTransitE_excessUB commitEC_excessUB_le compExcessUB compExcessUB_bind compExcessUB_caseOpt
  compExcessUB_ite compExcessUB_ret corrDoomE_excessUB exprExcessUB exprExcessUB_add exprExcessUB_and
  exprExcessUB_anyB exprExcessUB_bool exprExcessUB_caseOpt exprExcessUB_cons exprExcessUB_eqN
  exprExcessUB_foldrB exprExcessUB_fst exprExcessUB_inl exprExcessUB_inr exprExcessUB_ite
  exprExcessUB_letE exprExcessUB_lt exprExcessUB_modK exprExcessUB_nat exprExcessUB_nil
  exprExcessUB_none exprExcessUB_not exprExcessUB_op exprExcessUB_pair exprExcessUB_snd
  exprExcessUB_some exprExcessUB_tget exprExcessUB_tset exprExcessUB_unit exprExcessUB_v0
  exprExcessUB_v1 exprExcessUB_v2 exprExcessUB_v3 exprExcessUB_v4 exprExcessUB_var
  modeCfgEC_challMsgE_excessUB modeCfgEC_challOKE_excessUB modeCfgEC_injectFullE_excessUB
  optNatLit_excessUB vRecvC_excessUB_le vSendC_excessUB_le)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound compCostW_le_of_parts
  bits_le_add_one)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (bits_one)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos size_le_budget_of_log_cost)

@[local simp] private theorem priv_exprCostW_v0 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ)
    {t : Ty S'} {Γ' : List (Ty S')} :
    exprCostW opC (Expr.v0 : Expr O' (t :: Γ') t) = 1 := rfl

@[local simp] private theorem priv_exprCostW_v1 {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ)
    {t0 t1 : Ty S'} {Γ' : List (Ty S')} :
    exprCostW opC (Expr.v1 : Expr O' (t0 :: t1 :: Γ') t1) = 1 := rfl

section DeliverCostHelpers

private theorem mode_tH_le_add5 {mo : CryptoGames.SM.Construction.Mode} {m : ℕ}
    (h : mo.tL.getD 0 ≤ m) : mo.tH ≤ m + 2 := by
  unfold CryptoGames.SM.Construction.Mode.tH healEpoch
  cases ht : mo.tL <;> simp [ht] at h ⊢
  omega

private theorem priv_compCostW_bind_ret_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    {opC : O'.Op → ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {a r : Ty S'}
    (e : Expr O' Γ' a) (k : Comp O' I' (a :: Γ') r)
    {ce ck : ℕ} (he : exprCostW opC e ≤ ce) (hk : compCostW opC sC qC k ≤ ck) :
    compCostW opC sC qC (.bind (.ret e) k) ≤ ce + ck + 2 := by
  simp only [compCostW]; omega

private theorem priv_compCostW_bind_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    {opC : O'.Op → ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {a r : Ty S'}
    (c : Comp O' I' Γ' a) (k : Comp O' I' (a :: Γ') r)
    {cc ck : ℕ} (hc : compCostW opC sC qC c ≤ cc) (hk : compCostW opC sC qC k ≤ ck) :
    compCostW opC sC qC (.bind c k) ≤ cc + ck + 1 := by
  simp only [compCostW]; omega

private theorem priv_compCostW_caseSum_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    {opC : O'.Op → ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S')} {a b r : Ty S'}
    (s : Expr O' Γ' (.sum a b)) (l : Comp O' I' (a :: Γ') r) (d : Comp O' I' (b :: Γ') r)
    {cs m : ℕ} (hs : exprCostW opC s ≤ cs)
    (hl : compCostW opC sC qC l ≤ m) (hd : compCostW opC sC qC d ≤ m) :
    compCostW opC sC qC (.caseSum s l d) ≤ cs + m + 1 := by
  simp only [compCostW]
  exact Nat.add_le_add (Nat.add_le_add hs (max_le hl hd)) le_rfl

private theorem outer_df_compCostW_le {S' : Sig} {O' : Ops S'} {ι : Type}
    {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S' TSpec}
    (opC : O'.Op → ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {esT smqT dfqT rT1 rT2 outT : Ty S'}
    (c1 : Comp O' I' [smqT, .prod esT (.sum smqT dfqT), esT, .sum smqT dfqT] rT1)
    (k1 : Comp O' I' [rT1, smqT, .prod esT (.sum smqT dfqT), esT, .sum smqT dfqT] outT)
    (c2 : Comp O' I' [dfqT, .prod esT (.sum smqT dfqT), esT, .sum smqT dfqT] rT2)
    (k2 : Comp O' I' [rT2, dfqT, .prod esT (.sum smqT dfqT), esT, .sum smqT dfqT] outT)
    {w1 w2 : ℕ}
    (hw1 : compCostW opC sC qC c1 ≤ w1) (hk1 : compCostW opC sC qC k1 ≤ 15)
    (hw2 : compCostW opC sC qC c2 ≤ w2) (hk2 : compCostW opC sC qC k2 ≤ 15) :
    compCostW opC sC qC
      (.bind (.ret (.pair .v0 .v1))
        (.caseSum (.snd .v0)
          (.bind c1 k1)
          (.bind c2 k2))) ≤ max w1 w2 + 30 := by
  let M := max w1 w2
  refine (priv_compCostW_bind_ret_le _ _ (ce := 5) (ck := M + 22) ?_ ?_).trans (by dsimp only [M]; omega)
  · simp [exprCostW]
  refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 16) ?_ ?_ ?_).trans (by omega)
  · simp [exprCostW]
  · exact (priv_compCostW_bind_le _ _ (cc := M) (ck := 15)
      (hw1.trans (Nat.le_max_left _ _)) hk1).trans (by omega)
  · exact (priv_compCostW_bind_le _ _ (cc := M) (ck := 15)
      (hw2.trans (Nat.le_max_right _ _)) hk2).trans (by omega)

private theorem df_multi_step_arith
    (q qepC l : ℕ) (moHk mo : CryptoGames.SM.Construction.Mode)
    (htStarHk : moHk.tStar ≤ qepC + 3) (htLHk : moHk.tL.getD 0 ≤ qepC + 3)
    (htStar : mo.tStar ≤ qepC + 3) (htL : mo.tL.getD 0 ≤ qepC + 3) (hl : l ≤ qepC + 3) :
    let L := q + 1
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let H := 1400 * L + 2 * bits moHk.tStar + 2 * bits moHk.tH + (B0 + 1) + 3000
    let Ho := 3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000
    let Hs := 9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000
    let Hr := 14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000
    let w1 := 3 * H + 2 * Ho + Hs + Hr + 18500 * L +
      L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
      2 * (maxForwardJumps + 1) + 5 * bits qepC + bits (mo.tL.getD 0) +
      9 * bits mo.tStar + 72 * bits l + bits mo.tStar + 41000
    let w2 := 3 * H + 2 * Ho + Hr + 1150 * L + bits qepC + 2 * bits mo.tStar + 7200
    max w1 w2 + 30 + 200000 ≤ fig8AtomicStepBound q qepC := by
  intro L B0 H Ho Hs Hr w1 w2
  have hL : L = q + 1 := rfl
  have hB0 : B0 = (q + 1) * (maxForwardJumps + 1) := rfl
  have hH_def : H = 1400 * L + 2 * bits moHk.tStar + 2 * bits moHk.tH + (B0 + 1) + 3000 := rfl
  have hHo_def : Ho = 3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000 := rfl
  have hHs_def : Hs = 9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000 := rfl
  have hHr_def : Hr = 14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000 := rfl
  have hw1_def : w1 = 3 * H + 2 * Ho + Hs + Hr + 18500 * L +
      L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
      2 * (maxForwardJumps + 1) + 5 * bits qepC + bits (mo.tL.getD 0) +
      9 * bits mo.tStar + 72 * bits l + bits mo.tStar + 41000 := rfl
  have hw2_def : w2 = 3 * H + 2 * Ho + Hr + 1150 * L + bits qepC + 2 * bits mo.tStar + 7200 := rfl
  clear_value L B0 H Ho Hs Hr w1 w2
  have hw2 : w2 ≤ w1 := by rw [hw1_def, hw2_def]; omega
  rw [Nat.max_eq_left hw2]
  have hfig : fig8AtomicStepBound q qepC =
      100000 * L + L * (3 * bits qepC + 60) + 120 * B0 + 200 * bits qepC + 25000000 := by
    unfold fig8AtomicStepBound
    dsimp only
    rw [← hB0, ← hL]
  rw [hfig]
  have htHHk7 : moHk.tH ≤ qepC + 7 := by
    have := mode_tH_le_add5 htLHk; omega
  have hbtStarHk := bits_le_bits_qep_add (show moHk.tStar ≤ qepC + 7 by omega)
  have hbtHHk := bits_le_bits_qep_add htHHk7
  have hbtStar := bits_le_bits_qep_add (show mo.tStar ≤ qepC + 7 by omega)
  have hbtL := bits_le_bits_qep_add (show mo.tL.getD 0 ≤ qepC + 7 by omega)
  have hbl := bits_le_bits_qep_add (show l ≤ qepC + 7 by omega)
  have hbq1 := bits_succ_le qepC
  have hbB0 := bits_le_add_one B0
  have hmfj_le : maxForwardJumps + 1 ≤ B0 := by
    rw [hB0]; exact Nat.le_mul_of_pos_left (maxForwardJumps + 1) (Nat.succ_pos q)
  have hmul : L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) ≤
      L * (3 * bits qepC + 60) :=
    Nat.mul_le_mul_left L (by omega)
  rw [hw1_def, hH_def, hHo_def, hHs_def, hHr_def]
  clear hL hB0 hH_def hHo_def hHs_def hHr_def hw1_def hw2_def hw2 hfig
  generalize L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) = Llhs at hmul ⊢
  generalize L * (3 * bits qepC + 60) = Lbq at hmul ⊢
  generalize bits B0 = bB0 at hbB0 ⊢
  generalize maxForwardJumps + 1 = mfj1 at hmfj_le ⊢
  generalize bits (qepC + 1) = bq1 at hbq1 ⊢
  generalize bits moHk.tStar = bsHk at hbtStarHk ⊢
  generalize bits moHk.tH = bhHk at hbtHHk ⊢
  generalize bits mo.tStar = bs at hbtStar ⊢
  generalize bits (mo.tL.getD 0) = btL at hbtL ⊢
  generalize bits l = blv at hbl ⊢
  generalize bits qepC = bq at hbq1 hbtStarHk hbtHHk hbtStar hbtL hbl ⊢
  omega

end DeliverCostHelpers

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "S_cka" => CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" => CryptoGames.CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
  fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "mHsTy" => CryptoGames.SM.Construction.fsMultiHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mEsTy" => CryptoGames.SM.Construction.fsMultiEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "ckaHdrCtT" => CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem optNatLit_cost_le_priv {O' : Ops S_cka} {Γ'} (o : Option ℕ) :
    (CryptoGames.SM.Engine.optNatLit (O' := O') (Γ' := Γ') o).cost ≤ bits (o.getD 0) + 3 := by
  cases o <;> simp only [CryptoGames.SM.Engine.optNatLit, Option.getD, Expr.cost] <;> omega

private theorem leakDoomE_cost_le_priv {O' : Ops S_cka} {vpT : Ty S_cka}
    (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g g' : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) :
    (CryptoGames.SM.Engine.leakDoomE L π g g').cost ≤
      g.cost + g'.cost +
        L * (bits (π.tL.getD 0) + 2 * bits π.tStar + 40) +
        2 * bits π.tStar + 105 := by
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.cGsTy vpT) (CryptoGames.SM.Engine.cGsTy vpT) :: Γ'
  have hopt := optNatLit_cost_le_priv (O' := O') (Γ' := .nat :: Γ0) π.tL
  have hmax14 : max 1 4 = 4 := rfl
  have hmax33 : max 3 3 = 3 := rfl
  simp only [CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.orE, CryptoGames.SM.ltOptE,
    CryptoGames.SM.leN, CryptoGames.SM.pGet, CryptoGames.SM.Engine.cGsLeaks,
    CryptoGames.SM.Engine.cGsEpoch, Expr.cost, v0_cost, v1_cost, hmax14, hmax33, Nat.reduceAdd]
  have hbody1 :
      (CryptoGames.SM.Engine.optNatLit (O' := O') (Γ' := .nat :: Γ0) π.tL).cost + 1 + 1 + 7 + 1 +
        (1 + bits π.tStar + 1) + 1 + 1 ≤
        bits (π.tL.getD 0) + bits π.tStar + 20 := by omega
  have hbody2 : 1 + bits π.tStar + 1 + 1 + 1 ≤ bits π.tStar + 10 := by omega
  have hmul1 := Nat.mul_le_mul_left L hbody1
  have hmul2 := Nat.mul_le_mul_left L hbody2
  have hmul3 :
      L * (bits (π.tL.getD 0) + bits π.tStar + 20) + L * (bits π.tStar + 10) ≤
      L * (bits (π.tL.getD 0) + 2 * bits π.tStar + 40) := by
    rw [← Nat.left_distrib]
    exact Nat.mul_le_mul_left L (by omega)
  omega

private theorem corrDoomE_cost_le_priv {O' : Ops S_cka} {vpT : Ty S_cka}
    (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.corrDoomE π g p).cost ≤
      g.cost + p.cost + (bits (π.tL.getD 0) + 3) + 2 * bits π.tStar + 105 := by
  have hopt := optNatLit_cost_le_priv (O' := O') (Γ' := .prod (CryptoGames.SM.Engine.cGsTy vpT) .bool :: Γ') π.tL
  cases hAuth : π.auth <;>
  · simp only [CryptoGames.SM.Engine.corrDoomE, hAuth, ↓reduceIte, Bool.false_eq_true,
      CryptoGames.SM.boolEq, CryptoGames.SM.ltOptE, CryptoGames.SM.leN, CryptoGames.SM.maxN,
      pGet_cost, cGsEpoch_cost, Expr.cost, v0_cost, v1_cost, Nat.reduceAdd]
    omega

private theorem cSafeChE_cost_le_priv {O' : Ops S_cka} {vpT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cSafeChE 3 s p).cost ≤ s.cost + p.cost + 80 := by
  have hb3 : bits 3 = 2 := rfl
  simp only [CryptoGames.SM.Engine.cSafeChE, CryptoGames.SM.healedByE, CryptoGames.SM.leN,
    CryptoGames.SM.pGet, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsEpoch,
    Expr.cost, Expr.v0, Expr.v1, hb3, Nat.reduceAdd]
  omega

private theorem modeCfgEC_challOKE_cost_le_priv {O' : Ops S_cka} (mo : CryptoGames.SM.Construction.Mode)
    {Γ'} (e : Expr O' Γ' .nat) :
    ((CryptoGames.SM.Engine.modeCfgEC O' mo).challOKE e).cost ≤ e.cost + bits mo.tStar + 6 := by
  cases h : mo.auth <;>
    simp only [CryptoGames.SM.Engine.modeCfgEC, h, ↓reduceIte, Bool.false_eq_true, Expr.cost] <;>
    omega

private theorem modeCfgEC_challMsgE_cost_le_priv {O' : Ops S_cka} (mo : CryptoGames.SM.Construction.Mode)
    {Γ'} (ep : Expr O' Γ' .nat) (b : Expr O' Γ' .bool) (m0 m1 : Expr O' Γ' (.base .msg)) :
    ((CryptoGames.SM.Engine.modeCfgEC O' mo).challMsgE ep b m0 m1).cost ≤
      ep.cost + b.cost + m0.cost + m1.cost + 2 * bits mo.tStar + 20 := by
  cases h : mo.auth <;>
    simp only [CryptoGames.SM.Engine.modeCfgEC, h, ↓reduceIte, Bool.false_eq_true, Expr.cost] <;>
    omega

private theorem transmitEC_cost_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (π : CryptoGames.SM.Engine.Policy) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    (CryptoGames.SM.Engine.transmitEC hk L 3 qep π es arg).cost ≤
      es.cost + arg.cost + 2 * H + 70 * L +
        L * (bits (π.tL.getD 0) + 2 * bits π.tStar + 40) +
        2 * bits π.tStar + 5 * bits qep + 3500 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT)
    (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ0
  let Γ2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) hsT :: Γ1
  have hep := DFProgBucketBounds.cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) 3 qep (by omega)
    (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.isSomeE (.snd (.snd (.snd .v0))))
  have hld := leakDoomE_cost_le_priv (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
  have hvs := DFProgBucketBounds.vSendC_any_cost_le hk H hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
  have hrec := DFProgBucketBounds.cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L 3 (by omega)
    (Γ' := Γ2) .v2 (.fst (.snd .v3)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v3)) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair (.fst (.snd (.snd .v3))) (.snd .v0)))
    (.bool false)
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost,
    CryptoGames.SM.Engine.cGsIdx, isSomeE_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Expr.cost, bits_one, Nat.reduceAdd] at hep hld hvs hrec
  simp only [CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esSetAbort,
    esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private theorem challEC_cost_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (π : CryptoGames.SM.Engine.Policy)
    (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    (CryptoGames.SM.Engine.challEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) π es arg).cost ≤
      es.cost + arg.cost + 2 * H + 70 * L +
        L * (bits (π.tL.getD 0) + 2 * bits π.tStar + 40) +
        2 * bits π.tStar + 7 * bits mo.tStar + 5 * bits qep + 4200 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT)
    (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cGsTy vpT :: Γ0
  let Γ2 : List (Ty S_cka) := .prod vpT ckaHdrCtT :: .prod (.opt (.prod vpT ckaHdrCtT)) hsT :: Γ1
  have hep := DFProgBucketBounds.cEpMgmtE_any_cost_le (O' := OO_cka) (vpT := vpT) 3 qep (by omega)
    (Γ' := Γ0) (CryptoGames.SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (CryptoGames.SM.isSomeE (.snd (.snd (.snd (.snd .v0)))))
  have hsc := cSafeChE_cost_le_priv (O' := OO_cka) (vpT := vpT) (Γ' := Γ1) .v0 (.fst (.snd .v1))
  have hok := modeCfgEC_challOKE_cost_le_priv (O' := OO_cka) mo (Γ' := Γ1)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
  have hld := leakDoomE_cost_le_priv (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) .v0
  have hcm1 := modeCfgEC_challMsgE_cost_le_priv (O' := OO_cka) mo (Γ' := Γ1)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
    (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v1)))
    (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))
  have hvs := DFProgBucketBounds.vSendC_any_cost_le hk H hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    ((CryptoGames.SM.Engine.modeCfgEC OO_cka mo).challMsgE
      (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1))))
  have hcm2 := modeCfgEC_challMsgE_cost_le_priv (O' := OO_cka) mo (Γ' := Γ2)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
    (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v3)))
    (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))
  have hrec := DFProgBucketBounds.cRecordE_any_cost_le (O' := OO_cka) (vpT := vpT) L 3 (by omega)
    (Γ' := Γ2) .v2 (.fst (.snd .v3)) (.fst .v0)
    (.pair (.pair (.fst (.snd .v3)) (.pair (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (.add (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsIdx .v2) (.fst (.snd .v3))) (.nat 1))))
      (.pair ((CryptoGames.SM.Engine.modeCfgEC OO_cka mo).challMsgE
        (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v2) (.fst (.snd .v3)))
        (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v3)))
        (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3))))) (.snd .v0)))
    (.bool true)
  simp only [CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsIdx,
    esG_cost, esH_cost, pGet_cost, cGsSt_cost, cGsEpoch_cost, isSomeE_cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Expr.cost, bits_one, Nat.reduceAdd]
    at hep hsc hok hld hcm1 hvs hcm2 hrec
  simp only [CryptoGames.SM.Engine.challEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esSetAbort,
    esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, Nat.reduceAdd]
  omega

private theorem corrEC_cost_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L : ℕ)
    (π : CryptoGames.SM.Engine.Policy) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    (CryptoGames.SM.Engine.corrEC hk L π es p).cost ≤
      es.cost + p.cost + H + 18500 * L +
        L * (bits (π.tL.getD 0) + 2 * bits π.tStar + 40) +
        bits (π.tL.getD 0) + 4 * bits π.tStar + 16000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hca := DFProgBucketBounds.cCorrAllowedE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hac0 := DFProgBucketBounds.cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_priv (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0))
    (CryptoGames.SM.Engine.cAfterCorrE L (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0))
  have hcd := corrDoomE_cost_le_priv (O' := OO_cka) (vpT := vpT) π (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hrv := hhk.reveal_le (Γ' := Γ0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.snd .v0))
  have hac1 := DFProgBucketBounds.cAfterCorrE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [esG_cost, esH_cost, pGet_cost, cGsSt_cost, v0_cost, v2_cost,
    Expr.cost, Nat.reduceAdd] at hca hac0 hld hcd hrv hac1
  simp only [CryptoGames.SM.Engine.corrEC, CryptoGames.SM.orE, CryptoGames.SM.Engine.cGsWin,
    CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esSetAbort,
    esG_cost, esH_cost, esAbort_cost, Comp.cost, Expr.cost,
    v0_cost, v1_cost, v2_cost, Nat.reduceAdd]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem transmitEC_excessUB_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (π : CryptoGames.SM.Engine.Policy)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.transmitEC hk L 3 qep π es arg) ≤
      30 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) + Ho + Hs + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  have hvs_tr := vSendC_excessUB_le hk Ho Hs Hr hhk
    (Γ' := CryptoGames.SM.Engine.cGsTy vpT :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) trQ :: Γ')
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
  simp only [CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.pGet,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE, Nat.add_zero, Nat.zero_add,
    Nat.mul_zero] at hvs_tr
  simp only [CryptoGames.SM.Engine.transmitEC, CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    optNatLit_excessUB, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE, CryptoGames.SM.pGet,
    CryptoGames.SM.pSet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.posSender,
    CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v3, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_nil, exprExcessUB_add, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_cons,
    exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret,
    compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem challEC_excessUB_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.challEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es arg) ≤
      30 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) + Ho + Hs + 2000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  have hvs_ch := vSendC_excessUB_le hk Ho Hs Hr hhk
    (Γ' := CryptoGames.SM.Engine.cGsTy vpT :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) chQ :: Γ')
    (CryptoGames.SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    ((CryptoGames.SM.Engine.modeCfgEC OO_cka mo).challMsgE
      (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
      (CryptoGames.SM.Engine.cGsB (CryptoGames.SM.Engine.esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))) (.snd (.snd (.snd (.snd .v1))))
  have hok_ch := modeCfgEC_challOKE_excessUB (O' := OO_cka) (ckaOpC B0) mo
    (Γ' := CryptoGames.SM.Engine.cGsTy vpT :: .prod (CryptoGames.SM.Engine.esTy vpT hsT) chQ :: Γ')
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
  simp only [modeCfgEC_challMsgE_excessUB, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.pGet,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_some, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hvs_ch hok_ch
  simp only [CryptoGames.SM.Engine.challEC, CryptoGames.SM.Engine.cEpMgmtE, CryptoGames.SM.Engine.cSafeChE,
    CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.cRecordE, CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    modeCfgEC_challMsgE_excessUB, optNatLit_excessUB, CryptoGames.SM.sendsInE, CryptoGames.SM.healedByE,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.posSender,
    CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v3, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_nil, exprExcessUB_add, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_cons,
    exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset, compExcessUB_ret,
    compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem corrEC_excessUB_le_priv {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L : ℕ) (π : CryptoGames.SM.Engine.Policy)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.corrEC hk L π es p) ≤
      30 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) p) + Ho + 1000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ_cr0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ'
  have hcd_cr := corrDoomE_excessUB (O' := OO_cka) (ckaOpC B0) π (Γ' := Γ_cr0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hrv_cr := hhk.reveal_le (Γ' := Γ_cr0)
    (CryptoGames.SM.Engine.esH (.fst .v0)) (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v0))) (.snd .v0))
  simp only [CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, exprExcessUB_v0, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_letE, Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hcd_cr hrv_cr
  simp only [CryptoGames.SM.Engine.corrEC, CryptoGames.SM.Engine.cCorrAllowedE, CryptoGames.SM.Engine.cCompContainsE,
    CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE, CryptoGames.SM.Engine.cAfterCorrE,
    CryptoGames.SM.Engine.leakDoomE, CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    optNatLit_excessUB, CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.orE, CryptoGames.SM.otherE,
    CryptoGames.SM.leN, CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1,
    exprExcessUB_v2, exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE,
    exprExcessUB_cons, exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem implEC_tight_compCostW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H Ho Hs Hr L qep maxSkip : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (hes : exprCostW (ckaOpC B0) es ≤ 10) (hq : exprCostW (ckaOpC B0) q ≤ 10) :
    compCostW (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.implEC hk L 3 qep maxSkip
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      3 * H + 2 * Ho + Hs + Hr + 18500 * L +
        L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
        2 * (maxSkip + 1) + 5 * bits qep + bits (mo.tL.getD 0) + 9 * bits mo.tStar + 39000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let Γ_base : List (Ty S_cka) := .prod esT smqT :: Γ'; let Γ_cr : List (Ty S_cka) := .bool :: Γ_base
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base; let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1; let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3; let Γ_ch : List (Ty S_cka) := chQ :: Γ_s3
  let cfg := CryptoGames.SM.Engine.modeCfgEC OO_cka mo
  let M := 3 * H + 2 * Ho + Hs + Hr + 18500 * L + L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
    2 * (maxSkip + 1) + 5 * bits qep + bits (mo.tL.getD 0) + 9 * bits mo.tStar + 38000
  have hpolL : mo.policy.tL = mo.tL := rfl; have hpolS : mo.policy.tStar = mo.tStar := rfl
  have htrC := transmitEC_cost_le_priv hk H L qep mo.policy hhkC (Γ' := Γ_tr) (.fst .v4) .v0
  have htrE := transmitEC_excessUB_le_priv hk Ho Hs Hr L qep mo.policy hhkE (Γ' := Γ_tr) (.fst .v4) .v0
  have hchC := challEC_cost_le_priv hk H L qep mo mo.policy hhkC (Γ' := Γ_ch) (.fst .v4) .v0
  have hchE := challEC_excessUB_le_priv hk Ho Hs Hr L qep mo hhkE (Γ' := Γ_ch) (.fst .v4) .v0
  have hdlC := DFProgBucketBounds.deliverEC_any_cost_le hk H L maxSkip cfg hhkC (Γ' := Γ_dl) (.fst .v3) .v0
  have hdlE := DFProgBucketBounds.deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip cfg hhkE (Γ' := Γ_dl) (.fst .v3) .v0
  have hijC := DFProgBucketBounds.injectEC_anyCfg_cost_le hk H L 3 qep (bits mo.tStar + 6) (by omega) cfg
    (fun e => (modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo e).trans (by omega)) hhkC
    (Γ' := Γ_ij) (.fst .v2) .v0
  have hijE := DFProgBucketBounds.injectEC_anyCfg_excessUB_le hk Ho Hs Hr L 3 qep cfg
    (fun e => by have := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo e; dsimp only [cfg]; omega) hhkE
    (Γ' := Γ_ij) (.fst .v2) .v0
  have hcrC := corrEC_cost_le_priv hk H L mo.policy hhkC (Γ' := Γ_cr) (.fst .v1) .v0
  have hcrE := corrEC_excessUB_le_priv hk Ho Hs Hr L mo.policy hhkE (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [hpolL, hpolS, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Expr.cost, Nat.reduceAdd]
    at htrC hchC hdlC hijC hcrC
  simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_fst, Nat.add_zero, Nat.mul_zero, Nat.zero_add]
    at htrE hchE hdlE hijE hcrE
  dsimp only [CryptoGames.SM.Engine.implEC]
  refine (priv_compCostW_bind_ret_le _ _ (ce := 25) (ck := M + 100) ?_ ?_).trans (by dsimp only [M]; omega)
  · simp only [exprCostW]; omega
  refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 80) ?_ ?_ ?_).trans (by omega)
  · simp [exprCostW]
  · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 60) ?_ ?_ ?_).trans (by omega)
    · simp [exprCostW]
    · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 40) ?_ ?_ ?_).trans (by omega)
      · simp [exprCostW]
      · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 20) ?_ ?_ ?_).trans (by omega)
        · simp [exprCostW]
        · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
          · exact compCostW_le_of_parts htrC htrE (by dsimp only [M]; omega)
          · simp [compCostW, exprCostW]
        · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
          · exact compCostW_le_of_parts hchC hchE (by dsimp only [M]; omega)
          · simp [compCostW, exprCostW]
      · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
        · exact compCostW_le_of_parts hdlC hdlE (by dsimp only [M]; omega)
        · simp [compCostW, exprCostW]
    · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
      · exact compCostW_le_of_parts hijC hijE (by dsimp only [M]; omega)
      · simp [compCostW, exprCostW]
  · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
    · exact compCostW_le_of_parts hcrC hcrE (by dsimp only [M]; omega)
    · simp [compCostW, exprCostW]

private theorem cAfterCorrShiftedE_cost_le_cAfterCorrE {O' : Ops S_cka}
    {vpT : Ty S_cka} (L l : ℕ) {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cAfterCorrShiftedE L l s p).cost ≤
      (CryptoGames.SM.Engine.cAfterCorrE L s p).cost + 36 * bits l + 650 := by
  have hl1 := bits_mono (Nat.sub_le l 1)
  have hb1 : bits 1 = 1 := rfl
  simp only [CryptoGames.SM.Engine.cAfterCorrShiftedE, CryptoGames.SM.Engine.cAfterCorrE,
    CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cLeakE,
    CryptoGames.SM.maxOptE, CryptoGames.SM.maxN, CryptoGames.SM.leN, CryptoGames.SM.boolEq,
    CryptoGames.SM.otherE, CryptoGames.SM.pGet, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.posSender, CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx,
    CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall,
    CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
    Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private theorem leakDoomE_cost_le_add {O' : Ops S_cka}
    {vpT : Ty S_cka} (L : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (g g₁ g₂ : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) {d : ℕ} (h : g₁.cost ≤ g₂.cost + d) :
    (CryptoGames.SM.Engine.leakDoomE L π g g₁).cost ≤
      (CryptoGames.SM.Engine.leakDoomE L π g g₂).cost + d := by
  simp only [CryptoGames.SM.Engine.leakDoomE, Expr.cost]; omega

private theorem corrECShifted_cost_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    (CryptoGames.SM.Engine.corrECShifted hk L l π es p).cost ≤
      (CryptoGames.SM.Engine.corrEC hk L π es p).cost + 72 * bits l + 1300 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hac0 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_add (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (.fst .v0))
    (CryptoGames.SM.Engine.cAfterCorrShiftedE L l (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0))
    (CryptoGames.SM.Engine.cAfterCorrE L (CryptoGames.SM.Engine.esG (.fst .v0)) (.snd .v0))
    (Nat.add_assoc _ _ _ ▸ hac0)
  have hac1 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [CryptoGames.SM.Engine.corrECShifted, CryptoGames.SM.Engine.corrEC,
    CryptoGames.SM.orE, CryptoGames.SM.Engine.esMk, Comp.cost, Expr.cost]; omega

private theorem add_eq_both {a1 a2 b1 b2 : ℕ} (ha : a1 = a2) (hb : b1 = b2) :
    a1 + b1 + 1 = a2 + b2 + 1 := by omega
private theorem max_eq_right {a1 a2 b c1 c2 : ℕ} (ha : a1 = a2) (hc : c1 = c2) :
    a1 + max b c1 + 1 = a2 + max b c2 + 1 := by omega
private theorem cEpMgmtE_cost_2_eq_3 {O' : Ops S_cka} {vpT : Ty S_cka} {Γ'} (qep : ℕ)
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p bad : Expr O' Γ' .bool) :
    (CryptoGames.SM.Engine.cEpMgmtE 2 qep s p bad).cost =
      (CryptoGames.SM.Engine.cEpMgmtE 3 qep s p bad).cost := rfl
private theorem cSafeCh_or_cost_2_eq_3 {O' : Ops S_cka} {vpT : Ty S_cka} {Γ'}
    (s : Expr O' Γ' (CryptoGames.SM.Engine.cGsTy vpT)) (p b : Expr O' Γ' .bool) :
    (CryptoGames.SM.orE (.not (CryptoGames.SM.Engine.cSafeChE 2 s p)) b).cost =
      (CryptoGames.SM.orE (.not (CryptoGames.SM.Engine.cSafeChE 3 s p)) b).cost := rfl

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem corrECShiftedPaper_excessUB_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l : ℕ) (π : CryptoGames.SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.corrECShiftedPaper hk L l π es p) =
      compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.corrEC hk L π es p) := by
  cases π.auth <;>
  simp only [CryptoGames.SM.Engine.corrECShiftedPaper, CryptoGames.SM.Engine.corrEC,
    ↓reduceIte, Bool.false_eq_true,
    CryptoGames.SM.Engine.cCorrAllowedPaperE, CryptoGames.SM.Engine.cCorrAllowedE,
    CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cCompInsertE, CryptoGames.SM.Engine.cCompSetE,
    CryptoGames.SM.Engine.cAfterCorrShiftedE, CryptoGames.SM.Engine.cAfterCorrE, CryptoGames.SM.Engine.leakDoomE,
    CryptoGames.SM.Engine.corrDoomE, CryptoGames.SM.Engine.cLeakE, CryptoGames.SM.Engine.esMk,
    CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
    CryptoGames.SM.Engine.esSetAbort, CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
    CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
    CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
    CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
    CryptoGames.SM.pGet, CryptoGames.SM.pSet, CryptoGames.SM.orE, CryptoGames.SM.otherE, CryptoGames.SM.leN,
    CryptoGames.SM.maxN, CryptoGames.SM.maxOptE, CryptoGames.SM.ltOptE, CryptoGames.SM.boolEq,
    CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, optNatLit_excessUB,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none,
    exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_cons, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_foldrB, exprExcessUB_tget,
    exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem injectECGen_excessUB_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L Δ qep tStar : ℕ) (cfg : CryptoGames.SM.Engine.ConfigEC OO_cka) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool ckaHdrCtT)) :
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.injectECGen b1 hk L Δ qep tStar cfg es arg) =
      compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.injectEC hk L 3 qep cfg es arg) := by
  cases b1 <;>
    simp only [CryptoGames.SM.Engine.injectECGen, CryptoGames.SM.Engine.injectEC, CryptoGames.SM.Engine.injectECB1,
      Bool.false_eq_true, ↓reduceIte, CryptoGames.SM.Engine.cSafeInjE, CryptoGames.SM.Engine.cCompContainsE,
      CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.cTrivialB1E, CryptoGames.SM.Engine.esMk,
      CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH, CryptoGames.SM.Engine.esAbort,
      CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsSetWin,
      CryptoGames.SM.Engine.cGsSt, CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin,
      CryptoGames.SM.Engine.cGsEpoch, CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL,
      CryptoGames.SM.Engine.cGsTrans, CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp,
      CryptoGames.SM.Engine.cGsMaxAcc, CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs,
      CryptoGames.SM.Engine.cRecPos, CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
      CryptoGames.SM.otherE, CryptoGames.SM.leN, CryptoGames.SM.minN, CryptoGames.SM.healedByE,
      CryptoGames.SM.posEq, CryptoGames.SM.boolEq, CryptoGames.SM.posSender, CryptoGames.SM.posEpoch,
      CryptoGames.SM.posIdx, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      Nat.add_zero, Nat.zero_add, Nat.mul_zero]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem implECShiftedPaperGen_tight_compCostW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H Ho Hs Hr L l Δ qep maxSkip tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2))
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E))
    (hes : exprCostW (ckaOpC B0) es ≤ 10) (hq : exprCostW (ckaOpC B0) q ≤ 10) :
    compCostW (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.implECShiftedPaperGen b1 hk L l Δ qep maxSkip tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      3 * H + 2 * Ho + Hs + Hr + 18500 * L +
        L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
        2 * (maxSkip + 1) + 5 * bits qep + bits (mo.tL.getD 0) + 9 * bits mo.tStar +
        72 * bits l + bits tStar + 41000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := CryptoGames.SM.Engine.esTy vpT hsT
  let smqT := CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool ckaHdrCtT
  let Γ_base : List (Ty S_cka) := .prod esT smqT :: Γ'; let Γ_cr : List (Ty S_cka) := .bool :: Γ_base
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base; let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1; let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3; let Γ_ch : List (Ty S_cka) := chQ :: Γ_s3
  let M := 3 * H + 2 * Ho + Hs + Hr + 18500 * L + L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
    2 * (maxSkip + 1) + 5 * bits qep + bits (mo.tL.getD 0) + 9 * bits mo.tStar + 72 * bits l + bits tStar + 40000
  have hpolL : mo.policy.tL = mo.tL := rfl; have hpolS : mo.policy.tStar = mo.tStar := rfl
  have htrC3 := transmitEC_cost_le_priv hk H L qep mo.policy hhkC (Γ' := Γ_tr) (.fst .v4) .v0
  have htrE3 := transmitEC_excessUB_le_priv hk Ho Hs Hr L qep mo.policy hhkE (Γ' := Γ_tr) (.fst .v4) .v0
  have hchC3 := challEC_cost_le_priv hk H L qep mo mo.policy hhkC (Γ' := Γ_ch) (.fst .v4) .v0
  have hchE3 := challEC_excessUB_le_priv hk Ho Hs Hr L qep mo hhkE (Γ' := Γ_ch) (.fst .v4) .v0
  have hdlC := DFProgBucketBounds.deliverEC_any_cost_le hk H L maxSkip (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) hhkC (Γ' := Γ_dl) (.fst .v3) .v0
  have hdlE := DFProgBucketBounds.deliverEC_any_excessUB_le hk Ho Hs Hr L maxSkip (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) hhkE (Γ' := Γ_dl) (.fst .v3) .v0
  have hijC3 := DFProgBucketBounds.injectEC_anyCfg_cost_le hk H L 3 qep (bits mo.tStar + 6) (by omega)
    (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (fun e => (modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo e).trans (by omega)) hhkC (Γ' := Γ_ij) (.fst .v2) .v0
  have hijE3 := DFProgBucketBounds.injectEC_anyCfg_excessUB_le hk Ho Hs Hr L 3 qep
    (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (fun e => by have := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo e; omega) hhkE (Γ' := Γ_ij) (.fst .v2) .v0
  have hcrC3 := corrEC_cost_le_priv hk H L mo.policy hhkC (Γ' := Γ_cr) (.fst .v1) .v0
  have hcrE3 := corrEC_excessUB_le_priv hk Ho Hs Hr L mo.policy hhkE (Γ' := Γ_cr) (.fst .v1) .v0
  have hcrC0 := CryptoGames.SM.Engine.corrECShiftedPaper_cost_le hk L l mo.policy (Γ' := Γ_cr) (.fst .v1) .v0
  have hcrC1 := corrECShifted_cost_le_corrEC hk L l mo.policy (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [hpolL, hpolS, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Expr.cost, Nat.reduceAdd] at htrC3 hchC3 hdlC hijC3 hcrC3
  simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_fst, Nat.add_zero, Nat.mul_zero, Nat.zero_add] at htrE3 hchE3 hdlE hijE3 hcrE3
  have htrE : compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.transmitEC hk L Δ qep mo.policy (Γ' := Γ_tr) (.fst .v4) .v0) =
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.transmitEC hk L 3 qep mo.policy (Γ' := Γ_tr) (.fst .v4) .v0) := rfl
  have hchE : compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.challEC hk L Δ qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := Γ_ch) (.fst .v4) .v0) =
    compExcessUB (ckaOpC B0) sC qC (CryptoGames.SM.Engine.challEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy (Γ' := Γ_ch) (.fst .v4) .v0) := rfl
  have hcrE := corrECShiftedPaper_excessUB_eq (B0 := B0) (sC := sC) (qC := qC) hk L l mo.policy (Γ' := Γ_cr) (.fst .v1) .v0
  have hijE := injectECGen_excessUB_eq (B0 := B0) (sC := sC) (qC := qC) b1 hk L Δ qep tStar (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := Γ_ij) (.fst .v2) .v0
  have htrchijC :
      (CryptoGames.SM.Engine.transmitEC hk L Δ qep mo.policy (Γ' := Γ_tr) (.fst .v4) .v0).cost ≤
        (CryptoGames.SM.Engine.transmitEC hk L 3 qep mo.policy (Γ' := Γ_tr) (.fst .v4) .v0).cost ∧
      (CryptoGames.SM.Engine.challEC hk L Δ qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo)
        mo.policy (Γ' := Γ_ch) (.fst .v4) .v0).cost ≤
        (CryptoGames.SM.Engine.challEC hk L 3 qep (CryptoGames.SM.Engine.modeCfgEC OO_cka mo)
          mo.policy (Γ' := Γ_ch) (.fst .v4) .v0).cost ∧
      (CryptoGames.SM.Engine.injectECGen b1 hk L Δ qep tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := Γ_ij) (.fst .v2) .v0).cost ≤
        (CryptoGames.SM.Engine.injectEC hk L 3 qep
          (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := Γ_ij) (.fst .v2) .v0).cost +
          (bits tStar + 81) := by
    rcases hbΔ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨le_rfl, le_rfl, Nat.le_add_right _ _⟩
    · refine ⟨le_of_eq ?_, le_of_eq ?_,
        CryptoGames.SM.Engine.injectECB1_cost_le_injectEC hk L qep tStar
          (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) (Γ' := Γ_ij) (.fst .v2) .v0⟩
      · dsimp only [CryptoGames.SM.Engine.transmitEC, Comp.cost]
        with_reducible apply add_eq_both rfl
        with_reducible apply max_eq_right rfl
        with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
        with_reducible apply max_eq_right rfl
        with_reducible apply add_eq_both rfl
        with_reducible apply max_eq_right rfl
        rfl
      · dsimp only [CryptoGames.SM.Engine.challEC, Comp.cost]
        with_reducible apply add_eq_both rfl
        with_reducible apply max_eq_right rfl
        with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
        with_reducible apply max_eq_right (cSafeCh_or_cost_2_eq_3 _ _ _)
        with_reducible apply max_eq_right rfl
        with_reducible apply add_eq_both rfl
        with_reducible apply max_eq_right rfl
        rfl
  rcases htrchijC with ⟨htrC, hchC, hijC⟩
  dsimp only [CryptoGames.SM.Engine.implECShiftedPaperGen]
  refine (priv_compCostW_bind_ret_le _ _ (ce := 25) (ck := M + 100) ?_ ?_).trans (by dsimp only [M]; omega)
  · simp only [exprCostW]; omega
  refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 80) ?_ ?_ ?_).trans (by omega)
  · simp [exprCostW]
  · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 60) ?_ ?_ ?_).trans (by omega)
    · simp [exprCostW]
    · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 40) ?_ ?_ ?_).trans (by omega)
      · simp [exprCostW]
      · refine (priv_compCostW_caseSum_le _ _ _ (cs := 5) (m := M + 20) ?_ ?_ ?_).trans (by omega)
        · simp [exprCostW]
        · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
          · exact compCostW_le_of_parts (htrC.trans htrC3) ((le_of_eq htrE).trans htrE3) (by dsimp only [M]; omega)
          · simp [compCostW, exprCostW]
        · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
          · exact compCostW_le_of_parts (hchC.trans hchC3) ((le_of_eq hchE).trans hchE3) (by dsimp only [M]; omega)
          · simp [compCostW, exprCostW]
      · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
        · exact compCostW_le_of_parts hdlC hdlE (by dsimp only [M]; omega)
        · simp [compCostW, exprCostW]
    · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
      · exact compCostW_le_of_parts (hijC.trans (Nat.add_le_add_right hijC3 (bits tStar + 81)))
          ((le_of_eq hijE).trans hijE3) (by dsimp only [M]; omega)
      · simp [compCostW, exprCostW]
  · refine (priv_compCostW_bind_le _ _ (cc := M) (ck := 15) ?_ ?_).trans (by omega)
    · exact compCostW_le_of_parts
        ((hcrC0.trans hcrC1).trans (Nat.add_le_add_right (Nat.add_le_add_right hcrC3 (72 * bits l)) 1300))
        ((le_of_eq hcrE).trans hcrE3) (by dsimp only [M]; omega)
    · simp [compCostW, exprCostW]

private theorem hdrEqE_cost_le {Γ'} (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    (CryptoGames.SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    Expr.cost, v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]
  omega

private theorem deliverForgeEC_cost_le_local {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    {Γ'} (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L + bits qep + bits mo.tStar + 4210 := by
  have hqep1 := bits_succ_le qep
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 : List (Ty S_cka) := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (.fst .v1)) (CryptoGames.SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (CryptoGames.SM.Engine.esH (.fst .v1))
    (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2)
    (CryptoGames.SM.Engine.esG (.fst .v4)) (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd] at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [CryptoGames.SM.Engine.deliverForgeEC, CryptoGames.SM.orE, CryptoGames.SM.isSomeE,
    CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.esMk, CryptoGames.SM.posEpoch, cRecPos_cost,
    esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost, Comp.cost, Expr.cost,
    v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]
  omega

private theorem deliverForgeECGen_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H L Δ qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode) (hhk : HooksCostBounded hk H)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2)) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        bits qep + bits mo.tStar + bits tStar + 4300 := by
  have hdf := deliverForgeEC_cost_le_local hk H L qep mo hhk es arg
  rcases hbΔ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [CryptoGames.SM.Engine.deliverForgeECGen, Bool.false_eq_true, ↓reduceIte]; omega
  · have hb := CryptoGames.SM.Engine.deliverForgeECB1_cost_le_deliverForgeEC hk L qep tStar
      (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg
    simp only [CryptoGames.SM.Engine.deliverForgeECGen, ↓reduceIte]; omega

private theorem hdrEqE_excessUB_le (B0 : ℕ) {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' ckaHdrCtT) :
    exprExcessUB (ckaOpC B0) (CryptoGames.SM.Engine.hdrEqE c₁ c₂) ≤
      exprExcessUB (ckaOpC B0) c₁ + exprExcessUB (ckaOpC B0) c₂ + 300 := by
  simp only [CryptoGames.SM.Engine.hdrEqE, CryptoGames.SM.Engine.optTEqE, CryptoGames.CKA.ckaOps,
    ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_bool, exprExcessUB_eqN,
    exprExcessUB_and, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, Nat.add_zero, Nat.zero_add]
  omega

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
private theorem deliverForgeECGen_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L Δ qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT))) :
    compExcessUB (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) arg) +
        2 * Ho + Hr + 500 * L + 2000 := by
  let vpT := @CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 := .prod (CryptoGames.SM.Engine.esTy vpT hsT) (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := CryptoGames.SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_excessUB (vpT := vpT) B0 L (Γ' := Γ0)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v0)) (CryptoGames.SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_excessUB (vpT := vpT) B0 L (Γ' := Γ1)
    (CryptoGames.SM.Engine.esG (O' := OO_cka) (.fst .v1)) (CryptoGames.SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hhe1 := hdrEqE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT)
    (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ1)
    (.fst (.snd (.snd (Expr.v1 (O := OO_cka))))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ1)
    (CryptoGames.SM.Engine.esH (.fst .v1)) (CryptoGames.SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have hcm := commitEC_excessUB_le hk Ho Hs Hr L hhk (Γ' := Γ2)
    (CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2)) (CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (CryptoGames.SM.pGet (CryptoGames.SM.Engine.cGsSt (CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (CryptoGames.SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
    CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetH, CryptoGames.SM.Engine.cGsSt,
    CryptoGames.SM.pGet, CryptoGames.SM.otherE, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2,
    exprExcessUB_v4, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair,
    exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero] at hit0 hit1 hhe1 hvr hcm hij
  cases b1 <;>
    simp only [CryptoGames.SM.Engine.deliverForgeECGen, CryptoGames.SM.Engine.deliverForgeEC,
      CryptoGames.SM.Engine.deliverForgeECB1, Bool.false_eq_true, ↓reduceIte,
      CryptoGames.SM.Engine.cCompContainsE, CryptoGames.SM.Engine.cTrivialE, CryptoGames.SM.Engine.cTrivialB1E,
      CryptoGames.SM.Engine.esMk, CryptoGames.SM.Engine.esG, CryptoGames.SM.Engine.esH,
      CryptoGames.SM.Engine.esAbort, CryptoGames.SM.Engine.esSetG, CryptoGames.SM.Engine.esSetH,
      CryptoGames.SM.Engine.cGsMk, CryptoGames.SM.Engine.cGsSetWin, CryptoGames.SM.Engine.cGsSt,
      CryptoGames.SM.Engine.cGsB, CryptoGames.SM.Engine.cGsWin, CryptoGames.SM.Engine.cGsEpoch,
      CryptoGames.SM.Engine.cGsIdx, CryptoGames.SM.Engine.cGsTL, CryptoGames.SM.Engine.cGsTrans,
      CryptoGames.SM.Engine.cGsChall, CryptoGames.SM.Engine.cGsComp, CryptoGames.SM.Engine.cGsMaxAcc,
      CryptoGames.SM.Engine.cGsLeaks, CryptoGames.SM.Engine.cGsCorrs, CryptoGames.SM.Engine.cRecPos,
      CryptoGames.SM.pGet, CryptoGames.SM.orE, CryptoGames.SM.isSomeE, CryptoGames.SM.otherE,
      CryptoGames.SM.leN, CryptoGames.SM.healedByE, CryptoGames.SM.posEq, CryptoGames.SM.boolEq,
      CryptoGames.SM.posSender, CryptoGames.SM.posEpoch, CryptoGames.SM.posIdx, exprExcessUB_v0,
      exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_unit,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_add, exprExcessUB_lt,
      exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_anyB, exprExcessUB_tget, compExcessUB_ret,
      compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt, Nat.add_zero, Nat.zero_add, Nat.mul_zero] <;>
    omega

private theorem deliverForgeECGen_tight_compCostW_le_pure {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (b1 : Bool) (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H Ho Hs Hr L Δ qep tStar : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2)) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)))
    (hesC : es.cost ≤ 10) (hargC : arg.cost ≤ 10)
    (hesE : exprExcessUB (ckaOpC B0) es = 0) (hargE : exprExcessUB (ckaOpC B0) arg = 0) :
    compCostW (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.deliverForgeECGen b1 hk L Δ qep tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      3 * H + 2 * Ho + Hr + 1150 * L + bits qep + bits mo.tStar + bits tStar + 7200 := by
  have hC := deliverForgeECGen_cost_le b1 hk H L Δ qep tStar mo hhkC hbΔ es arg
  have hE := deliverForgeECGen_excessUB_le b1 hk Ho Hs Hr L Δ qep tStar mo hhkE es arg
  exact compCostW_le_of_parts hC hE (by omega)

private theorem deliverForgeEC_tight_compCostW_le_pure {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ}
    {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (H Ho Hs Hr L qep : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (hhkC : HooksCostBounded hk H)
    (hhkE : HooksExcessBounded B0 sC qC hk Ho Hs Hr) {Γ'}
    (es : Expr OO_cka Γ' (CryptoGames.SM.Engine.esTy
      (@CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod ckaHdrCtT ckaHdrCtT)))
    (hesC : es.cost ≤ 10) (hargC : arg.cost ≤ 10)
    (hesE : exprExcessUB (ckaOpC B0) es = 0) (hargE : exprExcessUB (ckaOpC B0) arg = 0) :
    compCostW (ckaOpC B0) sC qC
      (CryptoGames.SM.Engine.deliverForgeEC hk L 3 qep
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) es arg) ≤
      3 * H + 2 * Ho + Hr + 1150 * L + bits qep + 2 * bits mo.tStar + 7200 := by
  have h := deliverForgeECGen_tight_compCostW_le_pure false hk H Ho Hs Hr L 3 qep mo.tStar mo
    hhkC hhkE (Or.inl ⟨rfl, rfl⟩) es arg hesC hargC hesE hargE
  simp only [CryptoGames.SM.Engine.deliverForgeECGen, Bool.false_eq_true, ↓reduceIte] at h
  omega

theorem implECDF_multi_compCostW_le
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)}
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.base .sig)
      (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mHsTy)
    (q qepC : ℕ) (mo : CryptoGames.SM.Construction.Mode)
    (htStar : mo.tStar ≤ qepC + 3) (htL : mo.tL.getD 0 ≤ qepC + 3)
    {qC : I'.Tag → ℕ}
    (hhkC : HooksCostBounded hk
      (1400 * (q + 1) + 2 * bits mo.tStar + 2 * bits mo.tH +
        ((q + 1) * (maxForwardJumps + 1) + 1) + 3000))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (3350 * (q + 1) + 6 * bits (qepC + 1) + 10 * ((q + 1) * (maxForwardJumps + 1)) + 53000)
      (9000 * (q + 1) + 18 * bits (qepC + 1) + 30 * ((q + 1) * (maxForwardJumps + 1)) + 4820000)
      (14000 * (q + 1) + 18 * bits (qepC + 1) + 50 * ((q + 1) * (maxForwardJumps + 1)) +
        3 * bits ((q + 1) * (maxForwardJumps + 1)) + 9800000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDF hk (q + 1) 3 qepC maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := [mEsTy, CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qepC := by
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let H := 1400 * L + 2 * bits mo.tStar + 2 * bits mo.tH + (B0 + 1) + 3000
  let Ho := 3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000
  let Hs := 9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000
  let Hr := 14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000
  let w1 := 3 * H + 2 * Ho + Hs + Hr + 18500 * L +
    L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
    2 * (maxForwardJumps + 1) + 5 * bits qepC + bits (mo.tL.getD 0) +
    9 * bits mo.tStar + 72 * bits 0 + bits mo.tStar + 41000
  let w2 := 3 * H + 2 * Ho + Hr + 1150 * L + bits qepC + 2 * bits mo.tStar + 7200
  dsimp only [CryptoGames.SM.Engine.implECDF]
  have hOut : compCostW (ckaOpC B0) ckaSampC qC
      (CryptoGames.SM.Engine.implECDF hk L 3 qepC maxForwardJumps
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := [mEsTy, CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1) ≤
      max w1 w2 + 30 := by
    dsimp only [CryptoGames.SM.Engine.implECDF]
    refine outer_df_compCostW_le (O' := OO_cka) (ckaOpC B0) ckaSampC qC _ _ _ _ ?_ ?_ ?_ ?_
    · exact (implEC_tight_compCostW_le hk H Ho Hs Hr L qepC maxForwardJumps mo hhkC hhkE
        (.fst .v1) .v0 (by simp [exprCostW]) (by simp)).trans (by dsimp only [w1]; omega)
    · simp [compCostW, exprCostW]
    · exact deliverForgeEC_tight_compCostW_le_pure hk H Ho Hs Hr L qepC mo hhkC hhkE
        (.fst .v1) .v0 (by simp [Expr.cost]) (by simp)
        (by simp [exprExcessUB_fst, exprExcessUB_v1]) (by simp [exprExcessUB_v0])
    · simp [compCostW, exprCostW]
  exact (Nat.add_le_add_right hOut 200000).trans
    (df_multi_step_arith q qepC 0 mo mo htStar htL htStar htL (Nat.zero_le _))

theorem implECDFShiftedPaperGen_multi_compCostW_le
    {ι : Type} {TSpec : OracleSpec.{0, 0} ι} {I' : Iface S_cka (unifSpec + TSpec)}
    (b1 : Bool)
    (hk : CryptoGames.SM.Engine.HooksC OO_cka I' (.base .γ) (.base .sig)
      (.sum (.base .ss) .nat) (.sum (.base .rs) .nat) mHsTy)
    (q qepC l Δ : ℕ) (moHk mo : CryptoGames.SM.Construction.Mode)
    (hbΔ : (b1 = false ∧ Δ = 3) ∨ (b1 = true ∧ Δ = 2))
    (htStarHk : moHk.tStar ≤ qepC + 3) (htLHk : moHk.tL.getD 0 ≤ qepC + 3)
    (htStar : mo.tStar ≤ qepC + 3) (htL : mo.tL.getD 0 ≤ qepC + 3) (hl : l ≤ qepC + 3)
    {qC : I'.Tag → ℕ}
    (hhkC : HooksCostBounded hk
      (1400 * (q + 1) + 2 * bits moHk.tStar + 2 * bits moHk.tH +
        ((q + 1) * (maxForwardJumps + 1) + 1) + 3000))
    (hhkE : HooksExcessBounded ((q + 1) * (maxForwardJumps + 1)) ckaSampC qC hk
      (3350 * (q + 1) + 6 * bits (qepC + 1) + 10 * ((q + 1) * (maxForwardJumps + 1)) + 53000)
      (9000 * (q + 1) + 18 * bits (qepC + 1) + 30 * ((q + 1) * (maxForwardJumps + 1)) + 4820000)
      (14000 * (q + 1) + 18 * bits (qepC + 1) + 50 * ((q + 1) * (maxForwardJumps + 1)) +
        3 * bits ((q + 1) * (maxForwardJumps + 1)) + 9800000)) :
    compCostW (ckaOpC ((q + 1) * (maxForwardJumps + 1))) ckaSampC qC
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen b1 hk (q + 1) l Δ qepC maxForwardJumps mo.tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := [mEsTy, CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1) + 200000 ≤
      fig8AtomicStepBound q qepC := by
  let L := q + 1
  let B0 := (q + 1) * (maxForwardJumps + 1)
  let H := 1400 * L + 2 * bits moHk.tStar + 2 * bits moHk.tH + (B0 + 1) + 3000
  let Ho := 3350 * L + 6 * bits (qepC + 1) + 10 * B0 + 53000
  let Hs := 9000 * L + 18 * bits (qepC + 1) + 30 * B0 + 4820000
  let Hr := 14000 * L + 18 * bits (qepC + 1) + 50 * B0 + 3 * bits B0 + 9800000
  let w1 := 3 * H + 2 * Ho + Hs + Hr + 18500 * L +
    L * (bits (mo.tL.getD 0) + 2 * bits mo.tStar + 40) +
    2 * (maxForwardJumps + 1) + 5 * bits qepC + bits (mo.tL.getD 0) +
    9 * bits mo.tStar + 72 * bits l + bits mo.tStar + 41000
  let w2 := 3 * H + 2 * Ho + Hr + 1150 * L + bits qepC + 2 * bits mo.tStar + 7200
  have hOut : compCostW (ckaOpC B0) ckaSampC qC
      (CryptoGames.SM.Engine.implECDFShiftedPaperGen b1 hk L l Δ qepC maxForwardJumps mo.tStar
        (CryptoGames.SM.Engine.modeCfgEC OO_cka mo) mo.policy
        (Γ' := [mEsTy, CryptoGames.CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1) ≤
      max w1 w2 + 30 := by
    dsimp only [CryptoGames.SM.Engine.implECDFShiftedPaperGen]
    refine outer_df_compCostW_le (O' := OO_cka) (ckaOpC B0) ckaSampC qC _ _ _ _ ?_ ?_ ?_ ?_
    · exact implECShiftedPaperGen_tight_compCostW_le b1 hk H Ho Hs Hr L l Δ qepC
        maxForwardJumps mo.tStar mo hbΔ hhkC hhkE (.fst .v1) .v0
        (by simp [exprCostW]) (by simp)
    · simp [compCostW, exprCostW]
    · exact (deliverForgeECGen_tight_compCostW_le_pure b1 hk H Ho Hs Hr L Δ qepC mo.tStar mo
        hhkC hhkE hbΔ (.fst .v1) .v0 (by simp [Expr.cost]) (by simp)
        (by simp [exprExcessUB_fst, exprExcessUB_v1]) (by simp [exprExcessUB_v0])).trans
        (by dsimp only [w2]; omega)
    · simp [compCostW, exprCostW]
  exact (Nat.add_le_add_right hOut 200000).trans
    (df_multi_step_arith q qepC l moHk mo htStarHk htLHk htStar htL hl)

end

end Computational.Proofs.SessionCostedFig8.DFProgFsStage2DeliverCost
