/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8WeightedParts -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Weighted Step-Cost (`compCostW`) and AST-Size (`compSizeW`) Bounds for `redPRNGAuthBucketHybridProg`-/

namespace Computational.Proofs.SessionCostedFig8.BucketPRNGProgBounds

public section

set_option autoImplicit false

open _root_.ReductionDsl (Sig Ty Var Ops Iface Expr Comp bits reductionSizeBudget)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.LibsignalSession (maxForwardJumps)
open _root_.CryptoGames.SM.Construction (Header healEpoch prngVpTy prngHsTy bucketAuthCfgEC
  abortedPartiesE)
open _root_.CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW exprCostW_rename
  compCostW_rename)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC prngQueryC)
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (bits_le_bits_qep_add targetsL_bounds)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound bits_le_add_one)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_succ_le)
open Computational.Proofs.SessionCostedFig8.Bundles (exprSizeW compSizeW exprSizeW_renameM
  compSizeW_renameM ckaOpS ckaSampS ckaQueryS)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (HooksSizeBounded HooksSizeBounded.mono
  bits_B0_le_ratchetCostBudget bits_le_ratchetCostBudget_of_le_linear
  bits_qep_le_ratchetCostBudget bits_zero bits_one bits_two bits_three bits_four
  optNatLit_sizeW vSendC_sizeW_le vRecvC_sizeW_le commitEC_sizeW_le cInTransitE_sizeW_le
  size_le_ratchetSizeBudget
  compSizeW_bind compSizeW_ite compSizeW_ret compSizeW_sample
  compSizeW_caseOpt compSizeW_caseSum compSizeW_query
  exprSizeW_v0 exprSizeW_v1 exprSizeW_v2 exprSizeW_v3 exprSizeW_v4
  exprSizeW_v5 exprSizeW_v6 exprSizeW_v7 exprSizeW_var
  exprSizeW_unit exprSizeW_bool exprSizeW_nat exprSizeW_none exprSizeW_nil
  exprSizeW_add exprSizeW_sub exprSizeW_mulK exprSizeW_divK exprSizeW_modK
  exprSizeW_lt exprSizeW_eqN exprSizeW_not exprSizeW_and exprSizeW_ite
  exprSizeW_pair exprSizeW_fst exprSizeW_snd exprSizeW_inl exprSizeW_inr
  exprSizeW_some exprSizeW_caseOpt exprSizeW_caseSum exprSizeW_letE
  exprSizeW_op exprSizeW_cons exprSizeW_len exprSizeW_take
  exprSizeW_appendL exprSizeW_findB exprSizeW_anyB exprSizeW_mapB
  exprSizeW_foldrB exprSizeW_tconst exprSizeW_tget exprSizeW_tset)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (
  pbaTableEntryTy prngBucketAuthHsTy prngBucketAuthEsTy prngBucketAuthRedEsTy
  prngBucketAuthStage2RedEsTy postLeakBucketE pbaHsCache pbaHsFTbl pbaHsCorrRoot
  pbaHsEmptyE pbaHsSetCache pbaHsSetFTblAt pbaHsSetCorrRoot resolveCorrRootE
  pbaTableLookupE lookupPRNGBucketAuthFC rootPRNGBucketAuthHybridC
  prngBucketAuthStartSendC prngBucketAuthStartRecvC prngBucketAuthFsSendC
  prngBucketAuthFsRecvC prngBucketAuthCommitC prngBucketAuthRevealC
  hooksPRNGBucketAuthC isHonestHdrPRNGBucketE prngBucketAuthMainStartRecvC
  prngBucketAuthForgedHdrRevealC hooksPRNGBucketAuthMainC hooksPRNGBucketAuthForgedHdrC
  initPRNGBucketAuthEStateC redPRNGAuthBucketHybridProg)

@[local simp] private theorem exprCostW_var {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (v : Var Γ t) : exprCostW opC (.var v) = 1 := rfl
@[local simp] private theorem exprCostW_v0 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {t : Ty S} {Γ : List (Ty S)} : exprCostW opC (.v0 : Expr O (t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v1 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a t : Ty S} {Γ : List (Ty S)} : exprCostW opC (.v1 : Expr O (a :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v2 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b t : Ty S} {Γ : List (Ty S)} : exprCostW opC (.v2 : Expr O (a :: b :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v3 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b c t : Ty S} {Γ : List (Ty S)} :
    exprCostW opC (.v3 : Expr O (a :: b :: c :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v4 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b c d t : Ty S} {Γ : List (Ty S)} :
    exprCostW opC (.v4 : Expr O (a :: b :: c :: d :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v5 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b c d e t : Ty S} {Γ : List (Ty S)} :
    exprCostW opC (.v5 : Expr O (a :: b :: c :: d :: e :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v6 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b c d e f t : Ty S} {Γ : List (Ty S)} :
    exprCostW opC (.v6 : Expr O (a :: b :: c :: d :: e :: f :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_v7 {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {a b c d e f g t : Ty S} {Γ : List (Ty S)} :
    exprCostW opC (.v7 : Expr O (a :: b :: c :: d :: e :: f :: g :: t :: Γ) t) = 1 := rfl
@[local simp] private theorem exprCostW_unit {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} : exprCostW opC (.unit : Expr O Γ .unit) = 1 := rfl
@[local simp] private theorem exprCostW_bool {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (b : Bool) : exprCostW opC (.bool b : Expr O Γ .bool) = 1 := rfl
@[local simp] private theorem exprCostW_nat {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (n : ℕ) : exprCostW opC (.nat n : Expr O Γ .nat) = bits n := rfl
@[local simp] private theorem exprCostW_none {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} : exprCostW opC (.none : Expr O Γ (.opt t)) = 1 := rfl
@[local simp] private theorem exprCostW_nil {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} : exprCostW opC (.nil : Expr O Γ (.list t)) = 1 := rfl
@[local simp] private theorem exprCostW_add {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a b : Expr O Γ .nat) :
    exprCostW opC (.add a b) = exprCostW opC a + exprCostW opC b + 1 := rfl
@[local simp] private theorem exprCostW_sub {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a b : Expr O Γ .nat) :
    exprCostW opC (.sub a b) = exprCostW opC a + exprCostW opC b + 1 := rfl
@[local simp] private theorem exprCostW_mulK {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (k : ℕ) (a : Expr O Γ .nat) :
    exprCostW opC (.mulK k a) = exprCostW opC a + bits k := rfl
@[local simp] private theorem exprCostW_divK {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (k : ℕ) (a : Expr O Γ .nat) :
    exprCostW opC (.divK k a) = exprCostW opC a + bits k := rfl
@[local simp] private theorem exprCostW_modK {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (k : ℕ) (a : Expr O Γ .nat) :
    exprCostW opC (.modK k a) = exprCostW opC a + bits k := rfl
@[local simp] private theorem exprCostW_lt {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a b : Expr O Γ .nat) :
    exprCostW opC (.lt a b) = exprCostW opC a + exprCostW opC b + 1 := rfl
@[local simp] private theorem exprCostW_eqN {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a b : Expr O Γ .nat) :
    exprCostW opC (.eqN a b) = exprCostW opC a + exprCostW opC b + 1 := rfl
@[local simp] private theorem exprCostW_not {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a : Expr O Γ .bool) : exprCostW opC (.not a) = exprCostW opC a + 1 := rfl
@[local simp] private theorem exprCostW_and {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (a b : Expr O Γ .bool) :
    exprCostW opC (.and a b) = exprCostW opC a + exprCostW opC b + 1 := rfl
@[local simp] private theorem exprCostW_ite {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Expr O Γ .bool) (a b : Expr O Γ t) :
    exprCostW opC (.ite c a b) = exprCostW opC c + max (exprCostW opC a) (exprCostW opC b) + 1 := rfl
@[local simp] private theorem exprCostW_pair {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ a) (y : Expr O Γ b) :
    exprCostW opC (.pair x y) = exprCostW opC x + exprCostW opC y + 1 := rfl
@[local simp] private theorem exprCostW_fst {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ (.prod a b)) :
    exprCostW opC (.fst x) = exprCostW opC x + 1 := rfl
@[local simp] private theorem exprCostW_snd {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ (.prod a b)) :
    exprCostW opC (.snd x) = exprCostW opC x + 1 := rfl
@[local simp] private theorem exprCostW_inl {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ a) :
    exprCostW opC (.inl x : Expr O Γ (.sum a b)) = exprCostW opC x + 1 := rfl
@[local simp] private theorem exprCostW_inr {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ b) :
    exprCostW opC (.inr x : Expr O Γ (.sum a b)) = exprCostW opC x + 1 := rfl
@[local simp] private theorem exprCostW_some {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (x : Expr O Γ t) :
    exprCostW opC (.some x) = exprCostW opC x + 1 := rfl
@[local simp] private theorem exprCostW_caseOpt {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ (.opt a))
    (n : Expr O Γ b) (s : Expr O (a :: Γ) b) : exprCostW opC (.caseOpt x n s) =
      exprCostW opC x + max (exprCostW opC n) (exprCostW opC s) + 1 := rfl
@[local simp] private theorem exprCostW_caseSum {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b c : Ty S} (x : Expr O Γ (.sum a b))
    (l : Expr O (a :: Γ) c) (r : Expr O (b :: Γ) c) : exprCostW opC (.caseSum x l r) =
      exprCostW opC x + max (exprCostW opC l) (exprCostW opC r) + 1 := rfl
@[local simp] private theorem exprCostW_letE {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ a) (k : Expr O (a :: Γ) b) :
    exprCostW opC (.letE x k) = exprCostW opC x + exprCostW opC k + 1 := rfl
@[local simp] private theorem exprCostW_op {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} (o : O.Op) (a : Expr O Γ (O.dom o)) :
    exprCostW opC (.op o a) = exprCostW opC a + opC o := rfl
@[local simp] private theorem exprCostW_cons {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (x : Expr O Γ t) (xs : Expr O Γ (.list t)) :
    exprCostW opC (.cons x xs) = exprCostW opC x + exprCostW opC xs + 1 := rfl
@[local simp] private theorem exprCostW_findB {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprCostW opC (.findB K l p) = exprCostW opC l + K * (exprCostW opC p + 1) + 1 := rfl
@[local simp] private theorem exprCostW_anyB {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprCostW opC (.anyB K l p) = exprCostW opC l + K * (exprCostW opC p + 1) + 1 := rfl
@[local simp] private theorem exprCostW_foldrB {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t u : Ty S} (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u)
    (f : Expr O (t :: u :: Γ) u) : exprCostW opC (.foldrB K l z f) =
      exprCostW opC l + exprCostW opC z + K * (exprCostW opC f + 1) + 1 := rfl
@[local simp] private theorem exprCostW_tconst {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (a : Expr O Γ t) :
    exprCostW opC (.tconst a) = exprCostW opC a + 1 := rfl
@[local simp] private theorem exprCostW_tget {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) :
    exprCostW opC (.tget m i) = exprCostW opC m + exprCostW opC i + 64 := rfl
@[local simp] private theorem exprCostW_tset {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) (a : Expr O Γ t) :
    exprCostW opC (.tset m i a) = exprCostW opC m + exprCostW opC i + exprCostW opC a + 128 := rfl

@[local simp] private theorem compCostW_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    compCostW opC sC qC (.ret e) = exprCostW opC e + 1 := rfl
@[local simp] private theorem compCostW_bind {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (c : Comp O I Γ a) (k : Comp O I (a :: Γ) b) :
    compCostW opC sC qC (.bind c k) = compCostW opC sC qC c + compCostW opC sC qC k + 1 := rfl
@[local simp] private theorem compCostW_ite {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (b : Expr O Γ .bool) (c d : Comp O I Γ t) :
    compCostW opC sC qC (.ite b c d) =
      exprCostW opC b + max (compCostW opC sC qC c) (compCostW opC sC qC d) + 1 := rfl
@[local simp] private theorem compCostW_caseOpt {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {a b : Ty S} (x : Expr O Γ (.opt a))
    (n : Comp O I Γ b) (s : Comp O I (a :: Γ) b) : compCostW opC sC qC (.caseOpt x n s) =
      exprCostW opC x + max (compCostW opC sC qC n) (compCostW opC sC qC s) + 1 := rfl
@[local simp] private theorem compCostW_caseSum {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {a b c : Ty S} (x : Expr O Γ (.sum a b))
    (l : Comp O I (a :: Γ) c) (r : Comp O I (b :: Γ) c) : compCostW opC sC qC (.caseSum x l r) =
      exprCostW opC x + max (compCostW opC sC qC l) (compCostW opC sC qC r) + 1 := rfl
@[local simp] private theorem compCostW_sample {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} (s : I.smp.Samp) (e : Expr O Γ (I.smp.sDom s)) :
    compCostW opC sC qC (.sample s e) = exprCostW opC e + sC s := rfl
@[local simp] private theorem compCostW_query {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} (g : I.Tag) (e : Expr O Γ (I.dom g)) :
    compCostW opC sC qC (.query g e) = exprCostW opC e + qC g := rfl

private theorem healEpoch_le_of_forall_some {tL : Option ℕ} {qep : ℕ}
    (htL : ∀ x, tL = some x → x ≤ qep + 3) : healEpoch tL ≤ qep + 6 := by
  cases tL with
  | none => simp [healEpoch]
  | some x =>
    have hx := htL x rfl
    simp [healEpoch]
    omega

private theorem optGetD_le_of_forall_some {tL : Option ℕ} {qep : ℕ}
    (htL : ∀ x, tL = some x → x ≤ qep + 3) : tL.getD 0 ≤ qep + 3 := by
  cases tL with
  | none => simp
  | some x => exact htL x rfl

private theorem bits_healEpoch_le_getD (tL : Option ℕ) :
    bits (healEpoch tL) ≤ bits (tL.getD 0) + 2 := by
  cases tL with
  | none => simp [healEpoch]
  | some l =>
    have h1 := bits_succ_le (l + 1)
    have h2 := bits_succ_le l
    simpa [healEpoch, Option.getD, Nat.add_assoc] using le_trans h1 (Nat.add_le_add_right h2 1)

private theorem bits_le_bits_add {x y d : ℕ} (h : x ≤ y + d) :
    bits x ≤ bits y + d := by
  induction d generalizing x with
  | zero => exact bits_mono (by omega)
  | succ d ih =>
    by_cases hle : x ≤ y + d
    · have := ih hle; omega
    · have hx : x = (y + d) + 1 := by omega
      rw [hx]
      have := bits_succ_le (y + d)
      have := ih (Nat.le_refl (y + d))
      omega

section GenericCkaBounds

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}
  {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S_cka" => _root_.CryptoGames.CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  _root_.CryptoGames.PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II_cka" =>
  _root_.CryptoGames.PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E
    sampKR sampKC sampCCoins sampI sampK
local notation "pbaVpT" => @prngVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaHsT" => @prngBucketAuthHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaEsT" => @prngBucketAuthEsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "pbaS2T" => @prngBucketAuthStage2RedEsTy KC Γ CCoins T I KR RSt K SS RS M E

private theorem optNatLit_costW_le {S' : Sig} {O' : Ops S'} (opC : O'.Op → ℕ)
    {Γ' : List (Ty S')} (o : Option ℕ) :
    exprCostW opC (_root_.CryptoGames.SM.Engine.optNatLit (O' := O') (Γ' := Γ') o) ≤
      bits (o.getD 0) + 2 := by
  cases o <;> simp [_root_.CryptoGames.SM.Engine.optNatLit, Option.getD]

private theorem postLeakBucketE_costW_le (B0 : ℕ) (tL : Option ℕ) {vpT : Ty S_cka} {Γ'}
    (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprCostW (ckaOpC B0) (postLeakBucketE tL ctx) ≤
      exprCostW (ckaOpC B0) ctx + bits (tL.getD 0) + 25 := by
  cases tL <;> simp only [postLeakBucketE, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.Engine.optNatLit, Option.getD, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_caseOpt, exprCostW_fst, exprCostW_snd,
    exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_not,
    exprCostW_lt, exprCostW_v0, exprCostW_v1, exprCostW_var,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd] <;> omega

private theorem validGuessE3_costW_le (B0 : ℕ) (tL : Option ℕ) {Γ'} (tE : Expr OO_cka Γ' .nat) :
    exprCostW (ckaOpC B0)
      (_root_.CryptoGames.SM.validGuessE 3 (_root_.CryptoGames.SM.Engine.optNatLit tL) tE) ≤
      4 * exprCostW (ckaOpC B0) tE + 2 * bits (tL.getD 0) + 60 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  have hb4 : bits 4 = 3 := rfl
  cases tL <;> ·
    simp only [_root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
      _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
      _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
      _root_.CryptoGames.SM.Engine.optNatLit, Option.getD, exprCostW_rename,
      exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool, exprCostW_nat, exprCostW_none,
      exprCostW_some, exprCostW_add, exprCostW_modK, exprCostW_lt, exprCostW_eqN, exprCostW_not,
      exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
      exprCostW_caseOpt, exprCostW_letE, hb0, hb1, hb2, hb3, hb4, Nat.reduceAdd]
    omega

private theorem compCostW_bind_le' {ι : Type} {E_sp : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka E_sp} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S_cka)} {τ₁ τ₂ : Ty S_cka}
    (c1 : Comp OO_cka I' Γ' τ₁) (c2 : Comp OO_cka I' (τ₁ :: Γ') τ₂) (k1 k2 : ℕ)
    (h1 : compCostW (ckaOpC B0) sC qC c1 ≤ k1)
    (h2 : compCostW (ckaOpC B0) sC qC c2 ≤ k2) :
    compCostW (ckaOpC B0) sC qC (.bind c1 c2) ≤ k1 + k2 + 1 := by
  rw [compCostW_bind]; omega

private theorem compCostW_ite_le' {ι : Type} {E_sp : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka E_sp} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S_cka)} {τ : Ty S_cka}
    (b : Expr OO_cka Γ' .bool) (c1 c2 : Comp OO_cka I' Γ' τ) (kb kc : ℕ)
    (hb : exprCostW (ckaOpC B0) b ≤ kb)
    (h1 : compCostW (ckaOpC B0) sC qC c1 ≤ kc)
    (h2 : compCostW (ckaOpC B0) sC qC c2 ≤ kc) :
    compCostW (ckaOpC B0) sC qC (.ite b c1 c2) ≤ kb + kc + 1 := by
  rw [compCostW_ite]; omega

private theorem compCostW_caseOpt_le' {ι : Type} {E_sp : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka E_sp} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S_cka)} {τ₁ τ₂ : Ty S_cka}
    (e : Expr OO_cka Γ' (.opt τ₁))
    (c1 : Comp OO_cka I' Γ' τ₂) (c2 : Comp OO_cka I' (τ₁ :: Γ') τ₂) (ke kc : ℕ)
    (he : exprCostW (ckaOpC B0) e ≤ ke)
    (h1 : compCostW (ckaOpC B0) sC qC c1 ≤ kc)
    (h2 : compCostW (ckaOpC B0) sC qC c2 ≤ kc) :
    compCostW (ckaOpC B0) sC qC (.caseOpt e c1 c2) ≤ ke + kc + 1 := by
  rw [compCostW_caseOpt]; omega

private theorem compCostW_caseSum_le' {ι : Type} {E_sp : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka E_sp} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {Γ' : List (Ty S_cka)} {τ₁ τ₂ τ₃ : Ty S_cka}
    (e : Expr OO_cka Γ' (.sum τ₁ τ₂))
    (c1 : Comp OO_cka I' (τ₁ :: Γ') τ₃) (c2 : Comp OO_cka I' (τ₂ :: Γ') τ₃) (ke kc : ℕ)
    (he : exprCostW (ckaOpC B0) e ≤ ke)
    (h1 : compCostW (ckaOpC B0) sC qC c1 ≤ kc)
    (h2 : compCostW (ckaOpC B0) sC qC c2 ≤ kc) :
    compCostW (ckaOpC B0) sC qC (.caseSum e c1 c2) ≤ ke + kc + 1 := by
  rw [compCostW_caseSum]; omega

private theorem rootPRNGBucketAuthHybridC_costW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT) (tE : Expr OO_cka Γ' .nat) (plE : Expr OO_cka Γ' .bool)
    (ikE : Expr OO_cka Γ' (.base .i)) (σvE : Expr OO_cka Γ' (.opt (.base .sig))) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (rootPRNGBucketAuthHybridC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE tE plE ikE σvE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) plE +
        exprCostW (ckaOpC B0) ikE + exprCostW (ckaOpC B0) σvE +
        30 * L + 2 * bits t + 3 * bits (healEpoch tL) + 2000 := by
  have hb1 : bits 1 = 1 := rfl
  simp only [rootPRNGBucketAuthHybridC, lookupPRNGBucketAuthFC, pbaTableLookupE,
    resolveCorrRootE, pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetFTblAt, pbaHsSetCorrRoot,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE,
    ckaOpC, ckaSampC, prngQueryC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_sample,
    compCostW_query,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_var,
    exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some,
    exprCostW_cons, exprCostW_sub, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and,
    exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt,
    exprCostW_letE, exprCostW_op, exprCostW_foldrB, exprCostW_tget, exprCostW_tset,
    hb1, show max 3 1 = 3 from rfl, Nat.reduceAdd]
  omega

private theorem prngBucketAuthStartSendC_costW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (rE : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthStartSendC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE ctxE pE tE γE σvE rE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σvE +
        exprCostW (ckaOpC B0) rE +
        30 * L + bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 4000 := by
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT)
    (.prod .nat (.prod (.base .γ) (.prod (.opt (.base .sig)) (.opt (.base .ccoins))))))
  let Γ0 : List (Ty S_cka) := .base .ccoins :: tupT :: Γ'
  have hpl := postLeakBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v1))
  have hrt := rootPRNGBucketAuthHybridC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := Γ0)
    (.fst .v1) (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1)))))
  simp only [ckaOpC, exprCostW_op, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v1, Nat.reduceAdd] at hpl hrt
  simp only [prngBucketAuthStartSendC, pbaHsCache, pbaHsSetCache,
    ckaOpC, ckaSampC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_caseOpt, compCostW_sample,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_unit, exprCostW_none, exprCostW_some, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_op, exprCostW_tset, Nat.reduceAdd]
  omega

private theorem prngBucketAuthStartRecvC_costW_le (B0 L qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (tnE : Expr OO_cka Γ' (.base .t)) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep tL t hE ctxE pE tE γE σvE tnE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σvE +
        exprCostW (ckaOpC B0) tnE +
        30 * L + bits qep + 3 * bits (tL.getD 0) + 2 * bits t + 2 * bits (healEpoch tL) + 4000 := by
  have hbq1 := bits_succ_le qep
  have hb1 : bits 1 = 1 := rfl
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT)
    (.prod .nat (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .t)))))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hpl := postLeakBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v0))
  have hvg := validGuessE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd (.snd .v0)))
  simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd] at hpl hvg
  dsimp only [prngBucketAuthStartRecvC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [lookupPRNGBucketAuthFC, pbaTableLookupE, resolveCorrRootE,
    pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetFTblAt,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE,
    ckaOpC, ckaSampC, prngQueryC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_sample,
    compCostW_query,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some,
    exprCostW_cons, exprCostW_sub, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and,
    exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt,
    exprCostW_letE, exprCostW_op, exprCostW_foldrB, exprCostW_tget, exprCostW_tset,
    hb1, show max 3 1 = 3 from rfl, Nat.reduceAdd]
  omega

private theorem prngBucketAuthMainStartRecvC_costW_le (B0 qep : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (tnE : Expr OO_cka Γ' (.base .t)) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthMainStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) 1 qep tL hE ctxE pE tE γE σvE tnE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σvE +
        exprCostW (ckaOpC B0) tnE +
        bits qep + 2 * bits (tL.getD 0) + bits (healEpoch tL) + 1500 := by
  have hbq1 := bits_succ_le qep
  let tupT : Ty S_cka := .prod pbaHsT (.prod .nat (.prod (.base .γ) (.base .t)))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hvg := validGuessE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd .v0))
  simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd] at hvg
  dsimp only [prngBucketAuthMainStartRecvC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [resolveCorrRootE, pbaHsCache, pbaHsCorrRoot,
    ckaOpC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some,
    exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_op, exprCostW_tget, Nat.reduceAdd]
  omega

private theorem prngBucketAuthRevealC_costW_le (B0 : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' pbaVpT) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) vpE + bits (tL.getD 0) + 2 * bits (healEpoch tL) + 1500 := by
  have hb0 : bits 0 = 1 := rfl
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT) pbaVpT)
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hpl := postLeakBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v0))
  simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd] at hpl
  simp only [prngBucketAuthRevealC, resolveCorrRootE,
    pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetCorrRoot,
    _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.vpId,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.cGsEpoch, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.isSomeE, prngQueryC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_query,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some,
    exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE,
    hb0, Nat.reduceAdd]
  omega

private theorem prngBucketAuthForgedHdrRevealC_costW_le (B0 : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' pbaVpT) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthForgedHdrRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) vpE + 2 * bits (healEpoch tL) + 1000 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [prngBucketAuthForgedHdrRevealC, _root_.CryptoGames.SM.Engine.realPartyE,
    _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpΓ,
    _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS,
    _root_.CryptoGames.SM.Engine.vpVR, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some,
    exprCostW_lt, exprCostW_not, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_caseOpt, exprCostW_letE, hb0, Nat.reduceAdd]
  omega

private theorem initPRNGBucketAuthEStateC_costW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (initPRNGBucketAuthEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t bE) ≤
      exprCostW (ckaOpC B0) bE + 30 * L + 2 * bits t + 3 * bits (healEpoch tL) + 5000 := by
  have hb0 : bits 0 = 1 := rfl
  let Γ0 : List (Ty S_cka) := .base .kc :: .bool :: Γ'
  have hrt := rootPRNGBucketAuthHybridC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := Γ0)
    pbaHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit) .none
  simp only [pbaHsEmptyE, ckaOpC, exprCostW_pair, exprCostW_tconst, exprCostW_none,
    exprCostW_nil, exprCostW_nat, exprCostW_bool, exprCostW_op, exprCostW_unit,
    hb0, Nat.reduceAdd] at hrt
  simp only [initPRNGBucketAuthEStateC, pbaHsEmptyE, abortedPartiesE,
    _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.cGsInitE,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.vpMk, ckaOpC, ckaSampC, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_caseOpt, compCostW_sample,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_nil,
    exprCostW_some, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_letE,
    exprCostW_op, exprCostW_tconst, exprCostW_tget, exprCostW_tset, hb0, Nat.reduceAdd]
  omega

private theorem prngBucketAuthFsSendC_costW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (ssE : Expr OO_cka Γ' (.base .ss))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : Expr OO_cka Γ' (.base .msg))
    (pairE : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthFsSendC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE tE ssE hdrE mE pairE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) ssE + exprCostW (ckaOpC B0) hdrE +
        exprCostW (ckaOpC B0) mE + exprCostW (ckaOpC B0) pairE + 380100 := by
  simp only [prngBucketAuthFsSendC, ckaOpC, compCostW_ret, exprCostW_pair, exprCostW_some,
    exprCostW_op, Nat.reduceAdd]
  omega

private theorem prngBucketAuthFsRecvC_costW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsE : Expr OO_cka Γ' (.base .rs))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct))
    (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthFsRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B0 hE ctxE pE tE rsE hdrE eE recE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) rsE + exprCostW (ckaOpC B0) hdrE +
        exprCostW (ckaOpC B0) eE + exprCostW (ckaOpC B0) recE +
        20 * B0 + 3 * bits B0 + 2710100 := by
  simp only [prngBucketAuthFsRecvC, ckaOpC, compCostW_ret, exprCostW_pair, exprCostW_some,
    exprCostW_op, Nat.reduceAdd]
  generalize bits B0 = bB at *
  omega

private theorem prngBucketAuthCommitC_costW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (oldE newE : Expr OO_cka Γ' pbaVpT) :
    compCostW (ckaOpC B0) ckaSampC prngQueryC
      (prngBucketAuthCommitC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) oldE + exprCostW (ckaOpC B0) newE + 10 := by
  simp only [prngBucketAuthCommitC, compCostW_ret, exprCostW_pair, exprCostW_some, Nat.reduceAdd]
  omega

private theorem isHonestHdrPRNGBucketE_costW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprCostW (ckaOpC B0) (isHonestHdrPRNGBucketE hE hdrE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) hdrE + 150 := by
  simp only [isHonestHdrPRNGBucketE, pbaHsCache, ckaOpC, exprCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool, exprCostW_pair,
    exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE, exprCostW_op,
    exprCostW_tget, Nat.reduceAdd]
  omega

private structure HooksCostWBounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} (B0 : ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (W_o W_s W_r W_cm W_rv : ℕ) : Prop where
  startSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (γv : Expr OO_cka Γ' γvT)
      (σ : Expr OO_cka Γ' svT) (r : Expr OO_cka Γ' (.opt (.base .ccoins))),
      compCostW (ckaOpC B0) sC qC (hk.startSend h ctx p t γv σ r) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) t + exprCostW (ckaOpC B0) γv + exprCostW (ckaOpC B0) σ +
          exprCostW (ckaOpC B0) r + W_o
  startRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (γv : Expr OO_cka Γ' γvT)
      (σ : Expr OO_cka Γ' svT) (tn : Expr OO_cka Γ' (.base .t)),
      compCostW (ckaOpC B0) sC qC (hk.startRecv h ctx p t γv σ tn) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) t + exprCostW (ckaOpC B0) γv + exprCostW (ckaOpC B0) σ +
          exprCostW (ckaOpC B0) tn + W_o
  fsSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (ss : Expr OO_cka Γ' ssvT)
      (hdr : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (m : Expr OO_cka Γ' (.base .msg)) (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))),
      compCostW (ckaOpC B0) sC qC (hk.fsSend h ctx p t ss hdr m pair) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) t + exprCostW (ckaOpC B0) ss + exprCostW (ckaOpC B0) hdr +
          exprCostW (ckaOpC B0) m + exprCostW (ckaOpC B0) pair + W_s
  fsRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (rs : Expr OO_cka Γ' rsvT)
      (hdr : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (e : Expr OO_cka Γ' (.base .ct)) (rec_ : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)),
      compCostW (ckaOpC B0) sC qC (hk.fsRecv h ctx p t rs hdr e rec_) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) t + exprCostW (ckaOpC B0) rs + exprCostW (ckaOpC B0) hdr +
          exprCostW (ckaOpC B0) e + exprCostW (ckaOpC B0) rec_ + W_r
  commit_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (old new : Expr OO_cka Γ' (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compCostW (ckaOpC B0) sC qC (hk.commit h ctx p old new) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) old + exprCostW (ckaOpC B0) new + W_cm
  reveal_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (vp : Expr OO_cka Γ' (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compCostW (ckaOpC B0) sC qC (hk.reveal h ctx p vp) ≤
        exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
          exprCostW (ckaOpC B0) vp + W_rv

private theorem hooksPRNGBucketAuthForgedHdrC_costWBounded (B0 L qep : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    HooksCostWBounded B0 ckaSampC prngQueryC
      (hooksPRNGBucketAuthForgedHdrC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep tL t)
      (30 * L + bits qep + 3 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 4000)
      380100
      (20 * B0 + 3 * bits B0 + 2710100)
      10
      (bits (tL.getD 0) + 2 * bits (healEpoch tL) + 1500) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ' h ctx p tE γv σ r
    exact (prngBucketAuthStartSendC_costW_le B0 L tL t h ctx p tE γv σ r).trans (by omega)
  · intro Γ' h ctx p tE γv σ tn
    exact (prngBucketAuthStartRecvC_costW_le B0 L qep tL t h ctx p tE γv σ tn).trans (by omega)
  · intro Γ' h ctx p tE ss hdr m pair
    exact (prngBucketAuthFsSendC_costW_le B0 h ctx p tE ss hdr m pair).trans (by omega)
  · intro Γ' h ctx p tE rs hdr e rec_
    exact (prngBucketAuthFsRecvC_costW_le B0 h ctx p tE rs hdr e rec_).trans (by omega)
  · intro Γ' h ctx p old new
    exact (prngBucketAuthCommitC_costW_le B0 h ctx p old new).trans (by omega)
  · intro Γ' h ctx p vp
    exact (prngBucketAuthForgedHdrRevealC_costW_le B0 tL h ctx p vp).trans (by omega)

private theorem hooksPRNGBucketAuthMainC_costWBounded (B0 L qep : ℕ)
    (tL : Option ℕ) (t : ℕ) :
    HooksCostWBounded B0 ckaSampC prngQueryC
      (hooksPRNGBucketAuthMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep tL t)
      (30 * L + bits qep + 3 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 4000)
      380100
      (20 * B0 + 3 * bits B0 + 2710100)
      10
      (bits (tL.getD 0) + 2 * bits (healEpoch tL) + 1500) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ' h ctx p tE γv σ r
    exact (prngBucketAuthStartSendC_costW_le B0 L tL t h ctx p tE γv σ r).trans (by omega)
  · intro Γ' h ctx p tE γv σ tn
    exact (prngBucketAuthMainStartRecvC_costW_le B0 qep tL h ctx p tE γv σ tn).trans (by omega)
  · intro Γ' h ctx p tE ss hdr m pair
    exact (prngBucketAuthFsSendC_costW_le B0 h ctx p tE ss hdr m pair).trans (by omega)
  · intro Γ' h ctx p tE rs hdr e rec_
    exact (prngBucketAuthFsRecvC_costW_le B0 h ctx p tE rs hdr e rec_).trans (by omega)
  · intro Γ' h ctx p old new
    exact (prngBucketAuthCommitC_costW_le B0 h ctx p old new).trans (by omega)
  · intro Γ' h ctx p vp
    exact (prngBucketAuthRevealC_costW_le B0 tL h ctx p vp).trans (by omega)

private theorem cInTransitE_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (qParty : Expr OO_cka Γ' .bool)
    (c : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cInTransitE L s qParty c) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) qParty +
        exprCostW (ckaOpC B0) c + 250 * L + 60 := by
  simp only [_root_.CryptoGames.SM.Engine.cInTransitE, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cRecCt,
    _root_.CryptoGames.SM.Engine.hdrCtEqE, _root_.CryptoGames.SM.Engine.optTEqE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.boolEq, ckaOpC, exprCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_var,
    exprCostW_bool, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_op, exprCostW_findB, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cEpMgmtE3_costW_le {vpT : Ty S_cka} (B0 qep : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p bad : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cEpMgmtE (2 + 1) qep s p bad) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + exprCostW (ckaOpC B0) bad +
        2 * bits qep + 600 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cLeakE, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.boolEq,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_cons,
    exprCostW_add, exprCostW_modK, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and,
    exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt,
    exprCostW_letE, hb0, hb1, hb2, hb3, Nat.reduceAdd]
  omega

private theorem cRecordE3_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) (st' : Expr OO_cka Γ' vpT)
    (r : Expr OO_cka Γ' _root_.CryptoGames.SM.Engine.cRecTy) (isChall : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cRecordE L (2 + 1) s p st' r isChall) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + exprCostW (ckaOpC B0) st' +
        exprCostW (ckaOpC B0) r + exprCostW (ckaOpC B0) isChall + 800 := by
  have hb3 : bits 3 = 2 := rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cRecordE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_cons, exprCostW_add, exprCostW_lt,
    exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_caseOpt, exprCostW_letE, exprCostW_tget, exprCostW_tset, hb3, Nat.reduceAdd]
  omega

private theorem cMustBeCorrectE_costW_le {vpT : Ty S_cka} (B0 L maxSkip : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr OO_cka Γ' .bool)
    (r : Expr OO_cka Γ' _root_.CryptoGames.SM.Engine.cRecTy) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cMustBeCorrectE L maxSkip s p r) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + exprCostW (ckaOpC B0) r +
        bits maxSkip + 400 := by
  have hb1 : bits 1 = 1 := rfl
  simp only [_root_.CryptoGames.SM.Engine.cMustBeCorrectE,
    _root_.CryptoGames.SM.Engine.cCompContainsE, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cGsMaxAcc, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.maxAccGet, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_nat,
    exprCostW_add, exprCostW_lt, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_letE, exprCostW_tget,
    hb1, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cChallContainsE_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cChallContainsE L s pos) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) pos + 50 * L + 40 := by
  simp only [_root_.CryptoGames.SM.Engine.cChallContainsE, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_eqN,
    exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_letE, exprCostW_anyB, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cTrivialE3_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cTrivialE L (2 + 1) s pos) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) pos + 60 * L + 350 := by
  have hb3 : bits 3 = 2 := rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cTrivialE, _root_.CryptoGames.SM.Engine.cCompContainsE,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool, exprCostW_nat,
    exprCostW_add, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_anyB, exprCostW_tget, hb3, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cCorrAllowedE_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cCorrAllowedE L s p) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + 250 * L + 60 := by
  simp only [_root_.CryptoGames.SM.Engine.cCorrAllowedE,
    _root_.CryptoGames.SM.Engine.cCompContainsE, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_var,
    exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_letE, exprCostW_anyB, exprCostW_tget,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cAfterCorrE_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) (p : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cAfterCorrE L s p) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + 6000 * L + 5000 := by
  simp only [_root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cLeakE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    exprCostW_bool, exprCostW_some, exprCostW_cons, exprCostW_lt,
    exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_caseOpt, exprCostW_letE, exprCostW_foldrB, exprCostW_tget, exprCostW_tset,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem cAuthOKE3_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (tLStar : Expr OO_cka Γ' (.opt .nat)) (tStar : Expr OO_cka Γ' .nat)
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cAuthOKE L (2 + 1) tLStar tStar s) ≤
      exprCostW (ckaOpC B0) tLStar + exprCostW (ckaOpC B0) tStar + exprCostW (ckaOpC B0) s +
        160 * L + 250 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cAuthOKE, _root_.CryptoGames.SM.Engine.cCanonE,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_add,
    exprCostW_modK, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_anyB, exprCostW_foldrB,
    hb0, hb1, hb2, hb3, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem vSendC_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    {W_o W_s W_r W_cm W_rv : ℕ} (hhk : HooksCostWBounded B0 sC qC hk W_o W_s W_r W_cm W_rv)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO_cka Γ' (.base .msg))
    (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compCostW (ckaOpC B0) sC qC (_root_.CryptoGames.SM.Engine.vSendC hk h ctx p s m pair r) ≤
      exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
        exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) m + exprCostW (ckaOpC B0) pair +
        exprCostW (ckaOpC B0) r + W_o + W_s + 400 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) ::
      .prod hsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (Ty S_cka) := ssvT :: vpT :: .prod (.opt vpT) hsT ::
      .prod hsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0) (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (_root_.CryptoGames.SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (_root_.CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (_root_.CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  have hfs := hhk.fsSend_le (Γ' := Γ1) (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (_root_.CryptoGames.SM.Engine.vpTcurNat .v1) .v0
    (.pair (_root_.CryptoGames.SM.Engine.vpTcurNat .v1) (_root_.CryptoGames.SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [_root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_nat, exprCostW_add, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    hb1, Nat.reduceAdd] at hss hfs
  simp only [_root_.CryptoGames.SM.Engine.vSendC, _root_.CryptoGames.SM.Engine.vSendStep1C,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.vpSetVS, _root_.CryptoGames.SM.Engine.vpΓ,
    _root_.CryptoGames.SM.Engine.vpRoot, ckaOpC, exprCostW_rename, compCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_var,
    exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_add, exprCostW_eqN, exprCostW_modK,
    exprCostW_lt, exprCostW_and, exprCostW_not, exprCostW_ite, exprCostW_pair, exprCostW_fst,
    exprCostW_snd, exprCostW_none, exprCostW_some, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_op, exprCostW_tget, exprCostW_tset,
    compCostW_ret, compCostW_bind, compCostW_ite, compCostW_caseOpt, hb0, hb1, hb2, Nat.reduceAdd]
  omega

private theorem vRecvC_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    {W_o W_s W_r W_cm W_rv : ℕ} (hhk : HooksCostWBounded B0 sC qC hk W_o W_s W_r W_cm W_rv)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
    (rec_ : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    compCostW (ckaOpC B0) sC qC (_root_.CryptoGames.SM.Engine.vRecvC hk h ctx p s c rec_) ≤
      exprCostW (ckaOpC B0) h + exprCostW (ckaOpC B0) ctx + exprCostW (ckaOpC B0) p +
        exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) c + exprCostW (ckaOpC B0) rec_ +
        W_o + W_r + 1500 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_outer : List (Ty S_cka) :=
    .prod hsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
      (.prod hdrCtT (.opt _root_.CryptoGames.SM.Engine.cRecTy))))) :: Γ'
  let Γ0 : List (Ty S_cka) :=
    .base .t :: .prod hsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT) (.prod .bool
      (.prod vpT hdrCtT))) :: Γ_outer
  let Γ1 : List (Ty S_cka) := rsvT :: vpT :: .opt vpT :: .prod (.opt (.opt vpT)) hsT :: Γ_outer
  have hsr := hhk.startRecv_le (Γ' := Γ0) (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (_root_.CryptoGames.SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v1)))))
    (_root_.CryptoGames.SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
  have hfr := hhk.fsRecv_le (Γ' := Γ1) (.snd .v3) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4)))))) (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
  simp only [_root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    exprCostW_v0, exprCostW_v1, exprCostW_v3, exprCostW_v4, exprCostW_v5, exprCostW_v6,
    exprCostW_var, exprCostW_fst, exprCostW_snd, Nat.reduceAdd] at hsr hfr
  simp only [_root_.CryptoGames.SM.Engine.vRecvC, _root_.CryptoGames.SM.Engine.vRecvStep1C,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.Engine.vpMk, _root_.CryptoGames.SM.Engine.vpId,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.vpSetVR, _root_.CryptoGames.SM.Engine.vpΓ,
    _root_.CryptoGames.SM.Engine.vpRoot, ckaOpC, exprCostW_rename, compCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_v5,
    exprCostW_v6, exprCostW_v7, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_add, exprCostW_eqN, exprCostW_modK,
    exprCostW_lt, exprCostW_and, exprCostW_not, exprCostW_ite, exprCostW_pair, exprCostW_fst,
    exprCostW_snd, exprCostW_none, exprCostW_some, exprCostW_caseOpt, exprCostW_letE,
    exprCostW_op, exprCostW_tget, exprCostW_tset,
    compCostW_ret, compCostW_bind, compCostW_ite, compCostW_caseOpt, hb0, hb1, hb2, Nat.reduceAdd]
  omega

private theorem commitEC_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L : ℕ)
    {W_o W_s W_r W_cm W_rv : ℕ} (hhk : HooksCostWBounded B0 sC qC hk W_o W_s W_r W_cm W_rv)
    {Γ'} (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (old new : Expr OO_cka Γ' (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    compCostW (ckaOpC B0) sC qC (_root_.CryptoGames.SM.Engine.commitEC hk L es s p old new pos) ≤
      exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) s + 2 * exprCostW (ckaOpC B0) p +
        exprCostW (ckaOpC B0) old + 2 * exprCostW (ckaOpC B0) new +
        2 * exprCostW (ckaOpC B0) pos + W_cm + 200 * L + 1800 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let Γ0 : List (Ty S_cka) := .prod esT (.prod (_root_.CryptoGames.SM.Engine.cGsTy vpT)
      (.prod .bool (.prod vpT vpT))) :: Γ'
  have hcm := hhk.commit_le (Γ' := Γ0) (_root_.CryptoGames.SM.Engine.esH (.fst .v0))
    (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  simp only [_root_.CryptoGames.SM.Engine.esH, exprCostW_fst, exprCostW_snd, exprCostW_v0,
    Nat.reduceAdd] at hcm
  simp only [_root_.CryptoGames.SM.Engine.commitEC, _root_.CryptoGames.SM.Engine.cAcceptE,
    _root_.CryptoGames.SM.Engine.cDeleteE, _root_.CryptoGames.SM.Engine.cCompDeleteE,
    _root_.CryptoGames.SM.Engine.cCompSetE, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.Engine.cGsSetStP,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.Engine.cGsB, _root_.CryptoGames.SM.Engine.cGsWin,
    _root_.CryptoGames.SM.Engine.cGsEpoch, _root_.CryptoGames.SM.Engine.cGsIdx,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cGsMaxAcc, _root_.CryptoGames.SM.Engine.cGsLeaks,
    _root_.CryptoGames.SM.Engine.cGsCorrs, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esAbort,
    _root_.CryptoGames.SM.maxAccSet, _root_.CryptoGames.SM.maxAccGet,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, compCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_bool, exprCostW_none, exprCostW_nil, exprCostW_some, exprCostW_cons,
    exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_letE,
    exprCostW_foldrB, exprCostW_tget, exprCostW_tset,
    compCostW_ret, compCostW_bind, compCostW_caseOpt,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem esSetG_costW {vpT hsT : Ty S_cka} (B0 : ℕ) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy vpT hsT))
    (g : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.esSetG es g) =
      exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) g + 14 := by
  simp only [_root_.CryptoGames.SM.Engine.esSetG, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
    exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]

private theorem esSetH_costW {vpT hsT : Ty S_cka} (B0 : ℕ) {Γ'}
    (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy vpT hsT))
    (h : Expr OO_cka Γ' hsT) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.esSetH es h) =
      exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) h + 13 := by
  simp only [_root_.CryptoGames.SM.Engine.esSetH, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esAbort,
    exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]

private theorem cGsSetWin_costW {vpT : Ty S_cka} (B0 : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (b : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cGsSetWin s b) =
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) b + 111 := by
  simp only [_root_.CryptoGames.SM.Engine.cGsSetWin, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsEpoch, _root_.CryptoGames.SM.Engine.cGsIdx,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsChall, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cGsMaxAcc, _root_.CryptoGames.SM.Engine.cGsLeaks,
    _root_.CryptoGames.SM.Engine.cGsCorrs,
    exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]

set_option maxRecDepth 100000 in
private theorem deliverEC_bucket_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L maxSkip : ℕ) (tL : Option ℕ)
    {W_o W_s W_r W_cm W_rv : ℕ} (hhk : HooksCostWBounded B0 sC qC hk W_o W_s W_r W_cm W_rv)
    {Γ'} (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compCostW (ckaOpC B0) sC qC (_root_.CryptoGames.SM.Engine.deliverEC hk L maxSkip
        (bucketAuthCfgEC 1 tL) es arg) ≤
      exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) arg +
        W_o + W_r + W_cm + 700 * L + bits maxSkip + 40000 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  let Γ_dl1 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cRecTy :: Γ_dl0
  let Γ_dl2 : List (Ty S_cka) := .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_dl1
  let Γ_dl3 : List (Ty S_cka) := decT :: Γ_dl2
  let Γ_dl4 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy vpT :: .prod (.opt (_root_.CryptoGames.SM.Engine.cGsTy vpT)) esT :: Γ_dl3
  dsimp only [_root_.CryptoGames.SM.Engine.deliverEC, bucketAuthCfgEC]
  refine le_trans (compCostW_bind_le' _ _
    (exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) arg + 5)
    (W_o + W_r + W_cm + 700 * L + bits maxSkip + 39990) ?_ ?_) (by omega)
  · simp only [compCostW_ret, exprCostW_pair, Nat.reduceAdd]; omega
  · refine le_trans (compCostW_ite_le' _ _ _ 30
      (W_o + W_r + W_cm + 700 * L + bits maxSkip + 39950) ?_ ?_ ?_) (by omega)
    · simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esAbort,
        _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.orE,
        exprCostW_ite, exprCostW_bool, exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]
      omega
    · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_fst, exprCostW_v0,
        Nat.reduceAdd]; omega
    · refine le_trans (compCostW_caseOpt_le' _ _ _ (250 * L + 100)
        (W_o + W_r + W_cm + 450 * L + bits maxSkip + 39800) ?_ ?_ ?_) (by omega)
      · have hit := cInTransitE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
          (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
          (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
          (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
          (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
          (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
          (.snd (.snd .v0))
        simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.otherE,
          exprCostW_not, exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd] at hit ⊢
        omega
      · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_fst, exprCostW_v0,
          Nat.reduceAdd]; omega
      · refine le_trans (compCostW_bind_le' _ _ (W_o + W_r + 1600)
          (W_cm + 450 * L + bits maxSkip + 38100) ?_ ?_) (by omega)
        · have hvr := vRecvC_costW_le hk hhk (Γ' := Γ_dl1)
            (_root_.CryptoGames.SM.Engine.esH (.fst .v1)) (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
            (.fst (.snd .v1))
            (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
            (.snd (.snd .v1)) (.some .v0)
          simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
            _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.pGet,
            exprCostW_letE, exprCostW_pair, exprCostW_ite, exprCostW_fst, exprCostW_snd,
            exprCostW_some, exprCostW_v0, exprCostW_v1, Nat.reduceAdd] at hvr ⊢
          omega
        · refine le_trans (compCostW_caseOpt_le' _ _ _ 5
            (W_cm + 450 * L + bits maxSkip + 38080) ?_ ?_ ?_) (by omega)
          · simp only [exprCostW_fst, exprCostW_v0, Nat.reduceAdd]; omega
          · simp only [_root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
              compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_bool, exprCostW_fst,
              exprCostW_snd, exprCostW_v0, exprCostW_v2, Nat.reduceAdd]; omega
          · refine le_trans (compCostW_caseOpt_le' _ _ _ 5
              (W_cm + 450 * L + bits maxSkip + 38060) ?_ ?_ ?_) (by omega)
            · simp only [exprCostW_v0]; omega
            · have hmbc0 := cMustBeCorrectE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
                (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L maxSkip (Γ' := Γ_dl2)
                (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3)) .v2
              simp only [_root_.CryptoGames.SM.Engine.esG, exprCostW_fst, exprCostW_snd,
                exprCostW_v2, exprCostW_v3, Nat.reduceAdd] at hmbc0
              simp only [_root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
                _root_.CryptoGames.SM.Engine.esAbort, cGsSetWin_costW,
                compCostW_ret, exprCostW_pair, exprCostW_some, exprCostW_inl,
                exprCostW_unit, exprCostW_bool, exprCostW_and, exprCostW_ite, exprCostW_fst,
                exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
                Nat.reduceAdd]
              omega
            · refine le_trans (compCostW_bind_le' _ _ (W_cm + 200 * L + 2000)
                (250 * L + bits maxSkip + 36000) ?_ ?_) (by omega)
              · have hcm := commitEC_costW_le hk L hhk (Γ' := Γ_dl3)
                  (_root_.CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2))
                  (_root_.CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
                  (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
                  (.fst .v0) (_root_.CryptoGames.SM.Engine.cRecPos .v3)
                simp only [esSetH_costW, _root_.CryptoGames.SM.Engine.esG,
                  _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cRecPos,
                  _root_.CryptoGames.SM.pGet, exprCostW_letE, exprCostW_ite, exprCostW_pair,
                  exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v2, exprCostW_v3,
                  exprCostW_v4, exprCostW_var, Nat.reduceAdd] at hcm ⊢
                omega
              · refine le_trans (compCostW_caseOpt_le' _ _ _ 5
                  (250 * L + bits maxSkip + 35980) ?_ ?_ ?_) (by omega)
                · simp only [exprCostW_fst, exprCostW_v0, Nat.reduceAdd]; omega
                · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_snd,
                    exprCostW_v0, Nat.reduceAdd]; omega
                · have hmbc1 := cMustBeCorrectE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
                    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L maxSkip (Γ' := Γ_dl4)
                    (_root_.CryptoGames.SM.Engine.esG (.fst .v6)) (.fst (.snd .v6)) .v5
                  have hch := cChallContainsE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
                    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl4)
                    (_root_.CryptoGames.SM.Engine.esG (.fst .v6)) (_root_.CryptoGames.SM.Engine.cRecPos .v5)
                  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.cRecPos,
                    exprCostW_fst, exprCostW_snd, exprCostW_v5, exprCostW_v6, Nat.reduceAdd]
                    at hmbc1 hch
                  simp only [_root_.CryptoGames.SM.Engine.esG, esSetG_costW, cGsSetWin_costW,
                    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cRecMsg,
                    _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx, ckaOpC,
                    compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_none,
                    exprCostW_some, exprCostW_inr, exprCostW_bool, exprCostW_eqN, exprCostW_not,
                    exprCostW_and, exprCostW_ite, exprCostW_op,
                    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4,
                    exprCostW_v5, exprCostW_v6, exprCostW_var, Nat.reduceAdd]
                  omega

private theorem injectEC_bucket_costW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L qep : ℕ) (tL : Option ℕ)
    {W_o W_s W_r W_cm W_rv : ℕ} (hhk : HooksCostWBounded B0 sC qC hk W_o W_s W_r W_cm W_rv)
    {Γ'} (es : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compCostW (ckaOpC B0) sC qC (_root_.CryptoGames.SM.Engine.injectEC hk L (2 + 1) qep
        (bucketAuthCfgEC 1 tL) es arg) ≤
      exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) arg +
        W_o + W_r + W_cm + 700 * L + bits qep + 2 * bits (tL.getD 0) + 8000 := by
  have hbq1 := bits_succ_le qep
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  let Γ_ij1 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0
  have hit := cInTransitE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_costW_le hk hhk (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v0)) (_root_.CryptoGames.SM.Engine.esG (.fst .v0))
    (.fst (.snd .v0))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have htrv := cTrivialE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3))
    (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_costW_le hk L hhk (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hvg := validGuessE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ_ij1) (.fst (.snd .v0))
  simp only [esSetH_costW, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_none, exprCostW_not, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_letE, Nat.reduceAdd] at hit hvr htrv hcm hvg
  dsimp only [_root_.CryptoGames.SM.Engine.injectEC, bucketAuthCfgEC]
  refine le_trans (compCostW_bind_le' _ _
    (exprCostW (ckaOpC B0) es + exprCostW (ckaOpC B0) arg + 5)
    (W_o + W_r + W_cm + 700 * L + bits qep + 2 * bits (tL.getD 0) + 7990) ?_ ?_) (by omega)
  · simp only [compCostW_ret, exprCostW_pair, Nat.reduceAdd]; omega
  · refine le_trans (compCostW_ite_le' _ _ _ (250 * L + 500)
      (W_o + W_r + W_cm + 450 * L + bits qep + 2 * bits (tL.getD 0) + 7480) ?_ ?_ ?_) (by omega)
    · simp only [_root_.CryptoGames.SM.Engine.cSafeInjE, _root_.CryptoGames.SM.healedByE,
        _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esAbort,
        _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
        _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.orE,
        _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.otherE,
        _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.minN,
        exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool,
        exprCostW_nat, exprCostW_add, exprCostW_lt, exprCostW_not, exprCostW_and,
        exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_caseOpt,
        exprCostW_letE, hb0, hb1, hb2, hb3, Nat.reduceAdd]
      omega
    · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_fst, exprCostW_v0,
        Nat.reduceAdd]; omega
    · refine le_trans (compCostW_bind_le' _ _ (W_o + W_r + 1600)
        (W_cm + 450 * L + bits qep + 2 * bits (tL.getD 0) + 5850) ?_ ?_) (by omega)
      · simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
          _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.pGet,
          exprCostW_letE, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
          exprCostW_none, exprCostW_v0, exprCostW_var, Nat.reduceAdd]
        omega
      · refine le_trans (compCostW_caseOpt_le' _ _ _ 5
          (W_cm + 450 * L + bits qep + 2 * bits (tL.getD 0) + 5830) ?_ ?_ ?_) (by omega)
        · simp only [exprCostW_fst, exprCostW_v0, Nat.reduceAdd]; omega
        · simp only [_root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
            compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_bool, exprCostW_fst,
            exprCostW_snd, exprCostW_v0, exprCostW_v1, Nat.reduceAdd]; omega
        · refine le_trans (compCostW_caseOpt_le' _ _ _ 5
            (W_cm + 450 * L + bits qep + 2 * bits (tL.getD 0) + 5810) ?_ ?_ ?_) (by omega)
          · simp only [exprCostW_v0]; omega
          · simp only [esSetH_costW,
              compCostW_ret, exprCostW_pair, exprCostW_some, exprCostW_inl,
              exprCostW_unit, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1,
              exprCostW_v2, exprCostW_var, Nat.reduceAdd]; omega
          · refine le_trans (compCostW_ite_le' _ _ _ (bits qep + 20)
              (W_cm + 450 * L + 2 * bits (tL.getD 0) + 5780) ?_ ?_ ?_) (by omega)
            · simp only [exprCostW_lt, exprCostW_nat, exprCostW_fst, exprCostW_snd, exprCostW_v0,
                Nat.reduceAdd]; omega
            · simp only [esSetH_costW,
                compCostW_ret, exprCostW_pair, exprCostW_some, exprCostW_inl,
                exprCostW_unit, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v2,
                exprCostW_v3, exprCostW_var, Nat.reduceAdd]; omega
            · refine le_trans (compCostW_ite_le' _ _ _ (60 * L + 400)
                (W_cm + 390 * L + 2 * bits (tL.getD 0) + 5350) ?_ ?_ ?_) (by omega)
              · simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.otherE,
                  exprCostW_not, exprCostW_pair, exprCostW_fst, exprCostW_snd,
                  exprCostW_v0, exprCostW_v3, Nat.reduceAdd]; omega
              · refine le_trans (compCostW_bind_le' _ _ (W_cm + 200 * L + 2000) 200 ?_ ?_)
                  (by omega)
                · simp only [esSetH_costW, _root_.CryptoGames.SM.Engine.esG,
                    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.otherE,
                    _root_.CryptoGames.SM.pGet, exprCostW_letE, exprCostW_not, exprCostW_ite,
                    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v2,
                    exprCostW_v3, exprCostW_var, Nat.reduceAdd]
                  omega
                · simp only [esSetG_costW,
                    compCostW_caseOpt, compCostW_ret, exprCostW_pair, exprCostW_fst,
                    exprCostW_snd, exprCostW_none, exprCostW_some, exprCostW_inr,
                    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var, Nat.reduceAdd]
                  omega
              · simp only [esSetH_costW, esSetG_costW, cGsSetWin_costW,
                  _root_.CryptoGames.SM.Engine.esG,
                  compCostW_ret, exprCostW_pair, exprCostW_some, exprCostW_inl,
                  exprCostW_unit, exprCostW_bool, exprCostW_ite, exprCostW_fst, exprCostW_snd,
                  exprCostW_v0, exprCostW_v2, exprCostW_v3, exprCostW_var, Nat.reduceAdd]
                omega

private structure BoxEq (a b : ℕ) : Prop where
  eq : a = b

private theorem box_le {x y : ℕ} (h : x ≤ y) : ∃ n : ℕ, BoxEq x n ∧ n ≤ y :=
  ⟨x, ⟨rfl⟩, h⟩

/-- Generic weighted step-cost bound for `redPRNGAuthBucketHybridProg`. -/
theorem redPRNGAuthBucketHybridProg_generic_costW_le
    (B0 L qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    let R := redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qep maxSkip tL t
    compCostW (ckaOpC B0) ckaSampC prngQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish ≤
          200 * L + bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 10000 ∧
      compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle ≤
        20 * B0 + 3 * bits B0 + 7000 * L + 4 * bits qep + 6 * bits (tL.getD 0) +
          2 * bits t + 5 * bits (healEpoch tL) + bits maxSkip + 2800000 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hhkF := hooksPRNGBucketAuthForgedHdrC_costWBounded (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep tL t
  have hhkM := hooksPRNGBucketAuthMainC_costWBounded (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep tL t
  constructor
  · have hinit := initPRNGBucketAuthEStateC_costW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := [.bool, .unit]) (.bool false)
    let Γf : List (Ty S_cka) :=
      .nat :: .prod pbaEsT (.opt .nat) :: [pbaS2T, .bool]
    have hopt := optNatLit_costW_le (O' := OO_cka) (ckaOpC B0) (Γ' := Γf) tL
    have haok := cAuthOKE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γf)
      (_root_.CryptoGames.SM.Engine.optNatLit tL) .v0 (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    simp only [_root_.CryptoGames.SM.Engine.esG, exprCostW_bool, exprCostW_fst, exprCostW_v0,
      exprCostW_v1, Nat.reduceAdd] at hinit haok
    rcases box_le hinit with ⟨cinit, hinit_eq, hinit⟩
    rcases box_le hopt with ⟨copt, hopt_eq, hopt⟩
    rcases box_le haok with ⟨caok, haok_eq, haok⟩
    simp only [redPRNGAuthBucketHybridProg, _root_.CryptoGames.SM.Engine.esAbort,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.cGsWin,
      ckaSampC, exprCostW_rename, compCostW_rename,
      compCostW_bind, compCostW_ret, compCostW_caseOpt, compCostW_sample,
      exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_unit, exprCostW_bool,
      exprCostW_none, exprCostW_not, exprCostW_and, exprCostW_pair, exprCostW_fst, exprCostW_snd,
      hinit_eq.eq, hopt_eq.eq, haok_eq.eq, Nat.reduceAdd]
    omega
  · let esT := pbaEsT
    let stT := pbaS2T
    let qT := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
    let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γh0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) (.prod .bool qT)) :: [stT, qT]
    let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
    let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
    let dlQ : Ty S_cka := .prod .bool hdrCtT
    let Γ_tr0 : List (Ty S_cka) :=
      trQ :: .sum trQ chQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_tr1 : List (Ty S_cka) := trQ :: Γ_tr0
    let Γ_tr2 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy pbaVpT :: Γ_tr1
    let Γ_tr3 : List (Ty S_cka) :=
      .prod pbaVpT hdrCtT :: .prod (.opt (.prod pbaVpT hdrCtT)) pbaHsT :: Γ_tr2
    let Γ_dl : List (Ty S_cka) :=
      dlQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_ij0 : List (Ty S_cka) := dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_cr : List (Ty S_cka) := .bool :: Γh0
    have hepm := cEpMgmtE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 qep (Γ' := Γ_tr1)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0)
      (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
    have hvsF := vSendC_costW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) hhkF (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hvsM := vSendC_costW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) hhkM (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hrec := cRecordE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γ_tr3) .v2 (.fst .v3) (.fst .v0)
      (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
        (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
        (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
    have hdlF := deliverEC_bucket_costW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) L maxSkip tL hhkF (Γ' := Γ_dl)
      (.fst .v3) .v0
    have hdlM := deliverEC_bucket_costW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) L maxSkip tL hhkM (Γ' := Γ_dl)
      (.fst .v3) .v0
    have hhh := isHonestHdrPRNGBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0
      (Γ' := .prod (.opt (_root_.CryptoGames.CKA.ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)) esT :: Γ_ij0)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v3)) (.fst (.snd .v1))
    have hijF := injectEC_bucket_costW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) L qep tL hhkF (Γ' := Γ_ij0) (.fst .v2) .v0
    have hijM := injectEC_bucket_costW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) L qep tL hhkM (Γ' := Γ_ij0) (.fst .v2) .v0
    have hca := cCorrAllowedE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    have hac := cAfterCorrE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L
      (Γ' := psT :: .prod (.opt psT) pbaHsT :: Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) .v2
    have hrvF := prngBucketAuthForgedHdrRevealC_costW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 tL (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v1))
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
    have hrvM := prngBucketAuthRevealC_costW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 tL (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v1))
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
    simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.pGet,
      _root_.CryptoGames.SM.isSomeE, exprCostW_rename, exprCostW_letE,
      exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
      exprCostW_v4, exprCostW_v5, exprCostW_v6, exprCostW_var, exprCostW_bool, exprCostW_nat,
      exprCostW_none, exprCostW_add, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
      exprCostW_caseOpt, hb0, hb1, Nat.reduceAdd]
      at hepm hvsF hvsM hrec hdlF hdlM hhh hijF hijM hca hac hrvF hrvM
    rcases box_le hepm with ⟨cepm, hepm_eq, hepm⟩
    rcases box_le hvsF with ⟨cvsF, hvsF_eq, hvsF⟩
    rcases box_le hvsM with ⟨cvsM, hvsM_eq, hvsM⟩
    rcases box_le hrec with ⟨crec, hrec_eq, hrec⟩
    rcases box_le hdlF with ⟨cdlF, hdlF_eq, hdlF⟩
    rcases box_le hdlM with ⟨cdlM, hdlM_eq, hdlM⟩
    rcases box_le hhh with ⟨chh, hhh_eq, hhh⟩
    rcases box_le hijF with ⟨cijF, hijF_eq, hijF⟩
    rcases box_le hijM with ⟨cijM, hijM_eq, hijM⟩
    rcases box_le hca with ⟨cca, hca_eq, hca⟩
    rcases box_le hac with ⟨cac, hac_eq, hac⟩
    rcases box_le hrvF with ⟨crvF, hrvF_eq, hrvF⟩
    rcases box_le hrvM with ⟨crvM, hrvM_eq, hrvM⟩
    let K0 : ℕ := 20 * B0 + 3 * bits B0 + 7000 * L + 4 * bits qep + 6 * bits (tL.getD 0) +
      2 * bits t + 5 * bits (healEpoch tL) + bits maxSkip
    dsimp only [redPRNGAuthBucketHybridProg]
    refine le_trans (compCostW_bind_le' _ _ 20 (K0 + 2799975) ?_ ?_) (by dsimp [K0]; omega)
    · simp only [compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd,
        exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
      omega
    · refine le_trans (compCostW_ite_le' _ _ _ 6 (K0 + 2799965) ?_ ?_ ?_) (by omega)
      · simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]; omega
      all_goals
        refine le_trans (compCostW_caseSum_le' _ _ _ 6 (K0 + 2799955) ?_ ?_ ?_) (by omega)
        · simp only [exprCostW_snd, exprCostW_v0, Nat.reduceAdd]; omega
        · refine le_trans (compCostW_caseSum_le' _ _ _ 2 (K0 + 2799945) ?_ ?_ ?_) (by omega)
          · simp only [exprCostW_v0]; omega
          · refine le_trans (compCostW_caseSum_le' _ _ _ 2 (K0 + 2799935) ?_ ?_ ?_) (by omega)
            · simp only [exprCostW_v0]; omega
            · refine le_trans (compCostW_caseSum_le' _ _ _ 2 (K0 + 2799925) ?_ ?_ ?_) (by omega)
              · simp only [exprCostW_v0]; omega
              · dsimp only [K0]
                simp only [_root_.CryptoGames.SM.Engine.esMk,
                  _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
                  _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
                  _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
                  _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
                  _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
                  exprCostW_rename, compCostW_rename,
                  compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
                  exprCostW_letE, exprCostW_caseOpt, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
                  exprCostW_v4, exprCostW_v5, exprCostW_v6, exprCostW_v7, exprCostW_var, exprCostW_bool,
                  exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_inr, exprCostW_add,
                  exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst,
                  exprCostW_snd, hb0, hb1, hepm_eq.eq, hvsF_eq.eq, hvsM_eq.eq, hrec_eq.eq, Nat.reduceAdd]
                generalize bits B0 = bB at *
                omega
              · simp only [compCostW_ret, exprCostW_pair, exprCostW_inl, exprCostW_inr,
                  exprCostW_none, exprCostW_fst, exprCostW_snd, exprCostW_v4, exprCostW_var,
                  Nat.reduceAdd]
                omega
            · dsimp only [K0]
              simp only [compCostW_bind, compCostW_ret, exprCostW_pair, exprCostW_inl,
                exprCostW_inr, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v3,
                exprCostW_v4, exprCostW_var, hdlF_eq.eq, hdlM_eq.eq, Nat.reduceAdd]
              generalize bits B0 = bB at *
              omega
          · dsimp only [K0]
            simp only [_root_.CryptoGames.SM.Engine.esMk,
              _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
              _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
              _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
              _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
              _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
              exprCostW_rename, compCostW_rename,
              compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
              exprCostW_letE, exprCostW_caseOpt, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
              exprCostW_v4, exprCostW_v5, exprCostW_v6, exprCostW_v7, exprCostW_var, exprCostW_bool,
              exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_inr, exprCostW_add,
              exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst,
              exprCostW_snd, hb0, hb1, hhh_eq.eq, hijF_eq.eq, hijM_eq.eq, Nat.reduceAdd]
            generalize bits B0 = bB at *
            omega
        · dsimp only [K0]
          simp only [_root_.CryptoGames.SM.Engine.esMk,
            _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
            _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
            _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
            _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
            _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
            exprCostW_rename, compCostW_rename,
            compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
            exprCostW_letE, exprCostW_caseOpt, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
            exprCostW_v4, exprCostW_v5, exprCostW_v6, exprCostW_v7, exprCostW_var, exprCostW_bool,
            exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_inr, exprCostW_add,
            exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst,
            exprCostW_snd, hb0, hb1, hca_eq.eq, hac_eq.eq, hrvF_eq.eq, hrvM_eq.eq, Nat.reduceAdd]
          generalize bits B0 = bB at *
          omega

/-- Atomic step-cost parts bound (`init + finish` and `handle`) for
`redPRNGAuthBucketHybridProg` against `fig8AtomicStepBound q qep`. -/
theorem redPRNGAuthBucketHybridProg_parts_le_qep (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2)
    (htL : tL ∈ _root_.CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1)) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL t
    compCostW (ckaOpC B0) ckaSampC prngQueryC R.init +
        compCostW (ckaOpC B0) ckaSampC prngQueryC R.finish + 100000 ≤ fig8AtomicStepBound q qep ∧
      compCostW (ckaOpC B0) ckaSampC prngQueryC R.handle + 200000 ≤ fig8AtomicStepBound q qep := by
  have htL_all : ∀ x, tL = some x → x ≤ qep + 3 := by
    intro x hx
    subst hx
    simp only [_root_.CryptoGames.SM.admissibleLastLeakGuesses, Finset.mem_insert,
      Finset.mem_image, Finset.mem_range, reduceCtorEq, Option.some.injEq, false_or] at htL
    rcases htL with ⟨y, hy, rfl⟩
    omega
  have hgetD : tL.getD 0 ≤ qep + 3 := optGetD_le_of_forall_some htL_all
  have hheal : healEpoch tL ≤ qep + 6 := healEpoch_le_of_forall_some htL_all
  have hbt : bits t ≤ bits qep + 2 := bits_le_bits_add (by omega : t ≤ qep + 2)
  have hbg : bits (tL.getD 0) ≤ bits qep + 3 := bits_le_bits_add hgetD
  have hbh : bits (healEpoch tL) ≤ bits qep + 6 := bits_le_bits_add hheal
  have hmfj : bits maxForwardJumps ≤ 25001 := by
    have := bits_le_add_one maxForwardJumps
    have : maxForwardJumps = 25000 := rfl
    omega
  have hbB0 : bits ((q + 1) * (maxForwardJumps + 1)) ≤
      (q + 1) * (maxForwardJumps + 1) + 1 :=
    bits_le_add_one ((q + 1) * (maxForwardJumps + 1))
  obtain ⟨hIF, hH⟩ := redPRNGAuthBucketHybridProg_generic_costW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) ((q + 1) * (maxForwardJumps + 1)) (q + 1) qep
    maxForwardJumps tL t
  unfold fig8AtomicStepBound
  dsimp only at hIF hH ⊢
  generalize bits qep = bq at hbt hbg hbh hIF hH ⊢
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hbB0 hH
  generalize bits t = bt at hbt hIF hH
  generalize bits (tL.getD 0) = bg at hbg hIF hH
  generalize bits (healEpoch tL) = bh at hbh hIF hH
  generalize bits maxForwardJumps = bm at hmfj hH
  generalize (q + 1) * (maxForwardJumps + 1) = B at hbB0 hIF hH ⊢
  omega

/-! ### Weighted AST-Size (`compSizeW`) Bounds for `redPRNGAuthBucketHybridProg` -/

private theorem postLeakBucketE_sizeW_le (B0 : ℕ) (tL : Option ℕ) {vpT : Ty S_cka} {Γ'}
    (ctx : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprSizeW (ckaOpS B0) (postLeakBucketE tL ctx) ≤
      exprSizeW (ckaOpS B0) ctx + bits (tL.getD 0) + 25 := by
  cases tL <;> ·
    simp only [postLeakBucketE, _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.ltOptE,
      _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.Engine.optNatLit, Option.getD,
      exprSizeW_renameM, exprSizeW_letE, exprSizeW_caseOpt, exprSizeW_pair, exprSizeW_fst,
      exprSizeW_snd, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_not,
      exprSizeW_lt, exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd]
    omega

private theorem validGuessE3_sizeW_le (B0 : ℕ) (tL : Option ℕ) {Γ'} (tE : Expr OO_cka Γ' .nat) :
    exprSizeW (ckaOpS B0)
      (_root_.CryptoGames.SM.validGuessE 3 (_root_.CryptoGames.SM.Engine.optNatLit tL) tE) ≤
      8 * exprSizeW (ckaOpS B0) tE + 4 * bits (tL.getD 0) + 100 := by
  cases tL <;> ·
    simp only [_root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
      _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
      _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
      _root_.CryptoGames.SM.Engine.optNatLit, Option.getD, exprSizeW_renameM,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_some, exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, bits_four,
      Nat.reduceAdd]
    omega

private theorem rootPRNGBucketAuthHybridC_sizeW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT) (tE : Expr OO_cka Γ' .nat) (plE : Expr OO_cka Γ' .bool)
    (ikE : Expr OO_cka Γ' (.base .i)) (σvE : Expr OO_cka Γ' (.opt (.base .sig))) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (rootPRNGBucketAuthHybridC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE tE plE ikE σvE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) plE +
        exprSizeW (ckaOpS B0) ikE + exprSizeW (ckaOpS B0) σvE +
        bits L + 2 * bits t + 3 * bits (healEpoch tL) + 4000 := by
  simp only [rootPRNGBucketAuthHybridC, lookupPRNGBucketAuthFC, pbaTableLookupE,
    resolveCorrRootE, pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetFTblAt, pbaHsSetCorrRoot,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE,
    ckaOpS, ckaSampS, ckaQueryS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_sample,
    compSizeW_query,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
    exprSizeW_cons, exprSizeW_sub, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, Nat.reduceAdd]
  omega

private theorem prngBucketAuthStartSendC_sizeW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (rE : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (prngBucketAuthStartSendC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t hE ctxE pE tE γE σvE rE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σvE +
        exprSizeW (ckaOpS B0) rE +
        bits L + bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 6000 := by
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT)
    (.prod .nat (.prod (.base .γ) (.prod (.opt (.base .sig)) (.opt (.base .ccoins))))))
  let Γ0 : List (Ty S_cka) := .base .ccoins :: tupT :: Γ'
  have hpl := postLeakBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v1))
  have hrt := rootPRNGBucketAuthHybridC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := Γ0)
    (.fst .v1) (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0))))
    (.fst (.snd (.snd (.snd (.snd .v1)))))
  simp only [ckaOpS, exprSizeW_op, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at hpl hrt
  simp only [prngBucketAuthStartSendC, pbaHsCache, pbaHsSetCache,
    ckaOpS, ckaSampS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_caseOpt, compSizeW_sample,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_unit, exprSizeW_none, exprSizeW_some, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_op, exprSizeW_tset, Nat.reduceAdd]
  omega

private theorem prngBucketAuthStartRecvC_sizeW_le (B0 L qep : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (tnE : Expr OO_cka Γ' (.base .t)) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (prngBucketAuthStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep tL t hE ctxE pE tE γE σvE tnE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σvE +
        exprSizeW (ckaOpS B0) tnE +
        bits L + bits qep + 5 * bits (tL.getD 0) + 2 * bits t + 2 * bits (healEpoch tL) + 6000 := by
  have hbq1 := bits_succ_le qep
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT)
    (.prod .nat (.prod (.base .γ) (.prod (.opt (.base .sig)) (.base .t)))))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hpl := postLeakBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v0))
  have hvg := validGuessE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd (.snd .v0)))
  simp only [exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, Nat.reduceAdd] at hpl hvg
  dsimp only [prngBucketAuthStartRecvC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [lookupPRNGBucketAuthFC, pbaTableLookupE, resolveCorrRootE,
    pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetFTblAt,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE,
    ckaOpS, ckaSampS, ckaQueryS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_sample,
    compSizeW_query,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
    exprSizeW_cons, exprSizeW_sub, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt,
    exprSizeW_letE, exprSizeW_op, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
    bits_zero, bits_one, Nat.reduceAdd]
  omega

private theorem prngBucketAuthMainStartRecvC_sizeW_le (B0 qep : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σvE : Expr OO_cka Γ' (.opt (.base .sig)))
    (tnE : Expr OO_cka Γ' (.base .t)) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (prngBucketAuthMainStartRecvC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) 1 qep tL hE ctxE pE tE γE σvE tnE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) tE + exprSizeW (ckaOpS B0) γE + exprSizeW (ckaOpS B0) σvE +
        exprSizeW (ckaOpS B0) tnE +
        bits qep + 4 * bits (tL.getD 0) + bits (healEpoch tL) + 3000 := by
  have hbq1 := bits_succ_le qep
  let tupT : Ty S_cka := .prod pbaHsT (.prod .nat (.prod (.base .γ) (.base .t)))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hvg := validGuessE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd .v0))
  simp only [exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, Nat.reduceAdd] at hvg
  dsimp only [prngBucketAuthMainStartRecvC]
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [resolveCorrRootE, pbaHsCache, pbaHsCorrRoot,
    ckaOpS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
    exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_op, exprSizeW_tget, Nat.reduceAdd]
  omega

private theorem prngBucketAuthRevealC_sizeW_le (B0 : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' pbaVpT) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (prngBucketAuthRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) vpE + bits (tL.getD 0) + 2 * bits (healEpoch tL) + 2000 := by
  let tupT : Ty S_cka := .prod pbaHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT) pbaVpT)
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  have hpl := postLeakBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := pbaVpT) (Γ' := Γ0) (.fst (.snd .v0))
  simp only [exprSizeW_fst, exprSizeW_snd, exprSizeW_v0, Nat.reduceAdd] at hpl
  simp only [prngBucketAuthRevealC, resolveCorrRootE,
    pbaHsCache, pbaHsFTbl, pbaHsCorrRoot, pbaHsSetCorrRoot,
    _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.vpId,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpTcur, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.cGsEpoch, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.isSomeE, ckaQueryS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_query,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
    exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    bits_zero, Nat.reduceAdd]
  omega

private theorem prngBucketAuthForgedHdrRevealC_sizeW_le (B0 : ℕ) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy pbaVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' pbaVpT) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (prngBucketAuthForgedHdrRevealC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) tL hE ctxE pE vpE) ≤
      exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) ctxE + exprSizeW (ckaOpS B0) pE +
        exprSizeW (ckaOpS B0) vpE + 2 * bits (healEpoch tL) + 1500 := by
  simp only [prngBucketAuthForgedHdrRevealC, _root_.CryptoGames.SM.Engine.realPartyE,
    _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpΓ,
    _root_.CryptoGames.SM.Engine.vpRoot, _root_.CryptoGames.SM.Engine.vpVS,
    _root_.CryptoGames.SM.Engine.vpVR, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.vpTcurNat, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some,
    exprSizeW_lt, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, bits_zero, Nat.reduceAdd]
  omega

private theorem hooksPRNGBucketAuthForgedHdrC_sizeBounded (B0 L qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (hooksPRNGBucketAuthForgedHdrC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep tL t)
      (bits L + bits qep + 5 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 6000)
      500 (5 * bits B0 + 1500) where
  startSend_le hE ctxE pE tE γE σvE rE :=
    (prngBucketAuthStartSendC_sizeW_le B0 L tL t hE ctxE pE tE γE σvE rE).trans (by omega)
  startRecv_le hE ctxE pE tE γE σvE tnE :=
    (prngBucketAuthStartRecvC_sizeW_le B0 L qep tL t hE ctxE pE tE γE σvE tnE).trans (by omega)
  fsSend_le hE ctxE pE tE ssE hdrE mE pairE := by
    simp only [hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC, prngBucketAuthFsSendC,
      ckaOpS, compSizeW_ret, exprSizeW_pair, exprSizeW_some, exprSizeW_op, Nat.reduceAdd]
    omega
  fsRecv_le hE ctxE pE tE rsE hdrE eE recE := by
    simp only [hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC, prngBucketAuthFsRecvC,
      ckaOpS, compSizeW_ret, exprSizeW_pair, exprSizeW_some, exprSizeW_op, Nat.reduceAdd]
    omega
  commit_le hE ctxE pE oldE newE := by
    simp only [hooksPRNGBucketAuthForgedHdrC, hooksPRNGBucketAuthC, prngBucketAuthCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some, Nat.reduceAdd]
    omega
  reveal_le hE ctxE pE vpE :=
    (prngBucketAuthForgedHdrRevealC_sizeW_le B0 tL hE ctxE pE vpE).trans (by omega)

private theorem hooksPRNGBucketAuthMainC_sizeBounded (B0 L qep : ℕ) (tL : Option ℕ) (t : ℕ) :
    HooksSizeBounded B0 ckaSampS ckaQueryS
      (hooksPRNGBucketAuthMainC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep tL t)
      (bits L + bits qep + 5 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 6000)
      500 (5 * bits B0 + 1500) where
  startSend_le hE ctxE pE tE γE σvE rE :=
    (prngBucketAuthStartSendC_sizeW_le B0 L tL t hE ctxE pE tE γE σvE rE).trans (by omega)
  startRecv_le hE ctxE pE tE γE σvE tnE :=
    (prngBucketAuthMainStartRecvC_sizeW_le B0 qep tL hE ctxE pE tE γE σvE tnE).trans (by omega)
  fsSend_le hE ctxE pE tE ssE hdrE mE pairE := by
    simp only [hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthFsSendC,
      ckaOpS, compSizeW_ret, exprSizeW_pair, exprSizeW_some, exprSizeW_op, Nat.reduceAdd]
    omega
  fsRecv_le hE ctxE pE tE rsE hdrE eE recE := by
    simp only [hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthFsRecvC,
      ckaOpS, compSizeW_ret, exprSizeW_pair, exprSizeW_some, exprSizeW_op, Nat.reduceAdd]
    omega
  commit_le hE ctxE pE oldE newE := by
    simp only [hooksPRNGBucketAuthMainC, hooksPRNGBucketAuthC, prngBucketAuthCommitC,
      compSizeW_ret, exprSizeW_pair, exprSizeW_some, Nat.reduceAdd]
    omega
  reveal_le hE ctxE pE vpE :=
    (prngBucketAuthRevealC_sizeW_le B0 tL hE ctxE pE vpE).trans (by omega)

private theorem initPRNGBucketAuthEStateC_sizeW_le (B0 L : ℕ) (tL : Option ℕ) (t : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS
      (initPRNGBucketAuthEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L tL t bE) ≤
      exprSizeW (ckaOpS B0) bE + bits L + 2 * bits t + 3 * bits (healEpoch tL) + 9000 := by
  let Γ0 : List (Ty S_cka) := .base .kc :: .bool :: Γ'
  have hrt := rootPRNGBucketAuthHybridC_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := Γ0)
    pbaHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit) .none
  simp only [pbaHsEmptyE, ckaOpS, exprSizeW_pair, exprSizeW_tconst, exprSizeW_none,
    exprSizeW_nil, exprSizeW_nat, exprSizeW_bool, exprSizeW_op, exprSizeW_unit,
    bits_zero, Nat.reduceAdd] at hrt
  simp only [initPRNGBucketAuthEStateC, pbaHsEmptyE, abortedPartiesE,
    _root_.CryptoGames.SM.Engine.mkPartiesE, _root_.CryptoGames.SM.Engine.cGsInitE,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.vpMk, ckaOpS, ckaSampS, exprSizeW_renameM, compSizeW_renameM,
    compSizeW_bind, compSizeW_ret, compSizeW_caseOpt, compSizeW_sample,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_unit, exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_nil,
    exprSizeW_some, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_letE,
    exprSizeW_op, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset, bits_zero, Nat.reduceAdd]
  omega

private theorem isHonestHdrPRNGBucketE_sizeW_le (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' pbaHsT)
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprSizeW (ckaOpS B0) (isHonestHdrPRNGBucketE hE hdrE) ≤
      4 * (exprSizeW (ckaOpS B0) hE + exprSizeW (ckaOpS B0) hdrE) + 500 := by
  simp only [isHonestHdrPRNGBucketE, pbaHsCache, ckaOpS, exprSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_pair,
    exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_op,
    exprSizeW_tget, Nat.reduceAdd]
  omega

private theorem cEpMgmtE3_sizeW_le {vpT : Ty S_cka} (B0 qep : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p bad : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cEpMgmtE (2 + 1) qep s p bad) ≤
      20 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p + exprSizeW (ckaOpS B0) bad) +
        4 * bits qep + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cEpMgmtE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cLeakE, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.sendsInE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet, _root_.CryptoGames.SM.boolEq,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_cons,
    exprSizeW_add, exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and,
    exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt,
    exprSizeW_letE, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

private theorem cRecordE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) (st' : Expr OO_cka Γ' vpT)
    (r : Expr OO_cka Γ' _root_.CryptoGames.SM.Engine.cRecTy)
    (isChall : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cRecordE L (2 + 1) s p st' r isChall) ≤
      20 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p + exprSizeW (ckaOpS B0) st' +
        exprSizeW (ckaOpS B0) r + exprSizeW (ckaOpS B0) isChall) + 4 * bits L + 1000 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cRecordE, _root_.CryptoGames.SM.Engine.cSafeChE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_cons, exprSizeW_add, exprSizeW_lt,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_tget, exprSizeW_tset, bits_three, Nat.reduceAdd]
  omega

private theorem cTrivialE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cTrivialE L (2 + 1) s pos) ≤
      8 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) pos) + 4 * bits L + 500 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cTrivialE, _root_.CryptoGames.SM.Engine.cCompContainsE,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsTrans,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cRecPos,
    _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_add, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_anyB, exprSizeW_tget, bits_three, Nat.reduceAdd]
  omega

private theorem cCorrAllowedE_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cCorrAllowedE L s p) ≤
      8 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p) + 4 * bits L + 500 := by
  simp only [_root_.CryptoGames.SM.Engine.cCorrAllowedE,
    _root_.CryptoGames.SM.Engine.cCompContainsE, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsComp,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_var,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_letE, exprSizeW_anyB, exprSizeW_tget, Nat.reduceAdd]
  omega

private theorem cAfterCorrE_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cAfterCorrE L s p) ≤
      40 * (exprSizeW (ckaOpS B0) s + exprSizeW (ckaOpS B0) p) + 20 * bits L + 8000 := by
  simp only [_root_.CryptoGames.SM.Engine.cAfterCorrE, _root_.CryptoGames.SM.Engine.cLeakE,
    _root_.CryptoGames.SM.Engine.cCompInsertE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.maxOptE, _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_var,
    exprSizeW_bool, exprSizeW_some, exprSizeW_cons, exprSizeW_lt,
    exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_caseOpt, exprSizeW_letE, exprSizeW_foldrB, exprSizeW_tget, exprSizeW_tset,
    Nat.reduceAdd]
  omega

private theorem cAuthOKE3_sizeW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (tLStar : Expr OO_cka Γ' (.opt .nat)) (tStar : Expr OO_cka Γ' .nat)
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT)) :
    exprSizeW (ckaOpS B0) (_root_.CryptoGames.SM.Engine.cAuthOKE L (2 + 1) tLStar tStar s) ≤
      8 * (exprSizeW (ckaOpS B0) tLStar + exprSizeW (ckaOpS B0) tStar + exprSizeW (ckaOpS B0) s) +
        10 * bits L + 500 := by
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cAuthOKE, _root_.CryptoGames.SM.Engine.cCanonE,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.validGuessE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.optNatEqE, _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
    exprSizeW_renameM, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_bool, exprSizeW_nat, exprSizeW_none, exprSizeW_some, exprSizeW_add,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    exprSizeW_anyB, exprSizeW_foldrB, bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

private theorem deliverEC_bucket_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L maxSkip : ℕ) (tL : Option ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (_root_.CryptoGames.SM.Engine.deliverEC hk L maxSkip (bucketAuthCfgEC 1 tL) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 9 * bits L + 5 * bits maxSkip + 6000 := by
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := _root_.CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v1)) (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    (.fst (.snd .v1))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: _root_.CryptoGames.SM.Engine.cRecTy :: Γ_dl0)
    (_root_.CryptoGames.SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (_root_.CryptoGames.SM.Engine.cRecPos .v3)
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esSetH, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.otherE, exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
    exprSizeW_v4, exprSizeW_var, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_some, exprSizeW_letE, Nat.reduceAdd] at hit hvr hcm
  simp only [_root_.CryptoGames.SM.Engine.deliverEC, _root_.CryptoGames.SM.Engine.cCompContainsE,
    _root_.CryptoGames.SM.Engine.cChallContainsE, _root_.CryptoGames.SM.Engine.cMustBeCorrectE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
    _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
    _root_.CryptoGames.SM.Engine.esSetG, _root_.CryptoGames.SM.Engine.esSetH,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSetWin,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cRecMsg,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxAccGet, _root_.CryptoGames.SM.posEq,
    _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch,
    _root_.CryptoGames.SM.posIdx, ckaOpS, exprSizeW_renameM, compSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_nil, exprSizeW_add, exprSizeW_sub, exprSizeW_mulK, exprSizeW_divK,
    exprSizeW_modK, exprSizeW_lt, exprSizeW_eqN, exprSizeW_not, exprSizeW_and, exprSizeW_ite,
    exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, exprSizeW_inl, exprSizeW_inr, exprSizeW_some,
    exprSizeW_caseOpt, exprSizeW_caseSum, exprSizeW_letE, exprSizeW_op, exprSizeW_cons,
    exprSizeW_len, exprSizeW_take, exprSizeW_appendL, exprSizeW_findB, exprSizeW_anyB,
    exprSizeW_mapB, exprSizeW_foldrB, exprSizeW_tconst, exprSizeW_tget, exprSizeW_tset,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
    bits_zero, bits_one, bits_two, bits_three, bits_four, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd]
  omega

private theorem injectEC_bucket_sizeW_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sS : I'.smp.Samp → ℕ} {qS : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : _root_.CryptoGames.SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (Ho Hs Hr L qep : ℕ) (tL : Option ℕ)
    (hhk : HooksSizeBounded B0 sS qS hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (_root_.CryptoGames.SM.Engine.esTy (@_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    compSizeW (ckaOpS B0) sS qS
      (_root_.CryptoGames.SM.Engine.injectEC hk L (2 + 1) qep (bucketAuthCfgEC 1 tL) es arg) ≤
      6 * (exprSizeW (ckaOpS B0) es + exprSizeW (ckaOpS B0) arg) +
        2 * Ho + Hr + 10 * bits L + 4 * bits qep + 6 * bits (tL.getD 0) + 6000 := by
  have hbq1 := bits_succ_le qep
  let vpT := @_root_.CryptoGames.SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := _root_.CryptoGames.SM.Engine.esTy vpT hsT
  let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ'
  let Γ_ij1 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0
  have hit := cInTransitE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v0)) (_root_.CryptoGames.SM.otherE (.fst (.snd .v0)))
    (.snd (.snd .v0))
  have hvr := vRecvC_sizeW_le hk Ho Hs Hr hhk (Γ' := Γ_ij0)
    (_root_.CryptoGames.SM.Engine.esH (.fst .v0)) (_root_.CryptoGames.SM.Engine.esG (.fst .v0))
    (.fst (.snd .v0))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have htrv := cTrivialE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3))
    (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_sizeW_le hk Ho Hs Hr L hhk (Γ' := Γ_ij1)
    (_root_.CryptoGames.SM.Engine.esSetH (.fst .v3) (.snd .v2))
    (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0)
    (.pair (_root_.CryptoGames.SM.otherE (.fst (.snd .v3)))
      (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hvg := validGuessE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ_ij1) (.fst (.snd .v0))
  simp only [_root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
    _root_.CryptoGames.SM.Engine.esSetH, _root_.CryptoGames.SM.Engine.esMk,
    _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsSt,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.otherE,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_var,
    exprSizeW_none, exprSizeW_not, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
    exprSizeW_letE, Nat.reduceAdd] at hit hvr htrv hcm hvg
  simp only [_root_.CryptoGames.SM.Engine.injectEC,
    bucketAuthCfgEC,
    _root_.CryptoGames.SM.Engine.cSafeInjE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.esG,
    _root_.CryptoGames.SM.Engine.esH, _root_.CryptoGames.SM.Engine.esAbort,
    _root_.CryptoGames.SM.Engine.esSetG, _root_.CryptoGames.SM.Engine.esSetH,
    _root_.CryptoGames.SM.Engine.cGsMk, _root_.CryptoGames.SM.Engine.cGsSetWin,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.otherE,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.minN,
    exprSizeW_renameM, compSizeW_renameM,
    exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
    exprSizeW_v6, exprSizeW_var, exprSizeW_unit, exprSizeW_bool, exprSizeW_nat,
    exprSizeW_none, exprSizeW_some, exprSizeW_inl, exprSizeW_inr, exprSizeW_add,
    exprSizeW_lt, exprSizeW_not, exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst,
    exprSizeW_snd, exprSizeW_caseOpt, exprSizeW_letE,
    compSizeW_ret, compSizeW_bind, compSizeW_ite, compSizeW_caseOpt,
    bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

/-- Generic weighted AST-size bound for `redPRNGAuthBucketHybridProg`. -/
theorem redPRNGAuthBucketHybridProg_generic_sizeW_le
    (B0 L qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    let R := redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qep maxSkip tL t
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.init +
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.handle +
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.finish ≤
        25 * bits B0 + 140 * bits L + 40 * bits qep + 85 * bits (tL.getD 0) +
          35 * bits t + 60 * bits (healEpoch tL) + 10 * bits maxSkip + 250000 := by
  let Ho := bits L + bits qep + 5 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 6000
  let Hs := 500
  let Hr := 5 * bits B0 + 1500
  have hhkF : HooksSizeBounded B0 ckaSampS ckaQueryS
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) Ho Hs Hr :=
    hooksPRNGBucketAuthForgedHdrC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep tL t
  have hhkM : HooksSizeBounded B0 ckaSampS ckaQueryS
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) Ho Hs Hr :=
    hooksPRNGBucketAuthMainC_sizeBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep tL t
  have hIF :
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS
          (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip tL t).init +
        compSizeW (ckaOpS B0) ckaSampS ckaQueryS
          (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip tL t).finish ≤
        12 * bits L + 10 * bits (tL.getD 0) + 2 * bits t + 3 * bits (healEpoch tL) + 11000 := by
    have hinit := initPRNGBucketAuthEStateC_sizeW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L tL t (Γ' := [.bool, .unit]) (.bool false)
    let Γf : List (Ty S_cka) :=
      .nat :: .prod pbaEsT (.opt .nat) :: [pbaS2T, .bool]
    have haok := cAuthOKE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γf)
      (_root_.CryptoGames.SM.Engine.optNatLit tL) .v0 (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    simp only [_root_.CryptoGames.SM.Engine.esG, optNatLit_sizeW, exprSizeW_bool, exprSizeW_fst,
      exprSizeW_v0, exprSizeW_v1, Nat.reduceAdd] at hinit haok
    simp only [redPRNGAuthBucketHybridProg, _root_.CryptoGames.SM.Engine.esAbort,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.cGsWin,
      ckaSampS, exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_caseOpt, compSizeW_sample,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_var, exprSizeW_unit, exprSizeW_bool,
      exprSizeW_none, exprSizeW_not, exprSizeW_and, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      Nat.reduceAdd]
    (try split_ifs at haok) <;> omega
  have hH :
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS
          (redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
            (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
            (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM)
            (eqE := eqE) (lam := lam) (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC)
            (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK)
            L B0 1 qep maxSkip tL t).handle ≤
        25 * bits B0 + 120 * bits L + 35 * bits qep + 75 * bits (tL.getD 0) +
          30 * bits t + 50 * bits (healEpoch tL) + 10 * bits maxSkip + 220000 := by
    let esT := pbaEsT
    let stT := pbaS2T
    let qT := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
    let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γh0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) (.prod .bool qT)) :: [stT, qT]
    let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
    let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
    let dlQ : Ty S_cka := .prod .bool hdrCtT
    let Γ_tr0 : List (Ty S_cka) :=
      trQ :: .sum trQ chQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_tr1 : List (Ty S_cka) := trQ :: Γ_tr0
    let Γ_tr2 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy pbaVpT :: Γ_tr1
    let Γ_tr3 : List (Ty S_cka) :=
      .prod pbaVpT hdrCtT :: .prod (.opt (.prod pbaVpT hdrCtT)) pbaHsT :: Γ_tr2
    let Γ_dl : List (Ty S_cka) :=
      dlQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_ij0 : List (Ty S_cka) := dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_cr : List (Ty S_cka) := .bool :: Γh0
    have hepm := cEpMgmtE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 qep (Γ' := Γ_tr1)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0)
      (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
    have hvsF := vSendC_sizeW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) Ho Hs Hr hhkF (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hvsM := vSendC_sizeW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) Ho Hs Hr hhkM (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hrec := cRecordE3_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γ_tr3)
      .v2 (.fst .v3) (.fst .v0)
      (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
        (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
        (.pair (.fst (.snd .v3)) (.snd .v0)))
      (.bool false)
    have hdlF := deliverEC_bucket_sizeW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) Ho Hs Hr L maxSkip tL hhkF (Γ' := Γ_dl)
      (.fst .v3) .v0
    have hdlM := deliverEC_bucket_sizeW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) Ho Hs Hr L maxSkip tL hhkM (Γ' := Γ_dl)
      (.fst .v3) .v0
    have hhh := isHonestHdrPRNGBucketE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0
      (Γ' := .prod (.opt (_root_.CryptoGames.CKA.ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)) esT :: Γ_ij0)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v3)) (.fst (.snd .v1))
    have hijF := injectEC_bucket_sizeW_le
      (hooksPRNGBucketAuthForgedHdrC L B0 1 qep tL t) Ho Hs Hr L qep tL hhkF (Γ' := Γ_ij0)
      (.fst .v2) .v0
    have hijM := injectEC_bucket_sizeW_le
      (hooksPRNGBucketAuthMainC L B0 1 qep tL t) Ho Hs Hr L qep tL hhkM (Γ' := Γ_ij0)
      (.fst .v2) .v0
    have hca := cCorrAllowedE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    have hac := cAfterCorrE_sizeW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := pbaVpT) B0 L
      (Γ' := psT :: .prod (.opt psT) pbaHsT :: Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) .v2
    have hrvF := prngBucketAuthForgedHdrRevealC_sizeW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 tL (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v1))
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
    have hrvM := prngBucketAuthRevealC_sizeW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 tL (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v1))
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt (_root_.CryptoGames.SM.Engine.esG (.fst .v1))) .v0)
    simp only [Ho, Hs, Hr, _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.pGet,
      _root_.CryptoGames.SM.isSomeE, exprSizeW_renameM, exprSizeW_letE,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3,
      exprSizeW_v4, exprSizeW_v5, exprSizeW_v6, exprSizeW_var, exprSizeW_bool, exprSizeW_nat,
      exprSizeW_none, exprSizeW_add, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd,
      exprSizeW_caseOpt, bits_one, Nat.reduceAdd]
      at hepm hvsF hvsM hrec hdlF hdlM hhh hijF hijM hca hac hrvF hrvM
    rcases box_le hepm with ⟨sepm, hepm_eq, hepm⟩
    rcases box_le hvsF with ⟨svsF, hvsF_eq, hvsF⟩
    rcases box_le hvsM with ⟨svsM, hvsM_eq, hvsM⟩
    rcases box_le hrec with ⟨srec, hrec_eq, hrec⟩
    rcases box_le hdlF with ⟨sdlF, hdlF_eq, hdlF⟩
    rcases box_le hdlM with ⟨sdlM, hdlM_eq, hdlM⟩
    rcases box_le hhh with ⟨shh, hhh_eq, hhh⟩
    rcases box_le hijF with ⟨sijF, hijF_eq, hijF⟩
    rcases box_le hijM with ⟨sijM, hijM_eq, hijM⟩
    rcases box_le hca with ⟨sca, hca_eq, hca⟩
    rcases box_le hac with ⟨sac, hac_eq, hac⟩
    rcases box_le hrvF with ⟨srvF, hrvF_eq, hrvF⟩
    rcases box_le hrvM with ⟨srvM, hrvM_eq, hrvM⟩
    simp only [redPRNGAuthBucketHybridProg, _root_.CryptoGames.SM.Engine.esMk,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
      _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
      _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
      _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
      exprSizeW_renameM, compSizeW_renameM,
      compSizeW_bind, compSizeW_ret, compSizeW_ite, compSizeW_caseOpt, compSizeW_caseSum,
      exprSizeW_letE, exprSizeW_caseOpt,
      exprSizeW_v0, exprSizeW_v1, exprSizeW_v2, exprSizeW_v3, exprSizeW_v4, exprSizeW_v5,
      exprSizeW_v6, exprSizeW_v7, exprSizeW_var, exprSizeW_bool, exprSizeW_nat, exprSizeW_none,
      exprSizeW_some, exprSizeW_inl, exprSizeW_inr, exprSizeW_add, exprSizeW_eqN, exprSizeW_not,
      exprSizeW_and, exprSizeW_ite, exprSizeW_pair, exprSizeW_fst, exprSizeW_snd, bits_one,
      hepm_eq.eq, hvsF_eq.eq, hvsM_eq.eq, hrec_eq.eq, hdlF_eq.eq, hdlM_eq.eq,
      hhh_eq.eq, hijF_eq.eq, hijM_eq.eq, hca_eq.eq, hac_eq.eq, hrvF_eq.eq, hrvM_eq.eq,
      Nat.reduceAdd]
    generalize bits B0 = bB at *
    generalize bits L = bL at *
    generalize bits qep = bq at *
    generalize bits (tL.getD 0) = bTL at *
    generalize bits t = bt at *
    generalize bits (healEpoch tL) = bTH at *
    generalize bits maxSkip = bSk at *
    omega
  dsimp only
  omega

/-- Weighted AST-size bound for `redPRNGAuthBucketHybridProg` against
`reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep)`. -/
theorem redPRNGAuthBucketHybridProg_size_le_qep (q qep t : ℕ) (tL : Option ℕ)
    (ht : t < qep + 2)
    (htL : tL ∈ _root_.CryptoGames.SM.admissibleLastLeakGuesses (2 + 1) (qep + 1))
    (hqep : qep ≤ 4096 * q + 100000000) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    let R := redPRNGAuthBucketHybridProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) (q + 1) B0 1 qep maxForwardJumps tL t
    compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.init +
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.handle +
      compSizeW (ckaOpS B0) ckaSampS ckaQueryS R.finish + 400 ≤
        reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep) := by
  have htL_all : ∀ x, tL = some x → x ≤ qep + 3 := by
    intro x hx
    subst hx
    simp only [_root_.CryptoGames.SM.admissibleLastLeakGuesses, Finset.mem_insert,
      Finset.mem_image, Finset.mem_range, reduceCtorEq, Option.some.injEq, false_or] at htL
    rcases htL with ⟨y, hy, rfl⟩
    omega
  have hgetD : tL.getD 0 ≤ qep + 3 := optGetD_le_of_forall_some htL_all
  have hheal : healEpoch tL ≤ qep + 6 := healEpoch_le_of_forall_some htL_all
  have hbB0 : bits ((q + 1) * (maxForwardJumps + 1)) ≤ bits (ratchetCostBudget q qep) :=
    bits_B0_le_ratchetCostBudget q qep
  have hbL : bits (q + 1) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbqep : bits qep ≤ bits (ratchetCostBudget q qep) :=
    bits_qep_le_ratchetCostBudget hqep
  have hbTL : bits (tL.getD 0) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbt : bits t ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbTH : bits (healEpoch tL) ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by omega)
  have hbSk : bits maxForwardJumps ≤ bits (ratchetCostBudget q qep) :=
    bits_le_ratchetCostBudget_of_le_linear (by unfold maxForwardJumps; omega)
  have hgen := redPRNGAuthBucketHybridProg_generic_sizeW_le (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
    (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
    (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) ((q + 1) * (maxForwardJumps + 1)) (q + 1) qep
    maxForwardJumps tL t
  dsimp only at hgen ⊢
  refine size_le_ratchetSizeBudget (C₀ := 250400) (C₁ := 395) (by norm_num) (by norm_num) ?_
  generalize bits (ratchetCostBudget q qep) = bR at hbB0 hbL hbqep hbTL hbt hbTH hbSk ⊢
  generalize bits ((q + 1) * (maxForwardJumps + 1)) = bB at hbB0 hgen
  generalize bits (q + 1) = bL at hbL hgen
  generalize bits qep = bq at hbqep hgen
  generalize bits (tL.getD 0) = bTL at hbTL hgen
  generalize bits t = bt at hbt hgen
  generalize bits (healEpoch tL) = bTH at hbTH hgen
  generalize bits maxForwardJumps = bSk at hbSk hgen
  omega

end GenericCkaBounds

end

end Computational.Proofs.SessionCostedFig8.BucketPRNGProgBounds
