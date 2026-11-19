/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8ExcessCosts -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.PureAuxMacroLift -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesMultiFs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.SessionCostedFig8.ProgSizeBounds

/-!
# Generic Weighted Step-Cost Bound for `BucketPRNGAuth.redFSAuthMultiBucketProg`-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open _root_.ReductionDsl (Sig Ty Var Ops Iface Expr Comp bits)
open _root_.CryptoGames (Party)
open _root_.CryptoGames.SM.Construction (Header healEpoch)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (exprCostW compCostW exprCostW_rename
  compCostW_rename)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC ckaSampC)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono bits_pos bits_succ_le)
open Computational.Proofs.SessionCostedFig8.ProgSizeBounds (bits_le_succ_nat)
open Computational.Proofs.SessionCostedFig8.BundlesMultiFsBase (fsMultiQueryC fsMultiQueryC_tr
  fsMultiQueryC_ch fsMultiQueryC_cs fsMultiQueryC_cr fsMultiQueryC_dl fsMultiQueryC_ij)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (
  redFSAuthMultiBucketProg postLeakBucketE pbaTableLookupE pbaTableEntryTy mbHsCache
  mbHsTableTbl mbHsSessionsTbl mbHsBook mbHsLfWin mbHsMk mbHsSetCache mbHsSetTableAt
  mbHsSetSessionsAt mbHsSetBookAt mbHsGetBookAt mbHsSetLfWin mbHsEmptyE lookupMultiBucketFC
  sessionsMemBucketE sessionsIdxOfBucketE sessionsLenBucketE sessionsAppendOneBucketE
  regSessMultiBucketE regSessOptMultiBucketE validGuessBucketParAuthE rootFSMultiBucketAuthC
  fsMultiBucketAuthStartSendC isHonestHdrMultiBucketE fsMultiBucketAuthStartRecvC
  fsTransFindBucketE fsTransFilterBucketE fsMultiBucketAuthFsSendC fsMultiBucketAuthFsRecvC
  fsMultiBucketAuthCommitC rangeListBucketC isExtMultiBucketEntryE anyExtMultiBucketVRE
  unliftMultiBucketEntryE unliftMultiBucketVRE fsMultiBucketAuthRevealC hooksFSMultiBucketAuthC
  initFSMultiBucketAuthEStateC fsMultiBucketVpTy fsMultiBucketHsTy fsMultiBucketRedEsTy
  fsaeadMultiBucketIface)

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
@[local simp] private theorem compCostW_iter {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (n : ℕ) (e : Expr O Γ t) (body : Comp O I (t :: Γ) t) :
    compCostW opC sC qC (.iter n e body) =
      exprCostW opC e + n * (compCostW opC sC qC body + 1) + 1 := rfl
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

section GenericCkaCostW

set_option linter.unusedSimpArgs false

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
local notation "IIM_cka" =>
  @fsaeadMultiBucketIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "mVpT" => @fsMultiBucketVpTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "mbHsT" => @fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E

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
private theorem validGuessBucketParAuthE_costW_le (B0 : ℕ) (tL : Option ℕ) (par : Bool) {Γ'}
    (tE : Expr OO_cka Γ' .nat) : exprCostW (ckaOpC B0) (validGuessBucketParAuthE 1 tL par tE) ≤
      4 * exprCostW (ckaOpC B0) tE + 2 * bits (tL.getD 0) + 80 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  have hb4 : bits 4 = 3 := rfl
  cases tL <;> cases par <;> ·
    simp only [validGuessBucketParAuthE, _root_.CryptoGames.SM.validGuessE,
      _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.optNatEqE,
      _root_.CryptoGames.SM.ltOptE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.maxN,
      _root_.CryptoGames.SM.boolEq, _root_.CryptoGames.SM.receiverOfE,
      _root_.CryptoGames.SM.senderOfE, _root_.CryptoGames.SM.Engine.optNatLit,
      Option.getD, exprCostW_rename,
      exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool, exprCostW_nat, exprCostW_none,
      exprCostW_some, exprCostW_add, exprCostW_modK, exprCostW_lt, exprCostW_eqN, exprCostW_not,
      exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
      exprCostW_caseOpt, exprCostW_letE, hb0, hb1, hb2, hb3, hb4, Nat.reduceAdd]
    omega
private theorem pbaTableLookupE_costW_le (B0 L : ℕ) {Γ'}
    (tblE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.pbaTableEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E))) (ikE : Expr OO_cka Γ' (.base .i)) :
    exprCostW (ckaOpC B0) (pbaTableLookupE L tblE ikE) ≤
      exprCostW (ckaOpC B0) tblE + exprCostW (ckaOpC B0) ikE + 30 * L + 20 := by
  simp only [pbaTableLookupE, ckaOpC, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_foldrB, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var, exprCostW_none, exprCostW_some,
    exprCostW_ite, exprCostW_op, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega
private theorem lookupMultiBucketFC_costW_le (B0 L qep qR : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (lookupMultiBucketFC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L hE tE ikE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) ikE +
        30 * L + 700 := by
  let Γ0 := Ty.prod mbHsT (.prod .nat (.base .i)) :: Γ'
  have hlk := pbaTableLookupE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
    (.tget (mbHsTableTbl (.fst .v0)) (.fst (.snd .v0))) (.snd (.snd .v0))
  simp only [mbHsTableTbl, exprCostW_tget, exprCostW_fst, exprCostW_snd, exprCostW_v0,
    Nat.reduceAdd] at hlk
  simp only [lookupMultiBucketFC, mbHsSetTableAt, mbHsMk, mbHsCache, mbHsTableTbl,
    mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaSampC, exprCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_caseOpt, compCostW_sample,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_var,
    exprCostW_unit, exprCostW_cons, exprCostW_tget, exprCostW_tset, Nat.reduceAdd]
  omega
private theorem regSessMultiBucketE_costW_le (B0 L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (ikE : Expr OO_cka Γ' (.base .i)) :
    exprCostW (ckaOpC B0) (regSessMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE ikE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) ikE +
        250 * L + bits (healEpoch tL) + 1500 := by
  have hbL := bits_le_succ_nat L
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  cases gMain <;> ·
    simp only [regSessMultiBucketE, sessionsMemBucketE, sessionsIdxOfBucketE,
      sessionsLenBucketE, sessionsAppendOneBucketE, mbHsSetSessionsAt, mbHsMk, mbHsCache,
      mbHsTableTbl, mbHsSessionsTbl, mbHsBook, mbHsLfWin, _root_.CryptoGames.SM.orE,
      ckaOpC, exprCostW_rename, Bool.false_eq_true,
      exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_ite,
      exprCostW_foldrB, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
      exprCostW_bool, exprCostW_nat, exprCostW_nil, exprCostW_cons, exprCostW_add,
      exprCostW_sub, exprCostW_mulK, exprCostW_op, exprCostW_tget, exprCostW_tset,
      hb0, hb1, show max 1 1 = 1 from rfl, show max 1 3 = 3 from rfl, ↓reduceIte, Nat.reduceAdd]
    omega
private theorem regSessOptMultiBucketE_costW_le (B0 L : ℕ) (gMain : Bool) (tL : Option ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat)
    (sidE : Expr OO_cka Γ' (.opt (.base .i))) : exprCostW (ckaOpC B0)
      (regSessOptMultiBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L gMain tL hE tE sidE) ≤
      2 * exprCostW (ckaOpC B0) hE + 2 * exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) sidE +
        500 * L + 2 * bits (healEpoch tL) + 3100 := by
  let Γ0 : List (Ty S_cka) := .base .i :: .prod mbHsT (.prod .nat (.opt (.base .i))) :: Γ'
  have hreg := regSessMultiBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L gMain tL (Γ' := Γ0) (.fst .v1) (.fst (.snd .v1)) .v0
  simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, Nat.reduceAdd] at hreg
  simp only [regSessOptMultiBucketE, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_caseOpt, exprCostW_none, exprCostW_some,
    exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
  omega
private theorem rootFSMultiBucketAuthC_costW_le (B0 L qep qR : ℕ) (tL : Option ℕ) (par : Bool)
    {Γ'} (hE : Expr OO_cka Γ' mbHsT) (tE : Expr OO_cka Γ' .nat) (plE : Expr OO_cka Γ' .bool)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (rootFSMultiBucketAuthC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep tL par hE tE plE ikE σE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) plE +
        exprCostW (ckaOpC B0) ikE + exprCostW (ckaOpC B0) σE +
        30 * L + bits qep + 2 * bits (tL.getD 0) + 2 * bits (healEpoch tL) + 1600 := by
  have hbq1 := bits_succ_le qep
  let Γ0 := Ty.prod mbHsT (.prod .nat (.prod .bool (.prod (.base .i) (.base .sig)))) :: Γ'
  have hvg := validGuessBucketParAuthE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd .v0))
  have hlk := lookupMultiBucketFC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd (.snd .v0))))
  simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd] at hvg hlk
  simp only [rootFSMultiBucketAuthC, _root_.CryptoGames.SM.orE, ckaOpC, ckaSampC,
    exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_sample,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_v2,
    exprCostW_var, exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_none,
    exprCostW_some, exprCostW_lt, exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite,
    exprCostW_op, Nat.reduceAdd]
  omega
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
private theorem mbHsGetBookAt_costW (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (idxE : Expr OO_cka Γ' .nat) :
    exprCostW (ckaOpC B0) (mbHsGetBookAt hE idxE) =
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) idxE + 74 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [mbHsGetBookAt, mbHsBook, exprCostW_caseOpt, exprCostW_pair, exprCostW_bool,
    exprCostW_nat, exprCostW_nil, exprCostW_v0, exprCostW_tget, exprCostW_fst, exprCostW_snd,
    hb0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

private theorem mbHsSetBookAt_costW (B0 : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (idxE : Expr OO_cka Γ' .nat) (entryE : Expr OO_cka Γ' _) :
    exprCostW (ckaOpC B0) (mbHsSetBookAt hE idxE entryE) =
      5 * exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) idxE +
        exprCostW (ckaOpC B0) entryE + 147 := by
  simp only [mbHsSetBookAt, mbHsMk, mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook,
    mbHsLfWin, exprCostW_pair, exprCostW_some, exprCostW_tset, exprCostW_fst, exprCostW_snd,
    Nat.reduceAdd]
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

private theorem fsMultiBucketAuthStartSendC_costW_le (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'} (hE : Expr OO_cka Γ' mbHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σE : Expr OO_cka Γ' (.base .sig))
    (rE : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthStartSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep gMain tL par hE ctxE pE tE γE σE rE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σE +
        exprCostW (ckaOpC B0) rE +
        3700 * L + bits qep + 3 * bits (tL.getD 0) + 16 * bits (healEpoch tL) + 27000 := by
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
      (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.opt (.base .ccoins))))))
  let Γ0 : List (Ty S_cka) := .base .ccoins :: tupT :: Γ'
  let Γ1 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsT :: Γ0
  have hpl := postLeakBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := mVpT) (Γ' := Γ0) (.fst (.snd .v1))
  have hrt := rootFSMultiBucketAuthC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR tL par (Γ' := Γ0)
    (.fst .v1) (.fst (.snd (.snd .v1))) (postLeakBucketE tL (.fst (.snd .v1)))
    (.snd (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaSend
      (.pair (.fst (.snd (.snd (.snd .v1)))) .v0)))) (.fst (.snd (.snd (.snd (.snd .v1)))))
  have hreg := regSessOptMultiBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L gMain tL (Γ' := Γ1)
    (.snd .v0) (.fst (.snd (.snd .v2))) (.snd (.snd (.fst .v0)))
  simp only [ckaOpC, exprCostW_fst, exprCostW_snd, exprCostW_pair, exprCostW_op,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, Nat.reduceAdd] at hpl hrt hreg
  simp only [fsMultiBucketAuthStartSendC, mbHsSetCache, mbHsMk, mbHsCache, mbHsTableTbl,
    mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaOpC, ckaSampC, exprCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_caseOpt, compCostW_sample,
    exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1,
    exprCostW_v2, exprCostW_v3, exprCostW_var, exprCostW_unit, exprCostW_some, exprCostW_inl,
    exprCostW_inr, exprCostW_caseOpt, exprCostW_op, exprCostW_tset, Nat.reduceAdd]
  omega
private theorem fsMultiBucketAuthStartRecvC_costW_le (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'} (hE : Expr OO_cka Γ' mbHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (γE : Expr OO_cka Γ' (.base .γ)) (σE : Expr OO_cka Γ' (.base .sig))
    (tnE : Expr OO_cka Γ' (.base .t)) : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthStartRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep gMain tL par hE ctxE pE tE γE σE tnE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σE +
        exprCostW (ckaOpC B0) tnE +
        800 * L + bits qep + 6 * bits (tL.getD 0) + 6 * bits (healEpoch tL) + 10000 := by
  have hbq1 := bits_succ_le qep
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
      (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  let Γ1 : List (Ty S_cka) := .prod (.base .k) mbHsT :: Γ0
  have hpl := postLeakBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (vpT := mVpT) (Γ' := Γ0) (.fst (.snd .v0))
  have hvg3 := validGuessE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL (Γ' := Γ0) (.fst (.snd (.snd .v0)))
  have hvgP := validGuessBucketParAuthE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 tL par (Γ' := Γ0) (.fst (.snd (.snd .v0)))
  have hlk := lookupMultiBucketFC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0) (.fst .v0) (.fst (.snd (.snd .v0)))
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
      (.pair (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd (.snd .v0))))))))
  have hreg := regSessMultiBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L false tL (Γ' := Γ1)
    (.snd .v0) (.fst (.snd (.snd .v1)))
    (.snd (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.ckaReceive
      (.pair (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd (.snd .v1))))))))
  simp only [ckaOpC, exprCostW_fst, exprCostW_snd, exprCostW_pair, exprCostW_op,
    exprCostW_v0, exprCostW_v1, Nat.reduceAdd] at hpl hvg3 hvgP hlk hreg
  dsimp only [fsMultiBucketAuthStartRecvC]
  refine le_trans (compCostW_bind_le' _ _
    (exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) tE +
      exprCostW (ckaOpC B0) γE + exprCostW (ckaOpC B0) σE + exprCostW (ckaOpC B0) tnE + 10)
    (800 * L + bits qep + 6 * bits (tL.getD 0) + 6 * bits (healEpoch tL) + 9980) ?_ ?_) (by omega)
  · simp only [compCostW_ret, exprCostW_pair, Nat.reduceAdd]; omega
  · refine le_trans (compCostW_caseOpt_le' _ _ _ 200
      (800 * L + bits qep + 6 * bits (tL.getD 0) + 6 * bits (healEpoch tL) + 9750) ?_ ?_ ?_) (by omega)
    · simp only [mbHsCache, ckaOpC, exprCostW_caseOpt, exprCostW_ite, exprCostW_op,
        exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_tget, exprCostW_none,
        exprCostW_some, exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
      omega
    · refine le_trans (compCostW_ite_le' _ _ _ 5
        (800 * L + bits qep + 6 * bits (tL.getD 0) + 6 * bits (healEpoch tL) + 9730) ?_ ?_ ?_)
        (by omega)
      · simp only [exprCostW_bool]; omega
      · simp only [compCostW_ite, compCostW_ret, exprCostW_and, exprCostW_not, exprCostW_lt,
          exprCostW_eqN, exprCostW_bool, exprCostW_nat, exprCostW_pair, exprCostW_fst,
          exprCostW_snd, exprCostW_none, exprCostW_some, exprCostW_v0, Nat.reduceAdd]
        omega
      · refine le_trans (compCostW_ite_le' _ _ _ (bits qep + 2 * bits (tL.getD 0) + 100)
          (800 * L + 4 * bits (tL.getD 0) + 6 * bits (healEpoch tL) + 9600) ?_ ?_ ?_) (by omega)
        · simp only [exprCostW_and, exprCostW_not, exprCostW_lt, exprCostW_nat, exprCostW_fst,
            exprCostW_snd, exprCostW_v0, Nat.reduceAdd]; omega
        · refine le_trans (compCostW_ite_le' _ _ _ (bits (healEpoch tL) + 20)
            (800 * L + 4 * bits (tL.getD 0) + 5 * bits (healEpoch tL) + 9550) ?_ ?_ ?_) (by omega)
          · simp only [exprCostW_and, exprCostW_eqN, exprCostW_bool, exprCostW_nat,
              exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]; omega
          · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_fst,
              exprCostW_v0, Nat.reduceAdd]; omega
          · refine le_trans (compCostW_ite_le' _ _ _ (2 * bits (tL.getD 0) + 60)
              (800 * L + 2 * bits (tL.getD 0) + 5 * bits (healEpoch tL) + 9450) ?_ ?_ ?_) (by omega)
            · omega
            · simp only [ckaOpC, compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd,
                exprCostW_some, exprCostW_inl, exprCostW_op, exprCostW_v0, Nat.reduceAdd]
              omega
            · refine le_trans (compCostW_ite_le' _ _ _
                (2 * bits (tL.getD 0) + bits (healEpoch tL) + 250)
                (800 * L + 4 * bits (healEpoch tL) + 9100) ?_ ?_ ?_) (by omega)
              · omega
              · simp only [ckaOpC, compCostW_bind, compCostW_ret, exprCostW_pair, exprCostW_fst,
                  exprCostW_snd, exprCostW_some, exprCostW_inr, exprCostW_op,
                  exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
                omega
              · simp only [ckaOpC, compCostW_ite, compCostW_bind, compCostW_ret,
                  exprCostW_not, exprCostW_lt, exprCostW_nat, exprCostW_pair, exprCostW_fst,
                  exprCostW_snd, exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_op,
                  exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
                omega
        · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_some,
            exprCostW_fst, exprCostW_v0, Nat.reduceAdd]; omega
    · simp only [ckaOpC, compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd,
        exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_some, exprCostW_inl, exprCostW_inr,
        exprCostW_caseOpt, exprCostW_op, Nat.reduceAdd]
      omega
private theorem cSafeChE3_costW_le {vpT : Ty S_cka} (B0 : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cSafeChE (2 + 1) s p) ≤
      2 * exprCostW (ckaOpC B0) s + 2 * exprCostW (ckaOpC B0) p + 100 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits 3 = 2 := rfl
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  simp only [_root_.CryptoGames.SM.Engine.cSafeChE, _root_.CryptoGames.SM.healedByE,
    _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.pGet,
    _root_.CryptoGames.SM.Engine.cGsTL, _root_.CryptoGames.SM.Engine.cGsEpoch,
    exprCostW_rename, exprCostW_letE, exprCostW_pair, exprCostW_fst,
    exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool,
    exprCostW_nat, exprCostW_add, exprCostW_lt, exprCostW_not, exprCostW_and,
    exprCostW_ite, exprCostW_caseOpt, hb0, hb1, hb2, hb3, Nat.reduceAdd]
  omega

private theorem mbHsRecordSend_costW_le (B0 : ℕ) {Γ'}
    (h1 : Expr OO_cka Γ' mbHsT) (sIdx : Expr OO_cka Γ' .nat)
    (hdr0 : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (ct : Expr OO_cka Γ' (.base .ct)) :
    exprCostW (ckaOpC B0) (mbHsSetBookAt h1 sIdx
      (.pair (.fst (mbHsGetBookAt h1 sIdx))
        (.pair (.add (.fst (.snd (mbHsGetBookAt h1 sIdx))) (.nat 1))
          (.cons (.pair (.add (.fst (.snd (mbHsGetBookAt h1 sIdx))) (.nat 1)) (.pair hdr0 ct))
            (.snd (.snd (mbHsGetBookAt h1 sIdx))))))) ≤
      9 * exprCostW (ckaOpC B0) h1 + 5 * exprCostW (ckaOpC B0) sIdx +
        exprCostW (ckaOpC B0) hdr0 + exprCostW (ckaOpC B0) ct + 500 := by
  have hb1 : bits 1 = 1 := rfl
  simp only [mbHsGetBookAt_costW, mbHsSetBookAt_costW,
    exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_nat,
    exprCostW_cons, exprCostW_add, hb1, Nat.add_assoc, Nat.reduceAdd]
  omega

set_option maxRecDepth 100000 in
private theorem fsMultiBucketAuthFsSendC_costW_le (B0 qep qR : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (ssvE : Expr OO_cka Γ' (.sum (.base .ss) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (mE : Expr OO_cka Γ' (.base .msg))
    (pairE : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthFsSendC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) 1 la hE ctxE pE tE ssvE hdrE mE pairE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) ssvE + exprCostW (ckaOpC B0) hdrE +
        exprCostW (ckaOpC B0) mE + exprCostW (ckaOpC B0) pairE +
        20 * B0 + 12 * bits qep + 3000 * qR + 2060000 := by
  have hbq1 := bits_succ_le qep
  let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
    (.prod .bool (.prod (.sum (.base .ss) .nat) (.prod hdrT
      (.prod (.base .msg) (.opt (.prod (.base .msg) (.base .msg))))))))
  let Γ0 : List (Ty S_cka) := tupT :: Γ'
  let Γ1 : List (Ty S_cka) := .nat :: Γ0
  let Γ2 : List (Ty S_cka) := .base .ct :: .opt (.base .ct) :: .prod .bool mbHsT :: Γ1
  dsimp only [fsMultiBucketAuthFsSendC]
  refine le_trans (compCostW_bind_le' _ _
    (exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
      exprCostW (ckaOpC B0) ssvE + exprCostW (ckaOpC B0) hdrE + exprCostW (ckaOpC B0) mE +
      exprCostW (ckaOpC B0) pairE + 15)
    (20 * B0 + 12 * bits qep + 3000 * qR + 2059975) ?_ ?_) (by omega)
  · simp only [compCostW_ret, exprCostW_pair, Nat.add_assoc, Nat.reduceAdd]; omega
  · refine le_trans (compCostW_caseSum_le' _ _ _ 10
      (20 * B0 + 12 * bits qep + 3000 * qR + 2059960) ?_ ?_ ?_) (by omega)
    · simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.add_assoc, Nat.reduceAdd]; omega
    · simp only [ckaOpC, compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd,
        exprCostW_v0, exprCostW_v1, exprCostW_some, exprCostW_inl, exprCostW_op,
        Nat.add_assoc, Nat.reduceAdd]
      omega
    · refine le_trans (compCostW_bind_le' _ _
        (10 * B0 + 6 * bits qep + 1500 * qR + 55000)
        (10 * B0 + 6 * bits qep + 1500 * qR + 2004950) ?_ ?_) (by omega)
      · refine le_trans (compCostW_ite_le' _ _ _ 200
          (10 * B0 + 6 * bits qep + 1500 * qR + 54750) ?_ ?_ ?_) (by omega)
        · have hsc1 := cSafeChE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
            (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
            (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
            (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
            (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 (Γ' := Γ1)
            (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
          simp only [exprCostW_fst, exprCostW_snd, exprCostW_v1, Nat.add_assoc, Nat.reduceAdd] at hsc1
          simp only [mbHsGetBookAt_costW, exprCostW_pair, exprCostW_fst, exprCostW_snd,
            exprCostW_v0, exprCostW_v1, exprCostW_not, exprCostW_and,
            Nat.add_assoc, Nat.reduceAdd]
          omega
        · refine le_trans (compCostW_bind_le' _ _
            (10 * B0 + 6 * bits qep + 1500 * qR + 51000) 3700 ?_ ?_) (by omega)
          · simp only [fsMultiQueryC_cs, compCostW_query, exprCostW_pair, exprCostW_unit,
              exprCostW_v0, Nat.add_assoc, Nat.reduceAdd]
            omega
          · refine le_trans (compCostW_caseOpt_le' _ _ _ 5 3690 ?_ ?_ ?_) (by omega)
            · simp only [exprCostW_v0]; omega
            · simp only [compCostW_ret, exprCostW_pair, exprCostW_bool, exprCostW_fst,
                exprCostW_v2, Nat.add_assoc, Nat.reduceAdd]; omega
            · simp only [mbHsGetBookAt_costW, mbHsSetBookAt_costW, compCostW_ret,
                exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_bool,
                exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
                Nat.add_assoc, Nat.reduceAdd]
              omega
        · simp only [compCostW_ret, exprCostW_pair, exprCostW_bool, exprCostW_fst, exprCostW_v1,
            Nat.add_assoc, Nat.reduceAdd]
          omega
      · refine le_trans (compCostW_ite_le' _ _ _ 10
          (10 * B0 + 6 * bits qep + 1500 * qR + 2004930) ?_ ?_ ?_) (by omega)
        · simp only [exprCostW_not, exprCostW_fst, exprCostW_v0, Nat.add_assoc, Nat.reduceAdd]; omega
        · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_snd, exprCostW_v0,
            Nat.add_assoc, Nat.reduceAdd]; omega
        · refine le_trans (compCostW_bind_le' _ _
            (10 * B0 + 6 * bits qep + 1500 * qR + 2001000) 3900 ?_ ?_) (by omega)
          · simp only [fsMultiQueryC_tr, fsMultiQueryC_ch, compCostW_caseOpt, compCostW_query,
              exprCostW_pair, exprCostW_fst, exprCostW_snd,
              exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, Nat.add_assoc, Nat.reduceAdd]
            omega
          · refine le_trans (compCostW_caseOpt_le' _ _ _ 5 3890 ?_ ?_ ?_) (by omega)
            · simp only [exprCostW_v0]; omega
            · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_snd,
                exprCostW_v1, Nat.add_assoc, Nat.reduceAdd]; omega
            · have hrs := mbHsRecordSend_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
                (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
                (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
                (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
                (lam := lam) (defaultE := defaultE) B0 (Γ' := Γ2)
                (.snd .v2) .v3 (.fst (.snd (.snd (.snd (.snd .v4))))) .v0
              simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v2,
                exprCostW_v3, exprCostW_v4, Nat.add_assoc, Nat.reduceAdd] at hrs
              simp only [compCostW_ret, exprCostW_pair, exprCostW_some, exprCostW_inr,
                exprCostW_v0, exprCostW_v3, Nat.add_assoc, Nat.reduceAdd]
              omega
private theorem fsTransFindBucketE_costW_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketTransEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprCostW (ckaOpC B0) (fsTransFindBucketE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L trE hcE) ≤
      exprCostW (ckaOpC B0) trE + exprCostW (ckaOpC B0) hcE + 220 * L + 40 := by
  simp only [fsTransFindBucketE, _root_.CryptoGames.SM.Engine.hdrCtEqE,
    _root_.CryptoGames.SM.Engine.optTEqE, ckaOpC, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_findB, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_bool, exprCostW_eqN, exprCostW_and, exprCostW_caseOpt, exprCostW_op,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega
private theorem fsTransFilterBucketE_costW_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ' (.list (@Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth.fsMultiBucketTransEntryTy
      KC Γ CCoins T I KR RSt K SS RS M E))) (dropE : Expr OO_cka Γ' .nat) :
    exprCostW (ckaOpC B0) (fsTransFilterBucketE L trE dropE) ≤
      exprCostW (ckaOpC B0) trE + exprCostW (ckaOpC B0) dropE + 30 * L + 30 := by
  simp only [fsTransFilterBucketE, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_foldrB, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var, exprCostW_nil, exprCostW_cons,
    exprCostW_eqN, exprCostW_not, exprCostW_ite,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega
private theorem compCostW_bind_le {Γ' : List (Ty S_cka)} {τ₁ τ₂ : Ty S_cka}
    (B0 qep qR : ℕ) (c1 : Comp OO_cka IIM_cka Γ' τ₁) (c2 : Comp OO_cka IIM_cka (τ₁ :: Γ') τ₂)
    (k1 k2 : ℕ)
    (h1 : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) c1 ≤ k1)
    (h2 : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) c2 ≤ k2) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) (.bind c1 c2) ≤ k1 + k2 + 1 := by
  rw [compCostW_bind]; omega

private theorem compCostW_caseSum_le {Γ' : List (Ty S_cka)} {τ₁ τ₂ τ₃ : Ty S_cka}
    (B0 qep qR : ℕ) (e : Expr OO_cka Γ' (.sum τ₁ τ₂))
    (c1 : Comp OO_cka IIM_cka (τ₁ :: Γ') τ₃) (c2 : Comp OO_cka IIM_cka (τ₂ :: Γ') τ₃)
    (ke kc : ℕ)
    (he : exprCostW (ckaOpC B0) e ≤ ke)
    (h1 : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) c1 ≤ kc)
    (h2 : compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) c2 ≤ kc) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) (.caseSum e c1 c2) ≤ ke + kc + 1 := by
  rw [compCostW_caseSum]; omega

set_option maxRecDepth 100000 in
private theorem fsMultiBucketAuthFsRecvC_costW_le (B0 L qep qR : ℕ) (la : Bool) {Γ'}
    (hE : Expr OO_cka Γ' mbHsT) (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (tE : Expr OO_cka Γ' .nat)
    (rsvE : Expr OO_cka Γ' (.sum (.base .rs) .nat))
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
    (eE : Expr OO_cka Γ' (.base .ct))
    (recE : Expr OO_cka Γ' (.opt _root_.CryptoGames.SM.Engine.cRecTy)) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthFsRecvC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 la 1 hE ctxE pE tE rsvE hdrE eE recE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) tE + exprCostW (ckaOpC B0) rsvE + exprCostW (ckaOpC B0) hdrE +
        exprCostW (ckaOpC B0) eE + exprCostW (ckaOpC B0) recE +
        20 * B0 + 3 * bits B0 + 1050 * L + 12 * bits qep + 4000 * qR + 3600000 := by
  have hbq1 := bits_succ_le qep
  have hb0 : bits 0 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb3 : bits (2 + 1) = 2 := rfl
  let hdrT := _root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT)
    (.prod .nat (.prod (.sum (.base .rs) .nat) (.prod hdrT
      (.prod (.base .ct) (.opt _root_.CryptoGames.SM.Engine.cRecTy))))))
  let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
  let Γ_inr : List (Ty S_cka) := .nat :: tupT :: Γ'
  let Γ_ok : List (Ty S_cka) := .prod .bool mbHsT :: Γ_inr
  let Γ_res : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ_ok
  have htf0 := fsTransFindBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_inr)
    (.snd (.snd (mbHsGetBookAt (.fst .v1) .v0)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v1))))) (.fst (.snd (.snd (.snd (.snd (.snd .v1)))))))
  have htf_ok := fsTransFindBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_ok)
    (.snd (.snd (mbHsGetBookAt (.fst .v2) .v1)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v2))))) (.fst (.snd (.snd (.snd (.snd (.snd .v2)))))))
  have htf1 := fsTransFindBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_res)
    (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
    (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5)))))))
  have htflt := fsTransFilterBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ_res)
    (.snd (.snd (mbHsGetBookAt (.snd .v3) .v4)))
    (.caseOpt (fsTransFindBucketE L (.snd (.snd (mbHsGetBookAt (.fst .v5) .v4)))
      (.pair (.fst (.snd (.snd (.snd (.snd .v5))))) (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))))
      (.fst .v0) (.fst .v0))
  simp only [mbHsGetBookAt_costW, exprCostW_rename,
    exprCostW_letE, exprCostW_caseOpt, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_v5, exprCostW_var,
    exprCostW_bool, exprCostW_nat, exprCostW_nil, exprCostW_tget, hb0, Nat.reduceAdd]
    at htf0 htf_ok htf1 htflt
  dsimp only [fsMultiBucketAuthFsRecvC]
  refine le_trans (compCostW_bind_le B0 qep qR _ _
    (exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) tE +
      exprCostW (ckaOpC B0) rsvE + exprCostW (ckaOpC B0) hdrE +
      exprCostW (ckaOpC B0) eE + exprCostW (ckaOpC B0) recE + 15)
    (20 * B0 + 3 * bits B0 + 1050 * L + 12 * bits qep + 4000 * qR + 3599975) ?_ ?_) (by omega)
  · simp only [compCostW_ret, exprCostW_pair, Nat.reduceAdd]
    omega
  · refine le_trans (compCostW_caseSum_le B0 qep qR _ _ _ 10
      (20 * B0 + 3 * bits B0 + 1050 * L + 12 * bits qep + 4000 * qR + 3599955) ?_ ?_ ?_) (by omega)
    · simp only [exprCostW_fst, exprCostW_snd, exprCostW_v0, Nat.reduceAdd]
      omega
    · simp only [ckaOpC, compCostW_ret, compCostW_caseOpt,
        exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_v2,
        exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_op, Nat.reduceAdd]
      generalize bits B0 = bB at *
      omega
    · refine le_trans (compCostW_bind_le B0 qep qR _ _
        (10 * B0 + 250 * L + 6 * bits qep + 1500 * qR + 55000)
        (10 * B0 + 800 * L + 6 * bits qep + 2500 * qR + 3535000) ?_ ?_) (by omega)
      · refine le_trans (compCostW_caseOpt_le' _ _ _ (250 * L + 200)
          (10 * B0 + 6 * bits qep + 1500 * qR + 54750) ?_ ?_ ?_) (by omega)
        · omega
        · simp only [mbHsGetBookAt_costW, mbHsSetBookAt_costW, fsMultiQueryC_cs,
            _root_.CryptoGames.SM.healedByE, _root_.CryptoGames.SM.Engine.cGsTL,
            _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.minN,
            exprCostW_rename, compCostW_rename,
            compCostW_ite, compCostW_bind, compCostW_query, compCostW_caseOpt, compCostW_ret,
            exprCostW_letE, exprCostW_caseOpt, exprCostW_ite, exprCostW_pair, exprCostW_fst,
            exprCostW_snd, exprCostW_unit, exprCostW_bool, exprCostW_nat, exprCostW_add,
            exprCostW_lt, exprCostW_not, exprCostW_and,
            exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
            hb0, hb2, hb3, Nat.reduceAdd]
          omega
        · simp only [compCostW_ret, exprCostW_pair, exprCostW_bool, exprCostW_fst,
            exprCostW_v2, Nat.reduceAdd]
          omega
      · refine le_trans (compCostW_ite_le' _ _ _ 10
          (10 * B0 + 800 * L + 6 * bits qep + 2500 * qR + 3530000) ?_ ?_ ?_) (by omega)
        · simp only [exprCostW_not, exprCostW_fst, exprCostW_v0, Nat.reduceAdd]; omega
        · simp only [compCostW_ret, exprCostW_pair, exprCostW_none, exprCostW_snd, exprCostW_v0,
            Nat.reduceAdd]; omega
        · refine le_trans (compCostW_bind_le B0 qep qR _ _
            (10 * B0 + 250 * L + 6 * bits qep + 2500 * qR + 3505000) (500 * L + 20000) ?_ ?_) (by omega)
          · simp only [mbHsGetBookAt_costW, fsMultiQueryC_ij, fsMultiQueryC_dl,
              exprCostW_rename, compCostW_caseOpt, compCostW_query,
              exprCostW_pair, exprCostW_fst, exprCostW_snd,
              exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
              exprCostW_var, hb0, Nat.reduceAdd]
            omega
          · simp only [_root_.CryptoGames.SM.Engine.cRecMsg,
              mbHsGetBookAt_costW, mbHsSetBookAt, mbHsSetLfWin, mbHsMk, mbHsCache, mbHsTableTbl,
              mbHsSessionsTbl, mbHsBook, mbHsLfWin, ckaOpC,
              exprCostW_rename, compCostW_rename,
              compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_caseSum,
              exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1,
              exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_v5, exprCostW_var, exprCostW_bool, exprCostW_nat,
              exprCostW_none, exprCostW_nil, exprCostW_some, exprCostW_inl, exprCostW_inr, exprCostW_lt,
              exprCostW_not, exprCostW_and, exprCostW_caseOpt, exprCostW_op, exprCostW_tget, exprCostW_tset,
              hb0, Nat.reduceAdd]
            omega
private theorem fsMultiBucketAuthCommitC_costW_le (B0 qep qR : ℕ) {Γ'} (hE : Expr OO_cka Γ' mbHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (oldE newE : Expr OO_cka Γ' mVpT) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthCommitC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) hE ctxE pE oldE newE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) oldE + exprCostW (ckaOpC B0) newE + 10 := by
  simp only [fsMultiBucketAuthCommitC, compCostW_ret, exprCostW_pair, exprCostW_some]
  omega
private theorem rangeListBucketC_costW_le (B0 L qep qR : ℕ) {Γ' : List (Ty S_cka)} :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (rangeListBucketC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L (Γ' := Γ')) ≤ 20 * L + 20 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [rangeListBucketC, compCostW_bind, compCostW_iter, compCostW_ret,
    exprCostW_pair, exprCostW_nat, exprCostW_nil, exprCostW_add, exprCostW_fst, exprCostW_snd,
    exprCostW_cons, exprCostW_v0, hb0, hb1, Nat.reduceAdd]
  omega
private theorem anyExtMultiBucketVRE_costW_le (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) : exprCostW (ckaOpC B0)
      (anyExtMultiBucketVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprCostW (ckaOpC B0) vRE + exprCostW (ckaOpC B0) rngE + 110 * L + 20 := by
  simp only [anyExtMultiBucketVRE, isExtMultiBucketEntryE, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_foldrB, exprCostW_ite, exprCostW_caseOpt,
    exprCostW_caseSum, exprCostW_tget, exprCostW_fst, exprCostW_snd, exprCostW_bool,
    exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega
private theorem unliftMultiBucketVRE_costW_le (B0 L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.sum (.base .rs) .nat))))
    (rngE : Expr OO_cka Γ' (.list .nat)) : exprCostW (ckaOpC B0)
      (unliftMultiBucketVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE) L vRE rngE) ≤
      exprCostW (ckaOpC B0) vRE + exprCostW (ckaOpC B0) rngE + 260 * L + 20 := by
  simp only [unliftMultiBucketVRE, unliftMultiBucketEntryE, exprCostW_rename,
    exprCostW_letE, exprCostW_pair, exprCostW_foldrB, exprCostW_caseOpt, exprCostW_caseSum,
    exprCostW_tconst, exprCostW_tget, exprCostW_tset, exprCostW_none, exprCostW_some,
    exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_var,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega
private theorem fsMultiBucketAuthRevealC_costW_le (B0 L qep qR : ℕ) (gMain la : Bool)
    (tL : Option ℕ) {Γ'} (hE : Expr OO_cka Γ' mbHsT)
    (ctxE : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy mVpT))
    (pE : Expr OO_cka Γ' .bool) (vpE : Expr OO_cka Γ' mVpT) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (fsMultiBucketAuthRevealC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L gMain la tL hE ctxE pE vpE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) ctxE + exprCostW (ckaOpC B0) pE +
        exprCostW (ckaOpC B0) vpE +
        10 * B0 + 450 * L + 6 * bits qep + 2 * bits (healEpoch tL) + 1500 * qR + 60000 := by
  have hbq1 := bits_succ_le qep
  have hb0 : bits 0 = 1 := rfl
  let tupT : Ty S_cka := .prod mbHsT (.prod (_root_.CryptoGames.SM.Engine.cGsTy mVpT) mVpT)
  let Γ0 : List (Ty S_cka) :=
    .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) mbHsT :: tupT :: Γ'
  let Γ1 : List (Ty S_cka) := .list .nat :: Γ0
  have hrng := rangeListBucketC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR (Γ' := Γ0)
  have hany := anyExtMultiBucketVRE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (_root_.CryptoGames.SM.Engine.vpVR (.snd (.snd .v3))) .v0
  have hunl := unliftMultiBucketVRE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
    (_root_.CryptoGames.SM.Engine.vpVR (.snd (.snd .v3))) .v0
  simp only [_root_.CryptoGames.SM.Engine.vpVR, exprCostW_fst, exprCostW_snd,
    exprCostW_v0, exprCostW_v3, Nat.reduceAdd] at hany hunl
  simp only [fsMultiBucketAuthRevealC, _root_.CryptoGames.SM.Engine.vpTcurNat,
    _root_.CryptoGames.SM.Engine.vpVS, _root_.CryptoGames.SM.Engine.vpVR,
    _root_.CryptoGames.SM.Engine.vpΓ, _root_.CryptoGames.SM.Engine.vpRoot,
    _root_.CryptoGames.SM.Engine.vpId, _root_.CryptoGames.SM.Engine.vpTcur,
    _root_.CryptoGames.SM.Engine.vpMk,
    _root_.CryptoGames.SM.Engine.realPartyE, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN, _root_.CryptoGames.SM.orE,
    mbHsGetBookAt_costW, mbHsSetBookAt, mbHsMk, mbHsCache, mbHsTableTbl, mbHsSessionsTbl, mbHsBook,
    mbHsLfWin, fsMultiQueryC_cs, exprCostW_rename, compCostW_rename,
    compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_caseSum,
    compCostW_query,
    exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1,
    exprCostW_v2, exprCostW_v3, exprCostW_v4, exprCostW_v5, exprCostW_var, exprCostW_unit,
    exprCostW_bool, exprCostW_nat,
    exprCostW_none, exprCostW_nil, exprCostW_some, exprCostW_lt, exprCostW_not, exprCostW_and,
    exprCostW_ite, exprCostW_caseOpt, exprCostW_tget, exprCostW_tset, hb0, Nat.reduceAdd]
  omega
private theorem initFSMultiBucketAuthEStateC_costW_le (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par : Bool) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0)
      (initFSMultiBucketAuthEStateC (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L 1 qep gMain tL par bE) ≤ exprCostW (ckaOpC B0) bE +
        2600 * L + bits qep + 2 * bits (tL.getD 0) + 12 * bits (healEpoch tL) + 25000 := by
  have hb0 : bits 0 = 1 := rfl
  let Γ0 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) mbHsT :: Γ0
  have hrt := rootFSMultiBucketAuthC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR tL par (Γ' := Γ0)
    mbHsEmptyE (.nat 0) (.bool false)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) _root_.CryptoGames.CKA.CKAOp.prngInit .v1)
  have hreg := regSessOptMultiBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L true tL (Γ' := Γ1)
    (.snd .v0) (.nat 0) (.snd (.snd (.fst .v0)))
  simp only [mbHsEmptyE, mbHsMk, ckaOpC, exprCostW_pair, exprCostW_tconst, exprCostW_none,
    exprCostW_nil, exprCostW_bool, exprCostW_nat, exprCostW_op, exprCostW_unit,
    exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1, hb0, Nat.reduceAdd] at hrt hreg
  cases gMain <;> ·
    simp only [initFSMultiBucketAuthEStateC, _root_.CryptoGames.SM.Engine.mkPartiesE,
      _root_.CryptoGames.SM.Engine.cGsInitE, _root_.CryptoGames.SM.Engine.cGsMk,
      _root_.CryptoGames.SM.Engine.esMk, _root_.CryptoGames.SM.Engine.vpMk,
      mbHsEmptyE, mbHsMk, ↓reduceIte, Bool.false_eq_true,
      ckaOpC, ckaSampC, exprCostW_rename, compCostW_rename,
      compCostW_bind, compCostW_ret, compCostW_sample,
      exprCostW_letE, exprCostW_pair, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v1,
      exprCostW_v2, exprCostW_v3, exprCostW_var, exprCostW_unit, exprCostW_bool, exprCostW_nat,
      exprCostW_none, exprCostW_nil, exprCostW_some, exprCostW_inl, exprCostW_inr,
      exprCostW_caseOpt, exprCostW_op, exprCostW_tconst, exprCostW_tset, hb0, Nat.reduceAdd]
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
private theorem bits_healEpoch_le_getD (tL : Option ℕ) :
    bits (healEpoch tL) ≤ bits (tL.getD 0) + 2 := by
  cases tL with
  | none => simp [healEpoch]
  | some l =>
    have h1 := bits_succ_le (l + 1)
    have h2 := bits_succ_le l
    simpa [healEpoch, Option.getD, Nat.add_assoc] using le_trans h1 (Nat.add_le_add_right h2 1)

private theorem hooksFSMultiBucketAuthC_costWBounded (B0 L qep qR : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool) : HooksCostWBounded B0 ckaSampC (fsMultiQueryC qep qR B0)
      (hooksFSMultiBucketAuthC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
        (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
        (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
        (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B0 1 qep gMain tL par la)
      (3700 * L + bits qep + 6 * bits (tL.getD 0) + 15 * bits (healEpoch tL) + 27010)
      (20 * B0 + 12 * bits qep + 3000 * qR + 2060000)
      (20 * B0 + 3 * bits B0 + 1050 * L + 12 * bits qep + 4000 * qR + 3600000) 10
      (10 * B0 + 450 * L + 6 * bits qep + 2 * bits (healEpoch tL) + 1500 * qR + 60000) := by
  have hbH := bits_healEpoch_le_getD tL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ' h ctx p t γv σ r
    exact (fsMultiBucketAuthStartSendC_costW_le B0 L qep qR gMain tL par h ctx p t γv σ r).trans
      (by omega)
  · intro Γ' h ctx p t γv σ tn
    exact (fsMultiBucketAuthStartRecvC_costW_le B0 L qep qR gMain tL par h ctx p t γv σ tn).trans
      (by omega)
  · intro Γ' h ctx p t ss hdr m pair
    exact (fsMultiBucketAuthFsSendC_costW_le B0 qep qR la h ctx p t ss hdr m pair).trans (by omega)
  · intro Γ' h ctx p t rs hdr e rec_
    exact (fsMultiBucketAuthFsRecvC_costW_le B0 L qep qR la h ctx p t rs hdr e rec_).trans
      (by omega)
  · intro Γ' h ctx p old new
    exact (fsMultiBucketAuthCommitC_costW_le B0 qep qR h ctx p old new).trans (by omega)
  · intro Γ' h ctx p vp
    exact (fsMultiBucketAuthRevealC_costW_le B0 L qep qR gMain la tL h ctx p vp).trans (by omega)
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
private theorem cAcceptE_costW_le {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (_root_.CryptoGames.SM.Engine.cGsTy vpT))
    (p : Expr OO_cka Γ' .bool) (st' : Expr OO_cka Γ' vpT)
    (pos : Expr OO_cka Γ' _root_.CryptoGames.SM.posTy) :
    exprCostW (ckaOpC B0) (_root_.CryptoGames.SM.Engine.cAcceptE L s p st' pos) ≤
      exprCostW (ckaOpC B0) s + exprCostW (ckaOpC B0) p + exprCostW (ckaOpC B0) st' +
        2 * exprCostW (ckaOpC B0) pos + 160 * L + 1200 := by
  simp only [_root_.CryptoGames.SM.Engine.cAcceptE, _root_.CryptoGames.SM.Engine.cDeleteE,
    _root_.CryptoGames.SM.Engine.cCompDeleteE, _root_.CryptoGames.SM.Engine.cCompSetE,
    _root_.CryptoGames.SM.Engine.cRecPos, _root_.CryptoGames.SM.Engine.cGsMk,
    _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsB,
    _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.Engine.cGsEpoch,
    _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.cGsTL,
    _root_.CryptoGames.SM.Engine.cGsTrans, _root_.CryptoGames.SM.Engine.cGsChall,
    _root_.CryptoGames.SM.Engine.cGsComp, _root_.CryptoGames.SM.Engine.cGsMaxAcc,
    _root_.CryptoGames.SM.Engine.cGsLeaks, _root_.CryptoGames.SM.Engine.cGsCorrs,
    _root_.CryptoGames.SM.maxAccSet, _root_.CryptoGames.SM.maxAccGet,
    _root_.CryptoGames.SM.maxN, _root_.CryptoGames.SM.leN,
    _root_.CryptoGames.SM.pGet, _root_.CryptoGames.SM.pSet,
    _root_.CryptoGames.SM.posEq, _root_.CryptoGames.SM.boolEq,
    _root_.CryptoGames.SM.posSender, _root_.CryptoGames.SM.posEpoch, _root_.CryptoGames.SM.posIdx,
    exprCostW_rename, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3, exprCostW_var,
    exprCostW_bool, exprCostW_nil, exprCostW_cons, exprCostW_lt, exprCostW_eqN,
    exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
    exprCostW_letE, exprCostW_foldrB, exprCostW_tget, exprCostW_tset,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
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
private theorem isHonestHdrMultiBucketE_costW_le (B0 : ℕ) {Γ'} (hE : Expr OO_cka Γ' mbHsT)
    (hdrE : Expr OO_cka Γ' (_root_.CryptoGames.CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprCostW (ckaOpC B0) (isHonestHdrMultiBucketE hE hdrE) ≤
      exprCostW (ckaOpC B0) hE + exprCostW (ckaOpC B0) hdrE + 150 := by
  simp only [isHonestHdrMultiBucketE, mbHsCache, ckaOpC, exprCostW_rename,
    exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_bool, exprCostW_pair,
    exprCostW_fst, exprCostW_snd, exprCostW_caseOpt, exprCostW_letE, exprCostW_op,
    exprCostW_tget, Nat.reduceAdd]
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
        (_root_.CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) es arg) ≤
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
  dsimp only [_root_.CryptoGames.SM.Engine.deliverEC,
    _root_.CryptoGames.SM.Construction.bucketAuthCfgEC]
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
        (_root_.CryptoGames.SM.Construction.bucketAuthCfgEC 1 tL) es arg) ≤
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
  dsimp only [_root_.CryptoGames.SM.Engine.injectEC,
    _root_.CryptoGames.SM.Construction.bucketAuthCfgEC]
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

/-- Generic weighted step-cost bound for `redFSAuthMultiBucketProg`. -/
theorem redFSAuthMultiBucketProg_generic_costW_le
    (B0 L qep qR maxSkip : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    let R := redFSAuthMultiBucketProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B0 1 qep maxSkip gMain la tL par
    compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.init +
        compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.finish ≤
          2800 * L + bits qep + 6 * bits (tL.getD 0) + 12 * bits (healEpoch tL) + 30000 ∧
      compCostW (ckaOpC B0) ckaSampC (fsMultiQueryC qep qR B0) R.handle ≤
        20 * B0 + 3 * bits B0 + 16000 * L + 16 * bits qep + 10 * bits (tL.getD 0) +
          15 * bits (healEpoch tL) + bits maxSkip + 4000 * qR + 3800000 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hhk := hooksFSMultiBucketAuthC_costWBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par la
  constructor
  · have hinit := initFSMultiBucketAuthEStateC_costW_le (ckaInitA := ckaInitA)
      (ckaInitB := ckaInitB) (ckaSend := ckaSend) (ckaReceive := ckaReceive)
      (prngInit := prngInit) (prngUp := prngUp) (fsInitSender := fsInitSender)
      (fsInitReceiver := fsInitReceiver) (fsSend := fsSend) (fsReceive := fsReceive)
      (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR gMain tL par (Γ' := [.unit]) (.bool false)
    let Γf : List (Ty S_cka) :=
      .nat :: .prod (_root_.CryptoGames.SM.Engine.esTy mVpT mbHsT) (.opt .nat) ::
        [@fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E, .bool]
    have hopt := optNatLit_costW_le (O' := OO_cka) (ckaOpC B0) (Γ' := Γf) tL
    have haok := cAuthOKE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γf)
      (_root_.CryptoGames.SM.Engine.optNatLit tL) .v0 (_root_.CryptoGames.SM.Engine.esG (.fst .v1))
    have hb2 : bits 2 = 2 := rfl
    have hb3 : bits (2 + 1) = 2 := rfl
    simp only [_root_.CryptoGames.SM.Engine.esG, exprCostW_bool, exprCostW_fst, exprCostW_v0,
      exprCostW_v1, hb2, hb3, Nat.reduceAdd] at hinit haok
    simp only [redFSAuthMultiBucketProg, mbHsLfWin, _root_.CryptoGames.SM.Engine.esAbort,
      _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
      _root_.CryptoGames.SM.Engine.cGsWin, _root_.CryptoGames.SM.senderOfE,
      exprCostW_rename, compCostW_rename,
      compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt,
      exprCostW_letE, exprCostW_v0, exprCostW_v1, exprCostW_var, exprCostW_unit, exprCostW_bool,
      exprCostW_nat, exprCostW_none, exprCostW_modK, exprCostW_eqN, exprCostW_not, exprCostW_and,
      exprCostW_ite, exprCostW_pair, exprCostW_fst, exprCostW_snd,
      hb0, hb1, hb2, hb3, Nat.reduceAdd]
    omega
  · let esT := _root_.CryptoGames.SM.Engine.esTy mVpT mbHsT
    let stT := @fsMultiBucketRedEsTy KC Γ CCoins T I KR RSt K SS RS M E
    let qT := _root_.CryptoGames.CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
    let hdrCtT := _root_.CryptoGames.CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
    let psT := _root_.CryptoGames.CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γh0 : List (Ty S_cka) := .prod esT (.prod (.opt .nat) qT) :: [stT, qT]
    let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
    let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
    let dlQ : Ty S_cka := .prod .bool hdrCtT
    let Γ_tr0 : List (Ty S_cka) :=
      trQ :: .sum trQ chQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_tr1 : List (Ty S_cka) := trQ :: Γ_tr0
    let Γ_tr2 : List (Ty S_cka) := _root_.CryptoGames.SM.Engine.cGsTy mVpT :: Γ_tr1
    let Γ_tr3 : List (Ty S_cka) :=
      .prod mVpT hdrCtT :: .prod (.opt (.prod mVpT hdrCtT)) mbHsT :: Γ_tr2
    let Γ_dl : List (Ty S_cka) :=
      dlQ :: .sum (.sum trQ chQ) dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_ij0 : List (Ty S_cka) := dlQ :: .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γh0
    let Γ_cr : List (Ty S_cka) := .bool :: Γh0
    have hepm := cEpMgmtE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 qep (Γ' := Γ_tr1)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v5)) (.fst .v0)
      (_root_.CryptoGames.SM.isSomeE (.snd (.snd .v0)))
    have hvs := vSendC_costW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) hhk (Γ' := Γ_tr2)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v6)) .v0 (.fst .v1)
      (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsSt .v0) (.fst .v1))
      (.fst (.snd .v1)) .none (.snd (.snd .v1))
    have hrec := cRecordE3_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γ_tr3) .v2 (.fst .v3) (.fst .v0)
      (.pair (.pair (.fst .v3) (.pair (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsEpoch .v2) (.fst .v3))
        (.add (_root_.CryptoGames.SM.pGet (_root_.CryptoGames.SM.Engine.cGsIdx .v2) (.fst .v3)) (.nat 1))))
        (.pair (.fst (.snd .v3)) (.snd .v0))) (.bool false)
    have hdl := deliverEC_bucket_costW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) L maxSkip tL hhk (Γ' := Γ_dl)
      (.fst .v3) .v0
    have hhh := isHonestHdrMultiBucketE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0
      (Γ' := .prod (.opt (_root_.CryptoGames.CKA.ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)) esT :: Γ_ij0)
      (_root_.CryptoGames.SM.Engine.esH (.fst .v3)) (.fst (.snd .v1))
    have hij := injectEC_bucket_costW_le
      (hooksFSMultiBucketAuthC L B0 1 qep gMain tL par la) L qep tL hhk (Γ' := Γ_ij0) (.fst .v2) .v0
    have hca := cCorrAllowedE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L (Γ' := Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v1)) .v0
    have hac := cAfterCorrE_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (vpT := mVpT) B0 L
      (Γ' := psT :: .prod (.opt psT) mbHsT :: Γ_cr)
      (_root_.CryptoGames.SM.Engine.esG (.fst .v3)) .v2
    have hrv := fsMultiBucketAuthRevealC_costW_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L qep qR gMain la tL (Γ' := Γ_cr)
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
      exprCostW_caseOpt, hb0, hb1, Nat.reduceAdd] at hepm hvs hrec hdl hhh hij hca hac hrv
    let K0 : ℕ := 20 * B0 + 3 * bits B0 + 16000 * L + 16 * bits qep + 10 * bits (tL.getD 0) +
      15 * bits (healEpoch tL) + bits maxSkip + 4000 * qR
    dsimp only [redFSAuthMultiBucketProg]
    refine le_trans (compCostW_bind_le B0 qep qR _ _ 10 (K0 + 3799985) ?_ ?_) (by dsimp [K0]; omega)
    · simp only [compCostW_ret, exprCostW_pair, exprCostW_fst, exprCostW_snd,
        exprCostW_v0, exprCostW_v1, Nat.reduceAdd]
      omega
    · refine le_trans (compCostW_caseSum_le B0 qep qR _ _ _ 4 (K0 + 3799975) ?_ ?_ ?_) (by dsimp [K0]; omega)
      · simp only [exprCostW_snd, exprCostW_v0, Nat.reduceAdd]; omega
      · refine le_trans (compCostW_caseSum_le B0 qep qR _ _ _ 2 (K0 + 3799965) ?_ ?_ ?_) (by dsimp [K0]; omega)
        · simp only [exprCostW_v0]; omega
        · refine le_trans (compCostW_caseSum_le B0 qep qR _ _ _ 2 (K0 + 3799955) ?_ ?_ ?_) (by dsimp [K0]; omega)
          · simp only [exprCostW_v0]; omega
          · refine le_trans (compCostW_caseSum_le B0 qep qR _ _ _ 2 (K0 + 3799945) ?_ ?_ ?_) (by dsimp [K0]; omega)
            · simp only [exprCostW_v0]; omega
            · dsimp only [K0]
              simp only [_root_.CryptoGames.SM.Engine.esMk,
                _root_.CryptoGames.SM.Engine.esG, _root_.CryptoGames.SM.Engine.esH,
                _root_.CryptoGames.SM.Engine.esAbort, _root_.CryptoGames.SM.Engine.cGsWin,
                _root_.CryptoGames.SM.Engine.cGsSt, _root_.CryptoGames.SM.Engine.cGsEpoch,
                _root_.CryptoGames.SM.Engine.cGsIdx, _root_.CryptoGames.SM.Engine.vpTcurNat,
                _root_.CryptoGames.SM.isSomeE, _root_.CryptoGames.SM.orE, _root_.CryptoGames.SM.pGet,
                exprCostW_rename, compCostW_rename,
                compCostW_bind, compCostW_ret, compCostW_ite, compCostW_caseOpt, compCostW_caseSum,
                exprCostW_letE, exprCostW_caseOpt, exprCostW_v0, exprCostW_v1, exprCostW_v2, exprCostW_v3,
                exprCostW_v4, exprCostW_v5, exprCostW_v6, exprCostW_v7, exprCostW_var, exprCostW_bool,
                exprCostW_nat, exprCostW_none, exprCostW_some, exprCostW_inl, exprCostW_inr, exprCostW_add,
                exprCostW_eqN, exprCostW_not, exprCostW_and, exprCostW_ite, exprCostW_pair, exprCostW_fst,
                exprCostW_snd, hb0, hb1, Nat.reduceAdd]
              generalize bits B0 = bB at *
              omega
            · dsimp only [K0]
              simp only [compCostW_ret, exprCostW_pair, exprCostW_inl, exprCostW_inr,
                exprCostW_none, exprCostW_fst, exprCostW_snd, exprCostW_v4, exprCostW_var,
                Nat.reduceAdd]
              omega
          · dsimp only [K0]
            simp only [compCostW_bind, compCostW_ret, exprCostW_pair, exprCostW_inl,
              exprCostW_inr, exprCostW_fst, exprCostW_snd, exprCostW_v0, exprCostW_v3,
              exprCostW_v4, exprCostW_var, Nat.reduceAdd]
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
            exprCostW_snd, hb0, hb1, Nat.reduceAdd]
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
          exprCostW_snd, hb0, hb1, Nat.reduceAdd]
        generalize bits B0 = bB at *
        omega

end GenericCkaCostW

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthCostA
