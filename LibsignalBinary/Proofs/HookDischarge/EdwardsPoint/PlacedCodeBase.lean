/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs
public meta import Lean
public meta import ProofLib
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches

/-!
# Multi-Block Placement and Cross-Block Call Infrastructure

Placement and cross-block call-transfer infrastructure for `dalekCliMultiLib`:
- `DalekCliPlacement`, `dalekCliMpl`, `dbase`: ambient multi-block placement.
- `@[simp, arm64_norm, wp_norm]` symbol resolution lemmas (`resolve_blk00`..`resolve_blk36`,
  `resolve_ro00`..`resolve_ro10`).
- `DalekBlockOk`, `DalekBlockConstOk`, `dalekCall_of_blockOk`, `dalekSubroutineOk_of_blockOk`:
  per-block `MultiPlacedLib` subroutine contracts and cross-block call transfer.
- `wp_dalek_call` and `wp_dalek_tailcall`: cross-block `BL` and `B` tactics preserving
  `dalekCliMultiLib.CodeLoaded dalekCliMpl` across arbitrary memory writes.
- `DalekBase`, `dalekLeaf_ok`, `dalekCaller_ok`, `dalekBlockPlacement_ρ`: per-block entry
  combinators paired with `gen_block_fetches`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)

/-! ## 1. Ambient Multi-Block Placement -/

/-- Ambient valid multi-block placement for `dalekCliMultiLib`. -/
class DalekCliPlacement where
  mpl : MultiPlacement
  placeable : dalekCliMultiLib.Placeable mpl

/-- Ambient `MultiPlacement` projection. -/
abbrev dalekCliMpl [DalekCliPlacement] : MultiPlacement :=
  DalekCliPlacement.mpl

/-- Base address `mpl.base i` of block `i` under `DalekCliPlacement`. -/
abbrev dbase [DalekCliPlacement] (i : Nat) : BitVec 64 :=
  DalekCliPlacement.mpl.base i

@[simp] theorem dalekCliMultiLib_blocks_length : dalekCliMultiLib.blocks.length = 37 := rfl

private theorem add_zero_64 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x :=
  BitVec.add_zero x

/-! ## 2. Block & `.rodata` Symbol Resolution Normalization -/

@[simp, arm64_norm, wp_norm] theorem resolve_blk00 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "subtle::black_box::<u8>" = mpl.base 0 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk01 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order" = mpl.base 1 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk02 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide" = mpl.base 2 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk03 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::sqrt_ratio_i" = mpl.base 3 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk04 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" = mpl.base 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk05 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::CompressedEdwardsY>::decompress" = mpl.base 5 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk06 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::montgomery_mul" = mpl.base 6 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk07 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::mul" = mpl.base 7 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk08 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards" = mpl.base 8 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk09 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select" = mpl.base 9 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk10 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select" = mpl.base 10 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk11 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" = mpl.base 11 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk12 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::to_bytes" = mpl.base 12 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk13 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" = mpl.base 13 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk14 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::compress" = mpl.base 14 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk15 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar>::as_radix_16" = mpl.base 15 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk16 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar>::reduce" = mpl.base 16 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk17 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint" = mpl.base 17 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk18 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2" = mpl.base 18 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk19 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free" = mpl.base 19 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk20 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from" = mpl.base 20 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk21 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul" = mpl.base 21 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk22 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" = mpl.base 22 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk23 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add" = mpl.base 23 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk24 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<[u8] as subtle::ConstantTimeEq>::ct_eq" = mpl.base 24 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk25 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from" = mpl.base 25 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk26 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base" = mpl.base 26 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk27 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul" = mpl.base 27 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk28 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" = mpl.base 28 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk29 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::sub" = mpl.base 29 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk30 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint as subtle::ConstantTimeEq>::ct_eq" = mpl.base 30 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk31 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add" = mpl.base 31 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk32 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::sub" = mpl.base 32 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk33 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul" = mpl.base 33 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk34 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul" = mpl.base 34 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk35 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add" = mpl.base 35 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk36 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "memcpy" = mpl.base 36 := add_zero_64 _

-- `.rodata` / `.data.rel.ro` symbol resolution → `mpl.ρ sym`
@[simp, arm64_norm, wp_norm] theorem resolve_ro00 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE" =
      mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro01 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.0" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.0" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro02 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.6" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.6" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro03 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.7" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.7" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro04 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.8" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.8" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro05 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.16" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.16" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro06 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.17" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.17" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro07 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.22" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.22" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro08 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata.cst32+0x0" =
      mpl.ρ "curve25519_dalek:.rodata.cst32+0x0" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro09 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.36" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.36" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro10 (mpl : MultiPlacement) :
    dalekCliMultiLib.resolve mpl "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" =
      mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" := rfl

/-! ## 3. Per-Block Subroutine Contracts & Cross-Block Call Combinators -/

/-- Layout-generic block `j` contract under `DalekCliPlacement`, wrapped with
    `dalekCliMultiLib.withCodeLoaded dalekCliMpl`. -/
abbrev DalekBlockOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : MultiPlacement → S) : Prop :=
  ∀ [DalekCliPlacement],
    subroutine_ok (dalekCliMultiLib.blockProgram dalekCliMpl j)
      (dalekCliMpl.base j)
      (dalekCliMultiLib.withCodeLoaded dalekCliMpl
        (ToBaseSpec.toSpec (spec dalekCliMpl) (dalekCliMpl.base j)))

/-- Placement-independent specialization of `DalekBlockOk` (for functions with no `.rodata`
    symbol references). -/
abbrev DalekBlockConstOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : S) : Prop :=
  DalekBlockOk j (fun _ => spec)

/-- Adjoin `lib.withCodeLoaded mpl` to any `subroutine_ok` contract (used to lift pure leaf block
    proofs without `CodeLoaded` in context). -/
theorem withCodeLoaded_of_subroutine_ok {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok P entry spec) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  refine subroutine_ok_mono hok (fun x R s0 hpre => ?_) (fun _ _ _ _ hp => hp)
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Transfer a proved `DalekBlockOk` or `DalekBlockConstOk` contract for block `j` to any
    hook-free rebased block program `(lib.program pl).rebase b (fun _ => none)`. -/
theorem dalekCall_of_blockOk [DalekCliPlacement] (P : Program)
    {lib : PlacedLib} {pl : Placement} {b : BitVec 64} {j : Nat}
    {α : Type} {spec : Spec α}
    (hok : subroutine_ok (dalekCliMultiLib.blockProgram dalekCliMpl j) (dalekCliMpl.base j)
      (dalekCliMultiLib.withCodeLoaded dalekCliMpl spec))
    (hP : P = (lib.program pl).rebase b (fun _ => none) := by rfl)
    (hj : j < dalekCliMultiLib.blocks.length := by decide) :
    subroutine_ok P (dalekCliMpl.base j)
      (dalekCliMultiLib.withCodeLoaded dalekCliMpl spec) := by
  subst hP
  exact dalekCliMultiLib.subroutine_ok_of_block hj hok
    (fun pc => PlacedLib.externAt?_program_rebase_none lib pl b pc)
    rfl

/-- Export a `DalekBlockOk j spec` proof to `dalekCliMultiLib.subroutineOk sym spec`. -/
theorem dalekSubroutineOk_of_blockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : MultiPlacement → S}
    (hok : DalekBlockOk j spec)
    (hexp : sym ∈ dalekCliMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym dalekCliMultiLib.blocks = some (j, 0) := by decide) :
    dalekCliMultiLib.subroutineOk sym spec := by
  refine ⟨hexp, j, 0, hsym, fun mpl hP => ?_⟩
  letI : DalekCliPlacement := ⟨mpl, hP⟩
  have hfn : dalekCliMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact hok

/-- Export a `DalekBlockConstOk j spec` proof to `dalekCliMultiLib.subroutineOk sym (fun _ => spec)`. -/
theorem dalekSubroutineOk_of_constBlockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hok : DalekBlockConstOk j spec)
    (hexp : sym ∈ dalekCliMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym dalekCliMultiLib.blocks = some (j, 0) := by decide) :
    dalekCliMultiLib.subroutineOk sym (fun _ => spec) :=
  dalekSubroutineOk_of_blockOk (spec := fun _ => spec) hok hexp hsym

/-- Preserve `lib.CodeLoaded mpl` across a `BL` subroutine call returning to `s.readReg64 .lr`. -/
theorem seq_codeLoaded_lr {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog (s.readReg64 .lr) s P (fun sm Pm =>
      lib.CodeLoaded mpl sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom :=
  MultiPlacedLib.seq_codeLoaded hcl h

open Lean Meta in
/-- Check whether the current `SepWP` goal's continuation is a `MultiPlacedLib.seq_codeLoaded`
    cut (`fun sm Pm => MultiPlacedLib.CodeLoaded ... sm.mem → ...`). -/
meta def goalIsSeqCodeLoaded (g : MVarId) : MetaM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``SepWP 6 do return false
  let postExpr := (ty.getArg! 4).consumeMData
  unless postExpr.isLambda && postExpr.bindingBody!.consumeMData.isLambda do return false
  let body2 := postExpr.bindingBody!.consumeMData.bindingBody!.consumeMData
  match body2 with
  | .forallE _ dom _ _ => return dom.consumeMData.isAppOfArity ``MultiPlacedLib.CodeLoaded 3
  | _ => return false

open Lean Meta in
/-- Clear any existing `MultiPlacedLib.CodeLoaded` hypotheses from the current main goal
    before introducing a refreshed post-call `CodeLoaded` hypothesis, so sequential
    `wp_dalek_call` invocations keep `O(1)` `CodeLoaded` hypotheses in context. -/
meta def clearOldCodeLoadedHyps : Elab.Tactic.TacticM Unit := do
  let g ← Elab.Tactic.getMainGoal
  let fvars ← g.withContext do
    let mut acc : Array FVarId := #[]
    for ld in ← getLCtx do
      if ld.isImplementationDetail then continue
      let ty := (← instantiateMVars ld.type).consumeMData
      if ty.isAppOfArity ``MultiPlacedLib.CodeLoaded 3 then
        acc := acc.push ld.fvarId
    return acc
  if !fvars.isEmpty then
    Elab.Tactic.replaceMainGoal [← g.tryClearMany fvars]

/-- Step a cross-block `BL` call to `hcall : DalekBlockOk j spec` in O(1), closing any active
    `wp_cut_codeLoaded` segment before the call and refreshing `dalekCliMultiLib.CodeLoaded`
    on the post-call memory `sf.mem`. -/
syntax "wp_dalek_call" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_dalek_call $hcall:term $[$opts:wppCallOpt]*) => do
    if ← goalIsSeqCodeLoaded (← getMainGoal) then
      let hclPre ← mkFreshUserName `hcl_pre
      let hclPreId := mkIdent hclPre
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · first | assumption | wp_norm_lhs
        intro $hclPreId:ident)))
    let gCur ← getMainGoal
    let progStx ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      unless ty.isAppOfArity ``SepWP 6 do
        throwError "wp_dalek_call: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    let hclPost ← mkFreshUserName `hcl_post
    let hclPostId := mkIdent hclPost
    evalTactic (← `(tactic| (
      apply seq_codeLoaded_lr ‹_›
      wp_call (dalekCall_of_blockOk $progStx $hcall) $[$opts]*)))
    let postCallGoals ← getGoals
    let mut newGoals : List MVarId := []
    for g in postCallGoals do
      if ← goalIsSeqCodeLoaded g then
        setGoals [g]
        evalTactic (← `(tactic| (
          apply SepWP.done
          · first | assumption | wp_norm_lhs | wp_norm_goal | rfl
          · first | assumption | wp_norm_lhs)))
        clearOldCodeLoadedHyps
        evalTactic (← `(tactic| intro $hclPostId:ident))
        newGoals := newGoals ++ (← getGoals)
      else
        newGoals := newGoals ++ [g]
    setGoals newGoals

/-- Step a cross-block `B` tail-jump to `hcall : DalekBlockOk j spec` in O(1), closing any active
    `wp_cut_codeLoaded` segment before the tail-jump. -/
syntax "wp_dalek_tailcall" ppSpace colGt term:max : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_dalek_tailcall $hcall:term) => do
    if ← goalIsSeqCodeLoaded (← getMainGoal) then
      let hclPre ← mkFreshUserName `hcl_pre
      let hclPreId := mkIdent hclPre
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · first | assumption | wp_norm_lhs
        intro $hclPreId:ident)))
    let gCur ← getMainGoal
    let progStx ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      unless ty.isAppOfArity ``SepWP 6 do
        throwError "wp_dalek_tailcall: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    evalTactic (← `(tactic| wp_tailcall (dalekCall_of_blockOk $progStx $hcall)))

/-! ## 4. Per-Block Entry Combinators (`DalekBase`, `dalekLeaf_ok`, `dalekCaller_ok`)

In each proof module, generate per-block decode/fetch/pairStep lemmas with one command:
```
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli <NN> dalekCliMultiLib DalekCliPlacement <words> rebase rho sub
```
and start block `<NN>`'s proof with `apply dalekLeaf_ok dalekCliPC<NN> dalekCliPl<NN>` (pure leaf)
or `apply dalekCaller_ok dalekCliPC<NN> dalekCliPl<NN>` (cross-block caller). -/

@[simp, arm64_norm, wp_norm]
theorem add_off_reloc_cancel (b target off : BitVec 64) :
    b + off + (target - b - off) = target := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_zero_reloc_cancel (b target : BitVec 64) :
    b + (target - b - 0#64) = target := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_reloc_cancel (b target : BitVec 64) :
    b + (target - b) = target := by
  bv_omega

/-- Reducible abbreviation for `b = pl.base` that is not syntactically an `Eq`,
    preventing `wp_steps` from rewriting `b` in `b + off#64` PCs while allowing `tryPairStepHook`
    to discharge `b = pl.base` by reducible `assumption`. -/
abbrev DalekBase (pl : Placement) (b : BitVec 64) : Prop :=
  b = pl.base

/-- Pure-leaf entry combinator for block `j`: reduces `DalekBlockOk` or `DalekBlockConstOk`
    to proving `subroutine_ok (P.rebase b (fun _ => none)) b ...` with `hb : DalekBase pl b` and
    `hbase : pl.base = b` in context (omitting `CodeLoaded`). -/
theorem dalekLeaf_ok [DalekCliPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = dalekCliMultiLib.blockPlacement dalekCliMpl j := by rfl)
    (hP : P = (dalekCliMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), DalekBase pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (ToBaseSpec.toSpec spec b)) :
    subroutine_ok (dalekCliMultiLib.blockProgram dalekCliMpl j) (dalekCliMpl.base j)
      (dalekCliMultiLib.withCodeLoaded dalekCliMpl
        (ToBaseSpec.toSpec spec (dalekCliMpl.base j))) := by
  subst hpl hP
  exact withCodeLoaded_of_subroutine_ok (lib := dalekCliMultiLib) (mpl := dalekCliMpl)
    (h (dalekCliMultiLib.blockPlacement dalekCliMpl j).base rfl rfl)

/-- Cross-block caller entry combinator for block `j`: reduces `DalekBlockOk` or `DalekBlockConstOk`
    to proving `subroutine_ok (P.rebase b (fun _ => none)) b (dalekCliMultiLib.withCodeLoaded dalekCliMpl ...)`
    with `hb : DalekBase pl b` and `hbase : pl.base = b` in context so
    `wp_dalek_call` / `wp_dalek_tailcall` and `.rodata` `pairStep` loads normalize in O(1). -/
theorem dalekCaller_ok [DalekCliPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = dalekCliMultiLib.blockPlacement dalekCliMpl j := by rfl)
    (hP : P = (dalekCliMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), DalekBase pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (dalekCliMultiLib.withCodeLoaded dalekCliMpl
          (ToBaseSpec.toSpec spec b))) :
    subroutine_ok (dalekCliMultiLib.blockProgram dalekCliMpl j) (dalekCliMpl.base j)
      (dalekCliMultiLib.withCodeLoaded dalekCliMpl
        (ToBaseSpec.toSpec spec (dalekCliMpl.base j))) := by
  subst hpl hP
  exact h (dalekCliMultiLib.blockPlacement dalekCliMpl j).base rfl rfl

/-- Normalize `(dalekCliMultiLib.blockPlacement dalekCliMpl j).ρ sym` to
    `dalekCliMultiLib.resolve dalekCliMpl sym` so `resolve_blk*` and `resolve_ro*` fire automatically. -/
@[simp, arm64_norm, wp_norm]
theorem dalekBlockPlacement_ρ [DalekCliPlacement] (j : Nat) (sym : String) :
    (dalekCliMultiLib.blockPlacement dalekCliMpl j).ρ sym =
      dalekCliMultiLib.resolve dalekCliMpl sym := rfl

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase
