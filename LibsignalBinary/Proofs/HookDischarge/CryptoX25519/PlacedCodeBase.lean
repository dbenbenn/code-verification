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
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
public meta import Lean
public meta import ProofLib
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches

/-!
# Multi-block placement and cross-block call infrastructure

Shared placement and tactic infrastructure for `x25519CliMultiLib`:

- `X25519CliPlacement`, `x25519CliMpl`, `xbase`: ambient multi-block placement.
- `@[simp, arm64_norm, wp_norm]` symbol resolution lemmas (`resolve_blk00`..`resolve_blk18`
  and `resolve_ro00`..`resolve_ro02`).
- `X25519BlockOk`, `X25519BlockConstOk`, `x25519Call_of_blockOk`, `x25519SubroutineOk_of_blockOk`:
  per-block `MultiPlacedLib` subroutine contracts and O(1) cross-block call transfer.
- `wp_x25519_call` and `wp_x25519_tailcall`: cross-block `BL` and `B` tactics preserving
  `x25519CliMultiLib.CodeLoaded x25519CliMpl` across arbitrary memory writes.
- `X25519Base`, `x25519Leaf_ok`, `x25519Caller_ok`, and `x25519BlockPlacement_ρ`: per-block entry
  combinators paired with `gen_block_fetches`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)

/-! ## 1. Ambient Multi-Block Placement -/

/-- Ambient valid multi-block placement for `x25519CliMultiLib`. -/
class X25519CliPlacement where
  mpl : MultiPlacement
  placeable : x25519CliMultiLib.Placeable mpl

/-- Ambient `MultiPlacement` projection. -/
abbrev x25519CliMpl [X25519CliPlacement] : MultiPlacement :=
  X25519CliPlacement.mpl

/-- Base address `mpl.base i` of block `i` under `X25519CliPlacement`. -/
abbrev xbase [X25519CliPlacement] (i : Nat) : BitVec 64 :=
  X25519CliPlacement.mpl.base i

@[simp] theorem x25519CliMultiLib_blocks_length : x25519CliMultiLib.blocks.length = 19 := rfl

private theorem add_zero_64 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x :=
  BitVec.add_zero x

/-! ## 2. Block & `.rodata` Symbol Resolution Normalization -/

@[simp, arm64_norm, wp_norm] theorem resolve_blk00 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "subtle::black_box::<u8>" = mpl.base 0 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk01 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" = mpl.base 1 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk02 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" = mpl.base 2 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk03 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::scalar::Scalar>::as_radix_16" = mpl.base 3 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk04 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth" = mpl.base 4 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk05 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" = mpl.base 5 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk06 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select" = mpl.base 6 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk07 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" = mpl.base 7 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk08 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add" = mpl.base 8 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk09 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2" = mpl.base 9 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk10 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery" = mpl.base 10 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk11 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine" = mpl.base 11 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk12 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "curve25519_dalek::montgomery::differential_add_and_double" = mpl.base 12 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk13 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base" = mpl.base 13 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk14 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped" = mpl.base 14 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk15 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul" = mpl.base 15 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk16 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped" = mpl.base 16 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk17 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" = mpl.base 17 := add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk18 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from" = mpl.base 18 := add_zero_64 _

@[simp, arm64_norm, wp_norm] theorem resolve_ro00 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.0" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.0" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro01 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "curve25519_dalek:.rodata..Lanon.35" =
      mpl.ρ "curve25519_dalek:.rodata..Lanon.35" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro02 (mpl : MultiPlacement) :
    x25519CliMultiLib.resolve mpl "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" =
      mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" := rfl

/-! ## 3. Per-Block Subroutine Contracts & Cross-Block Call Combinators -/

/-- Layout-generic block `j` contract under `X25519CliPlacement`, wrapped with
    `x25519CliMultiLib.withCodeLoaded x25519CliMpl`. -/
abbrev X25519BlockOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : MultiPlacement → S) : Prop :=
  ∀ [X25519CliPlacement],
    subroutine_ok (x25519CliMultiLib.blockProgram x25519CliMpl j)
      (x25519CliMpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519CliMpl
        (ToBaseSpec.toSpec (spec x25519CliMpl) (x25519CliMpl.base j)))

/-- Placement-independent specialization of `X25519BlockOk` (for functions with no `.rodata`
    symbol references). -/
abbrev X25519BlockConstOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : S) : Prop :=
  X25519BlockOk j (fun _ => spec)

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

/-- Transfer a proved `X25519BlockOk` or `X25519BlockConstOk` contract for block `j` to any
    hook-free rebased block program `(lib.program pl).rebase b (fun _ => none)`. -/
theorem x25519Call_of_blockOk [X25519CliPlacement] (P : Program)
    {lib : PlacedLib} {pl : Placement} {b : BitVec 64} {j : Nat}
    {α : Type} {spec : Spec α}
    (hok : subroutine_ok (x25519CliMultiLib.blockProgram x25519CliMpl j) (x25519CliMpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519CliMpl spec))
    (hP : P = (lib.program pl).rebase b (fun _ => none) := by rfl)
    (hj : j < x25519CliMultiLib.blocks.length := by decide) :
    subroutine_ok P (x25519CliMpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519CliMpl spec) := by
  subst hP
  exact x25519CliMultiLib.subroutine_ok_of_block hj hok
    (fun pc => PlacedLib.externAt?_program_rebase_none lib pl b pc)
    rfl

/-- Export an `X25519BlockOk j spec` proof to `x25519CliMultiLib.subroutineOk sym spec`. -/
theorem x25519SubroutineOk_of_blockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : MultiPlacement → S}
    (hok : X25519BlockOk j spec)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide) :
    x25519CliMultiLib.subroutineOk sym spec := by
  refine ⟨hexp, j, 0, hsym, fun mpl hP => ?_⟩
  letI : X25519CliPlacement := ⟨mpl, hP⟩
  have hfn : x25519CliMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact hok

/-- Export an `X25519BlockConstOk j spec` proof to `x25519CliMultiLib.subroutineOk sym (fun _ => spec)`. -/
theorem x25519SubroutineOk_of_constBlockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hok : X25519BlockConstOk j spec)
    (hexp : sym ∈ x25519CliMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0) := by decide) :
    x25519CliMultiLib.subroutineOk sym (fun _ => spec) :=
  x25519SubroutineOk_of_blockOk (spec := fun _ => spec) hok hexp hsym

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
    `wp_x25519_call` invocations keep `O(1)` `CodeLoaded` hypotheses in context. -/
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

/-- Step a cross-block `BL` call to `hcall : X25519BlockOk j spec` in O(1), closing any active
    `wp_cut_codeLoaded` segment before the call and refreshing `x25519CliMultiLib.CodeLoaded`
    on the post-call memory `sf.mem`. -/
syntax "wp_x25519_call" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_x25519_call $hcall:term $[$opts:wppCallOpt]*) => do
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
        throwError "wp_x25519_call: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    let hclPost ← mkFreshUserName `hcl_post
    let hclPostId := mkIdent hclPost
    evalTactic (← `(tactic| (
      apply seq_codeLoaded_lr ‹_›
      wp_call (x25519Call_of_blockOk $progStx $hcall) $[$opts]*)))
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

/-- Step a cross-block `B` tail-jump to `hcall : X25519BlockOk j spec` in O(1), closing any active
    `wp_cut_codeLoaded` segment before the tail-jump. -/
syntax "wp_x25519_tailcall" ppSpace colGt term:max : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_x25519_tailcall $hcall:term) => do
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
        throwError "wp_x25519_tailcall: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    evalTactic (← `(tactic| wp_tailcall (x25519Call_of_blockOk $progStx $hcall)))

/-! ## 4. Per-Block Entry Combinators (`X25519Base`, `x25519Leaf_ok`, `x25519Caller_ok`) -/

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
abbrev X25519Base (pl : Placement) (b : BitVec 64) : Prop :=
  b = pl.base

/-- Pure-leaf entry combinator for block `j`: reduces `X25519BlockOk` or `X25519BlockConstOk`
    to proving `subroutine_ok (P.rebase b (fun _ => none)) b ...` with `hb : X25519Base pl b` and
    `hbase : pl.base = b` in context (without `CodeLoaded` cluttering context). -/
theorem x25519Leaf_ok [X25519CliPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = x25519CliMultiLib.blockPlacement x25519CliMpl j := by rfl)
    (hP : P = (x25519CliMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), X25519Base pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (ToBaseSpec.toSpec spec b)) :
    subroutine_ok (x25519CliMultiLib.blockProgram x25519CliMpl j) (x25519CliMpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519CliMpl
        (ToBaseSpec.toSpec spec (x25519CliMpl.base j))) := by
  subst hpl hP
  exact withCodeLoaded_of_subroutine_ok (lib := x25519CliMultiLib) (mpl := x25519CliMpl)
    (h (x25519CliMultiLib.blockPlacement x25519CliMpl j).base rfl rfl)

/-- Cross-block caller entry combinator for block `j`: reduces `X25519BlockOk` or `X25519BlockConstOk`
    to proving `subroutine_ok (P.rebase b (fun _ => none)) b (x25519CliMultiLib.withCodeLoaded x25519CliMpl ...)`
    with `hb : X25519Base pl b` and `hbase : pl.base = b` in context so
    `wp_x25519_call` / `wp_x25519_tailcall` and `.rodata` `pairStep` loads normalize in O(1). -/
theorem x25519Caller_ok [X25519CliPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = x25519CliMultiLib.blockPlacement x25519CliMpl j := by rfl)
    (hP : P = (x25519CliMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), X25519Base pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (x25519CliMultiLib.withCodeLoaded x25519CliMpl
          (ToBaseSpec.toSpec spec b))) :
    subroutine_ok (x25519CliMultiLib.blockProgram x25519CliMpl j) (x25519CliMpl.base j)
      (x25519CliMultiLib.withCodeLoaded x25519CliMpl
        (ToBaseSpec.toSpec spec (x25519CliMpl.base j))) := by
  subst hpl hP
  exact h (x25519CliMultiLib.blockPlacement x25519CliMpl j).base rfl rfl

/-- Normalize `(x25519CliMultiLib.blockPlacement x25519CliMpl j).ρ sym` to
    `x25519CliMultiLib.resolve x25519CliMpl sym` so `resolve_blk*` and `resolve_ro*` fire automatically. -/
@[simp, arm64_norm, wp_norm]
theorem x25519BlockPlacement_ρ [X25519CliPlacement] (j : Nat) (sym : String) :
    (x25519CliMultiLib.blockPlacement x25519CliMpl j).ρ sym =
      x25519CliMultiLib.resolve x25519CliMpl sym := rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
