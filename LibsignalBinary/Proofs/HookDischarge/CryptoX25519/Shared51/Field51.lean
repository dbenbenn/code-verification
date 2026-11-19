/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base

/-!
# `FieldElement51` machine-code leaf proofs

Verifies `x25519CliMultiLib` blocks `01` (`Mul::mul`) and `02` (`pow2k`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpPow)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl X25519Base X25519BlockConstOk x25519Leaf_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded
  fe51MulSpec Fe51MulOk
  fe51MulRoRightSpec Fe51MulRoRightOk
  fe51MulRoLeftSpec Fe51MulRoLeftOk
  fe51Pow2kSpec Fe51Pow2kOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  addWithCarry64_false_c stackFrame_eq_stackFrameAt stack_fold_step stack_fold_last
  stack_swap_slice pointsToBytes40_eq_cells pointsToBytesRO40_eq_cells fpPow_mod_eq_pow_mod)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base (
  packFe51Bytes pointsToBytes_packFe51Bytes fe51ValOfBytes_packFe51Bytes
  fe51LimbsBounded_packFe51Bytes bv64_and_mask51_toNat)

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 01 x25519CliMultiLib X25519CliPlacement 166 rebase rho sub

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 02 x25519CliMultiLib X25519CliPlacement 100 rebase rho sub

private meta partial def findTopRegVal (targetReg : Lean.Expr) (st : Lean.Expr) :
    Lean.MetaM (Option Lean.Expr) := do
  let st := st.consumeMData
  if st.isAppOfArity ``State.writeReg64 3 then
    let r := (st.getArg! 1).consumeMData
    if (← Lean.Meta.isDefEq r targetReg) then return some (st.getArg! 2)
    else findTopRegVal targetReg (st.getArg! 0)
  else if st.isAppOfArity ``State.setPState 2 || st.isAppOfArity ``State.setPC 2 ||
          st.isAppOfArity ``State.setMem 2 || st.isAppOfArity ``State.writeVReg128 3 then
    findTopRegVal targetReg (st.getArg! 0)
  else return none

open Lean Elab Tactic Meta in
local elab "wp_gen_reg " r:term:max x:ident h:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let targetReg ← elabTerm r (some (mkConst ``Reg))
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let s := ty.getArg! 2
    let some val ← findTopRegVal targetReg s
      | throwTacticEx `wp_gen_reg g m!"register {targetReg} not found in state"
    let (_, g') ← g.generalize #[{ expr := val, xName? := x.getId, hName? := h.getId }]
    replaceMainGoal [g']

arm64_proof_prelude

open Lean Meta in
local simproc [wp_norm] reduceStackFrameFVarFe51 (stackFrame _ _) := fun e => do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``Arm64.stackFrame 2 do return .continue
  let sExpr := (e.getArg! 0).consumeMData; let nExpr := e.getArg! 1
  let some n := nExpr.nat? | return .continue
  if (sExpr.isFVar || n ≤ 16) && n ≤ 2 ^ 64 then
    let rhs := mkApp2 (mkConst ``Arm64.stackFrameAt) (mkApp (mkConst ``Arm64.State.sp) sExpr) nExpr
    let hn ← mkDecideProof (← mkAppM ``LE.le #[nExpr, mkNatLit (2 ^ 64)])
    return .visit { expr := rhs, proof? := some (mkApp3 (mkConst ``stackFrame_eq_stackFrameAt) sExpr nExpr hn) }
  else
    let subExpr ← mkAppM ``HSub.hSub #[mkApp (mkConst ``Arm64.State.sp) sExpr, toExpr (BitVec.ofNat 64 n)]
    return .visit { expr := mkApp2 (mkConst ``Arm64.memRegion) subExpr nExpr, proof? := none }

private theorem stack_swap_slice_ro (sp off v p : BitVec 64) (bs : List (BitVec 8)) (rest : SepProp) :
    (((sp - off) ↦₆₄ v) ∗ ((p ↦ᵣ bs) ∗ rest)) = ((p ↦ᵣ bs) ∗ (((sp - off) ↦₆₄ v) ∗ rest)) :=
  sepConj_left_comm _ _ _

private meta def matchStackCell? (e : Lean.Expr) : Option (Lean.Expr × Nat × Lean.Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.pointsTo64 2 then
    let addr := (e.getArg! 0).consumeMData
    if addr.isAppOfArity ``HSub.hSub 6 then
      match ProofLib.evalBitVecLitPure? (addr.getArg! 5) with
      | some (64, n) => some (addr.getArg! 4, n, e.getArg! 1) | _ => none
    else none
  else none

private meta def matchStackRegion? (e : Lean.Expr) : Option (Lean.Expr × Nat) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.memRegion 2 then
    let addr := (e.getArg! 0).consumeMData
    if addr.isAppOfArity ``HSub.hSub 6 then
      match ProofLib.evalBitVecLitPure? (addr.getArg! 5), (e.getArg! 1).consumeMData.nat? with
      | some (64, n), some k => if n == k then some (addr.getArg! 4, k) else none | _, _ => none
    else none
  else none

private meta partial def foldStackEntails (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let P := e.getArg! 0; let Q := e.getArg! 1
    let (Q', hQ) ← foldStackEntails Q
    let step1 := Lean.mkApp4 (Lean.mkConst ``sepConj_mono_right) P Q Q' hQ
    let mid := Lean.mkApp2 (Lean.mkConst ``SepProp.sepConj) P Q'
    if let (some (sp1, n, v), some (sp2, k)) := (matchStackCell? P, matchStackRegion? Q') then
      if sp1 == sp2 && 8 + k == n && n ≤ 2 ^ 64 then
        let nExpr := Lean.mkNatLit n; let kExpr := Lean.mkNatLit k
        let hmk ← Lean.Meta.mkEqRefl nExpr
        let hn ← Lean.Meta.mkDecideProof (← Lean.Meta.mkAppM ``LE.le #[nExpr, Lean.mkNatLit (2 ^ 64)])
        let step2 := Lean.mkApp6 (Lean.mkConst ``stack_fold_step) sp1 v nExpr kExpr hmk hn
        let subN ← Lean.Meta.mkAppM ``HSub.hSub #[sp1, Lean.ToExpr.toExpr (BitVec.ofNat 64 n)]
        let rhs := Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) subN nExpr
        return (rhs, Lean.mkApp5 (Lean.mkConst ``Entails.trans) e mid rhs step1 step2)
    return (mid, step1)
  else if let some (sp, 8, v) := matchStackCell? e then
    let sub8 ← Lean.Meta.mkAppM ``HSub.hSub #[sp, Lean.ToExpr.toExpr (8#64)]
    return (Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) sub8 (Lean.mkNatLit 8),
            Lean.mkApp2 (Lean.mkConst ``stack_fold_last) sp v)
  else return (e, Lean.mkApp (Lean.mkConst ``Entails.refl) e)

local elab "wp_fold_stack" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| wp_conv_pre => simp only [stack_swap_slice, stack_swap_slice_ro, sepConj_assoc]))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return
    let prog := ty.getArg! 0; let targetPc := ty.getArg! 1; let s := ty.getArg! 2
    let P := ty.getArg! 3; let post := ty.getArg! 4; let oom := ty.getArg! 5
    let (P', hent) ← foldStackEntails P
    let gNew ← Lean.Meta.mkFreshExprMVar (Lean.mkApp6 (Lean.mkConst ``SepWP) prog targetPc s P' post oom) .syntheticOpaque (← g.getTag)
    g.assign (Lean.mkAppN (Lean.mkConst ``SepWP.weaken_pre) #[prog, targetPc, s, P, P', post, oom, hent, gNew])
    Lean.Elab.Tactic.replaceMainGoal [gNew.mvarId!]

private theorem cinc_ule_norm (s c H : BitVec 64) :
    (if s.ule (s + c) = true then H else H + 1#64) =
      H + (if (s + c).ult s = true then 1#64 else 0#64) := by bv_bits

private theorem bv64_ult_add_iff (a b : BitVec 64) : ((a + b).ult a = true) ↔ a.toNat + b.toNat ≥ 2 ^ 64 := by bv_bits
private theorem bv64_append_toNat (hi lo : BitVec 64) : (hi ++ lo).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by bv_bits

private theorem bv64_extr51_toNat (hi lo : BitVec 64) (h : hi.toNat < 2 ^ 51) :
    (BitVec.setWidth 64 ((hi ++ lo) >>> 51)).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) / 2 ^ 51 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, bv64_append_toNat]; omega

private theorem bv64_mask51_hi_lo_toNat (hi lo : BitVec 64) :
    (lo &&& 2251799813685247#64).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % 2 ^ 51 := by
  rw [bv64_and_mask51_toNat]; omega

private theorem mul128_hi_lo_toNat (x y : BitVec 64) :
    (BitVec.setWidth 64 ((BitVec.setWidth 128 x * BitVec.setWidth 128 y) >>> 64)).toNat * 2 ^ 64 +
      (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_mul]
  have hx : x.toNat < 2 ^ 64 := x.isLt; have hy : y.toNat < 2 ^ 64 := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by decide
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128), Nat.mod_eq_of_lt hxy]; omega

private theorem add128_ult_toNat (hi lo dh dl : BitVec 64)
    (h : (hi.toNat * 2 ^ 64 + lo.toNat) + (dh.toNat * 2 ^ 64 + dl.toNat) < 2 ^ 128) :
    (hi + dh + (if (lo + dl).ult lo = true then 1#64 else 0#64)).toNat * 2 ^ 64 +
      (lo + dl).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) + (dh.toNat * 2 ^ 64 + dl.toNat) := by
  have hlo : lo.toNat < 2 ^ 64 := lo.isLt; have hdl : dl.toNat < 2 ^ 64 := dl.isLt
  cases h_ult : (lo + dl).ult lo
  · have h_nlt : ¬ (lo.toNat + dl.toNat ≥ 2 ^ 64) := by rw [← bv64_ult_add_iff, h_ult]; decide
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]; rw [BitVec.toNat_add, BitVec.toNat_add]; omega
  · have h_ge : lo.toNat + dl.toNat ≥ 2 ^ 64 := (bv64_ult_add_iff lo dl).mp h_ult
    simp only [↓reduceIte]; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
    change (((hi.toNat + dh.toNat) % 2 ^ 64 + 1) % 2 ^ 64) * 2 ^ 64 + (lo.toNat + dl.toNat) % 2 ^ 64 =
      hi.toNat * 2 ^ 64 + lo.toNat + (dh.toNat * 2 ^ 64 + dl.toNat); omega

private theorem add128_adc_toNat (hi lo dh dl : BitVec 64)
    (h : (hi.toNat * 2 ^ 64 + lo.toNat) + (dh.toNat * 2 ^ 64 + dl.toNat) < 2 ^ 128) :
    (hi + dh + (if (AddWithCarry64 lo dl false).snd.c = true then 1#64 else 0#64)).toNat * 2 ^ 64 +
      (lo + dl).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) + (dh.toNat * 2 ^ 64 + dl.toNat) := by
  rw [addWithCarry64_false_c]; exact add128_ult_toNat hi lo dh dl h

private theorem add128_cinc_toNat (hi lo c : BitVec 64) (h : (hi.toNat * 2 ^ 64 + lo.toNat) + c.toNat < 2 ^ 128) :
    (if lo.ule (lo + c) = true then hi else hi + 1#64).toNat * 2 ^ 64 +
      (lo + c).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) + c.toNat := by
  rw [cinc_ule_norm]
  have h' : (hi.toNat * 2 ^ 64 + lo.toNat) + ((0#64 : BitVec 64).toNat * 2 ^ 64 + c.toNat) < 2 ^ 128 := by simpa using h
  simpa [BitVec.add_zero] using add128_ult_toNat hi lo 0#64 c h'

private theorem add128_adc_step (hi lo dh dl : BitVec 64) (S D : Nat)
    (hS : hi.toNat * 2 ^ 64 + lo.toNat = S) (hD : dh.toNat * 2 ^ 64 + dl.toNat = D) (h : S + D < 2 ^ 128) :
    (hi + dh + (if (AddWithCarry64 lo dl false).snd.c = true then 1#64 else 0#64)).toNat * 2 ^ 64 +
      (lo + dl).toNat = S + D := by rw [← hS, ← hD] at h ⊢; exact add128_adc_toNat hi lo dh dl h

private abbrev sum5ProdHi (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : BitVec 64) : BitVec 64 :=
  ((((BitVec.setWidth 64 ((BitVec.setWidth 128 x0 * BitVec.setWidth 128 y0) >>> 64) +
      BitVec.setWidth 64 ((BitVec.setWidth 128 x1 * BitVec.setWidth 128 y1) >>> 64) +
      if (AddWithCarry64 (x0 * y0) (x1 * y1) false).snd.c = true then 1#64 else 0#64) +
     BitVec.setWidth 64 ((BitVec.setWidth 128 x2 * BitVec.setWidth 128 y2) >>> 64) +
     if (AddWithCarry64 (x0 * y0 + x1 * y1) (x2 * y2) false).snd.c = true then 1#64 else 0#64) +
    BitVec.setWidth 64 ((BitVec.setWidth 128 x3 * BitVec.setWidth 128 y3) >>> 64) +
    if (AddWithCarry64 (x0 * y0 + x1 * y1 + x2 * y2) (x3 * y3) false).snd.c = true then 1#64 else 0#64) +
   BitVec.setWidth 64 ((BitVec.setWidth 128 x4 * BitVec.setWidth 128 y4) >>> 64) +
   if (AddWithCarry64 (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) (x4 * y4) false).snd.c = true then 1#64 else 0#64)

private theorem fe51_sum5_prod128_nat (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : BitVec 64)
    (hp0 : x0.toNat * y0.toNat < 2 ^ 115) (hp1 : x1.toNat * y1.toNat < 2 ^ 115)
    (hp2 : x2.toNat * y2.toNat < 2 ^ 115) (hp3 : x3.toNat * y3.toNat < 2 ^ 115) (hp4 : x4.toNat * y4.toNat < 2 ^ 115) :
    (sum5ProdHi x0 y0 x1 y1 x2 y2 x3 y3 x4 y4).toNat * 2 ^ 64 + (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4).toNat =
      x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat := by
  have s1 := add128_adc_step _ _ _ _ _ _ (mul128_hi_lo_toNat x0 y0) (mul128_hi_lo_toNat x1 y1) (by omega)
  have s2 := add128_adc_step _ _ _ _ _ _ s1 (mul128_hi_lo_toNat x2 y2) (by omega)
  have s3 := add128_adc_step _ _ _ _ _ _ s2 (mul128_hi_lo_toNat x3 y3) (by omega)
  exact add128_adc_step _ _ _ _ _ _ s3 (mul128_hi_lo_toNat x4 y4) (by omega)

private theorem bv64_mul19_toNat_of_lt (b : BitVec 64) (hb : b.toNat < 2 ^ 54) : (b * 19#64).toNat = b.toNat * 19 := by
  rw [BitVec.toNat_mul]; change (b.toNat * 19) % 2 ^ 64 = b.toNat * 19; omega
private theorem bv64_mul19_lt (b : BitVec 64) (hb : b.toNat < 2 ^ 54) : (b * 19#64).toNat < 19 * 2 ^ 54 := by
  rw [bv64_mul19_toNat_of_lt b hb]; omega
private theorem nat_lt_19_54 {b : Nat} (hb : b < 2 ^ 54) : b < 19 * 2 ^ 54 := by omega
private theorem nat_mul_lt_19_108 {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 19 * 2 ^ 54) : x * y < 19 * 2 ^ 108 := by
  calc x * y < 2 ^ 54 * (19 * 2 ^ 54) := Nat.mul_lt_mul'' hx hy
    _ = 19 * 2 ^ 108 := by decide
private theorem nat_mul_lt_108 {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) : x * y < 2 ^ 108 := by
  calc x * y < 2 ^ 54 * 2 ^ 54 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 108 := by decide

private theorem fe51_sum5_prod128_eq (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 s_hi s_lo : BitVec 64)
    (hs_hi : sum5ProdHi x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 = s_hi) (hs_lo : x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 = s_lo)
    (hx0 : x0.toNat < 2 ^ 54) (hy0 : y0.toNat < 19 * 2 ^ 54) (hx1 : x1.toNat < 2 ^ 54) (hy1 : y1.toNat < 19 * 2 ^ 54)
    (hx2 : x2.toNat < 2 ^ 54) (hy2 : y2.toNat < 19 * 2 ^ 54) (hx3 : x3.toNat < 2 ^ 54) (hy3 : y3.toNat < 19 * 2 ^ 54)
    (hx4 : x4.toNat < 2 ^ 54) (hy4 : y4.toNat < 19 * 2 ^ 54) :
    s_hi.toNat * 2 ^ 64 + s_lo.toNat =
      x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat ∧
    x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat < 95 * 2 ^ 108 := by
  have hp0 := nat_mul_lt_19_108 hx0 hy0; have hp1 := nat_mul_lt_19_108 hx1 hy1
  have hp2 := nat_mul_lt_19_108 hx2 hy2; have hp3 := nat_mul_lt_19_108 hx3 hy3; have hp4 := nat_mul_lt_19_108 hx4 hy4
  refine ⟨?_, by omega⟩; rw [← hs_hi, ← hs_lo]
  exact fe51_sum5_prod128_nat x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem fe51_sum5_prod128_eq_unscaled (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 s_hi s_lo : BitVec 64)
    (hs_hi : sum5ProdHi x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 = s_hi) (hs_lo : x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4 = s_lo)
    (hx0 : x0.toNat < 2 ^ 54) (hy0 : y0.toNat < 2 ^ 54) (hx1 : x1.toNat < 2 ^ 54) (hy1 : y1.toNat < 2 ^ 54)
    (hx2 : x2.toNat < 2 ^ 54) (hy2 : y2.toNat < 2 ^ 54) (hx3 : x3.toNat < 2 ^ 54) (hy3 : y3.toNat < 2 ^ 54)
    (hx4 : x4.toNat < 2 ^ 54) (hy4 : y4.toNat < 2 ^ 54) :
    s_hi.toNat * 2 ^ 64 + s_lo.toNat =
      x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat ∧
    x0.toNat * y0.toNat + x1.toNat * y1.toNat + x2.toNat * y2.toNat + x3.toNat * y3.toNat + x4.toNat * y4.toNat < 5 * 2 ^ 108 := by
  have hp0 := nat_mul_lt_108 hx0 hy0; have hp1 := nat_mul_lt_108 hx1 hy1
  have hp2 := nat_mul_lt_108 hx2 hy2; have hp3 := nat_mul_lt_108 hx3 hy3; have hp4 := nat_mul_lt_108 hx4 hy4
  refine ⟨?_, by omega⟩; rw [← hs_hi, ← hs_lo]
  exact fe51_sum5_prod128_nat x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem fe51_col0_extr_nat (hi lo : BitVec 64) (S : Nat) (hS : hi.toNat * 2 ^ 64 + lo.toNat = S) (h_lt : S < 2 ^ 115) :
    (lo &&& 2251799813685247#64).toNat = S % 2 ^ 51 ∧ (BitVec.setWidth 64 ((hi ++ lo) >>> 51)).toNat = S / 2 ^ 51 :=
  ⟨by rw [bv64_mask51_hi_lo_toNat hi lo, hS], by rw [bv64_extr51_toNat hi lo (by omega), hS]⟩

private theorem fe51_col_carry_extr_nat (hi lo c : BitVec 64) (S : Nat)
    (hS : hi.toNat * 2 ^ 64 + lo.toNat = S) (h_lt : S + c.toNat < 2 ^ 115) :
    ((lo + c) &&& 2251799813685247#64).toNat = (S + c.toNat) % 2 ^ 51 ∧
    (BitVec.setWidth 64 (((if lo.ule (lo + c) = true then hi else hi + 1#64) ++ (lo + c)) >>> 51)).toNat =
      (S + c.toNat) / 2 ^ 51 := by
  have hcinc := add128_cinc_toNat hi lo c (by omega); rw [hS] at hcinc
  exact fe51_col0_extr_nat (if lo.ule (lo + c) = true then hi else hi + 1#64) (lo + c) (S + c.toNat) hcinc h_lt

private theorem div_mod_51_rel {X r q : Nat} (h : r = X % 2 ^ 51 ∧ q = X / 2 ^ 51) : r + q * 2 ^ 51 = X ∧ r < 2 ^ 51 := by
  rcases h with ⟨hr, hq⟩; subst hr hq; exact ⟨by have := Nat.mod_add_div X (2 ^ 51); omega, Nat.mod_lt X (by decide)⟩

private theorem fe51_col0_extr_rel (hi lo c : BitVec 64) (S : Nat)
    (hc : BitVec.setWidth 64 ((hi ++ lo) >>> 51) = c) (hS : hi.toNat * 2 ^ 64 + lo.toNat = S) (h_lt : S < 2 ^ 115) :
    (lo &&& 2251799813685247#64).toNat + c.toNat * 2 ^ 51 = S ∧ (lo &&& 2251799813685247#64).toNat < 2 ^ 51 := by
  rw [← hc]; exact div_mod_51_rel (fe51_col0_extr_nat hi lo S hS h_lt)

private theorem fe51_col_carry_extr_rel (hi lo c c_next : BitVec 64) (S : Nat)
    (hc_next : BitVec.setWidth 64 (((if lo.ule (lo + c) = true then hi else hi + 1#64) ++ (lo + c)) >>> 51) = c_next)
    (hS : hi.toNat * 2 ^ 64 + lo.toNat = S) (h_lt : S + c.toNat < 2 ^ 115) :
    ((lo + c) &&& 2251799813685247#64).toNat + c_next.toNat * 2 ^ 51 = S + c.toNat ∧
    ((lo + c) &&& 2251799813685247#64).toNat < 2 ^ 51 := by
  rw [← hc_next]; exact div_mod_51_rel (fe51_col_carry_extr_nat hi lo c S hS h_lt)

private theorem fe51_final_c4_rel (l0 l1 c4 : BitVec 64)
    (hl0 : l0.toNat < 2 ^ 51) (hl1 : l1.toNat < 2 ^ 51) (hc4 : c4.toNat < 6 * 2 ^ 57) :
    ∃ d0 : Nat,
      (((l0 + c4 * 19#64) &&& 2251799813685247#64).toNat + d0 * 2 ^ 51 = l0.toNat + c4.toNat * 19 ∧
       ((l0 + c4 * 19#64) &&& 2251799813685247#64).toNat < 2 ^ 51) ∧
      (l1 + ((l0 + c4 * 19#64) >>> 51)).toNat = l1.toNat + d0 := by
  have hm19 : (c4 * 19#64).toNat = c4.toNat * 19 := by rw [BitVec.toNat_mul]; change (c4.toNat * 19) % 2 ^ 64 = c4.toNat * 19; omega
  have hsum : (l0 + c4 * 19#64).toNat = l0.toNat + c4.toNat * 19 := by rw [BitVec.toNat_add, hm19, Nat.mod_eq_of_lt (by omega)]
  have hmask : ((l0 + c4 * 19#64) &&& 2251799813685247#64).toNat = (l0.toNat + c4.toNat * 19) % 2 ^ 51 := by rw [bv64_and_mask51_toNat, hsum]
  have hshr : ((l0 + c4 * 19#64) >>> 51).toNat = (l0.toNat + c4.toNat * 19) / 2 ^ 51 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsum]
  refine ⟨(l0.toNat + c4.toNat * 19) / 2 ^ 51, div_mod_51_rel ⟨hmask, rfl⟩, ?_⟩
  rw [BitVec.toNat_add, hshr, Nat.mod_eq_of_lt (by omega)]

private theorem fe51_mul_carry_nat (S0 S1 S2 S3 S4 l0 l1 r0 r1 r2 r3 r4 c0 c1 c2 c3 c4 d0 : Nat)
    (hS0 : S0 < 95 * 2 ^ 108) (hS1 : S1 < 95 * 2 ^ 108) (hS2 : S2 < 95 * 2 ^ 108) (hS3 : S3 < 95 * 2 ^ 108) (hS4 : S4 < 5 * 2 ^ 108)
    (h0 : l0 + c0 * 2 ^ 51 = S0 ∧ l0 < 2 ^ 51) (h1 : l1 + c1 * 2 ^ 51 = S1 + c0 ∧ l1 < 2 ^ 51)
    (h2 : r2 + c2 * 2 ^ 51 = S2 + c1 ∧ r2 < 2 ^ 51) (h3 : r3 + c3 * 2 ^ 51 = S3 + c2 ∧ r3 < 2 ^ 51)
    (h4 : r4 + c4 * 2 ^ 51 = S4 + c3 ∧ r4 < 2 ^ 51) (hd0 : r0 + d0 * 2 ^ 51 = l0 + c4 * 19 ∧ r0 < 2 ^ 51) (hr1 : r1 = l1 + d0) :
    r0 < 2 ^ 52 ∧ r1 < 2 ^ 52 ∧ r2 < 2 ^ 52 ∧ r3 < 2 ^ 52 ∧ r4 < 2 ^ 52 ∧
    (r0 + r1 * 2 ^ 51 + r2 * 2 ^ 102 + r3 * 2 ^ 153 + r4 * 2 ^ 204) + c4 * p25519 =
      S0 + S1 * 2 ^ 51 + S2 * 2 ^ 102 + S3 * 2 ^ 153 + S4 * 2 ^ 204 := by dsimp only [p25519]; omega

private theorem expand5_mul (A0 A1 A2 A3 A4 B : Nat) :
    (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) * B =
      A0 * B + A1 * B * 2 ^ 51 + A2 * B * 2 ^ 102 + A3 * B * 2 ^ 153 + A4 * B * 2 ^ 204 := by
  simp only [Nat.add_mul, Nat.mul_right_comm _ _ B]

private theorem mul_expand5 (A B0 B1 B2 B3 B4 : Nat) :
    A * (B0 + B1 * 2 ^ 51 + B2 * 2 ^ 102 + B3 * 2 ^ 153 + B4 * 2 ^ 204) =
      A * B0 + A * B1 * 2 ^ 51 + A * B2 * 2 ^ 102 + A * B3 * 2 ^ 153 + A * B4 * 2 ^ 204 := by
  simp only [Nat.mul_add, ← Nat.mul_assoc]

private theorem fe51_mul_poly_nat (A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : Nat) :
    ∃ K : Nat,
      ((A4 * (B1 * 19) + B0 * A0 + A3 * (B2 * 19) + A2 * (B3 * 19) + A1 * (B4 * 19)) +
       (A4 * (B2 * 19) + A0 * B1 + A3 * (B3 * 19) + A2 * (B4 * 19) + A1 * B0) * 2 ^ 51 +
       (A4 * (B3 * 19) + A0 * B2 + A3 * (B4 * 19) + A2 * B0 + A1 * B1) * 2 ^ 102 +
       (A4 * (B4 * 19) + A0 * B3 + A3 * B0 + A2 * B1 + A1 * B2) * 2 ^ 153 +
       (A4 * B0 + A0 * B4 + A3 * B1 + A2 * B2 + A1 * B3) * 2 ^ 204) + K * p25519 =
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) *
      (B0 + B1 * 2 ^ 51 + B2 * 2 ^ 102 + B3 * 2 ^ 153 + B4 * 2 ^ 204) := by
  refine ⟨A4 * B1 + (A3 * B2 + A4 * B2 * 2 ^ 51) + (A2 * B3 + A3 * B3 * 2 ^ 51 + A4 * B3 * 2 ^ 102) +
    (A1 * B4 + A2 * B4 * 2 ^ 51 + A3 * B4 * 2 ^ 102 + A4 * B4 * 2 ^ 153), ?_⟩
  dsimp only [p25519]
  rw [mul_expand5, expand5_mul _ _ _ _ _ B0, expand5_mul _ _ _ _ _ B1,
      expand5_mul _ _ _ _ _ B2, expand5_mul _ _ _ _ _ B3, expand5_mul _ _ _ _ _ B4, Nat.mul_comm B0 A0]
  simp only [Nat.add_mul, ← Nat.mul_assoc]; omega

private theorem fe51_post_entails (out : BitVec 64) (res_bs : List (BitVec 8)) (stk : SepProp) (val : Nat)
    (hb : fe51LimbsBounded res_bs (2 ^ 52)) (hm : fe51ValOfBytes res_bs % p25519 = val) :
    ((out ↦ₛ res_bs) ∗ stk) ⊢
      (stk ∗ ∃∗ bs, (out ↦ₛ bs) ∗ ⌜fe51LimbsBounded bs (2 ^ 52) ∧ fe51ValOfBytes bs % p25519 = val⌝) := by
  rw [sepConj_comm]; refine sepConj_mono_right (Entails.sepExists_right res_bs ?_)
  rw [eq_true (And.intro hb hm), sepConj_pure_true]; exact Entails.refl _

private theorem stackFrame_of_sp_eq {s s0 : State} (n : Nat) (hsp : s.sp = s0.sp) (hn : n ≤ 2 ^ 64 := by decide) :
    stackFrame s n = memRegion (s0.sp - BitVec.ofNat 64 n) n := by
  rw [stackFrame_eq_stackFrameAt s n hn, hsp, stackFrameAt_eq_memRegion s0.sp n hn]

local macro "fe51_mul_body " pA:ident pB:ident s0:ident a:ident a_1:ident a_2:ident a_3:ident a_4:ident a_rest:ident h:ident h_4:ident h_5:ident : tactic => `(tactic| (
  obtain ⟨h_len_a, ha0, ha1, ha2, ha3, ha4⟩ := $h_5; obtain ⟨h_len_b, hb0, hb1, hb2, hb3, hb4⟩ := $h
  wp_conv_pre =>
    rw [$pA $a $a_4 h_len_a, $pB $a_2 $a_rest h_len_b, pointsToBytes40_eq_cells $a_1 $a_3 $h_4]
  generalize ha0_eq : ByteSlice.readLE $a_4 0 8 = a0 at *; generalize ha1_eq : ByteSlice.readLE $a_4 8 8 = a1 at *
  generalize ha2_eq : ByteSlice.readLE $a_4 16 8 = a2 at *; generalize ha3_eq : ByteSlice.readLE $a_4 24 8 = a3 at *
  generalize ha4_eq : ByteSlice.readLE $a_4 32 8 = a4 at *; generalize hb0_eq : ByteSlice.readLE $a_rest 0 8 = b0 at *
  generalize hb1_eq : ByteSlice.readLE $a_rest 8 8 = b1 at *; generalize hb2_eq : ByteSlice.readLE $a_rest 16 8 = b2 at *
  generalize hb3_eq : ByteSlice.readLE $a_rest 24 8 = b3 at *; generalize hb4_eq : ByteSlice.readLE $a_rest 32 8 = b4 at *
  wp_sym_steps 79; wp_gen_reg (Reg.gpr 10#5) s0_hi hs0_hi; wp_gen_reg (Reg.gpr 9#5) s0_lo hs0_lo
  wp_sym_steps 4; wp_gen_reg (Reg.gpr 10#5) c0 hc0; wp_sym_steps 13
  wp_gen_reg (Reg.gpr 11#5) s1_hi hs1_hi; wp_gen_reg (Reg.gpr 8#5) s1_lo hs1_lo
  wp_sym_steps 8; wp_gen_reg (Reg.gpr 11#5) c1 hc1; wp_sym_steps 12
  wp_gen_reg (Reg.gpr 15#5) s2_hi hs2_hi; wp_gen_reg (Reg.gpr 16#5) s2_lo hs2_lo
  wp_sym_steps 6; wp_gen_reg (Reg.gpr 15#5) c2 hc2; wp_sym_steps 13
  wp_gen_reg (Reg.gpr 18#5) s3_hi hs3_hi; wp_gen_reg (Reg.gpr 12#5) s3_lo hs3_lo
  wp_sym_steps 6; wp_gen_reg (Reg.gpr 15#5) c3 hc3; wp_sym_steps 10
  wp_gen_reg (Reg.gpr 10#5) s4_hi hs4_hi; wp_gen_reg (Reg.gpr 14#5) s4_lo hs4_lo
  wp_sym_steps 4; wp_gen_reg (Reg.gpr 10#5) c4 hc4; wp_sym_steps
  obtain ⟨hS0, hS0_lt⟩ := fe51_sum5_prod128_eq a4 (b1 * 19#64) b0 a0 a3 (b2 * 19#64) a2 (b3 * 19#64) a1 (b4 * 19#64)
    s0_hi s0_lo hs0_hi hs0_lo ha4 (bv64_mul19_lt b1 hb1) hb0 (nat_lt_19_54 ha0) ha3 (bv64_mul19_lt b2 hb2) ha2 (bv64_mul19_lt b3 hb3) ha1 (bv64_mul19_lt b4 hb4)
  obtain ⟨hS1, hS1_lt⟩ := fe51_sum5_prod128_eq a4 (b2 * 19#64) a0 b1 a3 (b3 * 19#64) a2 (b4 * 19#64) a1 b0
    s1_hi s1_lo hs1_hi hs1_lo ha4 (bv64_mul19_lt b2 hb2) ha0 (nat_lt_19_54 hb1) ha3 (bv64_mul19_lt b3 hb3) ha2 (bv64_mul19_lt b4 hb4) ha1 (nat_lt_19_54 hb0)
  obtain ⟨hS2, hS2_lt⟩ := fe51_sum5_prod128_eq a4 (b3 * 19#64) a0 b2 a3 (b4 * 19#64) a2 b0 a1 b1
    s2_hi s2_lo hs2_hi hs2_lo ha4 (bv64_mul19_lt b3 hb3) ha0 (nat_lt_19_54 hb2) ha3 (bv64_mul19_lt b4 hb4) ha2 (nat_lt_19_54 hb0) ha1 (nat_lt_19_54 hb1)
  obtain ⟨hS3, hS3_lt⟩ := fe51_sum5_prod128_eq a4 (b4 * 19#64) a0 b3 a3 b0 a2 b1 a1 b2
    s3_hi s3_lo hs3_hi hs3_lo ha4 (bv64_mul19_lt b4 hb4) ha0 (nat_lt_19_54 hb3) ha3 (nat_lt_19_54 hb0) ha2 (nat_lt_19_54 hb1) ha1 (nat_lt_19_54 hb2)
  obtain ⟨hS4, hS4_lt⟩ := fe51_sum5_prod128_eq_unscaled a4 b0 a0 b4 a3 b1 a2 b2 a1 b3
    s4_hi s4_lo hs4_hi hs4_lo ha4 hb0 ha0 hb4 ha3 hb1 ha2 hb2 ha1 hb3
  have h0 := fe51_col0_extr_rel s0_hi s0_lo c0 _ hc0 hS0 (by omega)
  have h1 := fe51_col_carry_extr_rel s1_hi s1_lo c0 c1 _ hc1 hS1 (by omega)
  have h2 := fe51_col_carry_extr_rel s2_hi s2_lo c1 c2 _ hc2 hS2 (by omega)
  have h3 := fe51_col_carry_extr_rel s3_hi s3_lo c2 c3 _ hc3 hS3 (by omega)
  have h4 := fe51_col_carry_extr_rel s4_hi s4_lo c3 c4 _ hc4 hS4 (by omega)
  obtain ⟨d0, hd0, hr1⟩ := fe51_final_c4_rel (s0_lo &&& 2251799813685247#64) (s1_lo + c0 &&& 2251799813685247#64) c4 h0.2 h1.2 (by omega)
  obtain ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt, hr4_lt, hcarry⟩ :=
    fe51_mul_carry_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d0 hS0_lt hS1_lt hS2_lt hS3_lt hS4_lt h0 h1 h2 h3 h4 hd0 hr1
  rw [bv64_mul19_toNat_of_lt b1 hb1, bv64_mul19_toNat_of_lt b2 hb2, bv64_mul19_toNat_of_lt b3 hb3, bv64_mul19_toNat_of_lt b4 hb4] at hcarry
  obtain ⟨K, hpoly⟩ := fe51_mul_poly_nat a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat
  let r0 := (s0_lo &&& 2251799813685247#64) + c4 * 19#64 &&& 2251799813685247#64
  let r1 := (s1_lo + c0 &&& 2251799813685247#64) + (((s0_lo &&& 2251799813685247#64) + c4 * 19#64) >>> 51)
  let r2 := s2_lo + c1 &&& 2251799813685247#64; let r3 := s3_lo + c2 &&& 2251799813685247#64; let r4 := s4_lo + c3 &&& 2251799813685247#64
  have hmod : fe51ValOfBytes (packFe51Bytes r0 r1 r2 r3 r4) % p25519 = (fe51ValOfBytes $a_4) * (fe51ValOfBytes $a_rest) % p25519 := by
    rw [fe51ValOfBytes_packFe51Bytes]; unfold fe51ValOfBytes
    rw [ha0_eq, ha1_eq, ha2_eq, ha3_eq, ha4_eq, hb0_eq, hb1_eq, hb2_eq, hb3_eq, hb4_eq]; unfold fe51Val
    have htot : (r0.toNat + r1.toNat * 2 ^ 51 + r2.toNat * 2 ^ 102 + r3.toNat * 2 ^ 153 + r4.toNat * 2 ^ 204) + (c4.toNat + K) * p25519 =
        (a0.toNat + a1.toNat * 2 ^ 51 + a2.toNat * 2 ^ 102 + a3.toNat * 2 ^ 153 + a4.toNat * 2 ^ 204) *
        (b0.toNat + b1.toNat * 2 ^ 51 + b2.toNat * 2 ^ 102 + b3.toNat * 2 ^ 153 + b4.toNat * 2 ^ 204) := by
      rw [Nat.add_mul, ← Nat.add_assoc, hcarry, hpoly]
    rw [← htot, Nat.add_mul_mod_self_right]
  have hbound : fe51LimbsBounded (packFe51Bytes r0 r1 r2 r3 r4) (2 ^ 52) :=
    fe51LimbsBounded_packFe51Bytes r0 r1 r2 r3 r4 (2 ^ 52) hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt
  wp_conv_pre =>
    rw [← ha0_eq, ← ha1_eq, ← ha2_eq, ← ha3_eq, ← ha4_eq, ← $pA $a $a_4 h_len_a,
        ← hb0_eq, ← hb1_eq, ← hb2_eq, ← hb3_eq, ← hb4_eq, ← $pB $a_2 $a_rest h_len_b,
        ← pointsToBytes_packFe51Bytes $a_1 r0 r1 r2 r3 r4]
  wp_fold_stack
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
    (fe51_post_entails $a_1 (packFe51Bytes r0 r1 r2 r3 r4) (memRegion (($s0).sp - 224#64) 224) _ hbound hmod))) ?_
  apply SepWP.done; · wp_norm_lhs
  · wp_norm_lhs
  · refine ⟨fun hsat => by rw [stackFrame_of_sp_eq 224 (by wp_norm_lhs)]; exact hsat, by wp_norm_lhs, ?_⟩
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
            by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩))

private theorem bv64_extr63_toNat (hi lo : BitVec 64) (h : hi.toNat < 2 ^ 63) :
    (BitVec.setWidth 64 ((hi ++ lo) >>> 63)).toNat = hi.toNat * 2 + lo.toNat / 2 ^ 63 := by bv_bits
private theorem bv64_shl1_toNat (lo : BitVec 64) : (lo <<< 1).toNat + (lo.toNat / 2 ^ 63) * 2 ^ 64 = lo.toNat * 2 := by bv_bits

private theorem bv64_extr63_shl1_toNat (hi lo : BitVec 64) (X : Nat) (hX : hi.toNat * 2 ^ 64 + lo.toNat = X) (h : X < 2 ^ 116) :
    (BitVec.setWidth 64 ((hi ++ lo) >>> 63)).toNat * 2 ^ 64 + (lo <<< 1).toNat = X * 2 := by
  have h1 := bv64_extr63_toNat hi lo (by omega); have h2 := bv64_shl1_toNat lo
  rw [h1, ← hX, Nat.add_mul, Nat.add_assoc, Nat.add_comm (lo.toNat / 2 ^ 63 * 2 ^ 64), h2,
      Nat.mul_right_comm hi.toNat 2 (2 ^ 64), ← Nat.add_mul]

private abbrev sqColHi (u0 v0 u1 v1 u2 v2 : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (((BitVec.setWidth 64 ((BitVec.setWidth 128 u1 * BitVec.setWidth 128 v1) >>> 64) +
    BitVec.setWidth 64 ((BitVec.setWidth 128 u2 * BitVec.setWidth 128 v2) >>> 64) +
    if (AddWithCarry64 (u1 * v1) (u2 * v2) false).snd.c = true then 1#64 else 0#64) ++
    (u1 * v1 + u2 * v2)) >>> 63) +
  BitVec.setWidth 64 ((BitVec.setWidth 128 u0 * BitVec.setWidth 128 v0) >>> 64) +
  if (AddWithCarry64 (u0 * v0) ((u1 * v1 + u2 * v2) <<< 1) false).snd.c = true then 1#64 else 0#64

private theorem fe51_sq_col128_nat (u0 v0 u1 v1 u2 v2 : BitVec 64)
    (hp0 : u0.toNat * v0.toNat < 2 ^ 115) (hp1 : u1.toNat * v1.toNat < 2 ^ 115) (hp2 : u2.toNat * v2.toNat < 2 ^ 115) :
    (sqColHi u0 v0 u1 v1 u2 v2).toNat * 2 ^ 64 + (u0 * v0 + ((u1 * v1 + u2 * v2) <<< 1)).toNat =
      u0.toNat * v0.toNat + (u1.toNat * v1.toNat + u2.toNat * v2.toNat) * 2 := by
  have s1 := add128_adc_step _ _ _ _ _ _ (mul128_hi_lo_toNat u1 v1) (mul128_hi_lo_toNat u2 v2) (by omega)
  have s2 := bv64_extr63_shl1_toNat _ _ _ s1 (by omega); dsimp only [sqColHi]
  rw [BitVec.add_comm (BitVec.setWidth 64 _) (BitVec.setWidth 64 ((BitVec.setWidth 128 u0 * _) >>> 64))]
  exact add128_adc_step _ _ _ _ _ _ (mul128_hi_lo_toNat u0 v0) s2 (by omega)

private theorem nat_mul_lt_19_108_symm {x y : Nat} (hx : x < 19 * 2 ^ 54) (hy : y < 2 ^ 54) :
    x * y < 19 * 2 ^ 108 := by rw [Nat.mul_comm]; exact nat_mul_lt_19_108 hy hx

private theorem fe51_sq_col128_eq (u0 v0 u1 v1 u2 v2 s_hi s_lo : BitVec 64)
    (hs_hi : sqColHi u0 v0 u1 v1 u2 v2 = s_hi) (hs_lo : u0 * v0 + ((u1 * v1 + u2 * v2) <<< 1) = s_lo)
    (hp0 : u0.toNat * v0.toNat < 19 * 2 ^ 108) (hp1 : u1.toNat * v1.toNat < 19 * 2 ^ 108) (hp2 : u2.toNat * v2.toNat < 19 * 2 ^ 108) :
    s_hi.toNat * 2 ^ 64 + s_lo.toNat = u0.toNat * v0.toNat + (u1.toNat * v1.toNat + u2.toNat * v2.toNat) * 2 ∧
    u0.toNat * v0.toNat + (u1.toNat * v1.toNat + u2.toNat * v2.toNat) * 2 < 95 * 2 ^ 108 := by
  refine ⟨?_, by omega⟩; rw [← hs_hi, ← hs_lo]; exact fe51_sq_col128_nat u0 v0 u1 v1 u2 v2 (by omega) (by omega) (by omega)

private theorem fe51_sq_col128_eq_unscaled (u0 v0 u1 v1 u2 v2 s_hi s_lo : BitVec 64)
    (hs_hi : sqColHi u0 v0 u1 v1 u2 v2 = s_hi) (hs_lo : u0 * v0 + ((u1 * v1 + u2 * v2) <<< 1) = s_lo)
    (hp0 : u0.toNat * v0.toNat < 2 ^ 108) (hp1 : u1.toNat * v1.toNat < 2 ^ 108) (hp2 : u2.toNat * v2.toNat < 2 ^ 108) :
    s_hi.toNat * 2 ^ 64 + s_lo.toNat = u0.toNat * v0.toNat + (u1.toNat * v1.toNat + u2.toNat * v2.toNat) * 2 ∧
    u0.toNat * v0.toNat + (u1.toNat * v1.toNat + u2.toNat * v2.toNat) * 2 < 5 * 2 ^ 108 := by
  refine ⟨?_, by omega⟩; rw [← hs_hi, ← hs_lo]; exact fe51_sq_col128_nat u0 v0 u1 v1 u2 v2 (by omega) (by omega) (by omega)

private theorem fe51_sq_poly_nat (A0 A1 A2 A3 A4 : Nat) :
    ∃ K : Nat,
      ((A0 * A0 + (A1 * (A4 * 19) + A2 * (A3 * 19)) * 2) +
       ((A3 * 19) * A3 + (A0 * A1 + A2 * (A4 * 19)) * 2) * 2 ^ 51 +
       (A1 * A1 + (A0 * A2 + (A3 * 19) * A4) * 2) * 2 ^ 102 +
       ((A4 * 19) * A4 + (A0 * A3 + A1 * A2) * 2) * 2 ^ 153 +
       (A2 * A2 + (A0 * A4 + A1 * A3) * 2) * 2 ^ 204) + K * p25519 =
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) *
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) := by
  obtain ⟨K, h⟩ := fe51_mul_poly_nat A0 A1 A2 A3 A4 A0 A1 A2 A3 A4; refine ⟨K, ?_⟩; rw [← h]
  have c0 : A4 * (A1 * 19) = A1 * (A4 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A4 A1, Nat.mul_assoc]
  have c1 : A3 * (A2 * 19) = A2 * (A3 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A3 A2, Nat.mul_assoc]
  have c2 : A4 * (A2 * 19) = A2 * (A4 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A4 A2, Nat.mul_assoc]
  have c3 : (A3 * 19) * A3 = A3 * (A3 * 19) := Nat.mul_comm _ _
  have c4 : A1 * A0 = A0 * A1 := Nat.mul_comm _ _; have c5 : A4 * (A3 * 19) = (A3 * 19) * A4 := Nat.mul_comm _ _
  have c6 : A3 * (A4 * 19) = (A3 * 19) * A4 := by rw [← Nat.mul_assoc, Nat.mul_right_comm A3 A4 19]
  have c7 : A2 * A0 = A0 * A2 := Nat.mul_comm _ _; have c8 : (A4 * 19) * A4 = A4 * (A4 * 19) := Nat.mul_comm _ _
  have c9 : A3 * A0 = A0 * A3 := Nat.mul_comm _ _; have c10 : A2 * A1 = A1 * A2 := Nat.mul_comm _ _
  have c11 : A4 * A0 = A0 * A4 := Nat.mul_comm _ _; have c12 : A3 * A1 = A1 * A3 := Nat.mul_comm _ _
  omega

private theorem fe51_pow2k_iter [X25519CliPlacement] (b : BitVec 64)
    (_hb : X25519Base x25519CliPl02 b) (_hbase : x25519CliPl02.base = b)
    (target_pc : BitVec 64) (s : State) (P : SepProp) (post : State → SepProp → Prop) (oom : State → SepProp)
    (l0 l1 l2 l3 l4 : BitVec 64) (cnt : BitVec 32)
    (hpc : s.pc = b + 40#64) (hrun : s.status = ExecStatus.Running)
    (hl0 : s.readReg64 (Reg.gpr 13#5) = l0) (hl1 : s.readReg64 (Reg.gpr 11#5) = l1)
    (hl2 : s.readReg64 (Reg.gpr 10#5) = l2) (hl3 : s.readReg64 (Reg.gpr 12#5) = l3)
    (hl4 : s.readReg64 (Reg.gpr 14#5) = l4) (hx9 : s.readReg64 (Reg.gpr 9#5) = 19#64)
    (hcnt : BitVec.truncate 32 (s.readReg64 (Reg.gpr 1#5)) = cnt)
    (hl0_lt : l0.toNat < 2 ^ 54) (hl1_lt : l1.toNat < 2 ^ 54) (hl2_lt : l2.toNat < 2 ^ 54) (hl3_lt : l3.toNat < 2 ^ 54) (hl4_lt : l4.toNat < 2 ^ 54)
    (hnext : ∀ (s' : State) (r0 r1 r2 r3 r4 : BitVec 64),
      s'.pc = (if (cnt != 1#32) = true then b + 40#64 else b + 360#64) →
      s'.status = ExecStatus.Running → s'.sp = s.sp →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) → calleeSavedVRegs s' = calleeSavedVRegs s →
      s'.readReg64 (Reg.gpr 9#5) = 19#64 → s'.readReg64 (Reg.gpr 1#5) = BitVec.setWidth 64 (cnt - 1#32) →
      s'.readReg64 (Reg.gpr 13#5) = r0 → s'.readReg64 (Reg.gpr 11#5) = r1 →
      s'.readReg64 (Reg.gpr 10#5) = r2 → s'.readReg64 (Reg.gpr 12#5) = r3 → s'.readReg64 (Reg.gpr 14#5) = r4 →
      r0.toNat < 2 ^ 52 → r1.toNat < 2 ^ 52 → r2.toNat < 2 ^ 52 → r3.toNat < 2 ^ 52 → r4.toNat < 2 ^ 52 →
      fe51Val r0 r1 r2 r3 r4 % p25519 = (fe51Val l0 l1 l2 l3 l4 * fe51Val l0 l1 l2 l3 l4) % p25519 →
      SepWP (x25519CliPC02.rebase b (fun _ => none)) target_pc s' P post oom) :
    SepWP (x25519CliPC02.rebase b (fun _ => none)) target_pc s P post oom := by
  wp_sym_steps 16; wp_gen_reg (Reg.gpr 17#5) s0_hi hs0_hi; wp_gen_reg (Reg.gpr 18#5) s0_lo hs0_lo
  wp_sym_steps 1; wp_gen_reg (Reg.gpr 17#5) c0 hc0
  wp_sym_steps 10; wp_gen_reg (Reg.gpr 2#5) s1_hi hs1_hi; wp_gen_reg (Reg.gpr 0#5) s1_lo hs1_lo
  wp_sym_steps 19; wp_gen_reg (Reg.gpr 12#5) s2_hi hs2_hi; wp_gen_reg (Reg.gpr 15#5) s2_lo hs2_lo
  wp_sym_steps 7; wp_gen_reg (Reg.gpr 16#5) s3_hi hs3_hi; wp_gen_reg (Reg.gpr 13#5) s3_lo hs3_lo
  wp_sym_steps 5; wp_gen_reg (Reg.gpr 10#5) s4_hi hs4_hi; wp_gen_reg (Reg.gpr 11#5) s4_lo hs4_lo
  wp_sym_steps 3; wp_gen_reg (Reg.gpr 17#5) c1 hc1; wp_sym_steps 3; wp_gen_reg (Reg.gpr 12#5) c2 hc2
  wp_sym_steps 3; wp_gen_reg (Reg.gpr 13#5) c3 hc3; wp_sym_steps 6; wp_gen_reg (Reg.gpr 10#5) c4 hc4; wp_sym_steps 7
  obtain ⟨hS0, hS0_lt⟩ := fe51_sq_col128_eq l0 l0 l1 (l4 * 19#64) l2 (l3 * 19#64) s0_hi s0_lo hs0_hi hs0_lo
    (nat_mul_lt_19_108 hl0_lt (nat_lt_19_54 hl0_lt)) (nat_mul_lt_19_108 hl1_lt (bv64_mul19_lt l4 hl4_lt)) (nat_mul_lt_19_108 hl2_lt (bv64_mul19_lt l3 hl3_lt))
  obtain ⟨hS1, hS1_lt⟩ := fe51_sq_col128_eq (l3 * 19#64) l3 l0 l1 l2 (l4 * 19#64) s1_hi s1_lo hs1_hi hs1_lo
    (nat_mul_lt_19_108_symm (bv64_mul19_lt l3 hl3_lt) hl3_lt) (nat_mul_lt_19_108 hl0_lt (nat_lt_19_54 hl1_lt)) (nat_mul_lt_19_108 hl2_lt (bv64_mul19_lt l4 hl4_lt))
  obtain ⟨hS2, hS2_lt⟩ := fe51_sq_col128_eq l1 l1 l0 l2 (l3 * 19#64) l4 s2_hi s2_lo hs2_hi hs2_lo
    (nat_mul_lt_19_108 hl1_lt (nat_lt_19_54 hl1_lt)) (nat_mul_lt_19_108 hl0_lt (nat_lt_19_54 hl2_lt)) (nat_mul_lt_19_108_symm (bv64_mul19_lt l3 hl3_lt) hl4_lt)
  obtain ⟨hS3, hS3_lt⟩ := fe51_sq_col128_eq (l4 * 19#64) l4 l0 l3 l1 l2 s3_hi s3_lo hs3_hi hs3_lo
    (nat_mul_lt_19_108_symm (bv64_mul19_lt l4 hl4_lt) hl4_lt) (nat_mul_lt_19_108 hl0_lt (nat_lt_19_54 hl3_lt)) (nat_mul_lt_19_108 hl1_lt (nat_lt_19_54 hl2_lt))
  obtain ⟨hS4, hS4_lt⟩ := fe51_sq_col128_eq_unscaled l2 l2 l0 l4 l1 l3 s4_hi s4_lo hs4_hi hs4_lo
    (nat_mul_lt_108 hl2_lt hl2_lt) (nat_mul_lt_108 hl0_lt hl4_lt) (nat_mul_lt_108 hl1_lt hl3_lt)
  have h0 := fe51_col0_extr_rel s0_hi s0_lo c0 _ hc0 hS0 (by omega)
  have h1 := fe51_col_carry_extr_rel s1_hi s1_lo c0 c1 _ hc1 hS1 (by omega)
  have h2 := fe51_col_carry_extr_rel s2_hi s2_lo c1 c2 _ hc2 hS2 (by omega)
  have h3 := fe51_col_carry_extr_rel s3_hi s3_lo c2 c3 _ hc3 hS3 (by omega)
  have h4 := fe51_col_carry_extr_rel s4_hi s4_lo c3 c4 _ hc4 hS4 (by omega)
  obtain ⟨d0, hd0, hr1⟩ := fe51_final_c4_rel
    (s0_lo &&& 2251799813685247#64) (s1_lo + c0 &&& 2251799813685247#64) c4 h0.2 h1.2 (by omega)
  obtain ⟨hr0_lt, hr1_lt, hr2_lt, hr3_lt, hr4_lt, hcarry⟩ :=
    fe51_mul_carry_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d0 hS0_lt hS1_lt hS2_lt hS3_lt hS4_lt h0 h1 h2 h3 h4 hd0 hr1
  rw [bv64_mul19_toNat_of_lt l3 hl3_lt, bv64_mul19_toNat_of_lt l4 hl4_lt] at hcarry
  obtain ⟨K, hpoly⟩ := fe51_sq_poly_nat l0.toNat l1.toNat l2.toNat l3.toNat l4.toNat
  let r0 := (s0_lo &&& 2251799813685247#64) + c4 * 19#64 &&& 2251799813685247#64
  let r1 := (s1_lo + c0 &&& 2251799813685247#64) + (((s0_lo &&& 2251799813685247#64) + c4 * 19#64) >>> 51)
  let r2 := s2_lo + c1 &&& 2251799813685247#64; let r3 := s3_lo + c2 &&& 2251799813685247#64; let r4 := s4_lo + c3 &&& 2251799813685247#64
  have hmod : fe51Val r0 r1 r2 r3 r4 % p25519 = (fe51Val l0 l1 l2 l3 l4 * fe51Val l0 l1 l2 l3 l4) % p25519 := by
    unfold fe51Val
    have htot : (r0.toNat + r1.toNat * 2 ^ 51 + r2.toNat * 2 ^ 102 + r3.toNat * 2 ^ 153 + r4.toNat * 2 ^ 204) + (c4.toNat + K) * p25519 =
        (l0.toNat + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204) *
        (l0.toNat + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204) := by
      rw [Nat.add_mul, ← Nat.add_assoc, hcarry, hpoly]
    rw [← htot, Nat.add_mul_mod_self_right]
  refine hnext _ r0 r1 r2 r3 r4 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod

private theorem bv32_ne_one_of_toNat_eq1 (cnt : BitVec 32) (h : cnt.toNat = 1) : (cnt != 1#32) = false := by bv_bits
private theorem bv32_ne_one_of_toNat_ge2 (cnt : BitVec 32) (h : cnt.toNat ≥ 2) : (cnt != 1#32) = true := by bv_bits
private theorem bv32_truncate_zext64 (x : BitVec 32) : BitVec.truncate 32 (BitVec.setWidth 64 x) = x := by bv_bits
private theorem bv32_sub1_toNat (cnt : BitVec 32) (m : Nat) (h : cnt.toNat = m + 2) : (cnt - 1#32).toNat = m + 1 := by
  have hle : (1#32 : BitVec 32) ≤ cnt := by bv_bits
  rw [BitVec.toNat_sub_of_le hle]; change cnt.toNat - 1 = m + 1; omega

private theorem sq_pow_two_pow_mod (A n M : Nat) (hM : M % p25519 = (A * A) % p25519) :
    M ^ (2 ^ n) % p25519 = A ^ (2 ^ (n + 1)) % p25519 := by
  have h2 : A * A = A ^ 2 := by rw [Nat.pow_two]
  have hp : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [Nat.pow_mod M, hM, ← Nat.pow_mod (A * A), h2, ← Nat.pow_mul, hp]

private theorem fe51_pow2k_loop [X25519CliPlacement] (b : BitVec 64)
    (hb : X25519Base x25519CliPl02 b) (hbase : x25519CliPl02.base = b)
    {target_pc : BitVec 64} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp} (m : Nat) :
    ∀ {s : State} (l0 l1 l2 l3 l4 : BitVec 64) (cnt : BitVec 32),
      s.pc = b + 40#64 → s.status = ExecStatus.Running →
      s.readReg64 (Reg.gpr 13#5) = l0 → s.readReg64 (Reg.gpr 11#5) = l1 →
      s.readReg64 (Reg.gpr 10#5) = l2 → s.readReg64 (Reg.gpr 12#5) = l3 →
      s.readReg64 (Reg.gpr 14#5) = l4 → s.readReg64 (Reg.gpr 9#5) = 19#64 →
      BitVec.truncate 32 (s.readReg64 (Reg.gpr 1#5)) = cnt → cnt.toNat = m + 1 →
      l0.toNat < 2 ^ 54 → l1.toNat < 2 ^ 54 → l2.toNat < 2 ^ 54 → l3.toNat < 2 ^ 54 → l4.toNat < 2 ^ 54 →
      (∀ (sf : State) (r0 r1 r2 r3 r4 : BitVec 64),
        sf.pc = b + 360#64 → sf.status = ExecStatus.Running → sf.sp = s.sp →
        sf.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
        sf.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) → calleeSavedVRegs sf = calleeSavedVRegs s →
        sf.readReg64 (Reg.gpr 13#5) = r0 → sf.readReg64 (Reg.gpr 11#5) = r1 →
        sf.readReg64 (Reg.gpr 10#5) = r2 → sf.readReg64 (Reg.gpr 12#5) = r3 → sf.readReg64 (Reg.gpr 14#5) = r4 →
        r0.toNat < 2 ^ 52 → r1.toNat < 2 ^ 52 → r2.toNat < 2 ^ 52 → r3.toNat < 2 ^ 52 → r4.toNat < 2 ^ 52 →
        fe51Val r0 r1 r2 r3 r4 % p25519 = (fe51Val l0 l1 l2 l3 l4) ^ (2 ^ (m + 1)) % p25519 →
        SepWP (x25519CliPC02.rebase b (fun _ => none)) target_pc sf P post oom) →
      SepWP (x25519CliPC02.rebase b (fun _ => none)) target_pc s P post oom := by
  induction m with
  | zero =>
    intro s l0 l1 l2 l3 l4 cnt hpc hrun hl0 hl1 hl2 hl3 hl4 hx9 hcnt hm hl0_lt hl1_lt hl2_lt hl3_lt hl4_lt hnext
    refine fe51_pow2k_iter b hb hbase target_pc s P post oom l0 l1 l2 l3 l4 cnt
      hpc hrun hl0 hl1 hl2 hl3 hl4 hx9 hcnt hl0_lt hl1_lt hl2_lt hl3_lt hl4_lt ?_
    intro s' r0 r1 r2 r3 r4 hpc' hrun' hsp' hx8' hx29' hv' _ _ hr0 hr1 hr2 hr3 hr4 hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod
    rw [bv32_ne_one_of_toNat_eq1 cnt hm] at hpc'; simp only [Bool.false_eq_true, ↓reduceIte] at hpc'
    rw [← Nat.pow_two, ← Nat.pow_one 2] at hmod
    exact hnext s' r0 r1 r2 r3 r4 hpc' hrun' hsp' hx8' hx29' hv' hr0 hr1 hr2 hr3 hr4 hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod
  | succ m' ih =>
    intro s l0 l1 l2 l3 l4 cnt hpc hrun hl0 hl1 hl2 hl3 hl4 hx9 hcnt hm hl0_lt hl1_lt hl2_lt hl3_lt hl4_lt hnext
    refine fe51_pow2k_iter b hb hbase target_pc s P post oom l0 l1 l2 l3 l4 cnt
      hpc hrun hl0 hl1 hl2 hl3 hl4 hx9 hcnt hl0_lt hl1_lt hl2_lt hl3_lt hl4_lt ?_
    intro s' m0 m1 m2 m3 m4 hpc' hrun' hsp' hx8' hx29' hv' hx9' hw1' hm0 hm1 hm2 hm3 hm4 hm0_lt hm1_lt hm2_lt hm3_lt hm4_lt hmod1
    rw [bv32_ne_one_of_toNat_ge2 cnt (by omega)] at hpc'; simp only [↓reduceIte] at hpc'
    have hcnt' : BitVec.truncate 32 (s'.readReg64 (Reg.gpr 1#5)) = cnt - 1#32 := by rw [hw1', bv32_truncate_zext64]
    refine ih m0 m1 m2 m3 m4 (cnt - 1#32) hpc' hrun' hm0 hm1 hm2 hm3 hm4 hx9' hcnt'
      (bv32_sub1_toNat cnt m' hm) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    intro sf r0 r1 r2 r3 r4 hpc_f hrun_f hsp_f hx8_f hx29_f hv_f hr0 hr1 hr2 hr3 hr4 hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod2
    rw [hsp'] at hsp_f; rw [hx8'] at hx8_f; rw [hx29'] at hx29_f; rw [hv'] at hv_f
    rw [sq_pow_two_pow_mod _ (m' + 1) _ hmod1] at hmod2
    exact hnext sf r0 r1 r2 r3 r4 hpc_f hrun_f hsp_f hx8_f hx29_f hv_f hr0 hr1 hr2 hr3 hr4 hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod2


public section

theorem fe51_mul_ok : Fe51MulOk := by
  intro _
  apply x25519Leaf_ok x25519CliPC01 x25519CliPl01
  intro b hb hbase
  unfold fe51MulSpec
  wp_init
  fe51_mul_body pointsToBytes40_eq_cells pointsToBytes40_eq_cells s0 a a_1 a_2 a_3 a_4 a_rest h h_4 h_5

theorem fe51_mul_ro_right_ok : Fe51MulRoRightOk := by
  intro _
  apply x25519Leaf_ok x25519CliPC01 x25519CliPl01
  intro b hb hbase
  unfold fe51MulRoRightSpec
  wp_init
  fe51_mul_body pointsToBytes40_eq_cells pointsToBytesRO40_eq_cells s0 a a_1 a_2 a_3 a_4 a_rest h h_4 h_5


theorem fe51_mul_ro_left_ok : Fe51MulRoLeftOk := by
  intro _
  apply x25519Leaf_ok x25519CliPC01 x25519CliPl01
  intro b hb hbase
  unfold fe51MulRoLeftSpec
  wp_init
  fe51_mul_body pointsToBytesRO40_eq_cells pointsToBytes40_eq_cells s0 a a_1 a_2 a_3 a_4 a_rest h h_4 h_5

abbrev rust_spec fe51Pow2kNatSpec (out : sret) (a : ptr) (k : u32)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ 0 < k.toNat
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         96
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs) ^ (2 ^ k.toNat) % p25519⌝

abbrev Fe51Pow2kNatOk : Prop :=
  X25519BlockConstOk 2 fe51Pow2kNatSpec

private theorem fe51_pow2k_nat_leaf [X25519CliPlacement] (b : BitVec 64)
    (hb : X25519Base x25519CliPl02 b) (hbase : x25519CliPl02.base = b) :
    subroutine_ok (x25519CliPC02.rebase b (fun _ => none)) b
      (ToBaseSpec.toSpec fe51Pow2kNatSpec b) := by
  unfold fe51Pow2kNatSpec
  wp_init
  obtain ⟨h_len_a, hl0, hl1, hl2, hl3, hl4⟩ := h_5
  wp_conv_pre => rw [pointsToBytes40_eq_cells a a_rest_1 h_len_a, pointsToBytes40_eq_cells a_1 a_3 h_4]
  generalize hl0_eq : ByteSlice.readLE a_rest_1 0 8 = l0 at *; generalize hl1_eq : ByteSlice.readLE a_rest_1 8 8 = l1 at *
  generalize hl2_eq : ByteSlice.readLE a_rest_1 16 8 = l2 at *; generalize hl3_eq : ByteSlice.readLE a_rest_1 24 8 = l3 at *
  generalize hl4_eq : ByteSlice.readLE a_rest_1 32 8 = l4 at *; wp_sym_steps 10
  refine fe51_pow2k_loop b hb hbase (a_2.toNat - 1) l0 l1 l2 l3 l4 a_2
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by omega) hl0 hl1 hl2 hl3 hl4 ?_
  intro sf r0 r1 r2 r3 r4 hpc_f hrun_f hsp_f hx8_f hx29_f hv_f hr0 hr1 hr2 hr3 hr4 hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt hmod_f
  have hsp_f' : sf.sp = s0.sp - 96#64 := by rw [hsp_f]; wp_norm_lhs
  have hx8_f' : sf.readReg64 (Reg.gpr 8#5) = a_1 := by rw [hx8_f]; wp_norm_lhs
  have hx29_f' : sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) := by rw [hx29_f]; wp_norm_lhs
  have hv_f' : calleeSavedVRegs sf = calleeSavedVRegs s0 := by rw [hv_f]; wp_norm_lhs
  clear hsp_f hx8_f hx29_f hv_f; wp_sym_steps
  have hk_eq : a_2.toNat - 1 + 1 = a_2.toNat := by omega
  rw [hk_eq] at hmod_f
  have hmod : fe51ValOfBytes (packFe51Bytes r0 r1 r2 r3 r4) % p25519 = (fe51ValOfBytes a_rest_1) ^ (2 ^ a_2.toNat) % p25519 := by
    rw [fe51ValOfBytes_packFe51Bytes, fe51ValOfBytes, hl0_eq, hl1_eq, hl2_eq, hl3_eq, hl4_eq, hmod_f]
  have hbound : fe51LimbsBounded (packFe51Bytes r0 r1 r2 r3 r4) (2 ^ 52) :=
    fe51LimbsBounded_packFe51Bytes r0 r1 r2 r3 r4 (2 ^ 52) hr0_lt hr1_lt hr2_lt hr3_lt hr4_lt
  wp_conv_pre =>
    rw [← hl0_eq, ← hl1_eq, ← hl2_eq, ← hl3_eq, ← hl4_eq,
        ← pointsToBytes40_eq_cells a a_rest_1 h_len_a, ← pointsToBytes_packFe51Bytes a_1 r0 r1 r2 r3 r4]
  wp_fold_stack
  refine SepWP.weaken_pre (sepConj_mono_right
    (fe51_post_entails a_1 (packFe51Bytes r0 r1 r2 r3 r4) (memRegion (s0.sp - 96#64) 96) _ hbound hmod)) ?_
  apply SepWP.done; · wp_norm_lhs
  · wp_norm_lhs
  · refine ⟨fun hsat => by rw [stackFrame_of_sp_eq 96 (by wp_norm_lhs)]; exact hsat, by wp_norm_lhs, ?_⟩
    rw [CalleeSavedPreserved.iff_regs]
    refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
            by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩

theorem fe51_pow2k_nat_ok : Fe51Pow2kNatOk := by
  intro _
  apply x25519Leaf_ok x25519CliPC02 x25519CliPl02
  intro b hb hbase
  exact fe51_pow2k_nat_leaf b hb hbase

theorem fe51_pow2k_ok : Fe51Pow2kOk := by
  intro _
  apply x25519Leaf_ok x25519CliPC02 x25519CliPl02
  intro b hb hbase
  refine subroutine_ok_refine (fe51_pow2k_nat_leaf b hb hbase) (fun x R s0 hpre => ?_)
    (by intro _ _ _ _ hp; simp at hp)
    (by intro _ _ _ _ _ he; simp at he)
    (by intro _ _ _ _ _ ho; simp at ho)
  have hent : (ToBaseSpec.toSpec fe51Pow2kSpec b).pre x s0 ⊢
      ⌜x.2.2.1.toNat < 256⌝ ∗ (ToBaseSpec.toSpec fe51Pow2kNatSpec b).pre x s0 := by
    dsimp only [ToBaseSpec.toSpec, fe51Pow2kSpec, fe51Pow2kNatSpec]; apply Entails.pure_left
    rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact Entails.pure_right h7 (Entails.pure_right ⟨h1, h2, h3, h4, h5, h6⟩ (Entails.refl _))
  have hpre' := Satisfies.of_entails hpre (sepConj_mono_left hent)
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  refine ⟨x, hpre'.2, fun sf hpost => Satisfies.of_entails hpost (sepConj_mono_left ?_)⟩
  have hpow : ∀ v : Nat, fpPow (v % p25519) (2 ^ x.2.2.1.toNat) = v ^ (2 ^ x.2.2.1.toNat) % p25519 :=
    fun v => fpPow_mod_eq_pow_mod v _ (Nat.pow_lt_pow_right (by decide) hpre'.1)
  dsimp only [ToBaseSpec.toSpec, fe51Pow2kSpec, fe51Pow2kNatSpec]; simp only [hpow]; exact Entails.refl _

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51
