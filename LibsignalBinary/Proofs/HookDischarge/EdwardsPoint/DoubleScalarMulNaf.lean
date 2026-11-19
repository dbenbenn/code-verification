/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
meta import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase
meta import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# NAF Recoding Helpers for `vartime_double_scalar_mul_basepoint`

Limb bounds for `oddMultiplesBasepointBytes`, width-5 and width-8 NAF recoding loops,
top-down NAF index scan (`find_max_naf_loop_ok`), and stack/read-only slice framing helpers
for `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` (`B17`) in `dalekCliMultiLib`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMulNaf

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul EdExtPoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase clearOldCodeLoadedHyps)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  oddMultiplesBasepointBytes fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  readLE_cons8 oddMultiplesBasepointBytes_length)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (fe51LimbsBounded)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  readLE_slice_eq fe51LimbsBoundedAt fe51Point4Bounded edExtOfBytes edAsExtended
  naf5BitBuf naf5Digit naf5NextCarry naf5Loop naf5ByteValid
  naf8BitBuf naf8NextCarry naf8Loop findMaxNafIdx)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add edAsExtended_of_append4
  completed_split4_props_54)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base

public section

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 17 dalekCliMultiLib DalekCliPlacement 316

theorem dalekCliPl17_eq [DalekCliPlacement] :
    dalekCliPl17 = dalekCliMultiLib.blockPlacement dalekCliMpl 17 := by
  unfold dalekCliPl17; rfl

theorem dalekCliPC17_eq [DalekCliPlacement] :
    dalekCliPC17 = dalekCliLib17.program dalekCliPl17 := by
  unfold dalekCliPC17; rfl

theorem dalekCliPC17_block_eq [DalekCliPlacement] :
    dalekCliPC17 = (dalekCliMultiLib.blockLib 17).program dalekCliPl17 := by
  unfold dalekCliPC17 dalekCliLib17; rfl

@[simp, arm64_norm, wp_norm]
theorem dalekCliPl17_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl17.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := by
  unfold dalekCliPl17; rfl

open Lean Elab Tactic in
/-- Close an active `wp_cut_codeLoaded` cut at the current symbolic state, replacing prior
    `CodeLoaded` hypotheses with a single fresh `hcl_cut` on the post-write memory. -/
local elab "close_cut_codeLoaded" : tactic => do
  evalTactic (← `(tactic| (
    apply SepWP.done
    · first | wp_norm_lhs | wp_norm_goal | rfl
    · first | assumption | wp_norm_lhs)))
  clearOldCodeLoadedHyps
  let hclId := mkIdent (← mkFreshUserName `hcl_cut)
  evalTactic (← `(tactic| intro $hclId:ident))

/-! ## 1. `oddMultiplesBasepointBytes` Limb Bounds (`64 × 120 = 7680` Bytes) -/

/-- Linear checker that `rem` consecutive 8-byte little-endian words of `bs` are `< bound`. -/
@[expose] def checkWordsBounded64 (bs : List (BitVec 8)) (bound : Nat) : Nat → Bool
  | 0 => true
  | rem + 1 =>
    match bs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      decide ((pack64 b0 b1 b2 b3 b4 b5 b6 b7).toNat < bound) &&
        checkWordsBounded64 rest bound rem
    | _ => false

theorem of_checkWordsBounded64 {bs : List (BitVec 8)} {bound rem k : Nat}
    (h : checkWordsBounded64 bs bound rem = true) (hk : k < rem) :
    (ByteSlice.readLE bs (8 * k) 8).toNat < bound := by
  induction rem generalizing bs k with
  | zero => omega
  | succ rem ih =>
    unfold checkWordsBounded64 at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try contradiction
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, ← ByteSlice.pack64_eq_readLE_8]; exact h.1
    · rw [show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]; exact ih h.2 (by omega)

theorem checkWordsBounded64_oddMultiplesBasepoint :
    checkWordsBounded64 oddMultiplesBasepointBytes (2 ^ 52) 960 = true := by decide +kernel

theorem oddMultiplesBasepointBytes_slice_bounded {i : Nat} (hi : i < 64) :
    let sl := ProofLib.ByteSlice.slice oddMultiplesBasepointBytes (120 * i) 120
    sl.length = 120 ∧
    fe51LimbsBoundedAt sl 0 (2 ^ 54) ∧
    fe51LimbsBoundedAt sl 40 (2 ^ 54) ∧
    fe51LimbsBoundedAt sl 80 (2 ^ 54) := by
  intro sl
  have hlen : sl.length = 120 := by
    change ((oddMultiplesBasepointBytes.drop (120 * i)).take 120).length = 120
    simp only [List.length_take, List.length_drop, oddMultiplesBasepointBytes_length]; omega
  have hlimb (j : Nat) (hj : j < 15) :
      (ByteSlice.readLE sl (8 * j) 8).toNat < 2 ^ 54 := by
    rw [readLE_slice_eq oddMultiplesBasepointBytes (120 * i) 120 (8 * j) (by rw [decide_eq_true_eq]; omega),
        show 120 * i + 8 * j = 8 * (15 * i + j) by omega]
    have h52 := of_checkWordsBounded64 checkWordsBounded64_oddMultiplesBasepoint (k := 15 * i + j) (by omega)
    omega
  refine ⟨hlen, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hlimb 0 (by decide)
  · simpa using hlimb 1 (by decide)
  · simpa using hlimb 2 (by decide)
  · simpa using hlimb 3 (by decide)
  · simpa using hlimb 4 (by decide)
  · simpa using hlimb 5 (by decide)
  · simpa using hlimb 6 (by decide)
  · simpa using hlimb 7 (by decide)
  · simpa using hlimb 8 (by decide)
  · simpa using hlimb 9 (by decide)
  · simpa using hlimb 10 (by decide)
  · simpa using hlimb 11 (by decide)
  · simpa using hlimb 12 (by decide)
  · simpa using hlimb 13 (by decide)
  · simpa using hlimb 14 (by decide)

/-! ## 2. Non-Adjacent Form (NAF) Width-5 & Width-8 Recoding & Top-Down Scan -/

private theorem lsr6_shl3_ofNat {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos >>> 6) <<< 3 = BitVec.ofNat 64 (8 * (pos / 64)) :=
  (by decide +kernel : ∀ k : Fin 256,
    (BitVec.ofNat 64 k.val >>> 6) <<< 3 = BitVec.ofNat 64 (8 * (k.val / 64))) ⟨pos, hpos⟩

private theorem ult_59_and63 {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos &&& 63#64).ult 59#64 = !decide (59 ≤ pos % 64) :=
  (by decide +kernel : ∀ k : Fin 256,
    (BitVec.ofNat 64 k.val &&& 63#64).ult 59#64 = !decide (59 ≤ k.val % 64)) ⟨pos, hpos⟩

private theorem ult_56_and63 {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos &&& 63#64).ult 56#64 = !decide (56 ≤ pos % 64) :=
  (by decide +kernel : ∀ k : Fin 256,
    (BitVec.ofNat 64 k.val &&& 63#64).ult 56#64 = !decide (56 ≤ k.val % 64)) ⟨pos, hpos⟩

private theorem ofNat_add_5 {pos : Nat} (hpos : pos < 256) :
    BitVec.ofNat 64 pos + 5#64 = BitVec.ofNat 64 (pos + 5) :=
  (by decide +kernel : ∀ k : Fin 256, BitVec.ofNat 64 k.val + 5#64 = BitVec.ofNat 64 (k.val + 5)) ⟨pos, hpos⟩

private theorem ofNat_add_8 {pos : Nat} (hpos : pos < 256) :
    BitVec.ofNat 64 pos + 8#64 = BitVec.ofNat 64 (pos + 8) :=
  (by decide +kernel : ∀ k : Fin 256, BitVec.ofNat 64 k.val + 8#64 = BitVec.ofNat 64 (k.val + 8)) ⟨pos, hpos⟩

private theorem ofNat_add_1 {pos : Nat} (hpos : pos < 256) :
    BitVec.ofNat 64 pos + 1#64 = BitVec.ofNat 64 (pos + 1) :=
  (by decide +kernel : ∀ k : Fin 256, BitVec.ofNat 64 k.val + 1#64 = BitVec.ofNat 64 (k.val + 1)) ⟨pos, hpos⟩

private theorem neg_ofNat_sub_1 {pos : Nat} (hpos : pos < 256) :
    -BitVec.ofNat 64 pos - 1#64 = -BitVec.ofNat 64 (pos + 1) :=
  (by decide +kernel : ∀ k : Fin 256,
    -BitVec.ofNat 64 k.val - 1#64 = -BitVec.ofNat 64 (k.val + 1)) ⟨pos, hpos⟩

private theorem ult_251_ofNat {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos).ult 251#64 = decide (pos + 5 < 256) :=
  (by decide +kernel : ∀ k : Fin 256, (BitVec.ofNat 64 k.val).ult 251#64 = decide (k.val + 5 < 256)) ⟨pos, hpos⟩

private theorem ult_248_ofNat {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos).ult 248#64 = decide (pos + 8 < 256) :=
  (by decide +kernel : ∀ k : Fin 256, (BitVec.ofNat 64 k.val).ult 248#64 = decide (k.val + 8 < 256)) ⟨pos, hpos⟩

private theorem bne_256_ofNat_add1 {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 (pos + 1) != 256#64) = decide (pos + 1 < 256) :=
  (by decide +kernel : ∀ k : Fin 256,
    (BitVec.ofNat 64 (k.val + 1) != 256#64) = decide (k.val + 1 < 256)) ⟨pos, hpos⟩

private theorem mod64_ofNat {pos : Nat} (hpos : pos < 256) :
    (BitVec.ofNat 64 pos).toNat % 64 = pos % 64 :=
  (by decide +kernel : ∀ k : Fin 256, (BitVec.ofNat 64 k.val).toNat % 64 = k.val % 64) ⟨pos, hpos⟩

private theorem mod64_neg_ofNat {pos : Nat} (hpos : pos < 256) (hge : 56 ≤ pos % 64) :
    (-BitVec.ofNat 64 pos).toNat % 64 = 64 - pos % 64 :=
  (by decide +kernel : ∀ k : Fin 256, 56 ≤ k.val % 64 →
    (-BitVec.ofNat 64 k.val).toNat % 64 = 64 - k.val % 64) ⟨pos, hpos⟩ hge

private theorem shiftLeft_64_sub_mod64 {n : Nat} (w1 : BitVec n) (pos : Nat) :
    w1 <<< (64 - pos % 64) = w1 <<< 1 <<< (63 - pos % 64) := by
  have h : 64 - pos % 64 = 1 + (63 - pos % 64) := by omega
  rw [h, BitVec.shiftLeft_add]

structure NafLoopRegs [DalekCliPlacement] (s0 s : State) (a_ptr b_ptr pc_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 2368#64
  hx1 : s.readReg64 (.gpr 1#5) = a_ptr
  hx2 : s.readReg64 (.gpr 2#5) = b_ptr
  hx19 : s.readReg64 (.gpr 19#5) = s0.sp - 560#64
  hx29 : s.readReg64 (.gpr 29#5) = s0.sp - 96#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem

private theorem naf5_tail [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (pos : Nat) (hpos : pos < 256) (carry width : BitVec 64)
    (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
    (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hregs : NafLoopRegs s0 s a_ptr b_ptr (if width.getLsbD 0 = true then b + 188#64 else b + 168#64))
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos) (hx9 : s.readReg64 (.gpr 9#5) = carry)
    (hx10 : s.readReg64 (.gpr 10#5) = s0.sp - 1840#64) (hx11 : s.readReg64 (.gpr 11#5) = 4294967264#64)
    (hx12 : s.readReg64 (.gpr 12#5) = s0.sp - 2352#64)
    (hx13 : s.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 pos)
    (hx14 : s.readReg64 (.gpr 14#5) = width)
    (hnaf_len : naf.length = 256)
    (hodd_next : width.getLsbD 0 = true →
      let naf' := ByteSlice.write8 naf pos (naf5Digit width); let carry' := naf5NextCarry width
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 5 < 256) = true then b + 116#64 else b + 224#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 5) → s'.readReg64 (.gpr 9#5) = carry' →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = 4294967264#64 →
        s'.readReg64 (.gpr 12#5) = s0.sp - 2352#64 →
        (pos + 5 < 256 → s'.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 (pos + 5)) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf') ∗ F) post)
    (heven_next : width.getLsbD 0 = false →
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 1 < 256) = true then b + 116#64 else b + 224#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 1) → s'.readReg64 (.gpr 9#5) = carry →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = 4294967264#64 →
        s'.readReg64 (.gpr 12#5) = s0.sp - 2352#64 →
        s'.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 (pos + 1) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
  cases hodd : width.getLsbD 0
  · simp only [hodd, Bool.false_eq_true, ↓ite_false] at hpc; wp_sym_steps 4
    simp only [ofNat_add_1 hpos, neg_ofNat_sub_1 hpos, bne_256_ofNat_add1 hpos]
    by_cases hlt1 : pos + 1 < 256
    · simp only [decide_eq_true hlt1, ↓ite_true]
      exact heven_next hodd _ ⟨by simp [decide_eq_true hlt1], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    · simp only [decide_eq_false hlt1, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 1
      exact heven_next hodd _ ⟨by simp [decide_eq_false hlt1], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · simp only [hodd, ↓ite_true] at hpc
    wp_cut_codeLoaded hcl
    wp_sym_steps 9
    close_cut_codeLoaded
    simp only [ofNat_add_5 hpos, ult_251_ofNat hpos]
    by_cases hlt5 : pos + 5 < 256
    · simp only [decide_eq_true hlt5, ↓ite_true]; wp_sym_steps 1
      exact hodd_next hodd _ ⟨by simp [decide_eq_true hlt5], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (fun _ => by wp_norm_lhs)
    · simp only [decide_eq_false hlt5, Bool.false_eq_true, ↓ite_false]
      exact hodd_next hodd _ ⟨by simp [decide_eq_false hlt5], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (fun h => absurd h hlt5)

private theorem naf5_iter [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b)
    (pos : Nat) (hpos : pos < 256) (carry : BitVec 64)
    (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
    (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hregs : NafLoopRegs s0 s a_ptr b_ptr (b + 116#64))
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos) (hx9 : s.readReg64 (.gpr 9#5) = carry)
    (hx10 : s.readReg64 (.gpr 10#5) = s0.sp - 1840#64) (hx11 : s.readReg64 (.gpr 11#5) = 4294967264#64)
    (hx12 : s.readReg64 (.gpr 12#5) = s0.sp - 2352#64)
    (hx13 : s.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 pos)
    (hx_len : x_buf.length = 40) (hnaf_len : naf.length = 256)
    (hodd_next : (naf5BitBuf x_buf pos + carry).getLsbD 0 = true →
      let width := naf5BitBuf x_buf pos + carry; let naf' := ByteSlice.write8 naf pos (naf5Digit width); let carry' := naf5NextCarry width
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 5 < 256) = true then b + 116#64 else b + 224#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 5) → s'.readReg64 (.gpr 9#5) = carry' →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = 4294967264#64 →
        s'.readReg64 (.gpr 12#5) = s0.sp - 2352#64 →
        (pos + 5 < 256 → s'.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 (pos + 5)) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf') ∗ F) post)
    (heven_next : (naf5BitBuf x_buf pos + carry).getLsbD 0 = false →
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 1 < 256) = true then b + 116#64 else b + 224#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 1) → s'.readReg64 (.gpr 9#5) = carry →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = 4294967264#64 →
        s'.readReg64 (.gpr 12#5) = s0.sp - 2352#64 →
        s'.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 (pos + 1) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
  wp_sym_steps 4; simp only [lsr6_shl3_ofNat hpos]; wp_sym_steps 3; simp only [ult_59_and63 hpos, mod64_ofNat hpos]
  by_cases h59 : 59 ≤ pos % 64
  · simp only [decide_eq_true h59, Bool.not_true, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 6
    simp only [mod64_neg_ofNat hpos (by omega), shiftLeft_64_sub_mod64, beq_true]
    exact naf5_tail b hb hbase pos hpos carry (naf5BitBuf x_buf pos + carry) s0 _ target_pc a_ptr b_ptr x_buf naf F post
      ⟨by simp [naf5BitBuf, h59], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [naf5BitBuf, h59, State.readReg64_setPC, State.readReg64_setPState]) hnaf_len hodd_next heven_next
  · simp only [decide_eq_false h59, Bool.not_false, ↓ite_true]; wp_sym_steps 3
    simp only [beq_true]
    exact naf5_tail b hb hbase pos hpos carry (naf5BitBuf x_buf pos + carry) s0 _ target_pc a_ptr b_ptr x_buf naf F post
      ⟨by simp [naf5BitBuf, h59], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [naf5BitBuf, h59, State.readReg64_setPC, State.readReg64_setPState]) hnaf_len hodd_next heven_next

theorem naf5_loop_ok [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b) :
    ∀ (fuel pos : Nat) (_hfuel : pos + (fuel + 1) = 256)
      (carry : BitVec 64) (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
      (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop),
      NafLoopRegs s0 s a_ptr b_ptr (b + 116#64) →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos → s.readReg64 (.gpr 9#5) = carry →
      s.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s.readReg64 (.gpr 11#5) = 4294967264#64 →
      s.readReg64 (.gpr 12#5) = s0.sp - 2352#64 →
      s.readReg64 (.gpr 13#5) = -BitVec.ofNat 64 pos →
      x_buf.length = 40 → naf.length = 256 →
      (∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (b + 224#64) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
          (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf5Loop x_buf (fuel + 1) pos carry naf) ∗ F) post) →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2352#64) ↦ₛ naf) ∗ F) post := by
  intro fuel; induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hfuel carry s0 s target_pc a_ptr b_ptr x_buf naf F post hregs hx8 hx9 hx10 hx11 hx12 hx13 hx_len hnaf_len hnext
    have hpos : pos < 256 := by omega
    apply naf5_iter b hb hbase pos hpos carry s0 s target_pc a_ptr b_ptr x_buf naf F post hregs hx8 hx9 hx10 hx11 hx12 hx13 hx_len hnaf_len
    · intro hodd width naf' carry' s' hregs' hx8' hx9' hx10' hx11' hx12' hx13'
      have hlen' : naf'.length = 256 := by rw [ByteSlice.write8_length _ _ _ (by omega), hnaf_len]
      by_cases hlt5 : pos + 5 < 256
      · simp only [hlt5, decide_true, ↓ite_true] at hregs'; have hsub : (fuel - 5) + 1 = fuel - 4 := by omega
        exact ih (fuel - 5) (by omega) (pos + 5) (by omega) carry' s0 s' target_pc a_ptr b_ptr x_buf naf' F post
          hregs' hx8' hx9' hx10' hx11' hx12' (hx13' hlt5) hx_len hlen' (fun s'' hregs'' => by
            have hgoal := hnext s'' hregs''; rw [naf5Loop] at hgoal; simp only [hodd, ↓ite_true, hlt5] at hgoal; rw [hsub]; exact hgoal)
      · simp only [hlt5, decide_false, Bool.false_eq_true, ↓ite_false] at hregs'
        have hgoal := hnext s' hregs'; rw [naf5Loop] at hgoal; simpa only [hodd, ↓ite_true, hlt5, ↓ite_false] using hgoal
    · intro heven s' hregs' hx8' hx9' hx10' hx11' hx12' hx13'
      by_cases hlt1 : pos + 1 < 256
      · simp only [hlt1, decide_true, ↓ite_true] at hregs'; have hsub : (fuel - 1) + 1 = fuel := by omega
        exact ih (fuel - 1) (by omega) (pos + 1) (by omega) carry s0 s' target_pc a_ptr b_ptr x_buf naf F post
          hregs' hx8' hx9' hx10' hx11' hx12' hx13' hx_len hnaf_len (fun s'' hregs'' => by
            have hgoal := hnext s'' hregs''; rw [naf5Loop] at hgoal; simp only [heven, Bool.false_eq_true, ↓ite_false, hlt1, ↓ite_true] at hgoal; rw [hsub]; exact hgoal)
      · simp only [hlt1, decide_false, Bool.false_eq_true, ↓ite_false] at hregs'
        have hgoal := hnext s' hregs'; rw [naf5Loop] at hgoal; simpa only [heven, Bool.false_eq_true, ↓ite_false, hlt1] using hgoal

private theorem getD_write8 (bs : List (BitVec 8)) (pos i : Nat) (v d : BitVec 8) (hpos : pos < bs.length) :
    (ByteSlice.write8 bs pos v).getD i d = if pos = i then v else bs.getD i d := by
  rw [ByteSlice.write8, ← ByteSlice.set_eq_write bs pos v hpos, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases heq : pos = i
  · subst heq; simp [hpos]
  · simp [heq]

private theorem naf5BitBuf_and31 (x_buf : List (BitVec 8)) (pos : Nat) :
    naf5BitBuf x_buf pos &&& 31#64 = naf5BitBuf x_buf pos := by
  unfold naf5BitBuf; split <;> rw [BitVec.and_assoc, show (31#64 &&& 31#64) = 31#64 by rfl]

private theorem naf5Digit_valid (w carry : BitVec 64) (hw : w &&& 31#64 = w)
    (hc : carry = 0#64 ∨ carry = 1#64) (hodd : (w + carry).getLsbD 0 = true) :
    naf5ByteValid (naf5Digit (w + carry)) = true := by
  have hlt : w.toNat < 32 := by
    rw [← hw, BitVec.toNat_and]; exact Nat.and_lt_two_pow _ (n := 5) (by decide)
  have hweq : w = BitVec.ofNat 64 w.toNat := by simp
  rw [hweq] at hodd ⊢
  rcases hc with rfl | rfl
  · exact (by decide +kernel : ∀ k : Fin 32,
      (BitVec.ofNat 64 k.val + 0#64).getLsbD 0 = true →
      naf5ByteValid (naf5Digit (BitVec.ofNat 64 k.val + 0#64)) = true) ⟨w.toNat, hlt⟩ hodd
  · exact (by decide +kernel : ∀ k : Fin 32,
      (BitVec.ofNat 64 k.val + 1#64).getLsbD 0 = true →
      naf5ByteValid (naf5Digit (BitVec.ofNat 64 k.val + 1#64)) = true) ⟨w.toNat, hlt⟩ hodd

private theorem naf5NextCarry_valid (w : BitVec 64) :
    naf5NextCarry w = 0#64 ∨ naf5NextCarry w = 1#64 := by
  unfold naf5NextCarry; split <;> simp

theorem naf5Loop_length_valid (x_buf : List (BitVec 8)) :
    ∀ (fuel pos : Nat) (_hpos : pos < 256) (carry : BitVec 64) (_hc : carry = 0#64 ∨ carry = 1#64)
      (naf : List (BitVec 8)) (_hlen : naf.length = 256) (_hval : ∀ i < 256, naf5ByteValid (naf.getD i 0#8) = true),
      (naf5Loop x_buf fuel pos carry naf).length = 256 ∧
      (∀ i < 256, naf5ByteValid ((naf5Loop x_buf fuel pos carry naf).getD i 0#8) = true) := by
  intro fuel; induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hpos carry hc naf hlen hval
    cases fuel with
    | zero => rw [naf5Loop]; exact ⟨hlen, hval⟩
    | succ f =>
      rw [naf5Loop]; cases hodd : (naf5BitBuf x_buf pos + carry).getLsbD 0
      · by_cases hlt1 : pos + 1 < 256
        · simp only [Bool.false_eq_true, ↓ite_false, hlt1, ↓ite_true]; exact ih f (by omega) (pos + 1) hlt1 carry hc naf hlen hval
        · simp only [Bool.false_eq_true, ↓ite_false, hlt1]; exact ⟨hlen, hval⟩
      · have hlen' : (ByteSlice.write8 naf pos (naf5Digit (naf5BitBuf x_buf pos + carry))).length = 256 := by
          rw [ByteSlice.write8_length _ _ _ (by omega), hlen]
        have hval' : ∀ i < 256, naf5ByteValid ((ByteSlice.write8 naf pos (naf5Digit (naf5BitBuf x_buf pos + carry))).getD i 0#8) = true := by
          intro i hi; rw [getD_write8 naf pos i _ _ (by omega)]
          by_cases heq : pos = i
          · subst heq; simp only [↓ite_true]; exact naf5Digit_valid _ carry (naf5BitBuf_and31 x_buf pos) hc hodd
          · simp only [heq, ↓ite_false]; exact hval i hi
        by_cases hlt5 : pos + 5 < 256
        · simp only [↓ite_true, hlt5]; exact ih (f - 4) (by omega) (pos + 5) hlt5 (naf5NextCarry (naf5BitBuf x_buf pos + carry)) (naf5NextCarry_valid _) _ hlen' hval'
        · simp only [↓ite_true, hlt5, ↓ite_false]; exact ⟨hlen', hval'⟩

private theorem naf8_tail [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (pos : Nat) (hpos : pos < 256) (carry width : BitVec 64)
    (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
    (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hregs : NafLoopRegs s0 s a_ptr b_ptr (if width.getLsbD 0 = true then b + 360#64 else b + 340#64))
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos) (hx9 : s.readReg64 (.gpr 9#5) = carry)
    (hx10 : s.readReg64 (.gpr 10#5) = s0.sp - 1840#64) (hx11 : s.readReg64 (.gpr 11#5) = s0.sp - 2096#64)
    (hx12 : s.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 pos)
    (hx13 : s.readReg64 (.gpr 13#5) = width) (hnaf_len : naf.length = 256)
    (hodd_next : width.getLsbD 0 = true →
      let naf' := ByteSlice.write8 naf pos (BitVec.setWidth 8 width); let carry' := naf8NextCarry width
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 8 < 256) = true then b + 292#64 else b + 388#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 8) → s'.readReg64 (.gpr 9#5) = carry' →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = s0.sp - 2096#64 →
        (pos + 8 < 256 → s'.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 (pos + 8)) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf') ∗ F) post)
    (heven_next : width.getLsbD 0 = false →
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 1 < 256) = true then b + 292#64 else b + 388#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 1) → s'.readReg64 (.gpr 9#5) = carry →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = s0.sp - 2096#64 →
        s'.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 (pos + 1) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
  cases hodd : width.getLsbD 0
  · simp only [hodd, Bool.false_eq_true, ↓ite_false] at hpc; wp_sym_steps 4
    simp only [ofNat_add_1 hpos, neg_ofNat_sub_1 hpos, bne_256_ofNat_add1 hpos]
    by_cases hlt1 : pos + 1 < 256
    · simp only [decide_eq_true hlt1, ↓ite_true]
      exact heven_next hodd _ ⟨by simp [decide_eq_true hlt1], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    · simp only [decide_eq_false hlt1, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 1
      exact heven_next hodd _ ⟨by simp [decide_eq_false hlt1], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · simp only [hodd, ↓ite_true] at hpc
    wp_cut_codeLoaded hcl
    wp_sym_steps 7
    close_cut_codeLoaded
    simp only [ofNat_add_8 hpos, ult_248_ofNat hpos]
    by_cases hlt8 : pos + 8 < 256
    · simp only [decide_eq_true hlt8, ↓ite_true]; wp_sym_steps 1
      exact hodd_next hodd _ ⟨by simp [decide_eq_true hlt8], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (fun _ => by wp_norm_lhs)
    · simp only [decide_eq_false hlt8, Bool.false_eq_true, ↓ite_false]
      exact hodd_next hodd _ ⟨by simp [decide_eq_false hlt8], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (fun h => absurd h hlt8)

private theorem naf8_iter [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b)
    (pos : Nat) (hpos : pos < 256) (carry : BitVec 64)
    (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
    (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop)
    (hregs : NafLoopRegs s0 s a_ptr b_ptr (b + 292#64))
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos) (hx9 : s.readReg64 (.gpr 9#5) = carry)
    (hx10 : s.readReg64 (.gpr 10#5) = s0.sp - 1840#64) (hx11 : s.readReg64 (.gpr 11#5) = s0.sp - 2096#64)
    (hx12 : s.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 pos)
    (hx_len : x_buf.length = 40) (hnaf_len : naf.length = 256)
    (hodd_next : (carry + naf8BitBuf x_buf pos).getLsbD 0 = true →
      let width := carry + naf8BitBuf x_buf pos; let naf' := ByteSlice.write8 naf pos (BitVec.setWidth 8 width); let carry' := naf8NextCarry width
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 8 < 256) = true then b + 292#64 else b + 388#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 8) → s'.readReg64 (.gpr 9#5) = carry' →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = s0.sp - 2096#64 →
        (pos + 8 < 256 → s'.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 (pos + 8)) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf') ∗ F) post)
    (heven_next : (carry + naf8BitBuf x_buf pos).getLsbD 0 = false →
      ∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (if decide (pos + 1 < 256) = true then b + 292#64 else b + 388#64) →
        s'.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (pos + 1) → s'.readReg64 (.gpr 9#5) = carry →
        s'.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s'.readReg64 (.gpr 11#5) = s0.sp - 2096#64 →
        s'.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 (pos + 1) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf) ∗ F) post) :
    SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf) ∗ F) post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
  wp_sym_steps 4; simp only [lsr6_shl3_ofNat hpos]; wp_sym_steps 3; simp only [ult_56_and63 hpos, mod64_ofNat hpos]
  by_cases h56 : 56 ≤ pos % 64
  · simp only [decide_eq_true h56, Bool.not_true, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 5
    simp only [mod64_neg_ofNat hpos h56, shiftLeft_64_sub_mod64, beq_true]
    exact naf8_tail b hb hbase pos hpos carry (carry + naf8BitBuf x_buf pos) s0 _ target_pc a_ptr b_ptr x_buf naf F post
      ⟨by simp [naf8BitBuf, h56], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [naf8BitBuf, h56, State.readReg64_setPC, State.readReg64_setPState]) hnaf_len hodd_next heven_next
  · simp only [decide_eq_false h56, Bool.not_false, ↓ite_true]; wp_sym_steps 2
    simp only [beq_true]
    exact naf8_tail b hb hbase pos hpos carry (carry + naf8BitBuf x_buf pos) s0 _ target_pc a_ptr b_ptr x_buf naf F post
      ⟨by simp [naf8BitBuf, h56], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp [naf8BitBuf, h56, State.readReg64_setPC, State.readReg64_setPState]) hnaf_len hodd_next heven_next

theorem naf8_loop_ok [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl17 b) (hbase : dalekCliPl17.base = b) :
    ∀ (fuel pos : Nat) (_hfuel : pos + (fuel + 1) = 256)
      (carry : BitVec 64) (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
      (x_buf naf : List (BitVec 8)) (F : SepProp) (post : State → SepProp → Prop),
      NafLoopRegs s0 s a_ptr b_ptr (b + 292#64) →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 pos → s.readReg64 (.gpr 9#5) = carry →
      s.readReg64 (.gpr 10#5) = s0.sp - 1840#64 → s.readReg64 (.gpr 11#5) = s0.sp - 2096#64 →
      s.readReg64 (.gpr 12#5) = -BitVec.ofNat 64 pos →
      x_buf.length = 40 → naf.length = 256 →
      (∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (b + 388#64) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s'
          (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf8Loop x_buf (fuel + 1) pos carry naf) ∗ F) post) →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 1840#64) ↦ₛ x_buf) ∗ ((s0.sp - 2096#64) ↦ₛ naf) ∗ F) post := by
  intro fuel; induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hfuel carry s0 s target_pc a_ptr b_ptr x_buf naf F post hregs hx8 hx9 hx10 hx11 hx12 hx_len hnaf_len hnext
    have hpos : pos < 256 := by omega
    apply naf8_iter b hb hbase pos hpos carry s0 s target_pc a_ptr b_ptr x_buf naf F post hregs hx8 hx9 hx10 hx11 hx12 hx_len hnaf_len
    · intro hodd width naf' carry' s' hregs' hx8' hx9' hx10' hx11' hx12'
      have hlen' : naf'.length = 256 := by rw [ByteSlice.write8_length _ _ _ (by omega), hnaf_len]
      by_cases hlt8 : pos + 8 < 256
      · simp only [hlt8, decide_true, ↓ite_true] at hregs'; have hsub : (fuel - 8) + 1 = fuel - 7 := by omega
        exact ih (fuel - 8) (by omega) (pos + 8) (by omega) carry' s0 s' target_pc a_ptr b_ptr x_buf naf' F post
          hregs' hx8' hx9' hx10' hx11' (hx12' hlt8) hx_len hlen' (fun s'' hregs'' => by
            have hgoal := hnext s'' hregs''; rw [naf8Loop] at hgoal; simp only [hodd, ↓ite_true, hlt8] at hgoal; rw [hsub]; exact hgoal)
      · simp only [hlt8, decide_false, Bool.false_eq_true, ↓ite_false] at hregs'
        have hgoal := hnext s' hregs'; rw [naf8Loop] at hgoal; simpa only [hodd, ↓ite_true, hlt8, ↓ite_false] using hgoal
    · intro heven s' hregs' hx8' hx9' hx10' hx11' hx12'
      by_cases hlt1 : pos + 1 < 256
      · simp only [hlt1, decide_true, ↓ite_true] at hregs'; have hsub : (fuel - 1) + 1 = fuel := by omega
        exact ih (fuel - 1) (by omega) (pos + 1) (by omega) carry s0 s' target_pc a_ptr b_ptr x_buf naf F post
          hregs' hx8' hx9' hx10' hx11' hx12' hx_len hnaf_len (fun s'' hregs'' => by
            have hgoal := hnext s'' hregs''; rw [naf8Loop] at hgoal; simp only [heven, Bool.false_eq_true, ↓ite_false, hlt1, ↓ite_true] at hgoal; rw [hsub]; exact hgoal)
      · simp only [hlt1, decide_false, Bool.false_eq_true, ↓ite_false] at hregs'
        have hgoal := hnext s' hregs'; rw [naf8Loop] at hgoal; simpa only [heven, Bool.false_eq_true, ↓ite_false, hlt1] using hgoal

private theorem naf8Digit_valid (width : BitVec 64) (hodd : width.getLsbD 0 = true) :
    (BitVec.setWidth 8 width != 128#8) = true := by
  rw [bne_iff_ne]; intro h
  have h0 := congrArg (fun x : BitVec 8 => x.getLsbD 0) h
  simp at h0 hodd; rw [h0] at hodd; contradiction

theorem naf8Loop_length_valid (x_buf : List (BitVec 8)) :
    ∀ (fuel pos : Nat) (_hpos : pos < 256) (carry : BitVec 64) (naf : List (BitVec 8))
      (_hlen : naf.length = 256) (_hval : ∀ i < 256, (naf.getD i 0#8 != 128#8) = true),
      (naf8Loop x_buf fuel pos carry naf).length = 256 ∧
      (∀ i < 256, ((naf8Loop x_buf fuel pos carry naf).getD i 0#8 != 128#8) = true) := by
  intro fuel; induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro pos hpos carry naf hlen hval
    cases fuel with
    | zero => rw [naf8Loop]; exact ⟨hlen, hval⟩
    | succ f =>
      rw [naf8Loop]; cases hodd : (carry + naf8BitBuf x_buf pos).getLsbD 0
      · by_cases hlt1 : pos + 1 < 256
        · simp only [Bool.false_eq_true, ↓ite_false, hlt1, ↓ite_true]; exact ih f (by omega) (pos + 1) hlt1 carry naf hlen hval
        · simp only [Bool.false_eq_true, ↓ite_false, hlt1]; exact ⟨hlen, hval⟩
      · have hlen' : (ByteSlice.write8 naf pos (BitVec.setWidth 8 (carry + naf8BitBuf x_buf pos))).length = 256 := by
          rw [ByteSlice.write8_length _ _ _ (by omega), hlen]
        have hval' : ∀ i < 256, ((ByteSlice.write8 naf pos (BitVec.setWidth 8 (carry + naf8BitBuf x_buf pos))).getD i 0#8 != 128#8) = true := by
          intro i hi; rw [getD_write8 naf pos i _ _ (by omega)]
          by_cases heq : pos = i
          · subst heq; simp only [↓ite_true]; exact naf8Digit_valid _ hodd
          · simp only [heq, ↓ite_false]; exact hval i hi
        by_cases hlt8 : pos + 8 < 256
        · simp only [↓ite_true, hlt8]; exact ih (f - 7) (by omega) (pos + 8) hlt8 (naf8NextCarry (carry + naf8BitBuf x_buf pos)) _ hlen' hval'
        · simp only [↓ite_true, hlt8, ↓ite_false]; exact ⟨hlen', hval'⟩

private theorem zeroExtend64_beq_zero8 (d : BitVec 8) :
    (BitVec.zeroExtend 64 d == 0#64) = (d == 0#8) :=
  (by decide +kernel : ∀ d : BitVec 8, (BitVec.zeroExtend 64 d == 0#64) = (d == 0#8)) d

theorem ofNat_sub_1 {k : Nat} (_hk : k + 1 < 256) :
    BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem ofNat_succ_beq_zero {k : Nat} (hk : k + 1 < 256) :
    (BitVec.ofNat 64 (k + 1) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h; simp [BitVec.toNat_ofNat] at h1; omega

theorem find_max_naf_loop_ok [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl17 b) (_hbase : dalekCliPl17.base = b)
    (naf_a naf_b : List (BitVec 8)) (ha_len : naf_a.length = 256) (hb_len : naf_b.length = 256) :
    ∀ (i : Nat) (_hi : i < 256) (s0 s : State) (target_pc a_ptr b_ptr : BitVec 64)
      (F : SepProp) (post : State → SepProp → Prop),
      NafLoopRegs s0 s a_ptr b_ptr (b + 400#64) →
      s.readReg64 (.gpr 8#5) = s0.sp - 2352#64 → s.readReg64 (.gpr 9#5) = s0.sp - 2096#64 →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 i →
      (∀ s' : State, NafLoopRegs s0 s' a_ptr b_ptr (b + 428#64) →
        s'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (findMaxNafIdx naf_a naf_b i) →
        SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s' (((s0.sp - 2352#64) ↦ₛ naf_a) ∗ ((s0.sp - 2096#64) ↦ₛ naf_b) ∗ F) post) →
      SepWP (dalekCliPC17.rebase b (fun _ => none)) target_pc s (((s0.sp - 2352#64) ↦ₛ naf_a) ∗ ((s0.sp - 2096#64) ↦ₛ naf_b) ∗ F) post := by
  intro i; induction i with
  | zero =>
    intro hi s0 s target_pc a_ptr b_ptr F post hregs hx8 hx9 hx10 hnext
    rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
    wp_sym_steps 3; simp only [zeroExtend64_beq_zero8]
    cases ha0 : (naf_a.getD 0 0#8 == 0#8)
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓ite_true]
      exact hnext _ ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by simp only [findMaxNafIdx]; wp_norm_lhs)
    · simp only [not_true_eq_false, ↓ite_false]; wp_sym_steps 1
      exact hnext _ ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by simp only [findMaxNafIdx]; wp_norm_lhs)
  | succ k ih =>
    intro hi s0 s target_pc a_ptr b_ptr F post hregs hx8 hx9 hx10 hnext
    rcases hregs with ⟨hpc, hrun, hsp, hx1, hx2, hx19, hx29, hvregs, hcl⟩
    wp_sym_steps 3; simp only [zeroExtend64_beq_zero8]
    cases hak : (naf_a.getD (k + 1) 0#8 == 0#8)
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓ite_true]
      exact hnext _ ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
        (by simp only [findMaxNafIdx, hak, Bool.false_eq_true, ↓ite_false]; wp_norm_lhs)
    · simp only [not_true_eq_false, ↓ite_false]; wp_sym_steps 1
      simp only [ofNat_succ_beq_zero hi, Bool.false_eq_true, ↓ite_false]; wp_sym_steps 3
      simp only [zeroExtend64_beq_zero8, ofNat_sub_1 hi]
      cases hbk : (naf_b.getD (k + 1) 0#8 == 0#8)
      · simp only [Bool.false_eq_true, ↓ite_false]
        exact hnext _ ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
          (by simp only [findMaxNafIdx, hak, hbk, Bool.false_eq_true, ↓ite_true, ↓ite_false]; wp_norm_lhs)
      · simp only [↓ite_true]
        exact ih (by omega) s0 _ target_pc a_ptr b_ptr F post
          ⟨rfl, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by first | assumption | (rw [show State.mem _ = _ by wp_norm_lhs]; assumption)⟩
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (fun s' hregs' hx20' => hnext s' hregs' (by simpa only [findMaxNafIdx, hak, hbk, ↓ite_true] using hx20'))

/-! ## 3. Stack & Read-Only Slice Framing Helpers for `DoubleScalarMul` -/

theorem sepWP_dsmb_callee_to (sp : BitVec 64) (n : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 2368#64 - 2640#64) 2640 ∗ P := by sep_frame) (hn : n ≤ 2640 := by decide)
    (hnext : SepWP prog target_pc s ((memRegion (sp - 2368#64 - BitVec.ofNat 64 n) n ∗
      stackAt (sp - 2368#64 - BitVec.ofNat 64 n) (2640 - n)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have heq : 2640 - n + n = 2640 := by omega
  rw [hf]; change SepWP prog target_pc s (stackAt (sp - 2368#64) 2640 ∗ P) post oom
  rw [← heq, stackAt_region (sp - 2368#64) (2640 - n) n (by omega), sepConj_comm (stackAt _ _) (memRegion _ _)]
  exact hnext

theorem sepWP_dsmb_callee_from (sp : BitVec 64) (n : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 2368#64 - BitVec.ofNat 64 n) n ∗
      stackAt (sp - 2368#64 - BitVec.ofNat 64 n) (2640 - n)) ∗ P := by sep_frame) (hn : n ≤ 2640 := by decide)
    (hnext : SepWP prog target_pc s (memRegion (sp - 2368#64 - 2640#64) 2640 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have heq : 2640 - n + n = 2640 := by omega
  rw [hf, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp - 2368#64) (2640 - n) n (by omega), heq]
  exact hnext

theorem fe51Point4Bounded_of_bounds {bs : List (BitVec 8)} {b0 b1 b2 b3 : Nat}
    (hlen : bs.length = 160) (h0 : fe51LimbsBoundedAt bs 0 b0) (h40 : fe51LimbsBoundedAt bs 40 b1)
    (h80 : fe51LimbsBoundedAt bs 80 b2) (h120 : fe51LimbsBoundedAt bs 120 b3)
    (hb0 : b0 ≤ 2 ^ 54 := by decide) (hb1 : b1 ≤ 2 ^ 54 := by decide)
    (hb2 : b2 ≤ 2 ^ 54 := by decide) (hb3 : b3 ≤ 2 ^ 54 := by decide) :
    fe51Point4Bounded bs (2 ^ 54) := by
  obtain ⟨_, _, _, _, _⟩ := h0; obtain ⟨_, _, _, _, _⟩ := h40
  obtain ⟨_, _, _, _, _⟩ := h80; obtain ⟨_, _, _, _, _⟩ := h120
  exact ⟨hlen, ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

theorem sepWP_split4_completed_432 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 432#64) ↦ₛ bs) ∗ P := by sep_frame)
    (hpt : fe51Point4Bounded bs (2 ^ 54) := by assumption) (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s ((((sp - 432#64) ↦ₛ b0) ∗ ((sp - 392#64) ↦ₛ b1) ∗
        ((sp - 352#64) ↦ₛ b2) ∗ ((sp - 312#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hbs := hpt.1; let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 432#64) ↦ₛ bs) = ((sp - 432#64) ↦ₛ bs.take 40) ∗ ((sp - 392#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 432 40]
  have hs1 : ((sp - 392#64) ↦ₛ d1) = ((sp - 392#64) ↦ₛ d1.take 40) ∗ ((sp - 352#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 392 40]
  have hs2 : ((sp - 352#64) ↦ₛ d2) = ((sp - 352#64) ↦ₛ d2.take 40) ∗ ((sp - 312#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 352 40]
  obtain ⟨hb0, hb1, hb2, hb3, hv0, hv1, hv2, hv3⟩ := completed_split4_props_54 bs C hpt hval
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    hb0.1 hb1.1 hb2.1 hb3.1 hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3

theorem sepWP_split4_stack_272 (sp : BitVec 64) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 272#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      SepWP prog target_pc s ((((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗
        ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 272#64) ↦ₛ bs) = ((sp - 272#64) ↦ₛ bs.take 40) ∗ ((sp - 232#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 272 40]
  have hs1 : ((sp - 232#64) ↦ₛ d1) = ((sp - 232#64) ↦ₛ d1.take 40) ∗ ((sp - 192#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 232 40]
  have hs2 : ((sp - 192#64) ↦ₛ d2) = ((sp - 192#64) ↦ₛ d2.take 40) ∗ ((sp - 152#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 192 40]
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    (by simp [hbs]) (by simp [hd1]) (by simp [hd2]) (by simp [hd2])

theorem sepWP_merge4_432_272_ext (sp : BitVec 64) (C : EdExtPoint) (b80 : Nat)
    {c0 c1 c2 c3 b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 432#64) ↦ₛ c0) ∗ ((sp - 392#64) ↦ₛ c1) ∗ ((sp - 352#64) ↦ₛ c2) ∗ ((sp - 312#64) ↦ₛ c3) ∗
                  ((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗ ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (hb80 : 2 ^ 52 ≤ b80 := by decide)
    (hc0 : c0.length = 40 := by assumption) (hc1 : c1.length = 40 := by assumption)
    (hc2 : c2.length = 40 := by assumption) (hc3 : c3.length = 40 := by assumption)
    (hcv0 : fe51ValOfBytes c0 % p25519 = C.X := by assumption)
    (hcv1 : fe51ValOfBytes c1 % p25519 = C.Y := by assumption)
    (hcv2 : fe51ValOfBytes c2 % p25519 = C.Z := by assumption)
    (hcv3 : fe51ValOfBytes c3 % p25519 = C.T := by assumption)
    (hb0 : fe51LimbsBounded b0 (2 ^ 52) := by assumption) (hb1 : fe51LimbsBounded b1 (2 ^ 52) := by assumption)
    (hb2 : fe51LimbsBounded b2 (2 ^ 52) := by assumption) (hb3 : fe51LimbsBounded b3 (2 ^ 52) := by assumption)
    (hp0 : fe51ValOfBytes b0 % p25519 = (fe51ValOfBytes c0 * fe51ValOfBytes c3) % p25519 := by assumption)
    (hp1 : fe51ValOfBytes b1 % p25519 = (fe51ValOfBytes c1 * fe51ValOfBytes c2) % p25519 := by assumption)
    (hp2 : fe51ValOfBytes b2 % p25519 = (fe51ValOfBytes c2 * fe51ValOfBytes c3) % p25519 := by assumption)
    (hp3 : fe51ValOfBytes b3 % p25519 = (fe51ValOfBytes c0 * fe51ValOfBytes c1) % p25519 := by assumption)
    (hnext : ∀ c_bs ext_bs : List (BitVec 8),
      c_bs.length = 160 → ext_bs.length = 160 →
      fe51LimbsBoundedAt ext_bs 0 (2 ^ 53) → fe51LimbsBoundedAt ext_bs 40 (2 ^ 53) →
      fe51LimbsBoundedAt ext_bs 80 b80 → fe51LimbsBoundedAt ext_bs 120 (2 ^ 54) →
      edExtOfBytes ext_bs = edAsExtended C →
      SepWP prog target_pc s ((((sp - 432#64) ↦ₛ c_bs) ∗ ((sp - 272#64) ↦ₛ ext_bs)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hc2' : sp - 352#64 + BitVec.ofNat 64 c2.length = sp - 312#64 := by rw [hc2]; exact sub_ofNat64_add sp 352 40
  have hc1' : sp - 392#64 + BitVec.ofNat 64 c1.length = sp - 352#64 := by rw [hc1]; exact sub_ofNat64_add sp 392 40
  have hc0' : sp - 432#64 + BitVec.ofNat 64 c0.length = sp - 392#64 := by rw [hc0]; exact sub_ofNat64_add sp 432 40
  have ha2 : sp - 192#64 + BitVec.ofNat 64 b2.length = sp - 152#64 := by rw [hb2.1]; exact sub_ofNat64_add sp 192 40
  have ha1 : sp - 232#64 + BitVec.ofNat 64 b1.length = sp - 192#64 := by rw [hb1.1]; exact sub_ofNat64_add sp 232 40
  have ha0 : sp - 272#64 + BitVec.ofNat 64 b0.length = sp - 232#64 := by rw [hb0.1]; exact sub_ofNat64_add sp 272 40
  have hmc : ((sp - 432#64) ↦ₛ (c0 ++ (c1 ++ (c2 ++ c3)))) ∗ ((sp - 272#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 432#64) ↦ₛ c0) ∗ ((sp - 392#64) ↦ₛ c1) ∗ ((sp - 352#64) ↦ₛ c2) ∗ ((sp - 312#64) ↦ₛ c3) ∗
      ((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗ ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, hc0', pointsToBytes_append, hc1', pointsToBytes_append, hc2',
        pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]; sep_ac_rfl
  rw [hf, ← hmc]
  have hv0 : fe51ValOfBytes b0 % p25519 = fpMul C.X C.T := by unfold fpMul; rw [hp0, Nat.mul_mod, hcv0, hcv3, ← Nat.mul_mod]
  have hv1 : fe51ValOfBytes b1 % p25519 = fpMul C.Y C.Z := by unfold fpMul; rw [hp1, Nat.mul_mod, hcv1, hcv2, ← Nat.mul_mod]
  have hv2 : fe51ValOfBytes b2 % p25519 = fpMul C.Z C.T := by unfold fpMul; rw [hp2, Nat.mul_mod, hcv2, hcv3, ← Nat.mul_mod]
  have hv3 : fe51ValOfBytes b3 % p25519 = fpMul C.X C.Y := by unfold fpMul; rw [hp3, Nat.mul_mod, hcv0, hcv1, ← Nat.mul_mod]
  obtain ⟨hl, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, hval⟩ :=
    edAsExtended_of_append4 b0 b1 b2 b3 C hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3
  exact hnext (c0 ++ (c1 ++ (c2 ++ c3))) (b0 ++ (b1 ++ (b2 ++ b3)))
    (by simp [List.length_append, hc0, hc1, hc2, hc3]) hl
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega, by omega⟩
    ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega, by omega⟩ hval

@[expose] def pointsToBytesRORest (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat) : SepProp :=
  (base ↦ᵣ buf.take off) ∗ ((base + BitVec.ofNat 64 (off + n)) ↦ᵣ buf.drop (off + n))

theorem pointsToBytesRO_focus (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat) (hlen : off + n ≤ buf.length) :
    (base ↦ᵣ buf) = ((base + BitVec.ofNat 64 off) ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRORest base buf off n := by
  have h1 : buf = buf.take off ++ (ProofLib.ByteSlice.slice buf off n ++ buf.drop (off + n)) := by
    simp only [ProofLib.ByteSlice.slice, List.take_append_drop, ← List.drop_drop]
  conv => lhs; rw [h1]
  rw [pointsToBytesRO_append, List.length_take, Nat.min_eq_left (by omega), pointsToBytesRO_append,
      ProofLib.ByteSlice.slice_length buf off n hlen, BitVec.add_assoc, ← BitVec.ofNat_add]
  unfold pointsToBytesRORest; rw [← sepConj_assoc, sepConj_comm (base ↦ᵣ buf.take off), sepConj_assoc]

theorem sepWP_focus_ro_slice (base ptr : BitVec 64) (off n : Nat) {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ᵣ buf) ∗ P := by sep_frame) (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : (ProofLib.ByteSlice.slice buf off n).length = n →
      SepWP prog target_pc s (((ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRORest base buf off n) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]; subst hptr; rw [pointsToBytesRO_focus base buf off n hlen]; exact hnext (ByteSlice.slice_length buf off n hlen)

theorem sepWP_unfocus_ro_slice (base ptr : BitVec 64) (off n : Nat) {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRORest base buf off n) ∗ P := by sep_frame)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : SepWP prog target_pc s ((base ↦ᵣ buf) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]; subst hptr; rw [← pointsToBytesRO_focus base buf off n hlen]; exact hnext

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DoubleScalarMulNaf
