/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.GF.AcceleratedMul
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<Poly>::lagrange_interpolate_prepare`: Inner Loop and Helpers

Bit-extraction (`sbfx`), inline carryless `GF(2^16)` multiplication, and inner trailing-multiply
loop verification for `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(`0x61c1c`, Block `372`).
-/

public section

namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.AcceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open LibsignalBinary.Heap (VmPreserved)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local wp_norm] zeroExtend_16_truncate_32_64

@[local arm64_norm, local wp_norm]
theorem truncate16_zext64 (u : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 u) = u := by
  bv_bits

theorem zext64_zext32_zext64 (u : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 u)) =
      BitVec.zeroExtend 64 u := by
  bv_bits

theorem and_one_of_mod_two {p : BitVec 64} (h : p.toNat % 2 = 0) :
    p &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change p.toNat &&& 1 = 0
  rw [Nat.and_one_is_mod, h]

theorem ofNat_mul_two_and_one (k : Nat) :
    (BitVec.ofNat 64 (2 * k)) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((2 * k) % 2 ^ 64) &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

theorem add_and_one_zero {a b : BitVec 64} (ha : a &&& 1#64 = 0#64) (hb : b &&& 1#64 = 0#64) :
    (a + b) &&& 1#64 = 0#64 := by
  revert ha hb; bv_bits

theorem aligned16_add_mul_two (p : BitVec 64) (hp : p &&& 1#64 = 0#64) (k : Nat) :
    MemWidth.isAligned .W16 (p + BitVec.ofNat 64 (2 * k)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact add_and_one_zero hp (ofNat_mul_two_and_one k)

theorem ofNat_mul_four_and_one (k : Nat) :
    (BitVec.ofNat 64 (4 * k)) &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((4 * k) % 2 ^ 64) &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

theorem aligned16_add_mul_four (p : BitVec 64) (hp : p &&& 1#64 = 0#64) (k : Nat) :
    MemWidth.isAligned .W16 (p + BitVec.ofNat 64 (4 * k)) = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  exact add_and_one_zero hp (ofNat_mul_four_and_one k)

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem memRegion_two (a : BitVec 64) :
    memRegion a 2 = ∃∗ v : BitVec 16, a ↦₁₆ v :=
  IsBlock.eq (IsBlock.memRegion a 2)
    (IsBlock.sepExists fun v => IsBlock.pointsTo16 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_alloc_split (ptr : BitVec 64) (n : Nat) (hn : 2 * (n + 1) ≤ 2 ^ 64) :
    memRegion ptr (2 * (n + 1)) =
      memRegion ptr (2 * n) ∗ (∃∗ v : BitVec 16, (ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ v) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, memRegion_split ptr (2 * n) 2 hn, memRegion_two]

/-- Result of `sbfx w_dst, w25, #bit, #1` as a 32-bit word (`readReg32`). -/
abbrev sbfxBit32 (w25 : BitVec 32) (bit : Nat) : BitVec 32 :=
  BitVec.truncate 32
    (BitVec.zeroExtend 64 w25 >>> bit &&& 1#64 |||
      (if (BitVec.zeroExtend 64 w25).getLsbD bit = true then
          18446744073709551615#64
        else 0#64) &&&
        18446744073709551614#64)

/-- Result of `sbfx w_dst, w25, #bit, #1` as a 64-bit register (`readReg64`). -/
abbrev sbfxBit64 (w25 : BitVec 32) (bit : Nat) : BitVec 64 :=
  BitVec.zeroExtend 64 (sbfxBit32 w25 bit)

theorem cmn_k_prev_ne_zero {k : Nat} (hk1 : 1 ≤ k) (hk_lt : k < 2 ^ 63) :
    (BitVec.ofNat 64 (k - 1) + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 : BitVec.ofNat 64 (k - 1) + 1#64 = BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [h1] at h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change k = 0 at ht
  omega

theorem add_neg_rem_eq_k_prev {n k rem' : Nat} (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) :
    BitVec.ofNat 64 n + (0#64 - BitVec.ofNat 64 (rem' + 1)) = BitVec.ofNat 64 (k - 1) := by
  have hn : n = (k - 1) + (rem' + 1) := by omega
  rw [hn, BitVec.ofNat_add]
  bv_omega

theorem adds_neg_one_carry :
    (AddWithCarry64 (0#64 - 1#64) 1#64 false).2.c = true := by
  decide +kernel

theorem neg_succ_add_one (r : Nat) :
    -BitVec.ofNat 64 (r + 1) + 1#64 = -BitVec.ofNat 64 r := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem neg_succ_ule_add_one {r : Nat} (hr_lt : r + 2 < 2 ^ 63) :
    (-BitVec.ofNat 64 (r + 1 + 1)).ule (-BitVec.ofNat 64 (r + 1 + 1) + 1#64) = true := by
  rw [neg_succ_add_one (r + 1), BitVec.ule_iff_toNat_le]
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

@[local arm64_norm, local wp_norm]
theorem ofNat_shl_two (i : Nat) :
    BitVec.ofNat 64 i <<< 2 = BitVec.ofNat 64 (4 * i) := by
  bv_omega

theorem ptr_sub_two_succ (ptr : BitVec 64) (r : Nat) :
    ptr + BitVec.ofNat 64 (2 * (r + 1)) - 2#64 = ptr + BitVec.ofNat 64 (2 * r) := by
  rw [show 2 * (r + 1) = 2 * r + 2 by omega, BitVec.ofNat_add]
  bv_omega

theorem neg_sub_one (m : Nat) :
    -BitVec.ofNat 64 m - 1#64 = -BitVec.ofNat 64 (m + 1) := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem ofNat_bne_true_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true := by
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

@[local arm64_norm, local wp_norm]
theorem truncate32_sext64_16 (yv : BitVec 16) :
    BitVec.truncate 32 (BitVec.signExtend 64 yv) = BitVec.signExtend 32 yv := by
  bv_bits

theorem sbfx64_helper (w : BitVec 64) :
    (w &&& 1#64 |||
      (if w.getLsbD 0 = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if w.getLsbD 0 then 18446744073709551615#64 else 0#64 := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem sbfx64_one_eq (v : BitVec 64) (i : Nat) :
    (v >>> i &&& 1#64 |||
      (if v.getLsbD i = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if v.getLsbD i then 18446744073709551615#64 else 0#64 := by
  have h0 : (v >>> i).getLsbD 0 = v.getLsbD i := by simp
  rw [← h0, sbfx64_helper]

@[local arm64_norm, local wp_norm]
theorem truncate32_if_all_ones (b : Bool) :
    BitVec.truncate 32 (if b then 18446744073709551615#64 else 0#64) =
      if b then 0xffffffff#32 else 0#32 := by
  cases b <;> rfl

@[local arm64_norm, local wp_norm]
theorem truncate32_zext64 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x) = x := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem zext64_zext32_16 (v : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v) = BitVec.zeroExtend 64 v := by
  bv_bits

@[local arm64_norm, local wp_norm]
theorem and_65535_zext64_16 (v : BitVec 16) :
    BitVec.zeroExtend 64 v &&& 65535#64 = BitVec.zeroExtend 64 v := by
  bv_bits

abbrev sxth32Zext64 (yv : BitVec 16) : BitVec 64 :=
  BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)

@[expose] def sbfxMask32 (yv : BitVec 16) (i : Nat) : BitVec 32 :=
  if (sxth32Zext64 yv).getLsbD i then 0xffffffff#32 else 0#32

@[expose] def sbfxMask64 (yv : BitVec 16) (i : Nat) : BitVec 64 :=
  BitVec.zeroExtend 64 (sbfxMask32 yv i)

theorem sbfxMask64_from_if (yv : BitVec 16) (bit : Nat) :
    (if (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD bit = true then 4294967295#64 else 0#64) =
      sbfxMask64 yv bit := by
  dsimp only [sbfxMask64, sbfxMask32, sxth32Zext64]
  cases (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)).getLsbD bit <;> rfl

theorem prepare_polyReduce_xor_helper (prev r2 : BitVec 16) (v1 : BitVec 32) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (BitVec.truncate 32
            (BitVec.zeroExtend 64 prev ^^^ BitVec.zeroExtend 64 v1)) ^^^
        BitVec.zeroExtend 64 r2) =
      prev ^^^ BitVec.truncate 16 (v1 ^^^ BitVec.zeroExtend 32 r2) := by
  bv_slice

@[local arm64_norm, local wp_norm]
theorem prepare_polyReduce_xor_eq (prev cv yv : BitVec 16) :
    BitVec.truncate 16
      (BitVec.zeroExtend 64
          (BitVec.truncate 32
            (BitVec.zeroExtend 64 prev ^^^
              BitVec.zeroExtend 64
                (unaccelerated.polyMul cv yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cv yv >>> 24))) <<<
                    8))) ^^^
        BitVec.zeroExtend 64
          (reduce.reduceByteEntry
            (BitVec.truncate 8
              ((unaccelerated.polyMul cv yv ^^^
                  BitVec.zeroExtend 32
                      (reduce.reduceByteEntry
                        (BitVec.truncate 8 (unaccelerated.polyMul cv yv >>> 24))) <<<
                    8) >>>
                16)))) =
      prev ^^^ unaccelerated.mul cv yv := by
  dsimp only [unaccelerated.mul, reduce.polyReduce]
  exact prepare_polyReduce_xor_helper prev _ _

theorem multXdiffLoopPure_succ (yv : BitVec 16) (k rem' : Nat) (cs : List GF16)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length) :
    multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs =
      multXdiffLoopPure ⟨yv⟩ (k + 1) rem'
        (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩) := by
  have hci : cs[k]? = some (cs[k]'hk) := List.getElem?_eq_getElem hk
  have hciprev : cs[k - 1]? = some (cs[k - 1]'hk_prev) := List.getElem?_eq_getElem hk_prev
  simp only [multXdiffLoopPure, hci, hciprev, Option.getD_some, GF16.mul, GF16.sub, GF16.add]

theorem prepareLoopPure_succ (pts : List Pt) (i r_out : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length)
    (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length) :
    prepareLoopPure pts pts.length i (r_out + 1) p =
      prepareLoopPure pts pts.length (i + 1) r_out
        ⟨multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients⟩ := by
  have hpi : pts[i]? = some (pts[i]'hi) := List.getElem?_eq_getElem hi
  have hsub : pts.length - i = r_out + 1 := by omega
  have hge : ¬ (r_out + 1 ≥ p.coefficients.length) := by omega
  have hl_sub : p.coefficients.length - (r_out + 1) = i + 1 := by omega
  have hpt : (pts[i]'hi).x = ⟨(pts[i]'hi).x.value⟩ := rfl
  simp only [prepareLoopPure, multXdiffPure, hpi, Option.getD_some, hsub, hge, ↓reduceIte, hl_sub]

@[local arm64_norm, local wp_norm]
theorem sxth32_trunc16 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 32 yv) = yv := by
  bv_bits

@[local arm64_norm, local wp_norm]
private theorem trunc16_zext64_sext32 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.signExtend 32 yv)) = yv := by
  bv_bits

theorem ptr_add_two_of_pos (ptr : BitVec 64) {k : Nat} (hk : 1 ≤ k) :
    ptr + BitVec.ofNat 64 (2 * (k - 1)) + 2#64 = ptr + BitVec.ofNat 64 (2 * k) := by
  rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
  congr 2; omega

private theorem sp_setMem_loc (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_loc (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_loc (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_loc (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_loc (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_loc (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
private theorem readReg32_setMem_loc (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
private theorem readReg_setMem_loc (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases s <;> cases r <;> rfl
private theorem calleeSavedVRegs_setMem_loc (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_loc pc_setMem_loc status_setMem_loc pstate_setMem_loc trace_setMem_loc
  readReg64_setMem_loc readReg32_setMem_loc readReg_setMem_loc calleeSavedVRegs_setMem_loc

private theorem sepWP_grab_vm_lp {prog : Program} {tgt : BitVec 64} {s0 s_call sf_call : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hcall : VmPreserved s_call sf_call) (htr_call : sf_call.trace = s_call.trace)
    (hpre : VmPreserved s0 s_call) (htr0 : s_call.trace = s0.trace)
    (h : VmPreserved s0 sf_call → sf_call.trace = s0.trace → SepWP prog tgt sf_call P Q) :
    SepWP prog tgt sf_call P Q :=
  h (hpre.trans hcall) (htr_call.trans htr0)

private theorem allocHookStack_split_once (sp' : BitVec 64) :
    stackAt sp' allocHookStack =
      memRegion (sp' - 4096#64) 3936 ∗ stackAt sp' 0xa0 := by
  show stackAt sp' (0xa0 + 3936) = _
  rw [ProofLib.stackAt_split_bottom sp' 0xa0 3936 (by decide)]

private theorem allocHookStack_merge_once (sp' : BitVec 64) :
    memRegion (sp' - 4096#64) 3936 ∗ stackAt sp' 0xa0 ⊢
      stackAt sp' allocHookStack := by
  rw [allocHookStack_split_once sp']
  exact Entails.refl _

private theorem prepScratch16_split_w0 (sp0 : BitVec 64) :
    memRegion (sp0 - 208#64) 16 =
      memRegion (sp0 - 208#64) 12 ∗ (∃∗ v : BitVec 32, (sp0 - 196#64) ↦₃₂ v) := by
  rw [ProofLib.memRegion_split' (b := sp0 - 208#64) (n := 12) (k := 4) (b' := sp0 - 196#64) rfl (by bv_arith) (by decide),
      memRegion_four (sp0 - 196#64)]

private theorem prepScratch16_merge_w0 (sp0 : BitVec 64) (v : BitVec 32) :
    memRegion (sp0 - 208#64) 12 ∗ ((sp0 - 196#64) ↦₃₂ v) ⊢ memRegion (sp0 - 208#64) 16 := by
  rw [prepScratch16_split_w0 sp0]
  exact sepConj_mono_right (Entails.sepExists_intro v)

private theorem prepScratch16_split_pair (sp0 : BitVec 64) :
    memRegion (sp0 - 112#64) 16 =
      (∃∗ v0 : BitVec 64, (sp0 - 112#64) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (sp0 - 104#64) ↦₆₄ v1) := by
  rw [ProofLib.memRegion_split' (b := sp0 - 112#64) (n := 8) (k := 8) (b' := sp0 - 104#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp0 - 112#64), memRegion_eight (sp0 - 104#64)]

private theorem prepScratch16_merge_pair (sp0 : BitVec 64) (v0 v1 : BitVec 64) :
    ((sp0 - 112#64) ↦₆₄ v0) ∗ ((sp0 - 104#64) ↦₆₄ v1) ⊢ memRegion (sp0 - 112#64) 16 := by
  rw [prepScratch16_split_pair sp0]
  exact sepConj_mono (Entails.sepExists_intro v0) (Entails.sepExists_intro v1)

set_option maxHeartbeats 1600000 in
theorem innerPolyMul_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (k : Nat) (hk1 : 1 ≤ k)
    (cv yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_372).base + 508#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.readReg64 .x8 = BitVec.zeroExtend 64 (unaccelerated.polyMul cv yv) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         memRegion (sp0 - 208#64) 16 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 208#64) allocHookStack ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       memRegion (sp0 - 208#64) 16 ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 208#64) allocHookStack ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F) Q := by
  have halign_bd8 := aligned_tokenOnce_placed
  have hptr_step := ptr_add_two_of_pos ptr hk1
  have hal_k := aligned16_add_mul_two ptr hptr_al k
  have hmul := lscall_blk (callerProg := (blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
    (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul
  have honce : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ spqrOnceCallSym) spqrOnceCallGhostSpec :=
    spqr_onceCall_ok hOnce
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_372).base + 508#64)
  wp_simp_pre [tokenInitPlacedAt]
  wp_pull_exists
  rename_i probed
  cases probed
  · -- Unprobed slow path (`probed = false`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenUnprobedPlacedAt, prepScratch16_split_w0 sp0, prepScratch16_split_pair sp0,
      allocHookStack_split_once]
    wp_pull_exists
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_372).base + 248#64)
    wp_steps 3
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs)
      (blkPC_372_rebase_fetch_0xe0 (blkPl_372).base (Rust.withPanics ext))
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_372).rebase (blkPl_372).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_372 (mid := (blkPl_372).base + 316#64)
    intro _m_strip
    wp_steps 13
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_once0 : VmPreserved s _ :=
      (by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    wp_steps 1
    wp_call honce
    have hvm_once1 : VmPreserved s sf :=
      (hvm_once0.trans (by
        unfold VmPreserved LibsignalBinary.Heap.PoolPreserved LibsignalBinary.Heap.FdsHiFrame
        exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)).trans (by assumption)
    have htr_once1 : sf.trace = s.trace := (by assumption : sf.trace = _).trans (by simp only [wp_norm, arm64_norm])
    have hx25_once : sf.readReg64 .x25 = sxth32Zext64 yv := by simp only [arm64_norm, wp_norm, *]
    wp_steps 5
    wp_step
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_once
    apply SepWP.fold (allocHookStack_merge_once (sp0 - 208#64)) (by sep_focus)
    apply SepWP.fold (prepScratch16_merge_pair sp0 _ _) (by sep_focus)
    apply SepWP.fold (prepScratch16_merge_w0 sp0 _) (by sep_focus)
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    have hmul_after := lscall_blk (callerProg := (blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (acceleratedMul2Unreduced_vm_placed_ok (Rust.withPanics ext)) hcl_once
    simp only [withMemEq, acceleratedMul2UnreducedPlacedSpec] at hmul_after
    wp_steps 2
    wp_call hmul_after (cv, yv, 0#16)
    refine sepWP_grab_vm_lp (s0 := s) (by assumption) (by assumption)
      (hvm_once1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [wp_norm, arm64_norm] using htr_once1)
      fun hvm_pre htr_mul => ?_
    wp_steps 2
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_f
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      tokenInitPlacedAt ∗
      memRegion (sp0 - 208#64) 16 ∗
      memRegion (sp0 - 112#64) 16 ∗
      stackAt (sp0 - 208#64) allocHookStack ∗
      ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
      ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
      ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
      ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
      ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
      ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F by
        simp only [Nat.mul_comm 2 k])) ?_
    apply hnext _ hcl_f (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hvm_pre.trans (by simp only [wp_norm, arm64_norm]))
    · simp only [arm64_norm, wp_norm, *, mul2UnreducedWord_shr32]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
  · -- Probed fast path (`probed = true`)
    have _hsp_al : (sp0 &&& 15#64 == 0#64) = true := beq_iff_eq.mpr hsp0
    wp_simp_pre [tokenProbedPlacedAt]
    wp_steps 3
    apply step_ldar32 (by wp_norm_lhs) (by wp_norm_lhs)
      (blkPC_372_rebase_fetch_0xe0 (blkPl_372).base (Rust.withPanics ext))
      (by wp_norm_lhs) (by wp_norm_lhs) halign_bd8 (by wp_sep_access) (by wp_norm_lhs)
    wp_steps 7
    apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
    wp_call hmul (cv, yv, 0#16)
    refine sepWP_grab_vm_lp (s0 := s) (by assumption) (by assumption)
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      fun hvm_pre htr_mul => ?_
    wp_steps 2
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_f
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      tokenInitPlacedAt ∗
      memRegion (sp0 - 208#64) 16 ∗
      memRegion (sp0 - 112#64) 16 ∗
      stackAt (sp0 - 208#64) allocHookStack ∗
      ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
      ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
      ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
      ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
      ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
      ((ptr + BitVec.ofNat 64 (2 * k)) ↦₁₆ cv) ∗ F by
        simp only [Nat.mul_comm 2 k])) ?_
    apply hnext _ hcl_f (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (hvm_pre.trans (by simp only [wp_norm, arm64_norm]))
    · simp only [arm64_norm, wp_norm, *, mul2UnreducedWord_shr32]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]
    · simp only [arm64_norm, wp_norm, *]

set_option maxHeartbeats 1600000 in
theorem innerStep_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (rem' k : Nat) (cs : List GF16)
    (hk1 : 1 ≤ k) (hk_rem : k + rem' = n) (hcs_len : cs.length = n + 1)
    (hk : k < cs.length) (hk_prev : k - 1 < cs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_372).base + 212#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : s.readReg64 .x21 = sbfxMask64 yv 6)
    (hx22 : s.readReg64 .x22 = sbfxMask64 yv 7)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx24 : s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)))
    (hx25 : s.readReg64 .x25 = sxth32Zext64 yv)
    (hx26 : s.readReg64 .x26 = sbfxMask64 yv 8)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1))
    (hx28 : s.readReg64 .x28 = sbfxMask64 yv 9)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_372).base + 564#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = addsPState64 (0#64 - BitVec.ofNat 64 (rem' + 1)) 1#64 →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x20 = BitVec.ofNat 64 n →
      sf.readReg64 .x21 = sbfxMask64 yv 6 →
      sf.readReg64 .x22 = sbfxMask64 yv 7 →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x25 = sxth32Zext64 yv →
      sf.readReg64 .x26 = sbfxMask64 yv 8 →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) + 1#64 →
      sf.readReg64 .x28 = sbfxMask64 yv 9 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         memRegion (sp0 - 208#64) 16 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 208#64) allocHookStack ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr
           (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩) ∗
         reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       memRegion (sp0 - 208#64) 16 ∗
       memRegion (sp0 - 112#64) 16 ∗
       stackAt (sp0 - 208#64) allocHookStack ∗
       ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
       ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
       ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
       ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
       ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
       gf16SliceAt ptr cs ∗
       reduceTablePlacedAt ∗ F) Q := by
  wp_conv_pre => rw [gf16SliceAt_focus_assoc hk ptr]
  apply innerPolyMul_placed_sepWP ext hOnce sp0 ptr hsp0 hptr_al k hk1 (cs[k]'hk).value yv ret_pc Q s
    (gf16SliceRest ptr cs k ∗ reduceTablePlacedAt ∗ F)
    hcl hpc hrun hsp hx21 hx22 hx24 hx25 hx26 hx28 hx29
  intro s1 hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx23] at hx23_1; rw [hx27] at hx27_1
  have hadd_k := add_neg_rem_eq_k_prev hk1 hk_rem
  have hcmn := cmn_k_prev_ne_zero hk1 (by omega)
  have hal_prev := aligned16_add_mul_two ptr hptr_al (k - 1)
  wp_conv_pre => rw [← gf16SliceAt_focus_assoc hk ptr, gf16SliceAt_focus_assoc hk_prev ptr]
  apply sepWP_seq_lscl (by exact hcl1) (mid := (blkPl_372).base + 564#64)
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_372).rebase (blkPl_372).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_372 (mid := (blkPl_372).base + 564#64)
  intro _m_strip
  wp_steps 6
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv)]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul (cs[k]'hk).value yv),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 4
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul (cs[k]'hk).value yv ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul (cs[k]'hk).value yv >>> 24))) <<<
                  8) >>>
              16)),
        gf16SliceAt_update_assoc hk_prev ptr]
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm_tot : VmPreserved s _ :=
    hvm1.trans (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_next
  apply hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
    (by simpa [arm64_norm, wp_norm] using htrace1) hvm_tot (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1) (by simpa [arm64_norm, wp_norm] using hx21_1)
    (by simpa [arm64_norm, wp_norm] using hx22_1) (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by simpa [arm64_norm, wp_norm] using hx24_1) (by simpa [arm64_norm, wp_norm] using hx25_1)
    (by simpa [arm64_norm, wp_norm] using hx26_1) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx28_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem innerLoop_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    (sp0 ptr : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem' k : Nat) (cs : List GF16)
      (_hk1 : 1 ≤ k) (_hk_rem : k + rem' = n) (_hcs_len : cs.length = n + 1)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_372).base + 212#64 →
      s.status = .Running →
      s.sp = sp0 - 208#64 →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x20 = BitVec.ofNat 64 n →
      s.readReg64 .x21 = sbfxMask64 yv 6 →
      s.readReg64 .x22 = sbfxMask64 yv 7 →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x25 = sxth32Zext64 yv →
      s.readReg64 .x26 = sbfxMask64 yv 8 →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) →
      s.readReg64 .x28 = sbfxMask64 yv 9 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_372).base + 568#64 →
        sf.status = .Running →
        sf.sp = sp0 - 208#64 →
        sf.trace = s.trace →
        VmPreserved s sf →
        sf.readReg64 .x20 = BitVec.ofNat 64 n →
        sf.readReg64 .x23 = lsρ reduceTableSym →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
          (tokenInitPlacedAt ∗
           memRegion (sp0 - 208#64) 16 ∗
           memRegion (sp0 - 112#64) 16 ∗
           stackAt (sp0 - 208#64) allocHookStack ∗
           ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
           ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
           ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
           ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
           ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
           gf16SliceAt ptr (multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs) ∗
           reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
        (tokenInitPlacedAt ∗
         memRegion (sp0 - 208#64) 16 ∗
         memRegion (sp0 - 112#64) 16 ∗
         stackAt (sp0 - 208#64) allocHookStack ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr cs ∗
         reduceTablePlacedAt ∗ F) Q := by
  intro rem'
  induction rem' with
  | zero =>
    intro k cs hk1 hk_rem hcs_len s F hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_sepWP ext hOnce sp0 ptr hsp0 hptr_al n hn_bound yv 0 k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hpstate1 _hx19_1 hx20_1 _hx21_1 _hx22_1 hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    have hcarry := adds_neg_one_carry
    apply sepWP_seq_lscl (by exact hcl1) (mid := (blkPl_372).base + 568#64)
    wp_steps 1
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    rw [multXdiffLoopPure_succ yv k 0 cs hk hk_prev] at hnext
    exact hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r ih =>
    intro k cs hk1 hk_rem hcs_len s F hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_placed_sepWP ext hOnce sp0 ptr hsp0 hptr_al n hn_bound yv (r + 1) k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hcl1 hpc1 hrun1 hsp1 htrace1 hvm1 hpstate1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    have hcarry := neg_succ_ule_add_one (r := r) (by omega)
    apply sepWP_seq_lscl (by exact hcl1) (mid := (blkPl_372).base + 212#64)
    wp_steps 1
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_next
    apply ih (k + 1)
      (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩)
      (by omega) (by omega) (by simp [List.length_set, hcs_len]) _ F hcl_next
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx22_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx26_1)
      (by simpa [arm64_norm, wp_norm, neg_succ_add_one (r + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hcl_f hpc_f hrun_f hsp_f htrace_f hvm_f hx20_f hx23_f hx29_f hvregs_f
    rw [multXdiffLoopPure_succ yv k (r + 1) cs hk hk_prev] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      hx20_f hx23_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

end CryptoVerification.SpqrV1.Poly.LagrangePrepare
