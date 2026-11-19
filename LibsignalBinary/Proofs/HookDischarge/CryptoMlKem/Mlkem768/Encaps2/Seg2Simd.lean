/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith

/-!
# `encapsulate2` (`B20`) — Segment 2 `{svc}`-Polymorphic AdvSIMD Bridges (`Seg2Simd`)

Provides `{svc}`-polymorphic `@[simp, arm64_norm, wp_norm]` instruction bridges (`tbl`, `ushl`,
`sshl`, `cmeq #0`, `dup .8h`, `mvni`, `bic #imm`) that fire under `[local irreducible] blkPC20`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16
  ext_lane16
  lane8
  lane16
  lane16_dup8x16
  lane16_mapLanes_8
  lane16_zipSimdLanes_true_16
  pack16x8
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdCmeqZero8h
  lane16_simdSshl8h
  lane16_simdUshl8h
  simdCmeqZero8h
  simdSshl8h
  simdSshlElem16
  simdTbl16b
  simdUshl8h
  simdUshlElem16
)

@[simp, arm64_norm, wp_norm]
theorem applySimdResult_ok (s : State) (rd : BitVec 5) (v : BitVec 128) :
    applySimdResult s rd (.ok v) = (s.writeVReg128 rd v).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem evalSimdModImmExt_mvni_4s_3_msl16 (vd : BitVec 128) :
    evalSimdModImmExt true true 0#3 26#5 3#5 vd =
      .ok 0xfffc0000fffc0000fffc0000fffc0000#128 := rfl

@[simp, arm64_norm, wp_norm]
theorem evalSimdModImmExt_bic_8h_0xf0_lsl8 (vd : BitVec 128) :
    evalSimdModImmExt true true 7#3 22#5 16#5 vd =
      .ok (vd &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128) := rfl

private theorem getLsbD_0xff128 :
    ∀ k : Fin 128, (0xff#128).getLsbD k.val = decide (k.val < 8) := by decide +kernel

private theorem getLsbD_0xffff128 :
    ∀ k : Fin 128, (65535#128).getLsbD k.val = decide (k.val < 16) := by
  decide +kernel

private theorem tblByte_1 (vn : BitVec 128) (idx : Nat) (h : idx < 16) :
    ((vn >>> (idx * 8)) &&& 0xff#128) = (lane8 vn ⟨idx, h⟩).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have hm := getLsbD_0xff128 ⟨b, hb⟩; dsimp only at hm
  simp only [lane8, BitVec.truncate_eq_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and, hm]
  by_cases hb8 : b < 8
  · simp only [hb8, decide_true, Bool.true_and, Bool.and_true, Nat.mul_comm idx 8]
  · simp only [hb8, decide_false, Bool.false_and, Bool.and_false]

private theorem tblIdx_eq (vm : BitVec 128) (j : Fin 16) :
    ((vm >>> (j.val * 8)) &&& 0xff#128).toNat = (lane8 vm j).toNat := by
  have h : ((vm >>> (j.val * 8)) &&& 0xff#128) = (lane8 vm j).zeroExtend 128 :=
    tblByte_1 vm j.val j.isLt
  rw [h, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hj := (lane8 vm j).isLt
  exact Nat.mod_eq_of_lt (by omega)

private theorem getLsbD_append3 {a b c : Nat} (x : BitVec a) (y : BitVec b) (z : BitVec c)
    (k : Nat) :
    (x ++ (y ++ z)).getLsbD k = ((x ++ y) ++ z).getLsbD k := by
  simp only [BitVec.getLsbD_append]
  by_cases h1 : k < c
  · simp [h1, show k < b + c by omega]
  · by_cases h2 : k < b + c
    · simp [h1, h2, show k - c < b by omega]
    · simp [h1, h2, show ¬ (k - c < b) by omega, show k - (b + c) = k - c - b by omega]

private theorem append16_right_eq_left
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : BitVec 8) :
    (x15 ++ (x14 ++ (x13 ++ (x12 ++ (x11 ++ (x10 ++ (x9 ++ (x8 ++
      (x7 ++ (x6 ++ (x5 ++ (x4 ++ (x3 ++ (x2 ++ (x1 ++ x0))))))))))))))).zeroExtend 128 =
      x15 ++ x14 ++ x13 ++ x12 ++ x11 ++ x10 ++ x9 ++ x8 ++
      x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  unfold BitVec.zeroExtend
  rw [BitVec.getLsbD_setWidth]
  simp only [hk, decide_true, Bool.true_and, getLsbD_append3]

private theorem zext_or_shift {w : Nat} (lo : BitVec w) (hi : BitVec 8) (_hw : w + 8 ≤ 128) :
    lo.zeroExtend 128 ||| (hi.zeroExtend 128 <<< w) = (hi ++ lo).zeroExtend 128 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases hbw : b < w
  · simp [hbw]
  · by_cases hb8 : b < w + 8
    · have hlo : lo.getLsbD b = false := BitVec.getLsbD_of_ge lo b (by omega)
      simp [hbw, hlo, show b - w < 128 by omega]
    · have hlo : lo.getLsbD b = false := BitVec.getLsbD_of_ge lo b (by omega)
      have hhi : hi.getLsbD (b - w) = false := BitVec.getLsbD_of_ge hi (b - w) (by omega)
      simp [hbw, hlo, hhi]

@[simp, arm64_norm, wp_norm]
theorem exec_simdTbl_16b_1 {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTbl true rm 0#2 false rn rd) s =
      (s.writeVReg128 rd (simdTbl16b (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  congr 2
  set vn := s.readVReg128 rn
  set vm := s.readVReg128 rm
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : List.range' ([:16] : Std.Legacy.Range).start ([:16] : Std.Legacy.Range).size
      ([:16] : Std.Legacy.Range).step = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  rw [hr]
  simp only [List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  have hstep (j : Fin 16) :
      (if ((vm >>> (j.val * 8)) &&& 0xff#128).toNat < 16 then
        (s.readVReg128 (rn + BitVec.ofNat 5 (((vm >>> (j.val * 8)) &&& 0xff#128).toNat / 16)) >>>
          ((((vm >>> (j.val * 8)) &&& 0xff#128).toNat % 16) * 8)) &&& 0xff#128
       else 0#128) =
      ((if h : (lane8 vm j).toNat < 16 then lane8 vn ⟨(lane8 vm j).toNat, h⟩ else 0#8).zeroExtend 128) := by
    rw [tblIdx_eq vm j]
    by_cases h : (lane8 vm j).toNat < 16
    · have hdiv : (lane8 vm j).toNat / 16 = 0 := Nat.div_eq_of_lt h
      have hmod : (lane8 vm j).toNat % 16 = (lane8 vm j).toNat := Nat.mod_eq_of_lt h
      simp only [h, ↓reduceIte, ↓reduceDIte, hdiv, hmod, BitVec.add_zero]
      exact tblByte_1 vn (lane8 vm j).toNat h
    · simp only [h, ↓reduceIte, ↓reduceDIte]; rfl
  change _ = simdTbl16b vn vm
  have h0 := hstep ⟨0, by decide⟩; have h1 := hstep ⟨1, by decide⟩
  have h2 := hstep ⟨2, by decide⟩; have h3 := hstep ⟨3, by decide⟩
  have h4 := hstep ⟨4, by decide⟩; have h5 := hstep ⟨5, by decide⟩
  have h6 := hstep ⟨6, by decide⟩; have h7 := hstep ⟨7, by decide⟩
  have h8 := hstep ⟨8, by decide⟩; have h9 := hstep ⟨9, by decide⟩
  have h10 := hstep ⟨10, by decide⟩; have h11 := hstep ⟨11, by decide⟩
  have h12 := hstep ⟨12, by decide⟩; have h13 := hstep ⟨13, by decide⟩
  have h14 := hstep ⟨14, by decide⟩; have h15 := hstep ⟨15, by decide⟩
  dsimp only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 ⊢
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [Nat.zero_mul, BitVec.shiftLeft_zero, BitVec.zero_or]
  rw [zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide),
      zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide),
      zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide),
      zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide),
      zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide), zext_or_shift _ _ (by decide)]
  simp only [
    show (⟨0, by decide⟩ : Fin 16) = 0 from rfl,
    show (⟨1, by decide⟩ : Fin 16) = 1 from rfl,
    show (⟨2, by decide⟩ : Fin 16) = 2 from rfl,
    show (⟨3, by decide⟩ : Fin 16) = 3 from rfl,
    show (⟨4, by decide⟩ : Fin 16) = 4 from rfl,
    show (⟨5, by decide⟩ : Fin 16) = 5 from rfl,
    show (⟨6, by decide⟩ : Fin 16) = 6 from rfl,
    show (⟨7, by decide⟩ : Fin 16) = 7 from rfl,
    show (⟨8, by decide⟩ : Fin 16) = 8 from rfl,
    show (⟨9, by decide⟩ : Fin 16) = 9 from rfl,
    show (⟨10, by decide⟩ : Fin 16) = 10 from rfl,
    show (⟨11, by decide⟩ : Fin 16) = 11 from rfl,
    show (⟨12, by decide⟩ : Fin 16) = 12 from rfl,
    show (⟨13, by decide⟩ : Fin 16) = 13 from rfl,
    show (⟨14, by decide⟩ : Fin 16) = 14 from rfl,
    show (⟨15, by decide⟩ : Fin 16) = 15 from rfl]
  unfold simdTbl16b pack16x8
  exact append16_right_eq_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdUshl_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    Bool.true_or, decide_false, decide_true, ↓reduceIte, BitVec.reduceEq,
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdUshl8h]
  set x := lane16 (s.readVReg128 rn) i
  set sh := lane16 (s.readVReg128 rm) i
  have htr : ((sh.zeroExtend 128).truncate 8) = sh.truncate 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hk,
      show k < 128 by omega, decide_true, Bool.true_and]
  dsimp only [simdUshlElem16]
  rw [htr]
  set sb := (sh.truncate 8).toInt
  by_cases hge : sb ≥ 0
  · simp only [hge, ↓reduceIte]
    by_cases hamt : sb.toNat ≥ 16
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [BitVec.truncate_eq_setWidth, show k < sb.toNat by omega]
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      have hm := getLsbD_0xffff128 ⟨k, by omega⟩; dsimp only at hm
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
        BitVec.getLsbD_shiftLeft, hm, hk, show k < 128 by omega, decide_true, Bool.true_and]
      by_cases hlt : k < sb.toNat
      · simp [hlt]
      · simp [hlt, show k - sb.toNat < 16 by omega, show k - sb.toNat < 128 by omega]
  · simp only [hge, ↓reduceIte]
    by_cases hamt : (-sb).toNat ≥ 16
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      have hx : x.getLsbD ((-sb).toNat + k) = false :=
        BitVec.getLsbD_of_ge x ((-sb).toNat + k) (by omega)
      simp [BitVec.truncate_eq_setWidth, hx]
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        hk, show (-sb).toNat + k < 128 by omega, decide_true, Bool.true_and]

@[simp, arm64_norm, wp_norm]
theorem exec_simdSshl_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq,
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdSshl8h]
  set x := lane16 (s.readVReg128 rn) i
  set sh := lane16 (s.readVReg128 rm) i
  have htr : ((sh.zeroExtend 128).truncate 8) = sh.truncate 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hk,
      show k < 128 by omega, decide_true, Bool.true_and]
  have hmsb_eq : (x.zeroExtend 128).getLsbD (16 - 1) = x.msb := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, show 16 - 1 < 128 by decide,
      decide_true, Bool.true_and, BitVec.msb_eq_getLsbD_last]
  dsimp only [simdSshlElem16]
  rw [htr, hmsb_eq]
  set sb := (sh.truncate 8).toInt
  by_cases hge : sb ≥ 0
  · simp only [hge, ↓reduceIte]
    by_cases hamt : sb.toNat ≥ 16
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [BitVec.truncate_eq_setWidth, show k < sb.toNat by omega]
    · simp only [hamt, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      have hm := getLsbD_0xffff128 ⟨k, by omega⟩; dsimp only at hm
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
        BitVec.getLsbD_shiftLeft, hm, hk, show k < 128 by omega, decide_true, Bool.true_and]
      by_cases hlt : k < sb.toNat
      · simp [hlt]
      · simp [hlt, show k - sb.toNat < 16 by omega, show k - sb.toNat < 128 by omega]
  · simp only [hge, ↓reduceIte]
    by_cases hmsbf : x.msb = false
    · simp only [hmsbf, Bool.not_false, Bool.false_or, ↓reduceIte]
      by_cases hamt : (-sb).toNat ≥ 16
      · simp only [hamt, ↓reduceIte]
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        rw [BitVec.getLsbD_sshiftRight]
        simp [hmsbf, hk, show ¬ ((-sb).toNat + k < 16) by omega]
      · simp only [hamt, ↓reduceIte]
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        rw [BitVec.getLsbD_sshiftRight, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
        by_cases hlt : (-sb).toNat + k < 16
        · simp [hlt, hk, show ¬ (16 ≤ k) by omega, show (-sb).toNat + k < 128 by omega]
        · have hx : x.getLsbD ((-sb).toNat + k) = false :=
            BitVec.getLsbD_of_ge x ((-sb).toNat + k) (by omega)
          simp [hlt, hk, hx, hmsbf, show ¬ (16 ≤ k) by omega, show (-sb).toNat + k < 128 by omega]
    · have hmsbt : x.msb = true := Bool.eq_true_of_not_eq_false hmsbf
      simp only [hmsbt, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hamt : (-sb).toNat ≥ 16
      · simp only [hamt, ↓reduceIte]
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        have hm := getLsbD_0xffff128 ⟨k, by omega⟩; dsimp only at hm
        rw [BitVec.getLsbD_sshiftRight, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
        simp [hm, hmsbt, hk, show ¬ (16 ≤ k) by omega, show ¬ ((-sb).toNat + k < 16) by omega]
      · simp only [hamt, ↓reduceIte]
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        have hm := getLsbD_0xffff128 ⟨k, by omega⟩; dsimp only at hm
        rw [BitVec.getLsbD_sshiftRight, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
        by_cases hlt : (-sb).toNat + k < 16
        · simp [hlt, hm, hk, show ¬ (16 ≤ k) by omega, show (-sb).toNat + k < 128 by omega,
            show k < 16 - (-sb).toNat by omega]
        · have hm2 := getLsbD_0xffff128 ⟨k - (16 - (-sb).toNat), by omega⟩; dsimp only at hm2
          have hx : x.getLsbD ((-sb).toNat + k) = false :=
            BitVec.getLsbD_of_ge x ((-sb).toNat + k) (by omega)
          simp [hlt, hm, hm2, hx, hmsbt, hk, show k < 128 by omega, show ¬ (16 ≤ k) by omega,
            show (-sb).toNat + k < 128 by omega, show ¬ (k < 16 - (-sb).toNat) by omega,
            show k - (16 - (-sb).toNat) < 16 by omega]

@[simp, arm64_norm, wp_norm]
theorem exec_simdCmeqZero_8h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTwoRegMisc true false 0b01#2 0b01001#5 rn rd) s =
      (s.writeVReg128 rd (simdCmeqZero8h (s.readVReg128 rn))).advancePC := by
  simp [execInstWithSvc]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_mapLanes_8, lane16_simdCmeqZero8h]
  set x := lane16 (s.readVReg128 rn) i
  by_cases hx : x = 0#16
  · rw [hx]; rfl
  · have hne : x.zeroExtend 128 ≠ 0#128 := by
      intro h; apply hx; apply BitVec.eq_of_toNat_eq
      have ht := congrArg BitVec.toNat h
      simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 2 ^ 16 < 2 ^ 128)),
        BitVec.toNat_ofNat] at ht
      exact ht
    have hbeq : (x == 0#16) = false := beq_false_of_ne hx
    simp [hne, hbeq]

@[simp, arm64_norm, wp_norm]
theorem exec_simdDup_8h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  simp [execInstWithSvc]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_mapLanes_8, lane16_dup8x16]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hm := getLsbD_0xffff128 ⟨k, by omega⟩; dsimp only at hm
  have hm_eq : (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 := rfl
  try rw [hm_eq]
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth]
  simp [hm, hk, show k < 64 by omega, show k < 128 by omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
