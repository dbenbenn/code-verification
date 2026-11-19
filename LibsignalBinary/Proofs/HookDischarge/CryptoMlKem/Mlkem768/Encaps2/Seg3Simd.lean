/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith

/-!
# `encapsulate2` (`B20`) — Segment 3 AdvSIMD Arithmetic & Lane-Transfer Bridges (`Seg3Simd`)

Provides `@[simp, arm64_norm, wp_norm]` symbolic-execution bridges for arithmetic, immediate,
and GPR↔SIMD lane-transfer instructions in `B20` `[0x0bdc .. 0x10a0]`, plus `State.orFpsr`
preservation for `UnspilledSaved20` and shared `4S` permute definitions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16
  ext_lane16
  lane16
  lane16_dup8x16
  lane16_mapSimdLanes_true_16
  lane16_zipSimdLanes_true_16
  lane32
  lane64
  pack2x64
  pack4x32
  simdLaneSInt_16_zeroExtend
  truncate16_intToSimdLane_16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h
  lane16_simdMla8h
  lane16_simdMul8h
  lane16_simdSqdmulh8h
  lane16_simdSshr8h
  lane16_simdSub8h
  simdAdd8h
  simdMla8h
  simdMul8h
  simdSqdmulh8h
  simdSshr8h
  simdSub8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  sqdmulh16_toInt
  toInt_sshiftRight_16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (UnspilledSaved20)

/-! ## 1. `State.orFpsr` Preservation & Shared `4S` Permute Definitions -/

@[simp, arm64_norm, wp_norm]
theorem unspilledSaved20_orFpsr (s0 s : State) (f : BitVec 32) :
    UnspilledSaved20 s0 (s.orFpsr f) ↔ UnspilledSaved20 s0 s := by
  simp [UnspilledSaved20, State.readReg64_orFpsr]

/-- Saturation-flag payload emitted by `SQDMULH Vd.8H, Vn.8H, Vm.8H` (kept opaque to `simp`). -/
def sqdmulh8hFlags (vn vm : BitVec 128) : BitVec 32 :=
  (evalSimdThreeSameExtSatFlags true false 0b01#2 0b10110#5 vn vm).getD 0#32

/-- `REV64 Vd.4S, Vn.4S`: swap adjacent 32-bit words within each 64-bit doubleword. -/
@[expose] def simdRev64_4s (vn : BitVec 128) : BitVec 128 :=
  pack4x32 fun i => lane32 vn ⟨(i.val / 2) * 2 + (1 - i.val % 2), by omega⟩

@[simp] theorem lane32_simdRev64_4s (vn : BitVec 128) (i : Fin 4) :
    lane32 (simdRev64_4s vn) i = lane32 vn ⟨(i.val / 2) * 2 + (1 - i.val % 2), by omega⟩ := by
  simp [simdRev64_4s]

/-- `UZP1 Vd.4S, Vn.4S, Vm.4S`: even 32-bit words `[Vn[0], Vn[2], Vm[0], Vm[2]]`. -/
@[expose] def simdUzp1_4s (vn vm : BitVec 128) : BitVec 128 :=
  pack4x32 fun i =>
    if h : i.val < 2 then lane32 vn ⟨2 * i.val, by omega⟩
    else lane32 vm ⟨2 * (i.val - 2), by omega⟩

@[simp] theorem lane32_simdUzp1_4s (vn vm : BitVec 128) (i : Fin 4) :
    lane32 (simdUzp1_4s vn vm) i =
      if h : i.val < 2 then lane32 vn ⟨2 * i.val, by omega⟩
      else lane32 vm ⟨2 * (i.val - 2), by omega⟩ := by
  simp [simdUzp1_4s]

@[simp, arm64_norm, wp_norm]
theorem bv128_or_self (v : BitVec 128) : v ||| v = v :=
  BitVec.or_self

/-! ## 2. Arithmetic & Immediate AdvSIMD Bridges -/

private theorem writeV_adv_congr {s : State} {rd : BitVec 5} {a b : BitVec 128} (h : a = b) :
    (s.writeVReg128 rd a).advancePC = (s.writeVReg128 rd b).advancePC :=
  h ▸ rfl

private theorem writeV_fpsr_adv_congr {s : State} {rd : BitVec 5} {f : BitVec 32}
    {a b : BitVec 128} (h : a = b) :
    ((s.writeVReg128 rd a).orFpsr f).advancePC = ((s.writeVReg128 rd b).orFpsr f).advancePC :=
  h ▸ rfl

private theorem lane16_zipLanes_16 (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (zipLanes 16 vn vm f 8) i =
      (f ((lane16 vn i).zeroExtend 128) ((lane16 vm i).zeroExtend 128)).truncate 16 := by
  simp

private theorem lane16_mapLanes_16 (v : BitVec 128)
    (f : BitVec 128 → BitVec 128) (i : Fin 8) :
    lane16 (mapLanes 16 v f 8) i = (f ((lane16 v i).zeroExtend 128)).truncate 16 := by
  simp

private theorem setWidth16_zext128 (v : BitVec 16) :
    (v.zeroExtend 128).setWidth 16 = v := by
  ext k hk
  simp

private theorem setWidth16_zext128_sub (x y : BitVec 16) :
    (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16 = x - y := by
  have h : (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16 + y = x := by
    calc (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16 + y
      _ = (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16 + (y.zeroExtend 128).setWidth 16 := by
          rw [setWidth16_zext128]
      _ = (x.zeroExtend 128 - y.zeroExtend 128 + y.zeroExtend 128).setWidth 16 := by
          rw [← BitVec.setWidth_add _ _ (by decide)]
      _ = x := by rw [BitVec.sub_add_cancel, setWidth16_zext128]
  calc (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16
    _ = (x.zeroExtend 128 - y.zeroExtend 128).setWidth 16 + y - y :=
        (BitVec.add_sub_cancel _ _).symm
    _ = x - y := by rw [h]

@[simp, arm64_norm, wp_norm]
theorem exec_simdAdd_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_simdAdd8h]
  change ((lane16 (s.readVReg128 rn) i).zeroExtend 128 +
      (lane16 (s.readVReg128 rm) i).zeroExtend 128).setWidth 16 = _
  rw [BitVec.setWidth_add _ _ (by decide), setWidth16_zext128, setWidth16_zext128]

@[simp, arm64_norm, wp_norm]
theorem exec_simdSub_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true true 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdSub8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_simdSub8h]
  exact setWidth16_zext128_sub _ _

@[simp, arm64_norm, wp_norm]
theorem exec_simdMul_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b01#2 rm 0b10011#5 rn rd) s =
      (s.writeVReg128 rd (simdMul8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags, applySimdSatResult]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_simdMul8h]
  change ((lane16 (s.readVReg128 rn) i).zeroExtend 128 *
      (lane16 (s.readVReg128 rm) i).zeroExtend 128).setWidth 16 = _
  rw [BitVec.setWidth_mul _ _ (by decide), setWidth16_zext128, setWidth16_zext128]

@[simp, arm64_norm, wp_norm]
theorem exec_simdMla_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b01#2 rm 0b10010#5 rn rd) s =
      (s.writeVReg128 rd
        (simdMla8h (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp [execInstWithSvc, evalSimdThreeSameExt, evalSimdThreeSameExtSatFlags, applySimdSatResult]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_zipLanes_16, lane16_simdMla8h]
  set d := lane16 (s.readVReg128 rd) i
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  change (d.zeroExtend 128 +
      ((x.zeroExtend 128 * y.zeroExtend 128).setWidth 16).zeroExtend 128).setWidth 16 =
    d + x * y
  rw [BitVec.setWidth_mul _ _ (by decide), setWidth16_zext128, setWidth16_zext128,
    BitVec.setWidth_add _ _ (by decide), setWidth16_zext128, setWidth16_zext128]

@[simp, arm64_norm, wp_norm]
theorem exec_simdOrr_16b (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b10#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn ||| s.readVReg128 rm)).advancePC := rfl

private theorem ofInt16_eq_of_toInt {x : BitVec 16} {z : Int} (h : x.toInt = z) :
    BitVec.ofInt 16 z = x := by
  subst h
  exact BitVec.ofInt_toInt

@[simp, arm64_norm, wp_norm]
theorem exec_simdSqdmulh_8h (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdThreeSame true false 0b01#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh8h (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  have hflags : evalSimdThreeSameExtSatFlags true false 0b01#2 0b10110#5
      (s.readVReg128 rn) (s.readVReg128 rm) =
      some (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm)) := rfl
  simp [execInstWithSvc, hflags, evalSimdThreeSameExt, applySimdSatResult]
  refine writeV_fpsr_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_simdSqdmulh8h,
    simdLaneSInt_16_zeroExtend, simdLaneSInt_16_zeroExtend]
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  by_cases hmin : x = 0x8000#16 ∧ y = 0x8000#16
  · rcases hmin with ⟨hx, hy⟩
    rw [hx, hy]
    decide
  · have hsq := sqdmulh16_toInt hmin
    have hx_lo : -32768 ≤ x.toInt := BitVec.le_toInt x
    have hx_hi : x.toInt < 32768 := BitVec.toInt_lt
    have hy_lo : -32768 ≤ y.toInt := BitVec.le_toInt y
    have hy_hi : y.toInt < 32768 := BitVec.toInt_lt
    have hnot_both : ¬ (x.toInt = -32768 ∧ y.toInt = -32768) := by
      intro ⟨hx, hy⟩
      apply hmin
      exact ⟨BitVec.eq_of_toInt_eq (by simpa using hx), BitVec.eq_of_toInt_eq (by simpa using hy)⟩
    have hprod_hi : x.toInt * y.toInt ≤ 32768 * 32767 := by
      by_cases hx0 : x.toInt = -32768
      · have hy' : -32767 ≤ y.toInt := by omega
        nlinarith
      · have hx' : -32767 ≤ x.toInt := by omega
        by_cases hy0 : 0 ≤ y.toInt <;> nlinarith
    have hprod_lo : -(32768 * 32767) ≤ x.toInt * y.toInt := by
      by_cases hy0 : 0 ≤ y.toInt <;> nlinarith
    have hdiv_eq : aslRShr (2 * x.toInt * y.toInt) 16 false = (x.toInt * y.toInt) / 32768 := by
      change (2 * x.toInt * y.toInt) / 65536 = (x.toInt * y.toInt) / 32768
      rw [Int.mul_assoc 2 x.toInt y.toInt]
      omega
    rw [hdiv_eq]
    unfold aslSignedSat
    simp only [show Int.ofNat (1 <<< (16 - 1)) = 32768 from rfl]
    have hgt : ¬ ((x.toInt * y.toInt) / 32768 > 32768 - 1) := by omega
    have hlt : ¬ ((x.toInt * y.toInt) / 32768 < -32768) := by omega
    simp only [hgt, hlt, ↓reduceIte, truncate16_intToSimdLane_16]
    exact ofInt16_eq_of_toInt hsq

private theorem int_ofNat_shiftLeft_eq_pow {sh : Nat} (hsh16 : sh < 16) :
    Int.ofNat (1 <<< sh) = (2 : Int) ^ sh := by
  revert sh hsh16
  decide

private theorem exec_simdSshr_8h_aux (immh : BitVec 4) (immb : BitVec 3) (sh : Nat)
    (h1 : immh ≠ 0#4)
    (h2 : (immh ++ immb).toNat ≥ 16 ∧ ¬ ((immh ++ immb).toNat ≥ 32))
    (hsh : 32 - (immh ++ immb).toNat = sh) (hsh16 : sh < 16)
    (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdImmShift true false immh immb 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) sh)).advancePC := by
  rcases h2 with ⟨hge16, hlt32⟩
  have hlt64 : ¬ ((immh ++ immb).toNat ≥ 64) := by omega
  simp [execInstWithSvc, h1, evalSimdImmShiftNonZeroExt, evalSimdImmShiftNonZeroExtSatFlags,
    applySimdSatResult, hlt64, hlt32, hge16, hsh]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_zipLanes_16, lane16_simdSshr8h, simdLaneSInt_16_zeroExtend]
  set x := lane16 (s.readVReg128 rn) i
  have hasl : aslRShr x.toInt sh false = x.toInt / (2 ^ sh : Int) := by
    unfold aslRShr
    by_cases hz : sh = 0
    · subst hz; simp
    · simp only [beq_iff_eq, hz, Bool.false_eq_true, ↓reduceIte, int_ofNat_shiftLeft_eq_pow hsh16]
  rw [hasl, truncate16_intToSimdLane_16]
  exact ofInt16_eq_of_toInt (toInt_sshiftRight_16 x sh hsh16)

@[simp, arm64_norm, wp_norm]
theorem exec_simdSshr_8h_1 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdImmShift true false 0b0011#4 0b111#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 1)).advancePC :=
  exec_simdSshr_8h_aux 0b0011#4 0b111#3 1 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdSshr_8h_11 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdImmShift true false 0b0010#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 11)).advancePC :=
  exec_simdSshr_8h_aux 0b0010#4 0b101#3 11 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_8h_1024 (rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdImmShift true false 0#4 0#3 0b10100#5 4#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  decide

@[simp, arm64_norm, wp_norm]
theorem exec_simdMvni_8h_f2ff (rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  decide

/-! ## 3. GPR ↔ SIMD Transfer & Lane Insert Bridges -/

private theorem mask_getElem_16_128 (k : Nat) (_hk : k < 128) :
    (65535#128)[k] = decide (k < 16) := by
  have hm : (65535#128) = (BitVec.allOnes 16).setWidth 128 := rfl
  rw [hm, BitVec.getElem_setWidth]
  by_cases h : k < 16
  · rw [BitVec.getLsbD_eq_getElem h, BitVec.getElem_allOnes, decide_eq_true h]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), decide_eq_false h]

private theorem zext64_and_ffff_eq (w : BitVec 64) :
    (w.zeroExtend 128) &&& (1#128 <<< 16 - 1#128) = (w.truncate 16).zeroExtend 128 := by
  ext k hk
  simp only [show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl,
    BitVec.getElem_and, mask_getElem_16_128 k hk]
  rw [BitVec.getElem_setWidth, BitVec.getElem_setWidth]
  simp [Bool.and_comm]

@[simp, arm64_norm, wp_norm]
theorem exec_simdDup_8h_gpr (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc] at hz ⊢
  rw [hz]
  refine writeV_adv_congr ?_
  apply ext_lane16; intro i
  rw [lane16_mapLanes_16, lane16_dup8x16]
  exact setWidth16_zext128 _

@[simp, arm64_norm, wp_norm]
theorem exec_fmov_s_w (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.fmovGprVec false 0b00#2 0b00#2 0b111#3 rn rd) s =
      (s.writeVReg128 rd (((s.readReg64 (Reg.fromZRBits rn)).truncate 32).zeroExtend 128)).advancePC := by
  simp [execInstWithSvc, State.writeVReg32, State.readReg32]

@[simp] theorem lane16_zext32_zero (w : BitVec 64) :
    lane16 (((w.truncate 32).zeroExtend 128)) 0 = w.truncate 16 := by
  ext k hk
  simp [lane16, BitVec.getElem_extractLsb', BitVec.getElem_setWidth,
    show k < 32 by omega, show k < 128 by omega]

private theorem exec_simdIns_h_aux (imm5 : BitVec 5) (idx : Nat)
    (h0 : imm5.extractLsb' 0 4 ≠ 0#4)
    (h1 : imm5.extractLsb' 0 1 ≠ 1#1)
    (h2 : imm5.extractLsb' 0 2 = 2#2)
    (hidx : imm5.toNat >>> 2 = idx)
    (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false imm5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd
        (setSimdLane (s.readVReg128 rd) 16 idx
          (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc, h0, h1, h2, hidx, setSimdLane] at hz ⊢
  rw [hz]
  congr 3
  ext k hk
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases hge : k < idx * 16
  · simp [hge]
  · have hsub : k - idx * 16 < 128 := by omega
    rw [mask_getElem_16_128 (k - idx * 16) hsub]
    by_cases h16 : k - idx * 16 < 16
    · simp [hge, h16]
    · simp [hge, h16]

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h1 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 6#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 1
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 6#5 1 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h2 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 10#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 2
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 10#5 2 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h3 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 14#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 3
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 14#5 3 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h4 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 18#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 4
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 18#5 4 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h5 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 22#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 5
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 22#5 5 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h6 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 26#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 6
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 26#5 6 (by decide) (by decide) (by decide) (by decide) rn rd s

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_h7 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true false 30#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 7
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h_aux 30#5 7 (by decide) (by decide) (by decide) (by decide) rn rd s

private theorem getLsbD_mask64_128 (b : Nat) :
    (18446744073709551615#128).getLsbD b = decide (b < 64) := by
  change (18446744073709551615#128).toNat.testBit b = decide (b < 64)
  have hval : (18446744073709551615#128).toNat = 2 ^ 64 - 1 := rfl
  rw [hval, Nat.testBit_two_pow_sub_one]

@[simp, arm64_norm, wp_norm]
theorem exec_simdIns_d1_d0 (rn rd : BitVec 5) (s : State) :
    execInstWithSvc Syscall.standard (.simdInsDup true true 24#5 0#4 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rd) 0
          else lane64 (s.readVReg128 rn) 0)).advancePC := by
  simp [execInstWithSvc]
  refine writeV_adv_congr ?_
  have hm : (1#128 <<< 64 - 1#128) = 18446744073709551615#128 := rfl
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [getSimdLane, hm]
  change (s.readVReg128 rd &&& 18446744073709551615#128 |||
      (s.readVReg128 rn >>> (0 * 64) &&& 18446744073709551615#128) <<< 64).getLsbD b =
    (lane64 (s.readVReg128 rn) 0 ++ lane64 (s.readVReg128 rd) 0).getLsbD b
  simp only [Nat.zero_mul, BitVec.ushiftRight_zero, lane64, Fin.val_zero,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', getLsbD_mask64_128, hb, decide_true,
    Bool.true_and]
  by_cases h64 : b < 64
  · simp [h64]
  · have hsub : b - 64 < 64 := by omega
    simp [h64, hsub]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
