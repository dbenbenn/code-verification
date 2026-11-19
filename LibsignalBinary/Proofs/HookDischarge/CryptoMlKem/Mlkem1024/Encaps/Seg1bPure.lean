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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop

/-!
# `kyber_encapsulate` (`B07`) — Segment 1b Pure Equivalences & Bridges (`Seg1bPure`)

- `tHatModPoly16` and `neonDeserialize12Mod8h_loadVec12_eq`: NEON modular `deserialize_12`
  matches `Spec.byteDecodeMod 12`.
- `{svc}`-polymorphic AdvSIMD bridges (`cmhs .8h`, `add .8h`, `bic #13, lsl #8`, `movi .2d #0`).
- `1568`-byte `pk` slice decomposition (`ek0..ek3` + `rho`), 128-bit `rho` load split, and
  16-byte-aligned `orr #11` address identities.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 byteDecodeMod)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16
  ext_lane16
  lane16
  lane16_pack8x16
  lane16_zipSimdLanes_true_16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h
  lane16_simdCmhs8h
  simdAdd8h
  simdCmhs8h
  simdTbl16b
  simdUshl8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 (
  lane16_neonDeserialize12Mod8h_eq_byteDecodeMod
  loadVec12
  neonDeserialize12Mod8h
  neonDeserialize12ModStep8h
  neonDeserialize12Raw8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdTbl_16b_1
  exec_simdUshl_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  exec_simdBic_8h_13_lsl8
  exec_simdBic_8h_f0_lsl8
  step_vreg1
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Vec128At
  VecRangeMem
  bytesToVecNat
  pointsToBytes_eq_vecRangeMem
  polyVecNat
)

/-! ## 1. Modular `deserialize_12` Polynomial Equivalence (`tHatModPoly16`) -/

/-- `Poly16` representation of `byteDecodeMod 12 bs` (`tHat[i]` in `Spec.indCpaEncryptWith`). -/
@[expose] def tHatModPoly16 (bs : List (BitVec 8)) : Poly16 :=
  (byteDecodeMod 12 bs).map fun c => BitVec.ofNat 16 c

private theorem getD_drop_take_24 (bs : List (BitVec 8)) (c idx : Nat) (hidx : idx < 24) :
    ((bs.drop (24 * c)).take 24).getD idx 0#8 = bs.getD (24 * c + idx) 0#8 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hidx]

private theorem loadVec12_drop_take_24 (bs : List (BitVec 8)) (c off : Nat) (hoff : off + 12 ≤ 24) :
    loadVec12 ((bs.drop (24 * c)).take 24) off = loadVec12 bs (24 * c + off) := by
  have g (j : Nat) (hj : j < 12) :
      ((bs.drop (24 * c)).take 24).getD (off + j) 0#8 = bs.getD ((24 * c + off) + j) 0#8 := by
    rw [getD_drop_take_24 bs c (off + j) (by omega), Nat.add_assoc]
  unfold loadVec12
  rw [show ((bs.drop (24 * c)).take 24).getD off 0#8 =
        ((bs.drop (24 * c)).take 24).getD (off + 0) 0#8 by simp,
      show bs.getD (24 * c + off) 0#8 = bs.getD ((24 * c + off) + 0) 0#8 by simp,
      g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
      g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide),
      g 8 (by decide), g 9 (by decide), g 10 (by decide), g 11 (by decide)]

private theorem array_getD_map_ofNat16 (xs : Array Nat) (idx : Nat) :
    (xs.map (fun c => BitVec.ofNat 16 c)).getD idx 0#16 = BitVec.ofNat 16 (xs.getD idx 0) := by
  unfold Array.getD
  by_cases h : idx < xs.size <;> simp [h]

theorem neonDeserialize12Mod8h_loadVec12_eq {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (m : Nat) (hm : m < 32) :
    neonDeserialize12Mod8h (loadVec12 bs (12 * m)) = polyVecNat (tHatModPoly16 bs) m := by
  apply ext_lane16; intro j
  rw [polyVecNat, lane16_pack8x16, tHatModPoly16, array_getD_map_ofNat16]
  set c := m / 2
  have hc : c < 16 := by omega
  have hlen : 24 * (c + 1) ≤ bs.length := by omega
  obtain ⟨heven, hodd⟩ := lane16_neonDeserialize12Mod8h_eq_byteDecodeMod bs c hc hlen j
  by_cases hpar : m % 2 = 0
  · have hm_eq : m = 2 * c := by omega
    rw [show 12 * m = 24 * c + 0 by omega,
        ← loadVec12_drop_take_24 bs c 0 (by decide), heven,
        show 16 * c + j.val = 8 * m + j.val by omega]
  · have hm_eq : m = 2 * c + 1 := by omega
    rw [show 12 * m = 24 * c + 12 by omega,
        ← loadVec12_drop_take_24 bs c 12 (by decide), hodd,
        show 16 * c + (8 + j.val) = 8 * m + j.val by omega]

/-! ## 2. `{svc}`-Polymorphic AdvSIMD Bridges for Modular `deserialize_12` -/

@[simp, arm64_norm, wp_norm]
theorem evalSimdModImmExt_bic_8h_13_lsl8 (vd : BitVec 128) :
    evalSimdModImmExt true true 0#3 22#5 13#5 vd =
      .ok (vd &&& 0xf2fff2fff2fff2fff2fff2fff2fff2ff#128) := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
theorem exec_simdCmhs_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b00111#5 rn rd) s =
      (s.writeVReg128 rd (simdCmhs8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq, show (8 <<< (0b01#2).toNat) = 16 from rfl]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdCmhs8h]
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  have hx := x.isLt; have hy := y.isLt
  have hule : BitVec.ule (y.zeroExtend 128) (x.zeroExtend 128) = decide (y.toNat ≤ x.toNat) := by
    simp only [BitVec.ule, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128)]
  rw [hule]
  by_cases hle : y.toNat ≤ x.toNat <;> simp [hle]

@[simp, arm64_norm, wp_norm]
theorem exec_simdAdd_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.false_eq_true,
    decide_false, decide_true, ↓reduceIte, BitVec.reduceEq, show (8 <<< (0b01#2).toNat) = 16 from rfl]
  congr 2
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdAdd8h]
  set x := lane16 (s.readVReg128 rn) i
  set y := lane16 (s.readVReg128 rm) i
  have hx := x.isLt; have hy := y.isLt
  change ((x.zeroExtend 128 + y.zeroExtend 128).setWidth 16) = x + y
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128)]
  omega

/-! ## 3. `1568`-Byte `pk` Decomposition, `rho` Vector Load, & Aligned `orr #11` -/

@[expose] def pkEk0 (pk : List (BitVec 8)) : List (BitVec 8) := pk.take 384
@[expose] def pkEk1 (pk : List (BitVec 8)) : List (BitVec 8) := (pk.drop 384).take 384
@[expose] def pkEk2 (pk : List (BitVec 8)) : List (BitVec 8) := (pk.drop 768).take 384
@[expose] def pkEk3 (pk : List (BitVec 8)) : List (BitVec 8) := (pk.drop 1152).take 384
@[expose] def pkRho (pk : List (BitVec 8)) : List (BitVec 8) := (pk.drop 1536).take 32
@[expose] def rhoW (rho : List (BitVec 8)) (k : Nat) : BitVec 64 := ByteSlice.readLE rho (8 * k) 8

theorem pkEk0_len {pk : List (BitVec 8)} (hpk : pk.length = 1568) : (pkEk0 pk).length = 384 := by
  simp [pkEk0, hpk]
theorem pkEk1_len {pk : List (BitVec 8)} (hpk : pk.length = 1568) : (pkEk1 pk).length = 384 := by
  simp [pkEk1, hpk]
theorem pkEk2_len {pk : List (BitVec 8)} (hpk : pk.length = 1568) : (pkEk2 pk).length = 384 := by
  simp [pkEk2, hpk]
theorem pkEk3_len {pk : List (BitVec 8)} (hpk : pk.length = 1568) : (pkEk3 pk).length = 384 := by
  simp [pkEk3, hpk]
theorem pkRho_len {pk : List (BitVec 8)} (hpk : pk.length = 1568) : (pkRho pk).length = 32 := by
  simp [pkRho, hpk]

theorem pk_pointsTo_split {pkA : BitVec 64} {pk : List (BitVec 8)} (hpk : pk.length = 1568) :
    (pkA ↦ₛ pk) =
      (pkA ↦ₛ pkEk0 pk) ∗ ((pkA + 384#64) ↦ₛ pkEk1 pk) ∗
      ((pkA + 768#64) ↦ₛ pkEk2 pk) ∗ ((pkA + 1152#64) ↦ₛ pkEk3 pk) ∗
      ((pkA + 1536#64) ↦ₛ pkRho pk) := by
  have heq : pk = pkEk0 pk ++ (pkEk1 pk ++ (pkEk2 pk ++ (pkEk3 pk ++ pkRho pk))) := by
    have h4 : pk.drop 1536 = pkRho pk := by
      unfold pkRho; exact (List.take_of_length_le (by simp [hpk])).symm
    have h3 : pk.drop 1152 = pkEk3 pk ++ pkRho pk := by
      rw [← h4, show (1536 : Nat) = 1152 + 384 from rfl, ← List.drop_drop]
      exact (List.take_append_drop 384 (pk.drop 1152)).symm
    have h2 : pk.drop 768 = pkEk2 pk ++ (pkEk3 pk ++ pkRho pk) := by
      rw [← h3, show (1152 : Nat) = 768 + 384 from rfl, ← List.drop_drop]
      exact (List.take_append_drop 384 (pk.drop 768)).symm
    have h1 : pk.drop 384 = pkEk1 pk ++ (pkEk2 pk ++ (pkEk3 pk ++ pkRho pk)) := by
      rw [← h2, show (768 : Nat) = 384 + 384 from rfl, ← List.drop_drop]
      exact (List.take_append_drop 384 (pk.drop 384)).symm
    rw [← h1]
    exact (List.take_append_drop 384 pk).symm
  conv => lhs; rw [heq]
  rw [pointsToBytes_append, pkEk0_len hpk,
      pointsToBytes_append, pkEk1_len hpk,
      pointsToBytes_append, pkEk2_len hpk,
      pointsToBytes_append, pkEk3_len hpk]
  simp only [BitVec.add_assoc]
  rfl

theorem rho_pointsTo_eq_vec128 {addr : BitVec 64} {rho : List (BitVec 8)} (hrho : rho.length = 32) :
    (addr ↦ₛ rho) =
      Vec128At addr (rhoW rho 1 ++ rhoW rho 0) ∗
      Vec128At (addr + 16#64) (rhoW rho 3 ++ rhoW rho 2) := by
  rw [pointsToBytes_eq_vecRangeMem 2 addr hrho]
  simp [VecRangeMem, bytesToVecNat, rhoW, sepConj_emp]

private theorem append_hi60_zero4 {x : BitVec 64} (h : x &&& 15#64 = 0#64) :
    x = x.extractLsb' 4 60 ++ 0#4 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_append]
  by_cases hi4 : i < 4
  · have hbit := congrArg (fun v => v.getLsbD i) h
    have hm : (15#64).getLsbD i = true := by
      rcases i with _ | _ | _ | _ | i <;> first | rfl | omega
    simp only [BitVec.getLsbD_and, hm, Bool.and_true, BitVec.getLsbD_zero] at hbit
    simp [hi4, hbit]
  · rw [BitVec.getLsbD_extractLsb']
    simp [hi4, show i - 4 < 60 by omega, show 4 + (i - 4) = i by omega]

private theorem toNat_append_4 (q : BitVec 60) (r : BitVec 4) :
    (q ++ r : BitVec 64).toNat = q.toNat * 16 + r.toNat := by
  have h1 : (q ++ r : BitVec 64) = (q.zeroExtend 64 <<< 4) + r.zeroExtend 64 := by bv_bits
  have hq := q.isLt; have hr := r.isLt
  rw [h1, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth]
  have hpow : (2 : Nat) ^ 60 * 16 = 2 ^ 64 := rfl
  have hs : (q.toNat % 2 ^ 64) <<< 4 = q.toNat * 16 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
  rw [hs, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem mod16_of_and15 {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) :
    x.toNat % 16 = 0 := by
  have hx := append_hi60_zero4 (eq_of_beq h)
  have ht := congrArg BitVec.toNat hx
  rw [toNat_append_4, show (0#4).toNat = 0 from rfl] at ht
  omega

private theorem or11_eq_add11_of_mod16 {x : BitVec 64} (hmod : x.toNat % 16 = 0) :
    (x ||| 11#64) = x + 11#64 := by
  have hxlt := x.isLt
  let q : BitVec 60 := BitVec.ofNat 60 (x.toNat / 16)
  have hq_nat : q.toNat = x.toNat / 16 := by
    dsimp [q]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx_eq : x = (q ++ 0#4 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_append_4, hq_nat, show (0#4).toNat = 0 from rfl]; omega
  have hor : ((q ++ 0#4 : BitVec 64) ||| 11#64) = (q ++ 11#4 : BitVec 64) := by bv_bits
  have hadd : (q ++ 0#4 : BitVec 64) + 11#64 = (q ++ 11#4 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    have hqlt := q.isLt
    rw [BitVec.toNat_add, toNat_append_4, toNat_append_4,
      show (0#4).toNat = 0 from rfl, show (11#4).toNat = 11 from rfl,
      show (11#64).toNat = 11 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [hx_eq, hor, hadd]

theorem sp_add_28848_or_11 {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 28672#64 + 176#64) ||| 11#64) = sp + 28859#64 := by
  have hm0 := mod16_of_and15 hsp
  have ha : sp + 28672#64 + 176#64 = sp + 28848#64 := by bv_omega
  have hm : (sp + 28848#64).toNat % 16 = 0 := by
    have hsplt := sp.isLt
    rw [BitVec.toNat_add, show (28848#64).toNat = 28848 from rfl]
    omega
  rw [ha, or11_eq_add11_of_mod16 hm]
  bv_omega

theorem sp_add_26768_or_11 {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 24576#64 + 2192#64) ||| 11#64) = sp + 26779#64 := by
  have hm0 := mod16_of_and15 hsp
  have ha : sp + 24576#64 + 2192#64 = sp + 26768#64 := by bv_omega
  have hm : (sp + 26768#64).toNat % 16 = 0 := by
    have hsplt := sp.isLt
    rw [BitVec.toNat_add, show (26768#64).toNat = 26768 from rfl]
    omega
  rw [ha, or11_eq_add11_of_mod16 hm]
  bv_omega

/-! ## 4. O(1) 12-Byte Load & 12-Instruction Modular `deserialize_12` Step Helpers -/

def rawLo64 (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  pack64 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8)
    (bs.getD (off + 3) 0#8) (bs.getD (off + 4) 0#8) (bs.getD (off + 5) 0#8)
    (bs.getD (off + 6) 0#8) (bs.getD (off + 7) 0#8)

def deserModTmp (v : BitVec 128) : BitVec 128 :=
  simdCmhs8h (neonDeserialize12Raw8h v) (dup8x16 3329#16) &&& dup8x16 0xf2ff#16

theorem step_ldrD64_raw {prog : Program} {target_pc base : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (vt : BitVec 5) (addr : AddrMode) (off : Nat)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (base + BitVec.ofNat 64 off, none))
    (hoff : off + 8 ≤ bs.length) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt ((rawLo64 bs off).zeroExtend 128)).setPC (b + BitVec.ofNat 64 nextOff))
      ((base ↦ₛ bs) ∗ F) post) :
    SepWP prog target_pc s ((base ↦ₛ bs) ∗ F) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hload : SepLoad64 (base + BitVec.ofNat 64 off) ((base ↦ₛ bs) ∗ F) (rawLo64 bs off) := by
    simpa only [rawLo64] using (SepLoad64.of_pointsToBytes (off := off) rfl hoff rfl :
      SepLoad64 (base + BitVec.ofNat 64 off) ((base ↦ₛ bs) ∗ F) _)
  exact SepWP.step_ldrSimd64 hpc hrun hfetch hsp haddr hload (by simp [applyWriteback, hpc']) hnext

theorem step_ld1S2_load {prog : Program} {target_pc base : BitVec 64}
    {s : State} {bs : List (BitVec 8)} {F : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rn : Reg) (vt : BitVec 5) (off : Nat)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.simdLdSt1Single true true false 0#5 0x4#3 false 0x0#2 rn vt))
    (hsp : checkRegSPAligned s rn = true)
    (hea : s.readReg64 rn = base + BitVec.ofNat 64 (off + 8))
    (hlo : s.readVReg128 vt = (rawLo64 bs off).zeroExtend 128)
    (hoff : off + 12 ≤ bs.length) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (loadVec12 bs off)).setPC (b + BitVec.ofNat 64 nextOff))
      ((base ↦ₛ bs) ∗ F) post) :
    SepWP prog target_pc s ((base ↦ₛ bs) ∗ F) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  let hi := pack32 (bs.getD (off + 8) 0#8) (bs.getD (off + 9) 0#8)
    (bs.getD (off + 10) 0#8) (bs.getD (off + 11) 0#8)
  have hload : SepLoad32 (base + BitVec.ofNat 64 (off + 8)) ((base ↦ₛ bs) ∗ F) hi := by
    simpa only [hi, Nat.add_assoc] using (SepLoad32.of_pointsToBytes (off := off + 8) rfl (by omega) rfl :
      SepLoad32 (base + BitVec.ofNat 64 (off + 8)) ((base ↦ₛ bs) ∗ F) _)
  exact step_simdLd1Single32 hpc hrun hfetch hsp hea hload
    (by simp [simdLdSt1SingleLaneIdx, hlo, rawLo64, loadVec12, hi, hpc']) hnext

theorem step_deser12_simd12_gen {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (p0 : Nat) (vsh vq : BitVec 5)
    (hne_sh2 : vsh ≠ 2#5) (hne_sh3 : vsh ≠ 3#5)
    (hne_q2 : vq ≠ 2#5) (hne_q3 : vq ≠ 3#5) (hne_q4 : vq ≠ 4#5)
    (hpc : s.pc = b + BitVec.ofNat 64 p0) (hrun : s.status = .Running)
    (hv_sh : s.readVReg128 vsh = 0xfffc0000fffc0000fffc0000fffc0000#128)
    (hv_q : s.readVReg128 vq = dup8x16 3329#16)
    (hv6 : s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128)
    (hf0 : prog.fetch (b + BitVec.ofNat 64 p0) = some (.simdTbl true 6#5 0#2 false 2#5 2#5))
    (hf1 : prog.fetch (b + BitVec.ofNat 64 (p0 + 4)) = some (.simdTbl true 6#5 0#2 false 3#5 3#5))
    (hf2 : prog.fetch (b + BitVec.ofNat 64 (p0 + 8)) = some (.simdThreeSame true true 0b01#2 vsh 0b01000#5 2#5 2#5))
    (hf3 : prog.fetch (b + BitVec.ofNat 64 (p0 + 12)) = some (.simdThreeSame true true 0b01#2 vsh 0b01000#5 3#5 3#5))
    (hf4 : prog.fetch (b + BitVec.ofNat 64 (p0 + 16)) = some (.simdImmShift true true 0#4 7#3 0b10110#5 16#5 2#5))
    (hf5 : prog.fetch (b + BitVec.ofNat 64 (p0 + 20)) = some (.simdImmShift true true 0#4 7#3 0b10110#5 16#5 3#5))
    (hf6 : prog.fetch (b + BitVec.ofNat 64 (p0 + 24)) = some (.simdThreeSame true true 0b01#2 vq 0b00111#5 2#5 4#5))
    (hf7 : prog.fetch (b + BitVec.ofNat 64 (p0 + 28)) = some (.simdThreeSame true true 0b01#2 vq 0b00111#5 3#5 5#5))
    (hf8 : prog.fetch (b + BitVec.ofNat 64 (p0 + 32)) = some (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 4#5))
    (hf9 : prog.fetch (b + BitVec.ofNat 64 (p0 + 36)) = some (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 5#5))
    (hf10 : prog.fetch (b + BitVec.ofNat 64 (p0 + 40)) = some (.simdThreeSame true false 0b01#2 2#5 0b10000#5 4#5 2#5))
    (hf11 : prog.fetch (b + BitVec.ofNat 64 (p0 + 44)) = some (.simdThreeSame true false 0b01#2 3#5 0b10000#5 5#5 3#5))
    (hnext : SepWP prog target_pc
      (((((s.writeVReg128 4#5 (deserModTmp (s.readVReg128 2#5))).writeVReg128 5#5
          (deserModTmp (s.readVReg128 3#5))).writeVReg128 2#5
          (neonDeserialize12Mod8h (s.readVReg128 2#5))).writeVReg128 3#5
          (neonDeserialize12Mod8h (s.readVReg128 3#5))).setPC (b + BitVec.ofNat 64 (p0 + 48))) P post) :
    SepWP prog target_pc s P post := by
  have hm0fff : (0x0fff0fff0fff0fff0fff0fff0fff0fff#128) = dup8x16 0x0fff#16 := rfl
  have hmf2ff : (0xf2fff2fff2fff2fff2fff2fff2fff2ff#128) = dup8x16 0xf2ff#16 := rfl
  let v2 := s.readVReg128 2#5
  let v3 := s.readVReg128 3#5
  let t2 := simdTbl16b v2 0x0b0a0a09080707060504040302010100#128
  let t3 := simdTbl16b v3 0x0b0a0a09080707060504040302010100#128
  let u2 := simdUshl8h t2 0xfffc0000fffc0000fffc0000fffc0000#128
  let u3 := simdUshl8h t3 0xfffc0000fffc0000fffc0000fffc0000#128
  let m2 := neonDeserialize12Raw8h v2
  let m3 := neonDeserialize12Raw8h v3
  let c2 := simdCmhs8h m2 (dup8x16 3329#16)
  let c3 := simdCmhs8h m3 (dup8x16 3329#16)
  refine step_vreg1 b p0 (p0 + 4) 2#5 t2 hpc hrun hf0
    (by rw [exec_simdTbl_16b_1]; simp [hv6, t2, v2]) rfl ?_
  refine step_vreg1 b (p0 + 4) (p0 + 8) 3#5 t3 rfl (by simp [hrun]) hf1
    (by rw [exec_simdTbl_16b_1]; simp [hv6, t3, v3]) (by omega) ?_
  refine step_vreg1 b (p0 + 8) (p0 + 12) 2#5 u2 rfl (by simp [hrun]) hf2
    (by rw [exec_simdUshl_8h]; simp [hne_sh2, hne_sh3, hv_sh, u2]) (by omega) ?_
  refine step_vreg1 b (p0 + 12) (p0 + 16) 3#5 u3 rfl (by simp [hrun]) hf3
    (by rw [exec_simdUshl_8h]; simp [hne_sh2, hne_sh3, hv_sh, u3]) (by omega) ?_
  refine step_vreg1 b (p0 + 16) (p0 + 20) 2#5 m2 rfl (by simp [hrun]) hf4
    (by rw [exec_simdBic_8h_f0_lsl8, hm0fff]; simp [m2, neonDeserialize12Raw8h, u2, t2]) (by omega) ?_
  refine step_vreg1 b (p0 + 20) (p0 + 24) 3#5 m3 rfl (by simp [hrun]) hf5
    (by rw [exec_simdBic_8h_f0_lsl8, hm0fff]; simp [m3, neonDeserialize12Raw8h, u3, t3]) (by omega) ?_
  refine step_vreg1 b (p0 + 24) (p0 + 28) 4#5 c2 rfl (by simp [hrun]) hf6
    (by rw [exec_simdCmhs_8h_svc]; simp [hne_q2, hne_q3, hv_q, c2]) (by omega) ?_
  refine step_vreg1 b (p0 + 28) (p0 + 32) 5#5 c3 rfl (by simp [hrun]) hf7
    (by rw [exec_simdCmhs_8h_svc]; simp [hne_q2, hne_q3, hne_q4, hv_q, c3]) (by omega) ?_
  refine step_vreg1 b (p0 + 32) (p0 + 36) 4#5 (deserModTmp v2) rfl (by simp [hrun]) hf8
    (by rw [exec_simdBic_8h_13_lsl8, hmf2ff]; simp [deserModTmp, c2, m2]) (by omega) ?_
  refine step_vreg1 b (p0 + 36) (p0 + 40) 5#5 (deserModTmp v3) rfl (by simp [hrun]) hf9
    (by rw [exec_simdBic_8h_13_lsl8, hmf2ff]; simp [deserModTmp, c3, m3]) (by omega) ?_
  refine step_vreg1 b (p0 + 40) (p0 + 44) 2#5 (neonDeserialize12Mod8h v2) rfl (by simp [hrun]) hf10
    (by rw [exec_simdAdd_8h_svc]; simp [neonDeserialize12Mod8h, neonDeserialize12ModStep8h, deserModTmp, m2])
    (by omega) ?_
  refine step_vreg1 b (p0 + 44) (p0 + 48) 3#5 (neonDeserialize12Mod8h v3) rfl (by simp [hrun]) hf11
    (by rw [exec_simdAdd_8h_svc]; simp [neonDeserialize12Mod8h, neonDeserialize12ModStep8h, deserModTmp, m3])
    (by omega) ?_
  refine SepWP.congr_state ?_ hnext
  dsimp only [v2, v3]
  cases s; simp only [State.writeVReg128, State.setPC, VRegFile.write]
  congr 1; congr 1; funext r
  by_cases h3 : r = 3#5; · subst h3; rfl
  by_cases h2 : r = 2#5; · subst h2; rfl
  by_cases h5 : r = 5#5; · subst h5; rfl
  by_cases h4 : r = 4#5; · subst h4; rfl
  simp [h3, h2, h5, h4]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
