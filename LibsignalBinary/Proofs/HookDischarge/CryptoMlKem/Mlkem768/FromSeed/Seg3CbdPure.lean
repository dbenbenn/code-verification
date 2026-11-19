/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base

/-!
# `generate_keypair_compressed` (`B05`): pure `CBD_2`, PRF staging, and zeta spill helpers

Shared pure and separation-logic lemmas for `sHat` and `eHat` PRF staging, SWAR `cbd2`,
24-vector `Fwd2` zeta spills, and `cbdNttPoly16` soundness.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  getLsbD_evalBitfield_w32_ubfm)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 polyNtt samplePolyCbd2 shake256 shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord cbd2SwarSum neonCbd2Poly16 neonCbd2Poly16_spec readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 lane16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  neonPolyNttBinomial16 neonPolyNttBinomial16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Vec128At VecRangeMem bytesToVecNat polyVecNat pointsToBytes_eq_vecRangeMem vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem halfRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (Spill40)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  cell_entails_memRegion8)

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

private theorem unpack32_append4 (b3 b2 b1 b0 : BitVec 8) :
    unpack32 (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  simp only [unpack32]
  refine congrArg₂ List.cons (by bv_bits)
    (congrArg₂ List.cons (by bv_bits)
      (congrArg₂ List.cons (by bv_bits)
        (congrArg₂ List.cons (by bv_bits) rfl)))

private theorem readU32LE_unpack (bs : List (BitVec 8)) (w : Nat) (hw : 4 * (w + 1) ≤ bs.length) :
    unpack32 (readU32LE bs w) = (bs.drop (4 * w)).take 4 := by
  unfold readU32LE
  rw [unpack32_append4]
  rcases hdrop : bs.drop (4 * w) with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, tl⟩⟩⟩⟩
  · have := congrArg List.length hdrop; simp at this; omega
  · have := congrArg List.length hdrop; simp at this; omega
  · have := congrArg List.length hdrop; simp at this; omega
  · have := congrArg List.length hdrop; simp at this; omega
  · have hget (j : Nat) (hj : j < 4) : (bs.toArray).getD (4 * w + j) 0#8 =
        (x0 :: x1 :: x2 :: x3 :: tl).getD j 0#8 := by
      have h1 : (bs.toArray).getD (4 * w + j) 0#8 = (bs[4 * w + j]?).getD 0#8 := by
        simp [Array.getD, show 4 * w + j < bs.length by omega]
      rw [h1, ← List.getElem?_drop, hdrop, List.getD_eq_getElem?_getD]
    have h0 := hget 0 (by omega)
    have h1 := hget 1 (by omega)
    have h2 := hget 2 (by omega)
    have h3 := hget 3 (by omega)
    simp only [Nat.add_zero] at h0
    simp [h0, h1, h2, h3]

theorem wordRangeMem_readU32LE_take (n : Nat) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hle : 4 * n ≤ bs.length) :
    WordRangeMem n ptr (readU32LE bs) = (ptr ↦ₛ bs.take (4 * n)) := by
  induction n with
  | zero => simp [WordRangeMem, pointsToBytes_nil]
  | succ n ih =>
    have htake : bs.take (4 * (n + 1)) = bs.take (4 * n) ++ (bs.drop (4 * n)).take 4 := by
      rw [show 4 * (n + 1) = 4 * n + 4 by omega, List.take_add]
    have hlen : (bs.take (4 * n)).length = 4 * n := List.length_take_of_le (by omega)
    simp only [WordRangeMem, ih (by omega), pointsTo32_eq_pointsToBytes, readU32LE_unpack bs n hle]
    rw [htake, pointsToBytes_append, hlen]

theorem wordRangeMem32_eq_pointsToBytes (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 128) :
    WordRangeMem 32 ptr (readU32LE bs) = (ptr ↦ₛ bs) := by
  rw [wordRangeMem_readU32LE_take 32 ptr (by omega), List.take_of_length_le (by omega)]

theorem vec2_bytesToVecNat_eq (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    Vec128At ptr (bytesToVecNat bs 0) ∗ Vec128At (ptr + 16#64) (bytesToVecNat bs 1) =
      (ptr ↦ₛ bs) := by
  have hv := pointsToBytes_eq_vecRangeMem 2 ptr h
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  exact hv.symm

theorem stage_prf33_eq (ptr : BitVec 64) {coins : List (BitVec 8)} (n : BitVec 8)
    (hc : coins.length = 32) :
    Vec128At ptr (bytesToVecNat coins 0) ∗ Vec128At (ptr + 16#64) (bytesToVecNat coins 1) ∗
      ((ptr + 32#64) ↦₈ n) = (ptr ↦ₛ (coins ++ [n])) := by
  rw [← sepConj_assoc, vec2_bytesToVecNat_eq ptr hc, pointsToBytes_append, hc, pointsToBytes_singleton]

theorem vec128At_eq_eight_16 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v =
      ((ptr ↦₁₆ lane16 v 0) ∗ ((ptr + 2#64) ↦₁₆ lane16 v 1) ∗
       ((ptr + 4#64) ↦₁₆ lane16 v 2) ∗ ((ptr + 6#64) ↦₁₆ lane16 v 3) ∗
       ((ptr + 8#64) ↦₁₆ lane16 v 4) ∗ ((ptr + 10#64) ↦₁₆ lane16 v 5) ∗
       ((ptr + 12#64) ↦₁₆ lane16 v 6) ∗ ((ptr + 14#64) ↦₁₆ lane16 v 7)) := by
  have hbyte (base : Nat) (hb : base = 0 ∨ base = 64) (j : Nat) (_hj : j < 8) :
      ((v.extractLsb' base 64) >>> (8 * j)).setWidth 8 =
        ((lane16 v ⟨base / 16 + j / 2, by rcases hb with rfl | rfl <;> omega⟩) >>>
          (8 * (j % 2))).setWidth 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rcases hb with rfl | rfl <;>
    (simp only [lane16, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
       BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
     rw [decide_eq_true (by omega : 8 * j + i < 64),
         decide_eq_true (by omega : 8 * (j % 2) + i < 16)]
     simp only [Bool.true_and]; congr 1; omega)
  have hlo : unpack64 (v.extractLsb' 0 64) =
      unpack16 (lane16 v 0) ++ unpack16 (lane16 v 1) ++
      unpack16 (lane16 v 2) ++ unpack16 (lane16 v 3) := by
    simp only [unpack64, unpack16, List.cons_append, List.nil_append]
    exact congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 0 (by omega))
      (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 1 (by omega))
        (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 2 (by omega))
          (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 3 (by omega))
            (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 4 (by omega))
              (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 5 (by omega))
                (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 6 (by omega))
                  (congrArg₂ List.cons (hbyte 0 (Or.inl rfl) 7 (by omega)) rfl)))))))
  have hhi : unpack64 (v.extractLsb' 64 64) =
      unpack16 (lane16 v 4) ++ unpack16 (lane16 v 5) ++
      unpack16 (lane16 v 6) ++ unpack16 (lane16 v 7) := by
    simp only [unpack64, unpack16, List.cons_append, List.nil_append]
    exact congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 0 (by omega))
      (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 1 (by omega))
        (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 2 (by omega))
          (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 3 (by omega))
            (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 4 (by omega))
              (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 5 (by omega))
                (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 6 (by omega))
                  (congrArg₂ List.cons (hbyte 64 (Or.inr rfl) 7 (by omega)) rfl)))))))
  simp only [Vec128At, pointsTo64_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, hlo, hhi,
    List.append_assoc, pointsToBytes_append, unpack16_length, sepConj_assoc,
    show ptr + 2#64 + 2#64 = ptr + 4#64 by bv_omega,
    show ptr + 4#64 + 2#64 = ptr + 6#64 by bv_omega,
    show ptr + 8#64 + 2#64 = ptr + 10#64 by bv_omega,
    show ptr + 10#64 + 2#64 = ptr + 12#64 by bv_omega,
    show ptr + 12#64 + 2#64 = ptr + 14#64 by bv_omega]

theorem eight_16_eq_vec128At_cbd2 (ptr : BitVec 64) (bs : List (BitVec 8)) (k : Nat) (hk : k < 32) :
    let w := readU32LE bs k
    ((ptr ↦₁₆ cbd2CoeffFromWord w 0) ∗ ((ptr + 2#64) ↦₁₆ cbd2CoeffFromWord w 1) ∗
     ((ptr + 4#64) ↦₁₆ cbd2CoeffFromWord w 2) ∗ ((ptr + 6#64) ↦₁₆ cbd2CoeffFromWord w 3) ∗
     ((ptr + 8#64) ↦₁₆ cbd2CoeffFromWord w 4) ∗ ((ptr + 10#64) ↦₁₆ cbd2CoeffFromWord w 5) ∗
     ((ptr + 12#64) ↦₁₆ cbd2CoeffFromWord w 6) ∗ ((ptr + 14#64) ↦₁₆ cbd2CoeffFromWord w 7)) =
      Vec128At ptr (polyVecNat (neonCbd2Poly16 bs) k) := by
  intro w
  rw [vec128At_eq_eight_16]
  have hlane (j : Fin 8) : lane16 (polyVecNat (neonCbd2Poly16 bs) k) j = cbd2CoeffFromWord w j := by
    unfold polyVecNat
    rw [lane16_pack8x16]
    have hdiv : (8 * k + j.val) / 8 = k := by omega
    with_unfolding_all simp [neonCbd2Poly16, Array.getD, show 8 * k + j.val < 256 by omega, hdiv]
    exact congrArg (cbd2CoeffFromWord (readU32LE bs k)) (Fin.ext (Nat.mod_eq_of_lt j.isLt))
  simp only [hlane 0, hlane 1, hlane 2, hlane 3, hlane 4, hlane 5, hlane 6, hlane 7]

theorem vec128At_eq_halfRangeMem8 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v = HalfRangeMem 8 ptr (fun j => lane16 v ⟨j % 8, Nat.mod_lt _ (by decide)⟩) := by
  rw [vec128At_eq_eight_16]
  dsimp only [HalfRangeMem]
  simp only [sepConj_emp,
    show ptr + 2#64 + 2#64 = ptr + 4#64 by bv_omega,
    show ptr + 4#64 + 2#64 = ptr + 6#64 by bv_omega,
    show ptr + 6#64 + 2#64 = ptr + 8#64 by bv_omega,
    show ptr + 8#64 + 2#64 = ptr + 10#64 by bv_omega,
    show ptr + 10#64 + 2#64 = ptr + 12#64 by bv_omega,
    show ptr + 12#64 + 2#64 = ptr + 14#64 by bv_omega]
  rfl

theorem halfRangeMem8_cbd2_eq (ptr : BitVec 64) (bs : List (BitVec 8)) (k : Nat) (hk : k < 32)
    (h : Nat → BitVec 16)
    (hh : ∀ j (hj : j < 8), h j = cbd2CoeffFromWord (readU32LE bs k) ⟨j, hj⟩) :
    HalfRangeMem 8 ptr h = Vec128At ptr (polyVecNat (neonCbd2Poly16 bs) k) := by
  rw [halfRangeMem_congr (g := fun j =>
      cbd2CoeffFromWord (readU32LE bs k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩)
      (fun j hj => by rw [hh j hj]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt hj).symm),
    ← eight_16_eq_vec128At_cbd2 ptr bs k hk]
  dsimp only [HalfRangeMem]
  simp only [sepConj_emp,
    show ptr + 2#64 + 2#64 = ptr + 4#64 by bv_omega,
    show ptr + 4#64 + 2#64 = ptr + 6#64 by bv_omega,
    show ptr + 6#64 + 2#64 = ptr + 8#64 by bv_omega,
    show ptr + 8#64 + 2#64 = ptr + 10#64 by bv_omega,
    show ptr + 10#64 + 2#64 = ptr + 12#64 by bv_omega,
    show ptr + 12#64 + 2#64 = ptr + 14#64 by bv_omega]
  rfl

theorem ubfx2_w32 (dst : BitVec 64) (d : BitVec 32) (r : Nat)
    (hr : decide (r ≤ 28) = true := by decide) :
    (evalBitfield .W32 .UBFM dst (d.zeroExtend 64) r (r + 1)).truncate 32 =
      (d >>> r) &&& 3#32 := by
  have hr28 : r ≤ 28 := of_decide_eq_true hr
  have hmask : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val ≤ 1) := by
    decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and,
    getLsbD_evalBitfield_w32_ubfm dst (d.setWidth 64) r (r + 1) i (decide_eq_true (by omega)),
    ↓reduceIte, show r ≤ r + 1 by omega, show r + 1 - r = 1 by omega,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hmask ⟨i, hi⟩]
  by_cases hi1 : i ≤ 1
  · simp [hi1, show r + i < 64 by omega]
  · simp [hi1]

@[simp, arm64_norm, wp_norm]
theorem ubfx2_w32_norm (dst : BitVec 64) (d : BitVec 32) (r s : Nat)
    (hs : decide (s = r + 1 ∧ r ≤ 28) = true := by decide) :
    setWidth 32 (evalBitfield .W32 .UBFM dst (setWidth 64 d) r s) = (d >>> r) &&& 3#32 := by
  have ⟨hsr, hr28⟩ := of_decide_eq_true hs
  subst hsr; exact ubfx2_w32 dst d r (decide_eq_true hr28)

@[simp, arm64_norm, wp_norm]
theorem truncate32_zext64 (w : BitVec 32) : setWidth 32 (setWidth 64 w) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

@[simp, arm64_norm, wp_norm]
theorem setWidth32_shr_zext64 (w : BitVec 32) (s : Nat) :
    setWidth 32 (setWidth 64 w >>> s) = w >>> s := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hs : s + i < 32
  · simp [hi, show s + i < 64 by omega]
  · simp [hi, BitVec.getLsbD_of_ge w (s + i) (by omega)]

theorem cbd2_swar_eq (t : BitVec 32) :
    (0x55555555#32 &&& (t >>> 1)) + (t &&& 0x55555555#32) = cbd2SwarSum t := by
  unfold cbd2SwarSum; rw [BitVec.and_comm 0x55555555#32 (t >>> 1)]

theorem cbd2_j3_eq (d : BitVec 32) :
    (((d >>> 12) &&& 3#32) - ((d &&& 0xc000#32) >>> 14)).setWidth 16 =
      (((d >>> 12) &&& 3#32) - ((d >>> 14) &&& 3#32)).setWidth 16 := by
  have hm1 : ∀ idx : Fin 32, (0xc000#32 : BitVec 32).getLsbD (14 + idx.val) = decide (idx.val < 2) := by
    decide
  have hm2 : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val < 2) := by decide
  have h : (d &&& 0xc000#32) >>> 14 = (d >>> 14) &&& 3#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm1 ⟨i, hi⟩, hm2 ⟨i, hi⟩]
  rw [h]

theorem cbd2_j7_eq (d : BitVec 32) :
    (((d >>> 28) &&& 3#32) - (d >>> 30)).setWidth 16 =
      (((d >>> 28) &&& 3#32) - ((d >>> 30) &&& 3#32)).setWidth 16 := by
  have hm : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val < 2) := by decide
  have h : d >>> 30 = (d >>> 30) &&& 3#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm ⟨i, hi⟩]
    by_cases hi2 : i < 2
    · rw [decide_eq_true hi2]; simp
    · rw [decide_eq_false hi2, BitVec.getLsbD_of_ge d (30 + i) (by omega)]; simp
  conv_lhs => rw [h]

theorem shake256List_length (n : Nat) (msg : List (BitVec 8)) :
    (shake256List n msg).length = n := by
  with_unfolding_all exact (shake256 n msg).2

theorem vecRangeMem_focus {n k : Nat} (hk : k < n) (ptr : BitVec 64) (f : Nat → BitVec 128) :
    ∃ Fk : SepProp,
      VecRangeMem n ptr f = Vec128At (ptr + BitVec.ofNat 64 (16 * k)) (f k) ∗ Fk ∧
      ∀ v' : BitVec 128,
        Vec128At (ptr + BitVec.ofNat 64 (16 * k)) v' ∗ Fk =
          VecRangeMem n ptr (Function.update f k v') := by
  induction n generalizing k ptr f with
  | zero => omega
  | succ n ih =>
    rcases k with _ | k
    · refine ⟨VecRangeMem n (ptr + 16#64) (fun i => f (i + 1)), ?_, fun v' => ?_⟩
      · simp [VecRangeMem]
      · have htail : VecRangeMem n (ptr + 16#64) (fun i => Function.update f 0 v' (i + 1)) =
            VecRangeMem n (ptr + 16#64) (fun i => f (i + 1)) :=
          vecRangeMem_congr fun i _ => Function.update_of_ne (Nat.succ_ne_zero i) v' f
        dsimp only [VecRangeMem]
        have hz : ptr + BitVec.ofNat 64 (16 * 0) = ptr := by simp
        rw [hz, Function.update_self, htail]
    · obtain ⟨Fk, hsplit, hupd⟩ := ih (k := k) (by omega) (ptr + 16#64) (fun i => f (i + 1))
      have ha : (ptr + 16#64) + BitVec.ofNat 64 (16 * k) = ptr + BitVec.ofNat 64 (16 * (k + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [ha] at hsplit hupd
      refine ⟨Vec128At ptr (f 0) ∗ Fk, ?_, fun v' => ?_⟩
      · dsimp only [VecRangeMem]
        rw [hsplit, ← sepConj_assoc, sepConj_comm (Vec128At ptr (f 0)), sepConj_assoc]
      · have hhead : Function.update f (k + 1) v' 0 = f 0 :=
          Function.update_of_ne (Nat.succ_ne_zero k).symm v' f
        have htail : (fun i => Function.update f (k + 1) v' (i + 1)) =
            Function.update (fun i => f (i + 1)) k v' := by
          funext i; by_cases h : i = k
          · subst h; simp
          · simp [Function.update_of_ne h, Function.update_of_ne (show i + 1 ≠ k + 1 by omega)]
        dsimp only [VecRangeMem]
        rw [hhead, htail, ← hupd v', ← sepConj_assoc,
          sepConj_comm (Vec128At (ptr + BitVec.ofNat 64 (16 * (k + 1))) v'), sepConj_assoc]

theorem orr_1_of_aligned16 (x : BitVec 64) (hx : (x &&& 15#64 == 0#64) = true) :
    (x ||| 1#64) = x + 1#64 := by
  have hx0 : x &&& 15#64 = 0#64 := of_decide_eq_true hx
  have h15 : (15#64 &&& 1#64 : BitVec 64) = 1#64 := by decide
  have hdisj : x &&& 1#64 = 0#64 := by rw [← h15, ← BitVec.and_assoc, hx0]; decide
  exact (BitVec.add_eq_or_of_and_eq_zero x 1#64 hdisj).symm

theorem sepWP_elim_byte {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ b0 : BitVec 8, SepWP prog target s ((a ↦₈ b0) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  apply SepWP.memRegion_bytes a 1 (by decide) rfl
  rintro (_ | ⟨b0, _ | _⟩) hlen <;> try simp at hlen
  simpa using h b0

theorem setPC_setMem_setPC (s : State) (p1 p2 : BitVec 64) (m : Memory) :
    ((s.setPC p1).setMem m).setPC p2 = (s.setPC p2).setMem m := by cases s; rfl

theorem setMem_setMem (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl

theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  rw [memRegion_split' (b := sPtr) (b' := sPtr + 8#64) (n := 8) (k := (24 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sPtr + 8#64) (b' := sPtr + 16#64) (n := 8) (k := (16 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sPtr + 16#64) (b' := sPtr + 24#64) (n := 8) (k := (8 : Nat))
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)))

@[expose] def setSpillZetas (t : Spill40) : Spill40 :=
  ⟨dup8x16 0xd43e#16, dup8x16 0xfa3e#16, dup8x16 0x054e#16, dup8x16 0xfb4e#16,
   dup8x16 0x29c2#16, dup8x16 0x03c2#16, dup8x16 0xc2b6#16, dup8x16 0xf129#16,
   dup8x16 0x0629#16, dup8x16 0x6c6e#16, dup8x16 0x026e#16, dup8x16 0xae55#16,
   dup8x16 0xbeca#16, dup8x16 0x6e1f#16, dup8x16 0x011f#16, dup8x16 0xcf8e#16,
   dup8x16 0x058e#16, dup8x16 0x34d5#16, dup8x16 0x05d5#16, dup8x16 0x0313#16,
   dup8x16 0xfa13#16, dup8x16 0x3999#16, dup8x16 0xfe99#16, dup8x16 0xf9c0#16,
   t.s24, t.s25, t.s26, t.s27, t.s28, t.s29, t.s30, t.s31,
   t.s32, t.s33, t.s34, t.s35, t.s36, t.s37, t.s38, t.s39⟩

@[expose] def cbdNttPoly16 (prf : List (BitVec 8)) : Poly16 :=
  neonPolyNttBinomial16 (neonCbd2Poly16 prf)

theorem cbdNttPoly16_spec {prf : List (BitVec 8)} (hprf : prf.length = 128) :
    (polyNtt (samplePolyCbd2 prf)).size = 256 ∧
    PolyBounded16 1664 (cbdNttPoly16 prf) ∧
    PolyRepresents (cbdNttPoly16 prf) (polyNtt (samplePolyCbd2 prf)) := by
  unfold cbdNttPoly16
  obtain ⟨⟨hsz, hb2⟩, hr⟩ := neonCbd2Poly16_spec hprf
  have hb3 : PolyBounded16 3 (neonCbd2Poly16 prf) :=
    ⟨hsz, fun i hi => ⟨by have := (hb2 i hi).1; omega, by have := (hb2 i hi).2; omega⟩⟩
  exact neonPolyNttBinomial16_spec hb3 hr (by simp [samplePolyCbd2])

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
