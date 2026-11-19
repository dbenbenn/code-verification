/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi

/-!
# `kyber_decapsulate` (`B06`) — Reusable SWAR `cbd2` and `PublicKeyStateAt` Bridges

Pure byte, `WordRangeMem`, `HalfRangeMem`, SWAR `cbd2`, and `PublicKeyStateAt` (`10,272` B)
lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  getLsbD_evalBitfield_w32_ubfm)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 sampleNtt shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord cbd2SwarSum neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At VecRangeMem bytesToVecNat pointsToBytes_eq_vecRangeMem polyVecNat
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem halfRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2Base (rowSeed)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi (RowPolyOut06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix (ATransMem06)

attribute [local irreducible] sampleNtt shake256List

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
      have hlen : 4 * w + j < bs.length := by
        have := congrArg List.length hdrop; simp at this; omega
      have ha : (bs.toArray).getD (4 * w + j) 0#8 = bs[4 * w + j]?.getD 0#8 := by
        simp [Array.getD, hlen]
      rw [ha, ← List.getElem?_drop, hdrop, List.getD_eq_getElem?_getD]
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
  rw [wordRangeMem_readU32LE_take 32 ptr (bs := bs) (by omega),
    List.take_of_length_le (by omega)]

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

private theorem extract8_lane16_eq (v : BitVec 128) (b64 b8 : Nat) (j : Fin 8) (off : Nat)
    (_h1 : b64 + b8 + 8 ≤ 128 := by decide) (h2 : b8 + 8 ≤ 64 := by decide)
    (h3 : off + 8 ≤ 16 := by decide) (h4 : b64 + b8 = 16 * j.val + off := by decide) :
    (v.extractLsb' b64 64).extractLsb' b8 8 = (lane16 v j).extractLsb' off 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lane16, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show b8 + i < 64 by omega, show off + i < 16 by omega]
  congr 1; omega

private theorem getD_ofFn {α : Type} {n : Nat} (g : Fin n → α) (i : Nat) (d : α) (hi : i < n) :
    (Array.ofFn g).getD i d = g ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem vec128At_eq_eight_16 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v =
      ((ptr ↦₁₆ lane16 v 0) ∗ ((ptr + 2#64) ↦₁₆ lane16 v 1) ∗
       ((ptr + 4#64) ↦₁₆ lane16 v 2) ∗ ((ptr + 6#64) ↦₁₆ lane16 v 3) ∗
       ((ptr + 8#64) ↦₁₆ lane16 v 4) ∗ ((ptr + 10#64) ↦₁₆ lane16 v 5) ∗
       ((ptr + 12#64) ↦₁₆ lane16 v 6) ∗ ((ptr + 14#64) ↦₁₆ lane16 v 7)) := by
  have hlo : unpack64 (v.extractLsb' 0 64) =
      unpack16 (lane16 v 0) ++ unpack16 (lane16 v 1) ++
      unpack16 (lane16 v 2) ++ unpack16 (lane16 v 3) := by
    simp only [unpack64, unpack16, List.cons_append, List.nil_append]
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 0 0 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 8 0 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 16 1 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 24 1 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 32 2 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 40 2 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 0 48 3 0) ?_
    exact congrArg₂ List.cons (extract8_lane16_eq v 0 56 3 8) rfl
  have hhi : unpack64 (v.extractLsb' 64 64) =
      unpack16 (lane16 v 4) ++ unpack16 (lane16 v 5) ++
      unpack16 (lane16 v 6) ++ unpack16 (lane16 v 7) := by
    simp only [unpack64, unpack16, List.cons_append, List.nil_append]
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 0 4 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 8 4 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 16 5 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 24 5 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 32 6 0) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 40 6 8) ?_
    refine congrArg₂ List.cons (extract8_lane16_eq v 64 48 7 0) ?_
    exact congrArg₂ List.cons (extract8_lane16_eq v 64 56 7 8) rfl
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
    have hidx : 8 * k + j.val < 256 := by omega
    rw [neonCbd2Poly16, getD_ofFn _ _ _ hidx]
    have hdiv : (8 * k + j.val) / 8 = k := by omega
    have hmod : (8 * k + j.val) % 8 = j.val := by omega
    congr 1
    · exact congrArg (readU32LE bs) hdiv
    · exact Fin.ext hmod
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
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and,
    getLsbD_evalBitfield_w32_ubfm dst (d.zeroExtend 64) r (r + 1) i
      (decide_eq_true (by omega)),
    ↓reduceIte, show r ≤ r + 1 by omega, show r + 1 - r = 1 by omega,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases hi1 : i ≤ 1
  · have hri32 : r + i < 32 := by omega
    have hri64 : r + i < 64 := by omega
    have h3 : (3#32 : BitVec 32).getLsbD i = true := by
      rcases i with _ | _ | i
      · decide
      · decide
      · omega
    simp [hi1, h3, BitVec.zeroExtend, hri32, hri64]
  · have h3 : (3#32 : BitVec 32).getLsbD i = false := by
      rcases i with _ | _ | i
      · omega
      · omega
      · have hpow : 4 ≤ 2 ^ (i + 1 + 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ i + 1 + 1 by omega)
        have hsh : (3 : Nat) / 2 ^ (i + 1 + 1) = 0 := Nat.div_eq_of_lt (by omega)
        simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, hsh]
    simp [hi1, h3]

@[simp, arm64_norm, wp_norm]
theorem ubfx2_w32_norm (dst : BitVec 64) (d : BitVec 32) (r s : Nat)
    (hs : decide (s = r + 1 ∧ r ≤ 28) = true := by decide) :
    BitVec.setWidth 32 (evalBitfield .W32 .UBFM dst (BitVec.setWidth 64 d) r s) =
      (d >>> r) &&& 3#32 := by
  have ⟨hsr, hr28⟩ := of_decide_eq_true hs
  subst hsr
  exact ubfx2_w32 dst d r (decide_eq_true hr28)

@[simp, arm64_norm, wp_norm]
theorem truncate32_zext64 (w : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 w) = w := by
  bv_bits

@[simp, arm64_norm, wp_norm]
theorem setWidth32_shr_zext64 (w : BitVec 32) (s : Nat) :
    BitVec.setWidth 32 (BitVec.setWidth 64 w >>> s) = w >>> s := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases hsi : s + i < 32
  · simp [hsi, show s + i < 64 by omega]
  · simp [BitVec.getLsbD_of_ge w (s + i) (by omega)]

theorem setPC_setMem_setPC (s : State) (p1 p2 : BitVec 64) (m : Memory) :
    ((s.setPC p1).setMem m).setPC p2 = (s.setPC p2).setMem m := by
  cases s; rfl

theorem setMem_setMem (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by
  cases s; rfl

theorem sepWP_elim_byte {P : Program} {t : BitVec 64} {s : State}
    {a : BitVec 64} {R : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ b : BitVec 8, SepWP P t s ((a ↦₈ b) ∗ R) post oom) :
    SepWP P t s (memRegion a 1 ∗ R) post oom := by
  rw [memRegion_eq_exists_bytes a 1 (by decide)]
  apply SepWP.of_sepExists_left; intro bs
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro hbs
  rcases bs with _ | ⟨b0, _ | _⟩ <;> try simp at hbs
  rw [pointsToBytes_singleton]; exact h b0

theorem cbd2_swar_eq (t : BitVec 32) :
    (0x55555555#32 &&& (t >>> 1)) + (t &&& 0x55555555#32) = cbd2SwarSum t := by
  unfold cbd2SwarSum
  rw [BitVec.and_comm 0x55555555#32 (t >>> 1)]

theorem cbd2_j3_eq (d : BitVec 32) :
    BitVec.setWidth 16 (((d >>> 12) &&& 3#32) - ((d &&& 0xc000#32) >>> 14)) =
      BitVec.setWidth 16 (((d >>> 12) &&& 3#32) - ((d >>> 14) &&& 3#32)) := by
  bv_bits

theorem cbd2_j7_eq (d : BitVec 32) :
    BitVec.setWidth 16 (((d >>> 28) &&& 3#32) - (d >>> 30)) =
      BitVec.setWidth 16 (((d >>> 28) &&& 3#32) - ((d >>> 30) &&& 3#32)) := by
  have h : d >>> 30 = (d >>> 30) &&& 3#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
    by_cases h2 : i < 2
    · have h3 : (3#32 : BitVec 32).getLsbD i = true := by
        rcases i with _ | _ | i
        · decide
        · decide
        · omega
      simp [h3]
    · simp [BitVec.getLsbD_of_ge d (30 + i) (by omega)]
  exact congrArg (fun x => BitVec.setWidth 16 (((d >>> 28) &&& 3#32) - x)) h

theorem shake256List_length (n : Nat) (msg : List (BitVec 8)) :
    (shake256List n msg).length = n := by
  with_unfolding_all exact (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.shake256 n msg).2

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
        rw [Function.update_self, htail, show ptr + BitVec.ofNat 64 (16 * 0) = ptr by bv_omega]
    · obtain ⟨Fk, hsplit, hupd⟩ := ih (k := k) (by omega) (ptr + 16#64) (fun i => f (i + 1))
      have ha : (ptr + 16#64) + BitVec.ofNat 64 (16 * k) = ptr + BitVec.ofNat 64 (16 * (k + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        rw [show 16 * (k + 1) = 16 + 16 * k by omega, BitVec.ofNat_add]
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
  have hdisj : x &&& 1#64 = 0#64 := by
    rw [← h15, ← BitVec.and_assoc, hx0]
    decide
  exact (BitVec.add_eq_or_of_and_eq_zero x 1#64 hdisj).symm

theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

theorem step_bCond_not_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = false) (hdst : pc + 4#64 = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

@[expose] noncomputable def aTransPoly06 (rho : List (BitVec 8)) (row col : Nat) : Poly16 :=
  (sampleNtt (rowSeed rho row col)).map (BitVec.ofNat 16)

@[expose] noncomputable def ATransRowAt (ptr : BitVec 64) (rho : List (BitVec 8)) (row : Nat) :
    SepProp :=
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row)) (polyVecNat (aTransPoly06 rho row 0)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 512)) (polyVecNat (aTransPoly06 rho row 1)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 1024)) (polyVecNat (aTransPoly06 rho row 2)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 1536)) (polyVecNat (aTransPoly06 rho row 3))

@[expose] noncomputable def ATransAt (ptr : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  ATransRowAt ptr rho 0 ∗ ATransRowAt ptr rho 1 ∗ ATransRowAt ptr rho 2 ∗ ATransRowAt ptr rho 3

@[expose] noncomputable def PublicKeyStateAt (ptr : BitVec 64) (pk : List (BitVec 8)) : SepProp :=
  ATransAt ptr (pkRho pk) ∗
  PolyMem (ptr + 8192#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
  PolyMem (ptr + 8704#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
  PolyMem (ptr + 9216#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
  PolyMem (ptr + 9728#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
  ((ptr + BitVec.ofNat 64 10240) ↦ₛ List.replicate 32 0#8)

theorem aTransAt_14432_eq (sp : BitVec 64) (rho : List (BitVec 8)) :
    ATransAt (sp + 14432#64) rho = ATransMem06 sp rho := rfl

private noncomputable def aTransRowBytes (rho : List (BitVec 8)) (row : Nat) : List (BitVec 8) :=
  vecRangeBytes 32 (polyVecNat (aTransPoly06 rho row 0)) ++
  (vecRangeBytes 32 (polyVecNat (aTransPoly06 rho row 1)) ++
   (vecRangeBytes 32 (polyVecNat (aTransPoly06 rho row 2)) ++
    vecRangeBytes 32 (polyVecNat (aTransPoly06 rho row 3))))

private theorem aTransRowBytes_length (rho : List (BitVec 8)) (row : Nat) :
    (aTransRowBytes rho row).length = 2048 := by
  simp [aTransRowBytes, vecRangeBytes_length]

private theorem aTransRowAt_eq_pointsToBytes (ptr : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (hrow : row < 4) :
    ATransRowAt ptr rho row =
      ((ptr + BitVec.ofNat 64 (2048 * row)) ↦ₛ aTransRowBytes rho row) := by
  unfold ATransRowAt aTransRowBytes PolyMem
  have h1 : ptr + BitVec.ofNat 64 (2048 * row) + BitVec.ofNat 64 512 =
      ptr + BitVec.ofNat 64 (2048 * row + 512) := by
    rcases row with _ | _ | _ | _ | row
    · bv_omega
    · bv_omega
    · bv_omega
    · bv_omega
    · omega
  have h2 : ptr + BitVec.ofNat 64 (2048 * row + 512) + BitVec.ofNat 64 512 =
      ptr + BitVec.ofNat 64 (2048 * row + 1024) := by
    rcases row with _ | _ | _ | _ | row
    · bv_omega
    · bv_omega
    · bv_omega
    · bv_omega
    · omega
  have h3 : ptr + BitVec.ofNat 64 (2048 * row + 1024) + BitVec.ofNat 64 512 =
      ptr + BitVec.ofNat 64 (2048 * row + 1536) := by
    rcases row with _ | _ | _ | _ | row
    · bv_omega
    · bv_omega
    · bv_omega
    · bv_omega
    · omega
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    vecRangeBytes_length, vecRangeBytes_length, vecRangeBytes_length]
  simp only [show 16 * 32 = 512 from rfl, h1, h2, h3, ← vecRangeMem_eq_pointsToBytes]

noncomputable def pkStateBytes (pk : List (BitVec 8)) : List (BitVec 8) :=
  let rho := pkRho pk
  aTransRowBytes rho 0 ++
  (aTransRowBytes rho 1 ++
   (aTransRowBytes rho 2 ++
    (aTransRowBytes rho 3 ++
     (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk0 pk))) ++
      (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk1 pk))) ++
       (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk2 pk))) ++
        (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk3 pk))) ++
         List.replicate 32 0#8)))))))

theorem pkStateBytes_length (pk : List (BitVec 8)) : (pkStateBytes pk).length = 10272 := by
  simp [pkStateBytes, aTransRowBytes_length, vecRangeBytes_length]

theorem publicKeyStateAt_eq_pointsToBytes (ptr : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt ptr pk = (ptr ↦ₛ pkStateBytes pk) := by
  unfold PublicKeyStateAt ATransAt pkStateBytes
  rw [aTransRowAt_eq_pointsToBytes ptr _ 0 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 1 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 2 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 3 (by decide)]
  simp only [PolyMem, vecRangeMem_eq_pointsToBytes, pointsToBytes_append,
    aTransRowBytes_length, vecRangeBytes_length, show 16 * 32 = 512 from rfl,
    sepConj_assoc,
    show ptr + BitVec.ofNat 64 (2048 * 0) = ptr by bv_omega,
    show ptr + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 1) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 1) + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 2) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 2) + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 3) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 3) + BitVec.ofNat 64 2048 = ptr + 8192#64 by bv_omega,
    show ptr + 8192#64 + BitVec.ofNat 64 512 = ptr + 8704#64 by bv_omega,
    show ptr + 8704#64 + BitVec.ofNat 64 512 = ptr + 9216#64 by bv_omega,
    show ptr + 9216#64 + BitVec.ofNat 64 512 = ptr + 9728#64 by bv_omega,
    show ptr + 9728#64 + BitVec.ofNat 64 512 = ptr + BitVec.ofNat 64 10240 by bv_omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure
