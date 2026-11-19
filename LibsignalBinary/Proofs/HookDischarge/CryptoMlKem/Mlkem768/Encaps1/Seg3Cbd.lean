/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedOddSites
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `encapsulate1_serialized` (`B03`) — Segment 3 PRF Setup & `cbd2` Loop (`+0x3280 .. +0x3754`)

1. Reusable SWAR `cbd2` word/halfword bridges (`wordRangeMem32_eq_pointsToBytes`,
   `halfRangeMem8_cbd2_eq_vec128At`, and `cbd2` ALU/UBFM extraction identities) shared by `Seg3`
   and `Seg4`.
2. `seg3_prf_setup` (`+0x3280 → +0x3624`): zeroes `ct1` (`960` B) and `rHat` (`1536` B), spills
   `coins` (`32` B) to `[sp + 12400, sp + 12432)`, stages `coins ++ [0#8]`, `coins ++ [1#8]`,
   `coins ++ [2#8]`, invokes `B01` (`RW2` + `RW1`) for `prf0..2`, copies `prf0..2` to
   `[sp + 2192, sp + 2576)`, and initializes the 24 `Fwd2` zeta vector constants at
   `[sp + 1552, sp + 1936)`.
3. `seg3_cbd2_loop` (`+0x3624 → +0x3754`): zeroes `[sp + 4272, sp + 4784)` and executes all 32
   SWAR `cbd2` iterations to produce `PolyMem (sp + 4272#64) (polyVecNat (neonCbd2Poly16 prf))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_blk29 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec keccak2_136_31_RW2Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.BitHelpers (
  getLsbD_evalBitfield_w32_ubfm)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord cbd2SwarSum neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane16 pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At Vec32 VecRangeMem bytesToVecNat poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat
  pointsToBytes_eq_vecRangeMem step_ldpQ128 step_ldrQ128 step_strQ128
  vec128At_eq_pointsToBytes vecRangeBytes vecRangeBytes_length
  vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdDup_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange halfRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem wordRangeMem_congr wordRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr SpillSliceMem SymSpill40 evalSExpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  blkPl03_ρ cells32_entails_memRegion sha3_512List_length)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x3280 → 0x3754]
gen_placed_odd_sites blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x3508 → 0x354c]
end

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local irreducible] sha3_512List shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 exec_simdDup_8h

/-! ## 1. Reusable `WordRangeMem`, `HalfRangeMem`, and SWAR `cbd2` Bridges -/

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
  have hbyte (base : Nat) (hb : base = 0 ∨ base = 64) (j : Nat) (hj : j < 8) :
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
    rw [LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16.lane16_pack8x16]
    have hidx : 8 * k + j.val < (neonCbd2Poly16 bs).size := by
      rw [show (neonCbd2Poly16 bs).size = 256 by with_unfolding_all simp [neonCbd2Poly16]]
      omega
    have hget : (neonCbd2Poly16 bs).getD (8 * k + j.val) 0#16 =
        cbd2CoeffFromWord (readU32LE bs k) j := by
      have hdiv : (8 * k + j.val) / 8 = k := by omega
      with_unfolding_all simp [neonCbd2Poly16, Array.getD, show 8 * k + j.val < 256 by omega, hdiv]
      exact congrArg (cbd2CoeffFromWord (readU32LE bs k)) (Fin.ext (Nat.mod_eq_of_lt j.isLt))
    exact hget
  simp only [hlane 0, hlane 1, hlane 2, hlane 3, hlane 4, hlane 5, hlane 6, hlane 7]

theorem ubfx2_w32 (dst : BitVec 64) (d : BitVec 32) (r : Nat)
    (hr : decide (r ≤ 28) = true := by decide) :
    (evalBitfield .W32 .UBFM dst (d.zeroExtend 64) r (r + 1)).truncate 32 =
      (d >>> r) &&& 3#32 := by
  have hr28 : r ≤ 28 := of_decide_eq_true hr
  have hmask : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val ≤ 1) := by
    decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and,
    getLsbD_evalBitfield_w32_ubfm dst (d.setWidth 64) r (r + 1) i
      (decide_eq_true (by omega)),
    ↓reduceIte, show r ≤ r + 1 by omega, show r + 1 - r = 1 by omega,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hmask ⟨i, hi⟩]
  by_cases hi1 : i ≤ 1
  · simp [hi1, show r + i < 64 by omega]
  · simp [hi1]

theorem cbd2_swar_eq (t : BitVec 32) :
    (0x55555555#32 &&& (t >>> 1)) + (t &&& 0x55555555#32) = cbd2SwarSum t := by
  unfold cbd2SwarSum
  rw [BitVec.and_comm 0x55555555#32 (t >>> 1)]

theorem cbd2_j3_eq (d : BitVec 32) :
    (((d >>> 12) &&& 3#32) - ((d &&& 0xc000#32) >>> 14)).setWidth 16 =
      (((d >>> 12) &&& 3#32) - ((d >>> 14) &&& 3#32)).setWidth 16 := by
  have hm1 : ∀ idx : Fin 32, (0xc000#32 : BitVec 32).getLsbD (14 + idx.val) = decide (idx.val < 2) := by
    decide
  have hm2 : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val < 2) := by
    decide
  have h : (d &&& 0xc000#32) >>> 14 = (d >>> 14) &&& 3#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm1 ⟨i, hi⟩, hm2 ⟨i, hi⟩]
  rw [h]

theorem cbd2_j7_eq (d : BitVec 32) :
    (((d >>> 28) &&& 3#32) - (d >>> 30)).setWidth 16 =
      (((d >>> 28) &&& 3#32) - ((d >>> 30) &&& 3#32)).setWidth 16 := by
  have hm : ∀ idx : Fin 32, (3#32 : BitVec 32).getLsbD idx.val = decide (idx.val < 2) := by
    decide
  have h : d >>> 30 = (d >>> 30) &&& 3#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm ⟨i, hi⟩]
    by_cases hi2 : i < 2
    · rw [decide_eq_true hi2]; simp
    · rw [decide_eq_false hi2, BitVec.getLsbD_of_ge d (30 + i) (by omega)]; simp
  conv_lhs => rw [h]

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
        have hz : ptr + BitVec.ofNat 64 (16 * 0) = ptr := by simp
        rw [hz, Function.update_self, htail]
    · obtain ⟨Fk, hsplit, hupd⟩ := ih (k := k) (by omega) (ptr + 16#64) (fun i => f (i + 1))
      have ha : (ptr + 16#64) + BitVec.ofNat 64 (16 * k) = ptr + BitVec.ofNat 64 (16 * (k + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
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

theorem sepWP_elim_byte {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ b0 : BitVec 8, SepWP prog target s ((a ↦₈ b0) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  apply SepWP.memRegion_bytes a 1 (by decide) rfl
  rintro (_ | ⟨b0, _ | _⟩) hlen <;> try simp at hlen
  simpa using h b0

theorem setPC_setMem_setPC (s : State) (p1 p2 : BitVec 64) (m : Memory) :
    ((s.setPC p1).setMem m).setPC p2 = (s.setPC p2).setMem m := by
  cases s; rfl

theorem setMem_setMem (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by
  cases s; rfl

/-! ## 2. `Seg3` PRF Entry Memsets (`+0x3280 → +0x32d4`) -/

@[simp, arm64_norm, wp_norm] abbrev offSeg3Start : BitVec 64 := BitVec.ofNat 64 12928
abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

theorem vecRangeBytes_zero : ∀ n : Nat,
    vecRangeBytes n (fun _ => 0#128) = List.replicate (16 * n) (0#8)
  | 0 => rfl
  | n + 1 => by
    rw [vecRangeBytes, vecRangeBytes_zero n, show 16 * (n + 1) = 16 + 16 * n by omega,
      List.replicate_add]
    rfl

theorem seg3_memset_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg3Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let coins := hashed.drop 32
    SepWP (blkPC03.rebase b (fun _ => none)) (b + BitVec.ofNat 64 13012) s
      (((sp + 6768#64) ↦ₛ hashed) ∗
       memRegion (sp + 11440#64) 960 ∗
       memRegion (sp + 12400#64) 33 ∗
       memRegion (sp + 12448#64) 1536 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 12448#64 ∧
        (Pm ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
          memRegion (sp + 11440#64) 960 ∗
          ((sp + 12400#64) ↦ₛ coins) ∗
          ((sp + 12432#64) ↦₈ 0#8) ∗
          PolyMem (sp + 12448#64) (fun _ => 0#128) ∗
          PolyMem (sp + 12960#64) (fun _ => 0#128) ∗
          PolyMem (sp + 13472#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins
  have _ : b = blkPl03.base := hb
  subst hbase
  have htake_len : (hashed.take 32).length = 32 := by simp [hh]
  have hcoins_len : coins.length = 32 := by simp [coins, hh]
  have hh_split : ((sp + 6768#64) ↦ₛ hashed) =
      ((sp + 6768#64) ↦ₛ hashed.take 32) ∗ ((sp + 6800#64) ↦ₛ coins) := by
    conv_lhs => rw [← List.take_append_drop 32 hashed]
    rw [pointsToBytes_append, htake_len,
      show sp + 6768#64 + BitVec.ofNat 64 32 = sp + 6800#64 by bv_omega]
  have hstep1 : SepWP (blkPC03.rebase blkPl03.base (fun _ => none))
      (blkPl03.base + BitVec.ofNat 64 12952) s
      (((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
        memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12448#64) 1536 ∗
        stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        (P1 ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
          memRegion (sp + 11440#64) 960 ∗
          memRegion (sp + 12400#64) 33 ∗
          memRegion (sp + 12448#64) 1536 ∗
          stackAt sp 1136 ∗ Rest)) := by
    wp_steps 5
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk29_memset_ok (sp + 11440#64, 0#8, (960 : Nat))
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
        Eq.trans ‹_› rfl, ?_⟩
    have hm960 : ((sp + 11440#64) ↦ₛ List.replicate 960 0#8) ⊢
        memRegion (sp + 11440#64) 960 := by
      simpa only [List.length_replicate] using
        pointsToBytes_entails_memRegion (sp + 11440#64) (List.replicate 960 0#8)
    exact entails_sub hm960 (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
          sm.sp = sp ∧ sm.spAligned = true ∧
          sm.readReg64 .x19 = 0x55555555#64 ∧
          (Pm ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
            memRegion (sp + 11440#64) 960 ∗
            memRegion (sp + 12400#64) 33 ∗
            memRegion (sp + 12448#64) 1536 ∗
            stackAt sp 1136 ∗ Rest))
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl hstep1 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hcl1, hsp1, hspA1, hx19_1, hP1⟩
  have hstep2 : SepWP (blkPC03.rebase blkPl03.base (fun _ => none))
      (blkPl03.base + BitVec.ofNat 64 13008) s1 P1
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x0 = sp + 12448#64 ∧
        s2.readReg64 .x1 = 0#64 ∧
        s2.readReg64 .x2 = 1536#64 ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧
        s2.readReg64 .x20 = sp + 12448#64 ∧
        (P2 ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
          memRegion (sp + 11440#64) 960 ∗
          ((sp + 12400#64) ↦ₛ coins) ∗
          ((sp + 12432#64) ↦₈ 0#8) ∗
          memRegion (sp + 12448#64) 1536 ∗
          stackAt sp 1136 ∗ Rest)) := by
    have _ := hpc1
    refine SepWP.weaken_pre hP1 ?_
    rw [memRegion_split' (b := sp + 12400#64) (b' := sp + 12416#64) (n := 16) (k := (17 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 12416#64) (b' := sp + 12432#64) (n := 16) (k := (1 : Nat))
          rfl (by bv_omega) (by decide)]
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 12400#64) (by decide) (by sep_focus); intro vc0
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 12416#64) (by decide) (by sep_focus); intro vc1
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    sep_frame_apply (sepWP_elim_byte (a := sp + 12432#64)); intro b0
    rw [hh_split, ← vec2_bytesToVecNat_eq (sp + 6800#64) hcoins_len]
    wp_steps 6
    refine step_ldpQ128 (wb := none) (ea := sp + 6800#64) (ea16 := sp + 6800#64 + 16#64)
      (v1 := bytesToVecNat coins 0) (v2 := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode]) rfl
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl)))))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.right (SepLoad128.vec128At rfl)))))))
      (by wp_norm_lhs) ?_
    wp_steps 5
    have hal_sp1 : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp1] using hspA1
    refine step_strQ128 (wb := none) (ea := sp + 12400#64) (val := bytesToVecNat coins 0)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp1, hal_sp1])
      (by simp [evalAddrMode, hsp1]) rfl
      (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) fun _ => ?_
    try rw [setPC_setMem_collapse]
    refine step_strQ128 (wb := none) (ea := sp + 12416#64) (val := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp1, hal_sp1])
      (by simp [evalAddrMode, hsp1]) rfl
      (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) fun _ => ?_
    simp only [setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
      ⟨by simp [hsp1], spAligned_of_sp_eq hspA1 hsp1 (by simp [hsp1]),
        by simp, by simp, by simp, by simp [hx19_1], by simp, ?_⟩
    rw [vec2_bytesToVecNat_eq (sp + 6800#64) hcoins_len, ← hh_split]
    have hc12400 : Vec128At (sp + 12400#64) (bytesToVecNat coins 0) ∗
        Vec128At (sp + 12416#64) (bytesToVecNat coins 1) = ((sp + 12400#64) ↦ₛ coins) := by
      simpa [show sp + 12400#64 + 16#64 = sp + 12416#64 by bv_omega] using
        vec2_bytesToVecNat_eq (sp + 12400#64) hcoins_len
    exact entails_sub (Entails.of_eq hc12400) (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ _)
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl1 hstep2 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hcl2, hsp2, hspA2, hx0_2, hx1_2, hx2_2, hx19_2, hx20_2, hP2⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem := hcl2
  have _ := hpc2
  refine SepWP.weaken_pre hP2 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 12448#64, 0#8, (1536 : Nat))
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp2, spAligned_of_sp_eq hspA2 hsp2 (hsp_sf.trans hsp2),
      Eq.trans ‹_› hx19_2, Eq.trans ‹_› hx20_2, ?_⟩
  have hz3 : ((sp + 12448#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 12448#64) (fun _ => 0#128) ∗
      PolyMem (sp + 12960#64) (fun _ => 0#128) ∗
      PolyMem (sp + 13472#64) (fun _ => 0#128) := by
    have hrep : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, show (1536 : Nat) = 512 + (512 + 512) from rfl,
        List.replicate_add, List.replicate_add]
    rw [hrep, pointsToBytes_append, pointsToBytes_append,
      vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp [PolyMem,
      show sp + 12448#64 + BitVec.ofNat 64 (16 * 32) = sp + 12960#64 by bv_omega,
      show sp + 12960#64 + BitVec.ofNat 64 (16 * 32) = sp + 13472#64 by bv_omega]
  rw [hz3]
  sep_frame

/-! ## 3. `Seg3` Scratch Zero & SWAR `cbd2` Loop (`+0x3624 → +0x3754`) -/

attribute [local irreducible] blkPC03

@[simp, arm64_norm, wp_norm] abbrev offSeg3CbdStart : BitVec 64 := BitVec.ofNat 64 13860
@[simp, arm64_norm, wp_norm] abbrev offSeg3CbdBody  : BitVec 64 := BitVec.ofNat 64 14004
@[simp, arm64_norm, wp_norm] abbrev offSeg3CbdBr    : BitVec 64 := BitVec.ofNat 64 14160
@[simp, arm64_norm, wp_norm] abbrev offSeg3CbdEnd   : BitVec 64 := BitVec.ofNat 64 14164

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
        cases s; subst hpc; subst hdst
        simp [wp_norm, arm64_norm, hcond, State.advancePC, State.setPC])
    rfl hnext

local macro "step_strQ4272 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg3_cbd2_zero [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdBody) s
      (memRegion (sp + 4272#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x6 = 0#64 ∧ s1.readReg64 .x7 = s.readReg64 .x7 ∧
        s1.readReg64 .x8 = s.readReg64 .x7 ∧ s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x10 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
        s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
        s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
        s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 4272#64) 512 ∗ Rest)) := by
  have _ : b = blkPl03.base := hb
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 4272#64) f = PolyMem (sp + 4272#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ4272 31; step_strQ4272 30; step_strQ4272 29; step_strQ4272 28
  step_strQ4272 27; step_strQ4272 26; step_strQ4272 25; step_strQ4272 24
  step_strQ4272 23; step_strQ4272 22; step_strQ4272 21; step_strQ4272 20
  step_strQ4272 19; step_strQ4272 18; step_strQ4272 17; step_strQ4272 16
  step_strQ4272 15; step_strQ4272 14; step_strQ4272 13; step_strQ4272 12
  step_strQ4272 11; step_strQ4272 10; step_strQ4272 9;  step_strQ4272 8
  step_strQ4272 7;  step_strQ4272 6;  step_strQ4272 5;  step_strQ4272 4
  step_strQ4272 3;  step_strQ4272 2;  step_strQ4272 1;  step_strQ4272 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

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

@[simp, arm64_norm, wp_norm]
theorem ubfx2_w32_norm (dst : BitVec 64) (d : BitVec 32) (r s : Nat)
    (hs : decide (s = r + 1 ∧ r ≤ 28) = true := by decide) :
    setWidth 32 (evalBitfield .W32 .UBFM dst (setWidth 64 d) r s) =
      (d >>> r) &&& 3#32 := by
  have ⟨hsr, hr28⟩ := of_decide_eq_true hs
  subst hsr
  exact ubfx2_w32 dst d r (decide_eq_true hr28)

@[simp, arm64_norm, wp_norm]
theorem truncate32_zext64 (w : BitVec 32) : setWidth 32 (setWidth 64 w) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

@[simp, arm64_norm, wp_norm]
theorem setWidth32_shr_zext64 (w : BitVec 32) (s : Nat) :
    setWidth 32 (setWidth 64 w >>> s) = w >>> s := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hs : s + i < 32
  · simp [hi, show s + i < 64 by omega]
  · have hge : w.getLsbD (s + i) = false := BitVec.getLsbD_of_ge w (s + i) (by omega)
    simp [hi, hge]

local macro "step_cbd_strh " cellPtr:ident hx21Id:term:arg hx6Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx21Id:term, $hx6Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg3_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3CbdBody) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if k < 31 then b + offSeg3CbdBody else b + offSeg3CbdEnd) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x6 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x7 = s.readReg64 .x7 ∧
        s'.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧ s'.readReg64 .x21 = dstPtr ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest)) := by
  subst hbase
  obtain ⟨Fk, hsplit, hupd⟩ := vecRangeMem_focus hk dstPtr f
  let cellPtr := dstPtr + BitVec.ofNat 64 (16 * k)
  let w := readU32LE prf k
  rw [hsplit, vec128At_eq_halfRangeMem8 cellPtr (f k),
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗
        (HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗ Fk) ∗ Rest =
      HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest by
      simp only [sepConj_assoc]; rw [sepConj_left_comm (WordRangeMem 32 prfPtr (readU32LE prf))]]
  refine SepWP.step_ldur32 (wb := none) (ea := prfPtr + BitVec.ofNat 64 (4 * k)) (v := w)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_cbd_strh cellPtr hx21 hx6 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx6 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx6 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx21 hx6 6 (cbd2CoeffFromWord w 6)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  have hmem_eq : ∀ hFin : Nat → BitVec 16,
      (∀ j (hj : j < 8), hFin j = cbd2CoeffFromWord w ⟨j, hj⟩) →
      HalfRangeMem 8 cellPtr hFin ∗ WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest := by
    intro hFin hhFin
    rw [halfRangeMem8_cbd2_eq cellPtr prf k hk hFin hhFin,
      sepConj_left_comm (Vec128At cellPtr _), ← sepConj_assoc (Vec128At cellPtr _) Fk Rest,
      hupd]
  by_cases hk31 : k < 31
  · simp only [hk31, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl03.base + offSeg3CbdBody)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offSeg3CbdBr, offSeg3CbdBody]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega, by simp,
        by simp; clear * -; bv_omega, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl03.base + offSeg3CbdEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg3CbdBr, offSeg3CbdEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp,
        by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg3_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offSeg3CbdBody else b + offSeg3CbdEnd) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x6 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdEnd) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
          s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
          s'.readReg64 .x7 = s.readReg64 .x7 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
          s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
          s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
          s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = s.readReg64 .x20 ∧ s'.readReg64 .x21 = dstPtr ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx21
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hx19, rfl, hx21, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx6 hx8 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + offSeg3CbdBody else b + offSeg3CbdEnd) =
        (if k + 1 < 32 then b + offSeg3CbdBody else b + offSeg3CbdEnd) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (seg3_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx6 hx8 hx19 hx21)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hr2, hr3, hr4, hr5, hx6_1, hr7, hx8_1,
        hr9, hr10, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hr20, hx21_1, hfp1, hv3_1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (ih (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx6_1 hx8_1 hx19_1 hx21_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, g20, gx21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g2.trans hr2, g3.trans hr3,
        g4.trans hr4, g5.trans hr5, g7.trans hr7, g9.trans hr9, g10.trans hr10,
        g12.trans hr12, g13.trans hr13, g14.trans hr14, g15.trans hr15, g16.trans hr16,
        g17.trans hr17, g18.trans hr18, gx19, g20.trans hr20, gx21, gfp.trans hfp1,
        gv3.trans hv3_1, hP2⟩

theorem seg3_cbd2_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + offSeg3CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx7 : s.readReg64 .x7 = prfPtr + 1#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 4272#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x7 = prfPtr + 1#64 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧ s'.readReg64 .x21 = sp + 4272#64 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 4272#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 4272#64) 512 ∗ Rest =
      memRegion (sp + 4272#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (seg3_cbd2_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, hx6_1, r7, hx8_1,
      r9, r10, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, rfp, rv3, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (by decide) rfl fun f => by
      rw [show VecRangeMem 32 (sp + 4272#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 4272#64) f ∗ Rest by
        rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 4272#64) f), sepConj_assoc]]
      refine SepWP.seq
        (seg3_cbd2_steps hb hbase sp prfPtr (sp + 4272#64) prf Rest 32 0 rfl s1 f
          (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx6_1
          (by simp [hx8_1, hx7]) (r19.trans hx19) (r21.trans hx21)) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, g20, gx21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g2.trans r2, g3.trans r3,
        g4.trans r4, g5.trans r5, g7.trans (r7.trans hx7), g9.trans r9, g10.trans r10,
        g12.trans r12, g13.trans r13, g14.trans r14, g15.trans r15, g16.trans r16,
        g17.trans r17, g18.trans r18, gx19, g20.trans r20, gx21, gfp.trans rfp,
        gv3.trans rv3, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
