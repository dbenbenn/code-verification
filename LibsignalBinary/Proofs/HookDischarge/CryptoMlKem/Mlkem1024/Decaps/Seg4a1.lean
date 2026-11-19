/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2

/-!
# `kyber_decapsulate` (`B06`) — Segment 4a1 (`+0x39c4 .. +0x3b78`)

Spills the 32 zero-extended words of `m'` to `[sp + 0 .. sp + 128)`, stages `m' ++ hPk` at
`[sp + 2432 .. sp + 2496)`, and calls `B00` (`keccak2::<72, 6>`) to compute
`(kBar', r') = sha3_512List (m' ++ hPk)` at `[sp + 4160 .. sp + 4224)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW keccak2_72_6_RW1Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6 (
  blk00_keccak2_72_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat pointsToBytes_eq_vecRangeMem step_ldpQ128 step_strQ128
  vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  msgW32 pair32_entails_memRegion8 sha3_512List_len stackAt_1136_split_720)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x39c4 → 0x3b74]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem trunc32_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 32 = b.zeroExtend 32 := by bv_omega

@[simp, arm64_norm, wp_norm]
private theorem trunc8_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 8 = b := by bv_omega

theorem blk00_rw1_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 0)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_72_6_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk00_keccak2_72_6_RW1_ok

attribute [local irreducible] blkPC06 sha3_512List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 trunc32_zext64_8 trunc8_zext64_8

@[simp, arm64_norm, wp_norm] abbrev off39c4 : BitVec 64 := 14788#64
@[simp, arm64_norm, wp_norm] private abbrev off3aac : BitVec 64 := 15020#64
@[simp, arm64_norm, wp_norm] private abbrev off3b74 : BitVec 64 := 15220#64
@[simp, arm64_norm, wp_norm] abbrev off3b78 : BitVec 64 := 15224#64

/-! ## 1. Spilled `m'` Word Slots (`[sp + 0 .. sp + 128)`) & Byte/Word Helpers -/

/-- Low 16 spilled words of `m'` (`[sp + 0 .. sp + 64)`). -/
@[expose] def SpilledDecapsLo (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  (sp ↦₃₂ msgW32 m 1) ∗ ((sp + 4#64) ↦₃₂ msgW32 m 0) ∗
  ((sp + 8#64) ↦₃₂ msgW32 m 3) ∗ ((sp + 12#64) ↦₃₂ msgW32 m 2) ∗
  ((sp + 16#64) ↦₃₂ msgW32 m 4) ∗ ((sp + 20#64) ↦₃₂ msgW32 m 5) ∗
  ((sp + 24#64) ↦₃₂ msgW32 m 7) ∗ ((sp + 28#64) ↦₃₂ msgW32 m 6) ∗
  ((sp + 32#64) ↦₃₂ msgW32 m 8) ∗ ((sp + 36#64) ↦₃₂ msgW32 m 9) ∗
  ((sp + 40#64) ↦₃₂ msgW32 m 11) ∗ ((sp + 44#64) ↦₃₂ msgW32 m 10) ∗
  ((sp + 48#64) ↦₃₂ msgW32 m 12) ∗ ((sp + 52#64) ↦₃₂ msgW32 m 13) ∗
  ((sp + 56#64) ↦₃₂ msgW32 m 14) ∗ ((sp + 60#64) ↦₃₂ msgW32 m 15)

/-- High 16 spilled words of `m'` (`[sp + 64 .. sp + 128)`). -/
@[expose] def SpilledDecapsHi (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  ((sp + 64#64) ↦₃₂ msgW32 m 17) ∗ ((sp + 68#64) ↦₃₂ msgW32 m 16) ∗
  ((sp + 72#64) ↦₃₂ msgW32 m 18) ∗ ((sp + 76#64) ↦₃₂ msgW32 m 19) ∗
  ((sp + 80#64) ↦₃₂ msgW32 m 21) ∗ ((sp + 84#64) ↦₃₂ msgW32 m 20) ∗
  ((sp + 88#64) ↦₃₂ msgW32 m 22) ∗ ((sp + 92#64) ↦₃₂ msgW32 m 23) ∗
  ((sp + 96#64) ↦₃₂ msgW32 m 25) ∗ ((sp + 100#64) ↦₃₂ msgW32 m 24) ∗
  ((sp + 104#64) ↦₃₂ msgW32 m 29) ∗ ((sp + 108#64) ↦₃₂ msgW32 m 26) ∗
  ((sp + 112#64) ↦₃₂ msgW32 m 27) ∗ ((sp + 116#64) ↦₃₂ msgW32 m 31) ∗
  ((sp + 120#64) ↦₃₂ msgW32 m 30) ∗ ((sp + 124#64) ↦₃₂ msgW32 m 28)

/-- All 32 spilled words of `m'` (`[sp + 0 .. sp + 128)`). -/
@[expose] def SpilledDecapsWords (sp : BitVec 64) (m : List (BitVec 8)) : SepProp :=
  SpilledDecapsLo sp m ∗ SpilledDecapsHi sp m

private theorem pairs8_entails_memRegion64 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 32) :
    ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗
      ((a + 8#64) ↦₃₂ w2) ∗ ((a + 12#64) ↦₃₂ w3) ∗
      ((a + 16#64) ↦₃₂ w4) ∗ ((a + 20#64) ↦₃₂ w5) ∗
      ((a + 24#64) ↦₃₂ w6) ∗ ((a + 28#64) ↦₃₂ w7) ∗
      ((a + 32#64) ↦₃₂ w8) ∗ ((a + 36#64) ↦₃₂ w9) ∗
      ((a + 40#64) ↦₃₂ w10) ∗ ((a + 44#64) ↦₃₂ w11) ∗
      ((a + 48#64) ↦₃₂ w12) ∗ ((a + 52#64) ↦₃₂ w13) ∗
      ((a + 56#64) ↦₃₂ w14) ∗ ((a + 60#64) ↦₃₂ w15)) ⊢ memRegion a 64 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := (56 : Nat)) rfl rfl (by decide),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := (48 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := (40 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := (24 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 40#64) (b' := a + 48#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := a + 48#64) (b' := a + 56#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  have hp (off : BitVec 64) (lo hi : BitVec 32) :
      (((a + off) ↦₃₂ lo) ∗ ((a + (off + 4#64)) ↦₃₂ hi)) ⊢ memRegion (a + off) 8 := by
    simpa [show a + off + 4#64 = a + (off + 4#64) by bv_omega] using
      pair32_entails_memRegion8 (a + off) lo hi
  have p0 := pair32_entails_memRegion8 a w0 w1
  exact entails_sub p0 (by sep_frame)
    (entails_sub (hp 8#64 w2 w3) (by sep_frame)
    (entails_sub (hp 16#64 w4 w5) (by sep_frame)
    (entails_sub (hp 24#64 w6 w7) (by sep_frame)
    (entails_sub (hp 32#64 w8 w9) (by sep_frame)
    (entails_sub (hp 40#64 w10 w11) (by sep_frame)
    (entails_sub (hp 48#64 w12 w13) (by sep_frame)
    (entails_sub (hp 56#64 w14 w15) (by sep_frame) (by sep_frame))))))))

theorem spilledDecapsWords_entails_memRegion128 (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledDecapsWords sp m ⊢ memRegion sp 128 := by
  rw [memRegion_split' (b := sp) (b' := sp + 64#64) (n := 64) (k := (64 : Nat)) rfl rfl (by decide)]
  refine sepConj_mono ?_ ?_
  · exact pairs8_entails_memRegion64 sp
      (msgW32 m 1) (msgW32 m 0) (msgW32 m 3) (msgW32 m 2)
      (msgW32 m 4) (msgW32 m 5) (msgW32 m 7) (msgW32 m 6)
      (msgW32 m 8) (msgW32 m 9) (msgW32 m 11) (msgW32 m 10)
      (msgW32 m 12) (msgW32 m 13) (msgW32 m 14) (msgW32 m 15)
  · simpa [SpilledDecapsHi, BitVec.add_assoc] using
      pairs8_entails_memRegion64 (sp + 64#64)
        (msgW32 m 17) (msgW32 m 16) (msgW32 m 18) (msgW32 m 19)
        (msgW32 m 21) (msgW32 m 20) (msgW32 m 22) (msgW32 m 23)
        (msgW32 m 25) (msgW32 m 24) (msgW32 m 29) (msgW32 m 26)
        (msgW32 m 27) (msgW32 m 31) (msgW32 m 30) (msgW32 m 28)

private theorem sepWP_elim_pair32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ w0 w1 : BitVec 32,
      SepWP prog target s (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1)) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  refine sepWP_elim_cell8 fun v => ?_
  have hv : (v.extractLsb' 32 32) ++ (v.truncate 32) = v := by bv_bits
  rw [← hv, ← pointsTo32_pair a (v.truncate 32) (v.extractLsb' 32 32)]
  exact h _ _

private theorem sepWP_elim_words8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 32,
      SepWP prog target s
        (((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗ ((a + 8#64) ↦₃₂ w2) ∗ ((a + 12#64) ↦₃₂ w3) ∗
          ((a + 16#64) ↦₃₂ w4) ∗ ((a + 20#64) ↦₃₂ w5) ∗ ((a + 24#64) ↦₃₂ w6) ∗
          ((a + 28#64) ↦₃₂ w7)) ∗ R0) post) :
    SepWP prog target s (memRegion a 32 ∗ R0) post := by
  have hsplit : memRegion a 32 =
      memRegion a 8 ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 := by
    rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := (24 : Nat)) rfl rfl (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  sep_frame_apply (sepWP_elim_pair32 (a := a)); intro w0 w1
  sep_frame_apply (sepWP_elim_pair32 (a := a + 8#64)); intro w2 w3
  sep_frame_apply (sepWP_elim_pair32 (a := a + 16#64)); intro w4 w5
  sep_frame_apply (sepWP_elim_pair32 (a := a + 24#64)); intro w6 w7
  refine SepWP.weaken_pre ?_ (h w0 w1 w2 w3 w4 w5 w6 w7)
  have e12 : a + 8#64 + 4#64 = a + 12#64 := by bv_omega
  have e20 : a + 16#64 + 4#64 = a + 20#64 := by bv_omega
  have e28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
  simp only [e12, e20, e28]
  sep_frame

private theorem list8_eq_getD (bs : List (BitVec 8)) (h : bs.length = 8) :
    bs = [bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
          bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8, bs.getD 7 0#8] := by
  rcases bs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all

private theorem pointsToBytes8_eq (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7]) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
       ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) := by
  simp [pointsToBytes_cons, pointsToBytes_nil]

private theorem sepWP_elim_bytes8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      SepWP prog target s
        (((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
          ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) ∗ R0)
        post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  rw [memRegion_eq_exists_bytes a 8 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hbs => ?_
  rw [list8_eq_getD bs hbs, pointsToBytes8_eq]
  exact h _ _ _ _ _ _ _ _

private theorem pointsToBytes_slice8 (a : BitVec 64) (m : List (BitVec 8)) (off : Nat)
    (hoff : off + 8 ≤ m.length) :
    ((a ↦₈ m.getD off 0#8) ∗ ((a + 1#64) ↦₈ m.getD (off + 1) 0#8) ∗
     ((a + 2#64) ↦₈ m.getD (off + 2) 0#8) ∗ ((a + 3#64) ↦₈ m.getD (off + 3) 0#8) ∗
     ((a + 4#64) ↦₈ m.getD (off + 4) 0#8) ∗ ((a + 5#64) ↦₈ m.getD (off + 5) 0#8) ∗
     ((a + 6#64) ↦₈ m.getD (off + 6) 0#8) ∗ ((a + 7#64) ↦₈ m.getD (off + 7) 0#8)) =
      (a ↦ₛ (m.drop off).take 8) := by
  have hlen : ((m.drop off).take 8).length = 8 := by rw [List.length_take, List.length_drop]; omega
  conv => rhs; rw [list8_eq_getD _ hlen]
  have hg (k : Nat) (hk : k < 8) : ((m.drop off).take 8).getD k 0#8 = m.getD (off + k) 0#8 := by
    simp [List.getD_eq_getElem?_getD, hk]
  rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide), hg 3 (by decide),
    hg 4 (by decide), hg 5 (by decide), hg 6 (by decide), hg 7 (by decide), Nat.add_zero]
  exact (pointsToBytes8_eq a _ _ _ _ _ _ _ _).symm

private theorem take8_append_drop8_take8 (m : List (BitVec 8)) (_hm : 16 ≤ m.length) :
    (m.drop 0).take 8 ++ (m.drop 8).take 8 = m.take 16 := by
  have h16 : m.take 16 = (m.take 16).take 8 ++ (m.take 16).drop 8 :=
    (List.take_append_drop 8 (m.take 16)).symm
  rw [h16]; simp [List.take_take, List.drop_take]

private theorem drop16_take8_append_drop24 (m : List (BitVec 8)) (hm : m.length = 32) :
    (m.drop 16).take 8 ++ (m.drop 24).take 8 = m.drop 16 := by
  have h16 : m.drop 16 = (m.drop 16).take 8 ++ (m.drop 16).drop 8 :=
    (List.take_append_drop 8 (m.drop 16)).symm
  have hd : (m.drop 16).drop 8 = (m.drop 24).take 8 := by
    rw [List.drop_drop, show 16 + 8 = 24 from rfl, List.take_of_length_le (by simp [hm])]
  conv => rhs; rw [h16, hd]

theorem vec2_bytesToVecNat_eq (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    Vec128At ptr (bytesToVecNat bs 0) ∗ Vec128At (ptr + 16#64) (bytesToVecNat bs 1) =
      (ptr ↦ₛ bs) := by
  have hv := pointsToBytes_eq_vecRangeMem 2 ptr h
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  exact hv.symm

theorem vec4_zero_entails_memRegion64 (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗
      (Vec128At (ptr + 16#64) 0#128 ∗
        (Vec128At (ptr + 16#64 + 16#64) 0#128 ∗
          Vec128At (ptr + 16#64 + 16#64 + 16#64) 0#128)) ⊢
      memRegion ptr 64 := by
  simpa [VecRangeMem, sepConj_emp] using vecRangeMem_entails_memRegion 4 ptr (fun _ => 0#128)

/-! ## 2. Part 1 (`+0x39c4 → +0x3aac`): `hPk` Load, Low 16 Spills & First 16 Bytes -/

private theorem seg4a1_part1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (m hPk : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hhPk : hPk.length = 32)
    (hpc : s.pc = b + off39c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3aac) s
      (((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
        ((sp + 28368#64) ↦ₛ m) ∗ memRegion sp 64 ∗ memRegion (sp + 2432#64) 16 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = sp + 30448#64 ∧
        s1.readReg64 .x1 = sp + 4160#64 ∧
        s1.readReg64 .x2 = sp + 14432#64 ∧
        s1.readReg64 .x8 = (m.getD 16 0#8).zeroExtend 64 ∧
        s1.readReg64 .x9 = (m.getD 19 0#8).zeroExtend 64 ∧
        s1.readReg64 .x10 = sp + 26272#64 ∧
        s1.readReg64 .x11 = (m.getD 18 0#8).zeroExtend 64 ∧
        s1.readReg64 .x12 = (m.getD 17 0#8).zeroExtend 64 ∧
        s1.readReg64 .x19 = sp + 4160#64 ∧
        s1.readReg64 .x20 = sp + 14432#64 ∧
        s1.readReg64 .x23 = ctA ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 0#5 = bytesToVecNat hPk 0 ∧
        s1.readVReg128 1#5 = bytesToVecNat hPk 1 ∧
        (P1 ⊢ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
          ((sp + 28368#64) ↦ₛ m) ∗ SpilledDecapsLo sp m ∗
          ((sp + 2432#64) ↦ₛ m.take 16) ∗ Rest)) := by
  subst hbase
  have hsplitW : memRegion sp 64 = memRegion sp 32 ∗ memRegion (sp + 32#64) 32 :=
    memRegion_split' (b := sp) (b' := sp + 32#64) (n := 32) (k := (32 : Nat)) rfl rfl (by decide)
  have hsplitB : memRegion (sp + 2432#64) 16 =
      memRegion (sp + 2432#64) 8 ∗ memRegion (sp + 2440#64) 8 :=
    memRegion_split' (b := sp + 2432#64) (b' := sp + 2440#64) (n := 8) (k := (8 : Nat))
      rfl (by bv_omega) (by decide)
  rw [hsplitW, hsplitB, ← vec2_bytesToVecNat_eq (skA + 3104#64) hhPk]
  sep_frame_apply (sepWP_elim_words8 (a := sp)); intro w0 w1 w2 w3 w4 w5 w6 w7
  sep_frame_apply (sepWP_elim_words8 (a := sp + 32#64)); intro w8 w9 w10 w11 w12 w13 w14 w15
  sep_frame_apply (sepWP_elim_bytes8 (a := sp + 2432#64)); intro b0 b1 b2 b3 b4 b5 b6 b7
  sep_frame_apply (sepWP_elim_bytes8 (a := sp + 2440#64)); intro b8 b9 b10 b11 b12 b13 b14 b15
  have ha_hpk : skA + 3104#64 + 16#64 = skA + 3120#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (show _ ⊢
    (Vec128At (skA + 3104#64) (bytesToVecNat hPk 0) ∗
      Vec128At (skA + 3104#64 + 16#64) (bytesToVecNat hPk 1)) ∗
    (((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 28368#64) ↦ₛ m) ∗
      ((sp ↦₃₂ w0) ∗ ((sp + 4#64) ↦₃₂ w1) ∗ ((sp + 8#64) ↦₃₂ w2) ∗ ((sp + 12#64) ↦₃₂ w3) ∗
        ((sp + 16#64) ↦₃₂ w4) ∗ ((sp + 20#64) ↦₃₂ w5) ∗ ((sp + 24#64) ↦₃₂ w6) ∗ ((sp + 28#64) ↦₃₂ w7)) ∗
      (((sp + 32#64) ↦₃₂ w8) ∗ ((sp + 32#64 + 4#64) ↦₃₂ w9) ∗ ((sp + 32#64 + 8#64) ↦₃₂ w10) ∗
        ((sp + 32#64 + 12#64) ↦₃₂ w11) ∗ ((sp + 32#64 + 16#64) ↦₃₂ w12) ∗ ((sp + 32#64 + 20#64) ↦₃₂ w13) ∗
        ((sp + 32#64 + 24#64) ↦₃₂ w14) ∗ ((sp + 32#64 + 28#64) ↦₃₂ w15)) ∗
      (((sp + 2432#64) ↦₈ b0) ∗ ((sp + 2432#64 + 1#64) ↦₈ b1) ∗ ((sp + 2432#64 + 2#64) ↦₈ b2) ∗
        ((sp + 2432#64 + 3#64) ↦₈ b3) ∗ ((sp + 2432#64 + 4#64) ↦₈ b4) ∗ ((sp + 2432#64 + 5#64) ↦₈ b5) ∗
        ((sp + 2432#64 + 6#64) ↦₈ b6) ∗ ((sp + 2432#64 + 7#64) ↦₈ b7)) ∗
      (((sp + 2440#64) ↦₈ b8) ∗ ((sp + 2440#64 + 1#64) ↦₈ b9) ∗ ((sp + 2440#64 + 2#64) ↦₈ b10) ∗
        ((sp + 2440#64 + 3#64) ↦₈ b11) ∗ ((sp + 2440#64 + 4#64) ↦₈ b12) ∗ ((sp + 2440#64 + 5#64) ↦₈ b13) ∗
        ((sp + 2440#64 + 6#64) ↦₈ b14) ∗ ((sp + 2440#64 + 7#64) ↦₈ b15)) ∗ Rest) by sep_frame) ?_
  wp_steps 9
  refine step_ldpQ128 (wb := none) (ea := skA + 3104#64) (ea16 := skA + 3120#64)
    (v1 := bytesToVecNat hPk 0) (v2 := bytesToVecNat hPk 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode]) ha_hpk
    (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))
    (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha_hpk)))
    (by wp_norm_lhs) ?_
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp [hx23], by simp, by simp, by simp, by simp, by simp, ?_⟩
  delta SpilledDecapsLo
  dsimp only [msgW32]
  have hb0 := pointsToBytes_slice8 (sp + 2432#64) m 0 (by omega)
  have hb8 := pointsToBytes_slice8 (sp + 2440#64) m 8 (by omega)
  have htake16 : ((sp + 2432#64) ↦ₛ m.take 16) =
      ((sp + 2432#64) ↦ₛ (m.drop 0).take 8) ∗ ((sp + 2440#64) ↦ₛ (m.drop 8).take 8) := by
    rw [← take8_append_drop8_take8 m (by omega), pointsToBytes_append]
    have hl : ((m.drop 0).take 8).length = 8 := by rw [List.length_take, List.length_drop]; omega
    rw [hl, show sp + 2432#64 + BitVec.ofNat 64 8 = sp + 2440#64 by bv_omega]
  rw [htake16, ← hb0, ← hb8, vec2_bytesToVecNat_eq (skA + 3104#64) hhPk]
  simp only [Nat.zero_add, BitVec.add_assoc]
  sep_frame


/-! ## 3. Part 2 (`+0x3aac → +0x3b78`): High 16 Spills, Staging & `B00` (`sha3_512List`) -/

set_option maxRecDepth 4096 in
private theorem seg4a1_prep_b00 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (m hPk : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hhPk : hPk.length = 32)
    (hpc : s.pc = b + off3aac) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 30448#64)
    (hx1 : s.readReg64 .x1 = sp + 4160#64)
    (hx2 : s.readReg64 .x2 = sp + 14432#64)
    (hx8 : s.readReg64 .x8 = (m.getD 16 0#8).zeroExtend 64)
    (hx9 : s.readReg64 .x9 = (m.getD 19 0#8).zeroExtend 64)
    (hx10 : s.readReg64 .x10 = sp + 26272#64)
    (hx11 : s.readReg64 .x11 = (m.getD 18 0#8).zeroExtend 64)
    (hx12 : s.readReg64 .x12 = (m.getD 17 0#8).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = sp + 4160#64)
    (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hx23 : s.readReg64 .x23 = ctA)
    (hv0 : s.readVReg128 0#5 = bytesToVecNat hPk 0)
    (hv1 : s.readVReg128 1#5 = bytesToVecNat hPk 1) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3b74) s
      (((sp + 28368#64) ↦ₛ m) ∗ memRegion (sp + 64#64) 64 ∗
        memRegion (sp + 2448#64) 48 ∗
        memRegion (sp + 4160#64) 64 ∗ memRegion (sp + 30448#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 30448#64 ∧
        sm.readReg64 .x1 = sp + 4160#64 ∧
        sm.readReg64 .x2 = sp + 14432#64 ∧
        sm.readReg64 .x19 = sp + 4160#64 ∧
        sm.readReg64 .x20 = sp + 14432#64 ∧
        sm.readReg64 .x23 = ctA ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 30448#64) (sp + 2432#64) (sp + 2432#64)
            (m ++ hPk).length (m ++ hPk).length ∗
          ((sp + 2448#64) ↦ₛ m.drop 16) ∗ ((sp + 2464#64) ↦ₛ hPk) ∗
          memRegion (sp + 4160#64) 64 ∗
          ((sp + 28368#64) ↦ₛ m) ∗ SpilledDecapsHi sp m ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_eq : s.sp &&& 15#64 = 0#64 := beq_iff_eq.mp (by simpa [State.spAligned] using hspA)
  have hsplitW : memRegion (s.sp + 64#64) 64 =
      memRegion (s.sp + 64#64) 32 ∗ memRegion (s.sp + 96#64) 32 :=
    memRegion_split' (b := s.sp + 64#64) (b' := s.sp + 96#64) (n := 32) (k := (32 : Nat))
      rfl (by bv_omega) (by decide)
  have hsplitB : memRegion (s.sp + 2448#64) 48 =
      memRegion (s.sp + 2448#64) 8 ∗ memRegion (s.sp + 2456#64) 8 ∗ memRegion (s.sp + 2464#64) 32 := by
    rw [memRegion_split' (b := s.sp + 2448#64) (b' := s.sp + 2456#64) (n := 8) (k := (40 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := s.sp + 2456#64) (b' := s.sp + 2464#64) (n := 8) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hsplitW, hsplitB]
  sep_frame_apply (sepWP_elim_words8 (a := s.sp + 64#64)); intro w16 w17 w18 w19 w20 w21 w22 w23
  sep_frame_apply (sepWP_elim_words8 (a := s.sp + 96#64)); intro w24 w25 w26 w27 w28 w29 w30 w31
  sep_frame_apply (sepWP_elim_bytes8 (a := s.sp + 2448#64)); intro b16 b17 b18 b19 b20 b21 b22 b23
  sep_frame_apply (sepWP_elim_bytes8 (a := s.sp + 2456#64)); intro b24 b25 b26 b27 b28 b29 b30 b31
  sep_frame_apply (sepWP_elim_region32 (a := s.sp + 30448#64)); intro c0 c1 c2 c3
  refine SepWP.of_memRegion_vecRangeMem 2 (s.sp + 2464#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun f24 => ?_
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  have ha24_16 : s.sp + 2464#64 + 16#64 = s.sp + 2480#64 := by clear * -; bv_omega
  have ha41_16 : s.sp + 4160#64 + 16#64 = s.sp + 4176#64 := by clear * -; bv_omega
  have ha41_32 : s.sp + 4160#64 + 16#64 + 16#64 = s.sp + 4192#64 := by clear * -; bv_omega
  have ha41_48 : s.sp + 4160#64 + 16#64 + 16#64 + 16#64 = s.sp + 4208#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (show _ ⊢
    (((s.sp + 2448#64) ↦₈ b16) ∗ ((s.sp + 2448#64 + 1#64) ↦₈ b17) ∗ ((s.sp + 2448#64 + 2#64) ↦₈ b18) ∗
      ((s.sp + 2448#64 + 3#64) ↦₈ b19) ∗ ((s.sp + 2448#64 + 4#64) ↦₈ b20) ∗ ((s.sp + 2448#64 + 5#64) ↦₈ b21) ∗
      ((s.sp + 2448#64 + 6#64) ↦₈ b22) ∗ ((s.sp + 2448#64 + 7#64) ↦₈ b23)) ∗
    (((s.sp + 2456#64) ↦₈ b24) ∗ ((s.sp + 2456#64 + 1#64) ↦₈ b25) ∗ ((s.sp + 2456#64 + 2#64) ↦₈ b26) ∗
      ((s.sp + 2456#64 + 3#64) ↦₈ b27) ∗ ((s.sp + 2456#64 + 4#64) ↦₈ b28) ∗ ((s.sp + 2456#64 + 5#64) ↦₈ b29) ∗
      ((s.sp + 2456#64 + 6#64) ↦₈ b30) ∗ ((s.sp + 2456#64 + 7#64) ↦₈ b31)) ∗
    (((s.sp + 64#64) ↦₃₂ w16) ∗ ((s.sp + 64#64 + 4#64) ↦₃₂ w17) ∗ ((s.sp + 64#64 + 8#64) ↦₃₂ w18) ∗
      ((s.sp + 64#64 + 12#64) ↦₃₂ w19) ∗ ((s.sp + 64#64 + 16#64) ↦₃₂ w20) ∗ ((s.sp + 64#64 + 20#64) ↦₃₂ w21) ∗
      ((s.sp + 64#64 + 24#64) ↦₃₂ w22) ∗ ((s.sp + 64#64 + 28#64) ↦₃₂ w23)) ∗
    (((s.sp + 96#64) ↦₃₂ w24) ∗ ((s.sp + 96#64 + 4#64) ↦₃₂ w25) ∗ ((s.sp + 96#64 + 8#64) ↦₃₂ w26) ∗
      ((s.sp + 96#64 + 12#64) ↦₃₂ w27) ∗ ((s.sp + 96#64 + 16#64) ↦₃₂ w28) ∗ ((s.sp + 96#64 + 20#64) ↦₃₂ w29) ∗
      ((s.sp + 96#64 + 24#64) ↦₃₂ w30) ∗ ((s.sp + 96#64 + 28#64) ↦₃₂ w31)) ∗
    ((s.sp + 30448#64) ↦₆₄ c0) ∗ ((s.sp + 30448#64 + 8#64) ↦₆₄ c1) ∗
    ((s.sp + 30448#64 + 16#64) ↦₆₄ c2) ∗ ((s.sp + 30448#64 + 24#64) ↦₆₄ c3) ∗
    ((s.sp + 28368#64) ↦ₛ m) ∗
    (Vec128At (s.sp + 2464#64) (f24 0) ∗ Vec128At (s.sp + 2464#64 + 16#64) (f24 1)) ∗
    memRegion (s.sp + 4160#64) 64 ∗ Rest by sep_frame) ?_
  wp_steps 23
  refine step_strQ128 (wb := none) (ea := s.sp + 2464#64) (val := bytesToVecNat hPk 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp [hv0])
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
        (SepStore128.right (SepStore128.left (SepStore128.left
          (SepStore128.vec128At rfl))))))))))))
    (by wp_norm_lhs) ?_
  intro _
  wp_steps 15
  refine step_strQ128 (wb := none) (ea := s.sp + 2480#64) (val := bytesToVecNat hPk 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp [hv1])
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
        (SepStore128.right (SepStore128.left (SepStore128.right
          (SepStore128.vec128At ha24_16))))))))))))
    (by wp_norm_lhs) ?_
  intro _
  wp_steps 6
  refine SepWP.of_memRegion_vecRangeMem 4 (s.sp + 4160#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun f41 => ?_
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  refine step_strQ128 (wb := none) (ea := s.sp + 4208#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp)
    (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.vec128At ha41_48)))))
    (by wp_norm_lhs) ?_
  intro _
  refine step_strQ128 (wb := none) (ea := s.sp + 4192#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp)
    (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vec128At ha41_32)))))
    (by wp_norm_lhs) ?_
  intro _
  refine step_strQ128 (wb := none) (ea := s.sp + 4176#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp)
    (SepStore128.left (SepStore128.right (SepStore128.left
      (SepStore128.vec128At ha41_16))))
    (by wp_norm_lhs) ?_
  intro _
  refine step_strQ128 (wb := none) (ea := s.sp + 4160#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
    (by simp [evalAddrMode]) (by simp)
    (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  intro _
  refine SepWP.weaken_pre (entails_sub (vec4_zero_entails_memRegion64 (s.sp + 4160#64)) (by sep_frame) (by sep_frame)) ?_
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, by simpa [State.spAligned] using hspA,
      by simp [hx0], by simp [hx1], by simp [hx2],
      by simp [hx19], by simp [hx20], by simp [hx23],
      by simp, by simp, by simp, ?_⟩
  delta SpilledDecapsHi
  dsimp only [msgW32]
  have hb16 := pointsToBytes_slice8 (s.sp + 2448#64) m 16 (by omega)
  have hb24 := pointsToBytes_slice8 (s.sp + 2456#64) m 24 (by omega)
  have hm_drop : ((s.sp + 2448#64) ↦ₛ m.drop 16) =
      ((s.sp + 2448#64) ↦ₛ (m.drop 16).take 8) ∗ ((s.sp + 2456#64) ↦ₛ (m.drop 24).take 8) := by
    have hl : ((m.drop 16).take 8).length = 8 := by rw [List.length_take, List.length_drop]; omega
    have ha : s.sp + 2448#64 + BitVec.ofNat 64 8 = s.sp + 2456#64 := by clear * -; bv_omega
    conv => lhs; rw [← drop16_take8_append_drop24 m hm, pointsToBytes_append, hl, ha]
  have hm_len : (m ++ hPk).length = 64 := by simp [hm, hhPk]
  rw [hm_len, hm_drop, ← hb16, ← hb24, ← vec2_bytesToVecNat_eq (s.sp + 2464#64) hhPk]
  unfold Keccak2SlicesRW
  dsimp only [Nat.reduceAdd]
  simp only [List.getD_eq_getElem?_getD, BitVec.add_assoc]
  sep_frame

/-- Segment 4a1 (`+0x39c4 → +0x3b78`): spills `SpilledDecapsWords sp m` to `[sp + 0 .. sp + 128)`
    and computes `kr = sha3_512List (m ++ hPk)` (`64` B) at `[sp + 4160 .. sp + 4224)`. -/
theorem seg4a1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (m hPk : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hhPk : hPk.length = 32)
    (hpc : s.pc = b + off39c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3b78) s
      (stackAt sp 1136 ∗ memRegion sp 128 ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
        memRegion (sp + 2432#64) 64 ∗ memRegion (sp + 4160#64) 64 ∗
        memRegion (sp + 14432#64) 64 ∗ ((sp + 28368#64) ↦ₛ m) ∗
        memRegion (sp + 30448#64) 32 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 4160#64 ∧
        sf.readReg64 .x20 = sp + 14432#64 ∧
        sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗
          ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ memRegion (sp + 2432#64) 64 ∗
          ((sp + 4160#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
          memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 28368#64) 32 ∗
          memRegion (sp + 30448#64) 32 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗ Rest)) := by
  have h128 : memRegion sp 128 = memRegion sp 64 ∗ memRegion (sp + 64#64) 64 :=
    memRegion_split' (b := sp) (b' := sp + 64#64) (n := 64) (k := (64 : Nat)) rfl rfl (by decide)
  have h24 : memRegion (sp + 2432#64) 64 =
      memRegion (sp + 2432#64) 16 ∗ memRegion (sp + 2448#64) 48 :=
    memRegion_split' (b := sp + 2432#64) (b' := sp + 2448#64) (n := 16) (k := (48 : Nat))
      rfl (by bv_omega) (by decide)
  rw [h128, h24]
  refine SepWP.weaken_pre (show _ ⊢
    ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
    ((sp + 28368#64) ↦ₛ m) ∗ memRegion sp 64 ∗ memRegion (sp + 2432#64) 16 ∗
    (stackAt sp 1136 ∗ memRegion (sp + 64#64) 64 ∗ memRegion (sp + 2448#64) 48 ∗
      memRegion (sp + 4160#64) 64 ∗ memRegion (sp + 14432#64) 64 ∗
      memRegion (sp + 30448#64) 32 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4a1_part1 hb hbase s sp skA ctA m hPk _ hm hhPk hpc hrun hsp hspA hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1,
      hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hfp_1, hv0_1, hv1_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
    ((sp + 28368#64) ↦ₛ m) ∗ memRegion (sp + 64#64) 64 ∗
    memRegion (sp + 2448#64) 48 ∗
    memRegion (sp + 4160#64) 64 ∗ memRegion (sp + 30448#64) 32 ∗
    (((sp + 2432#64) ↦ₛ m.take 16) ∗ stackAt sp 1136 ∗ SpilledDecapsLo sp m ∗
      ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      memRegion (sp + 14432#64) 64 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg4a1_prep_b00 hb hbase s1 sp ctA m hPk _ hm hhPk hpc1 hrun1 hsp1 hspA1
      hx0_1 hx1_1 hx2_1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hv0_1 hv1_1) ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, hfpm, hPm⟩
  subst hbase
  have hcat : ((sp + 2432#64) ↦ₛ (m ++ hPk)) =
      ((sp + 2432#64) ↦ₛ m.take 16) ∗ ((sp + 2448#64) ↦ₛ m.drop 16) ∗ ((sp + 2464#64) ↦ₛ hPk) := by
    rw [pointsToBytes_append, hm, show sp + 2432#64 + BitVec.ofNat 64 32 = sp + 2464#64 by clear * -; bv_omega]
    conv_lhs => rw [← List.take_append_drop 16 m]
    rw [pointsToBytes_append, show (m.take 16).length = 16 by simp [hm],
      show sp + 2432#64 + BitVec.ofNat 64 16 = sp + 2448#64 by clear * -; bv_omega, sepConj_assoc]
  rw [stackAt_1136_split_720 sp] at hPm
  refine SepWP.weaken_pre (Entails.trans hPm (show _ ⊢
    Keccak2SlicesRW (sp + 30448#64) (sp + 2432#64) (sp + 2432#64) (m ++ hPk).length (m ++ hPk).length ∗
    ((sp + 2432#64) ↦ₛ (m ++ hPk)) ∗ memRegion (sp + 4160#64) 64 ∗
    memRegion (sp + 14432#64) 64 ∗ stackAt sp 720 ∗
    (memRegion (sp - 1136#64) 416 ∗ ((sp + 28368#64) ↦ₛ m) ∗ SpilledDecapsLo sp m ∗
      SpilledDecapsHi sp m ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      ((skA + 3104#64) ↦ₛ hPk) ∗ Rest) by rw [hcat]; sep_frame)) ?_
  have hlt : (m ++ hPk).length < 72 := by simp [hm, hhPk]
  wp_call (blk00_rw1_06 blkPl06.base) (sp + 30448#64, sp + 2432#64, sp + 4160#64, sp + 14432#64, m ++ hPk)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, by simpa [State.spAligned, hsp_sf, ← hsp] using hspA,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 30448#64) (sp + 2432#64) (sp + 2432#64)
    (m ++ hPk).length (m ++ hPk).length
  have hin_reg : ((sp + 2432#64) ↦ₛ (m ++ hPk)) ⊢ memRegion (sp + 2432#64) 64 := by
    have h := pointsToBytes_entails_memRegion (sp + 2432#64) (m ++ hPk)
    rwa [show (m ++ hPk).length = 64 by simp [hm, hhPk]] at h
  have hout1_reg : ((sp + 14432#64) ↦ₛ sha3_512List (m ++ hPk)) ⊢ memRegion (sp + 14432#64) 64 := by
    have h := pointsToBytes_entails_memRegion (sp + 14432#64) (sha3_512List (m ++ hPk))
    rwa [sha3_512List_len (m ++ hPk)] at h
  have hm_reg : ((sp + 28368#64) ↦ₛ m) ⊢ memRegion (sp + 28368#64) 32 := by
    have h := pointsToBytes_entails_memRegion (sp + 28368#64) m; rwa [hm] at h
  rw [hspm, stackAt_1136_split_720 sp]
  unfold SpilledDecapsWords
  exact entails_sub hslices (by sep_frame)
    (entails_sub hin_reg (by sep_frame)
      (entails_sub hout1_reg (by sep_frame)
        (entails_sub hm_reg (by sep_frame) (by sep_frame))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1
