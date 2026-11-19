/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-! # `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`, `+1104`) — Part A -/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Callee Relocation Lemmas for `States::from_pb` (`0x5a0a4`) -/

/-- Seven 64-bit words of a 56-byte `Option<ProtoPolynomialEncoder>` at `a`. -/
@[expose] def v1_optProtoPolyEncoderWordsAt (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
  ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
  ((a + 48#64) ↦₆₄ w48)

/-- Heap and pure constraints of `Option<ProtoPolynomialEncoder>` associated with words `w0..w48`. -/
@[expose] def v1_optProtoPolyEncoderHeap (A : RustAlloc) :
    Option ProtoPolynomialEncoder → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, w0, _, _, _, _, _, _ => ⌜w0 = noneCap⌝
  | some pb, w0, w8, w16, w24, w32, w40, w48 =>
    ⌜w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
      w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx⌝ ∗
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys

theorem v1_optProtoPolyEncoderWordsAt_entails_56 (a w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ⊢ memRegion a 56 := by
  unfold v1_optProtoPolyEncoderWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

theorem v1_pointsTo32_4_entails_pointsTo64 (a : BitVec 64) (lo : BitVec 32) :
    (a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4 ⊢
      ∃∗ w : BitVec 64, ⌜w.extractLsb' 0 32 = lo⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro hi
  refine Entails.sepExists_right (hi ++ lo) ?_
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_kernel
  refine Entails.pure_right hlo ?_
  rw [ProofLib.pointsTo32_pair a lo hi]
  exact Entails.refl _

theorem v1_pointsTo64_entails_pointsTo32_4 (a w : BitVec 64) (lo : BitVec 32)
    (hlo : w.extractLsb' 0 32 = lo) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4 := by
  have hw : w = w.extractLsb' 32 32 ++ lo := by
    rw [← hlo]
    bv_kernel
  rw [hw, ← ProofLib.pointsTo32_pair a lo (w.extractLsb' 32 32)]
  exact sepConj_mono_right (ProofLib.pointsTo32_entails_memRegion _ _)

theorem v1_optProtoPolyEncoderAt_unpack (A : RustAlloc) (a : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A a optEnc ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64,
      ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
        v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 := by
  cases optEnc with
  | none =>
    dsimp only [optProtoPolynomialEncoderAt, optProtoPolynomialEncoderNoneTailSize,
      v1_optProtoPolyEncoderHeap]
    have hsplit : memRegion (a + 8#64) 48 ⊢
        (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
        (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
        (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
        (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
        (∃∗ w40 : BitVec 64, (a + 40#64) ↦₆₄ w40) ∗
        (∃∗ w48 : BitVec 64, (a + 48#64) ↦₆₄ w48) := by
      exact split_top <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| split_step (mem64_entails _) <|
        split_step (mem64_entails _) <| mem64_entails _
    refine Entails.trans (sepConj_mono_right hsplit) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    apply Entails.sepExists_elim; intro w40
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w16
    apply Entails.sepExists_elim; intro w8
    refine Entails.sepExists_right noneCap (Entails.sepExists_right w8
      (Entails.sepExists_right w16 (Entails.sepExists_right w24
        (Entails.sepExists_right w32 (Entails.sepExists_right w40
          (Entails.sepExists_right w48 ?_))))))
    unfold v1_optProtoPolyEncoderWordsAt
    exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  | some pb =>
    dsimp only [optProtoPolynomialEncoderAt, protoPolynomialEncoderAt,
      vecVecU8At, vecOf, vecAt, vecHeader,
      protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
      protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize,
      v1_optProtoPolyEncoderHeap]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w24
    apply Entails.sepExists_elim; intro w32
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w8
    have h48 := v1_pointsTo32_4_entails_pointsTo64 (a + 48#64) pb.idx
    have ha48 : (a + 48#64) + 4#64 = a + 52#64 := by bv_omega
    rw [ha48] at h48
    have hcap : vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗ vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts := by
      unfold vecBuf
      apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
      exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hcap (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right h48)))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro w48
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    rw [ha32, ha40]
    refine Entails.trans (Entails.of_eq (show _ =
      ⌜w0.toNat < 2 ^ 63⌝ ∗ ⌜w48.extractLsb' 0 32 = pb.idx⌝ ∗
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗
       ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗ ((a + 48#64) ↦₆₄ w48) ∗
       vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
       vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys) by ac_rfl)) ?_
    apply Entails.pure_left; intro hw0
    apply Entails.pure_left; intro hw48
    refine Entails.sepExists_right w0 (Entails.sepExists_right w8
      (Entails.sepExists_right (BitVec.ofNat 64 pb.pts.length)
        (Entails.sepExists_right w24 (Entails.sepExists_right w32
          (Entails.sepExists_right (BitVec.ofNat 64 pb.polys.length)
            (Entails.sepExists_right w48 ?_))))))
    unfold v1_optProtoPolyEncoderWordsAt
    have hpure : w0.toNat < 2 ^ 63 ∧ BitVec.ofNat 64 pb.pts.length = BitVec.ofNat 64 pb.pts.length ∧
        BitVec.ofNat 64 pb.polys.length = BitVec.ofNat 64 pb.polys.length ∧
        w48.extractLsb' 0 32 = pb.idx := ⟨hw0, rfl, rfl, hw48⟩
    exact Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by ac_rfl))

theorem v1_optProtoPolyEncoderAt_pack_some (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderWordsAt a w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A (some pb) w0 w8 w16 w24 w32 w40 w48 ⊢
      protoPolynomialEncoderAt A a pb := by
  dsimp only [v1_optProtoPolyEncoderWordsAt, v1_optProtoPolyEncoderHeap,
    protoPolynomialEncoderAt, vecVecU8At, vecOf, vecAt, vecHeader,
    protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
    protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
      w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx⌝ ∗
    (((a + 48#64) ↦₆₄ w48) ∗
     ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦₆₄ w32) ∗ ((a + 40#64) ↦₆₄ w40) ∗
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w0 w8 pb.pts ∗
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) w24 w32 pb.polys)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨_, rfl, rfl, hw48⟩
  have h48 := v1_pointsTo64_entails_pointsTo32_4 (a + 48#64) w48 pb.idx hw48
  have ha48 : (a + 48#64) + 4#64 = a + 52#64 := by bv_omega
  rw [ha48] at h48
  refine Entails.trans (sepConj_mono_left h48) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right w24 (Entails.sepExists_right w32
    (Entails.sepExists_right w0 (Entails.sepExists_right w8 ?_)))
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  exact Entails.of_eq (by ac_rfl)

theorem v1_optProtoPolyEncoderHeap_extract_w0 (A : RustAlloc)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 ⊢
      ⌜match optEnc with | none => w0 = noneCap | some _ => w0.toNat < 2 ^ 63⌝ ∗
      v1_optProtoPolyEncoderHeap A optEnc w0 w8 w16 w24 w32 w40 w48 := by
  cases optEnc with
  | none =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    conv => lhs; rw [← sepConj_emp ⌜w0 = noneCap⌝]
    apply Entails.pure_left; intro hw0
    exact Entails.pure_right hw0 (Entails.trans (Entails.pure_right hw0 (Entails.refl _)) (Entails.of_eq (sepConj_emp _)))
  | some pb =>
    dsimp only [v1_optProtoPolyEncoderHeap]
    apply Entails.pure_left; rintro ⟨hw0, hw16, hw40, hw48⟩
    have hp : w0.toNat < 2 ^ 63 ∧ w16 = BitVec.ofNat 64 pb.pts.length ∧
        w40 = BitVec.ofNat 64 pb.polys.length ∧ w48.extractLsb' 0 32 = pb.idx :=
      ⟨hw0, hw16, hw40, hw48⟩
    exact Entails.pure_right hw0 (Entails.pure_right hp (Entails.refl _))

theorem v1_tbz_63_of_lt {w : BitVec 64} (h : w.toNat < 2 ^ 63) :
    ((w >>> 63) &&& 1#64 == 0#64) = true := by
  have h1 : (w >>> 63) &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt h, Nat.zero_and]
    rfl
  simp [h1]

theorem v1_stackAt_encoder_split_dropStack48 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      memRegion (sp - 5152#64) 1008 ∗ stackAt sp dropStack48 :=
  stackAt_split_bottom sp dropStack48 1008 (by decide)

theorem v1_memRegion_1496_split_232 (fsp : BitVec 64) :
    memRegion fsp 1496 ⊢
      memRegion fsp 232 ∗
      (∃∗ w232 : BitVec 64, (fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1256 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    Entails.refl _

theorem v1_merge_stack_1496_56_752 (fsp w232 : BitVec 64) :
    memRegion fsp 232 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      memRegion (fsp + 240#64) 1256 ∗
      memRegion (fsp + 1496#64) 56 ∗
      memRegion (fsp + 1552#64) 752 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v1_shl8_extract_0_8 (w : BitVec 64) :
    ((w &&& 72057594037927935#64) <<< 8).extractLsb' 0 8 = 0#8 := by
  bv_kernel

theorem v1_merge_stack_192_216_224_1496 (fsp w192 w216 w224 : BitVec 64) :
    memRegion fsp 192 ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗
      memRegion (fsp + 200#64) 16 ∗
      ((fsp + 216#64) ↦₆₄ w216) ∗
      ((fsp + 224#64) ↦₆₄ w224) ∗
      memRegion (fsp + 232#64) 1264 ⊢
      memRegion fsp 1496 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

/-- Heap and pure constraints of `Option<ProtoAuthenticator>` associated with words `u56..u96`. -/
@[expose] def v1_optProtoAuthHeap (A : RustAlloc) :
    Option ProtoAuthenticator → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | none, u56, _, _, _, _, _ => ⌜u56 = noneCap⌝
  | some auth, u56, u64, u72, u80, u88, u96 =>
    ⌜u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 auth.rootKey.length ∧
      u96 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
    vecU8Payload A u56 u64 auth.rootKey ∗
    vecU8Payload A u80 u88 auth.macKey

@[local simp, local arm64_norm, local wp_norm]
theorem v1_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-- Thirteen 64-bit words of a 104-byte `Option<V1State.Unchunked.HeaderSent>` at `a`. -/
@[expose] def v1_ucWordsAt (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) : SepProp :=
  (a ↦₆₄ u8) ∗ ((a + 8#64) ↦₆₄ u16) ∗ ((a + 16#64) ↦₆₄ u24) ∗
  ((a + 24#64) ↦₆₄ u32) ∗ ((a + 32#64) ↦₆₄ u40) ∗ ((a + 40#64) ↦₆₄ u48) ∗
  ((a + 48#64) ↦₆₄ u56) ∗ ((a + 56#64) ↦₆₄ u64) ∗ ((a + 64#64) ↦₆₄ u72) ∗
  ((a + 72#64) ↦₆₄ u80) ∗ ((a + 80#64) ↦₆₄ u88) ∗ ((a + 88#64) ↦₆₄ u96) ∗
  ((a + 96#64) ↦₆₄ u104)

theorem v1_ucWordsAt_entails_104
    (a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 : BitVec 64) :
    v1_ucWordsAt a u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ⊢ memRegion a 104 := by
  unfold v1_ucWordsAt
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Drop.pointsTo64_entails_memRegion _ _

/-- Ten 128-bit (`↦₁₂₈`) chunks covering `pbA + 8..168` (`160` bytes). -/
@[expose] def v1_pb128At (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : SepProp :=
  ((pbA + 8#64) ↦₁₂₈ (u16 ++ u8)) ∗
  ((pbA + 24#64) ↦₁₂₈ (u32 ++ u24)) ∗
  ((pbA + 40#64) ↦₁₂₈ (u48 ++ u40)) ∗
  ((pbA + 56#64) ↦₁₂₈ (u64 ++ u56)) ∗
  ((pbA + 72#64) ↦₁₂₈ (u80 ++ u72)) ∗
  ((pbA + 88#64) ↦₁₂₈ (u96 ++ u88)) ∗
  ((pbA + 104#64) ↦₁₂₈ (w0 ++ u104)) ∗
  ((pbA + 120#64) ↦₁₂₈ (w16 ++ w8)) ∗
  ((pbA + 136#64) ↦₁₂₈ (w32 ++ w24)) ∗
  ((pbA + 152#64) ↦₁₂₈ (w48 ++ w40))

theorem v1_uc_and_enc_words_eq_pb128
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 =
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 := by
  dsimp only [v1_ucWordsAt, v1_optProtoPolyEncoderWordsAt, v1_pb128At]
  simp only [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128, arm64_norm]

theorem v1_pb128_entails_112_and_enc
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 ⊢
      memRegion pbA 112 ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 := by
  rw [← v1_uc_and_enc_words_eq_pb128]
  have h104 := v1_ucWordsAt_entails_104 (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
  have h112 : (pbA ↦₆₄ 0x8000000000000001#64) ∗ memRegion (pbA + 8#64) 104 ⊢ memRegion pbA 112 :=
    collapse_top <| collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104) ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 by ac_rfl)) ?_
  exact sepConj_mono (Entails.trans (sepConj_mono_right h104) h112) (Entails.refl _)

theorem v1_pb128_entails_full_224
    (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
     w0 w8 w16 w24 w32 w40 w48 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize := by
  have h1 := v1_pb128_entails_112_and_enc pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
    w0 w8 w16 w24 w32 w40 w48
  have h56 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48
  have h224 : memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    ((pbA ↦₆₄ 0x8000000000000001#64) ∗
      v1_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104
        w0 w8 w16 w24 w32 w40 w48) ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion pbA 112 ∗
    v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (pbA + 168#64) 56 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h56)) h224

end CryptoVerification.SpqrV1.States.FromPb
