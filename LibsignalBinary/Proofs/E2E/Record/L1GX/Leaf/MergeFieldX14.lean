/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on tag 14 (`pending_kyber_pre_key`)

Proves `mergeFieldX14_ok` (`0x581c`) on `GenFieldX.kyber i ct` (arbitrary `u32` `pre_key_id`
and 1569-byte ciphertext) starting from `pending_kyber_pre_key = None`.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX14

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq

private theorem wt_and_ff_eq_mf14 (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    r2.truncate 32 &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h ⊢
  change (r2.toNat % 4294967296 &&& (2 ^ 8 - 1)) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem wt_and_ff_64_eq_mf14 (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 r2) &&& 255#64) = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h ⊢
  change (((r2.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem post_of_decode_mf14 {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.decodeVarintSliceSpec A0).post
        ⟨sp0 - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr := by
  dsimp only [Prost.decodeVarintSliceSpec]
  rw [decode_kyber_result_mf14 hct, hsp, bytes_kyber_split_mf14, pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

private theorem post_of_bytesMerge_mf14 (ss bufRef slot ptr sp0 : BitVec 64)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.bytesMergeRawSpec A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ⌜Prost.BytesMergeCapOk cap' tail.length⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_mf14 (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    prostSSGXAt A0 ss (v.apply (GenFieldX.kyber 0#32 ct)) ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (prostSSGXAt_kyber_some_fold A0 ss cap' ptr' v 0#32 ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

/-! ## Postcondition assembly for `i ≠ 0#32` -/

private theorem post_of_decode_ne_mf14 (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length =
    1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.decodeVarintSliceSpec A0).post
        ⟨sp0 - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr := by
  dsimp only [Prost.decodeVarintSliceSpec]
  rw [decode_kyber_ne_result_mf14 i hct, hsp, bytes_kyber_ne_split_mf14,
      pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

private theorem pre_to_int32Merge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) (Fr : SepProp) :
    ((ss + 320#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
      memRegion (sp0 - 240#64 - 16144#64) 7872 ∗
      stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack ∗ Fr ⊢
    (memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.int32MergeStack) ∗
    (memRegion (sp0 - 240#64 - 16144#64) 7792 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  refine Entails.trans (sepConj_mono_left (Prost.pointsTo32_entails_memRegion4 (ss +
      320#64) 0#32)) ?_
  apply Entails.of_eq
  rw [← sepConj_assoc (memRegion (sp0 - 240#64 - 16144#64) 7872),
      decode_to_int32Merge_stack_mf14 (sp0 - 240#64)]
  ac_rfl

private theorem post_of_int32Merge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.int32MergeSpec A0).post
        ⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ((ss + 320#64) ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ kyberPtr2 ptr i) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.int32MergeStack ∗ Fr := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.int32MergeSpec]
  rw [mergeUint32_kyberIdBytes i tail]
  dsimp only
  rw [hsp, sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  simp only [sepConj_assoc]
  ac_rfl

private theorem post_of_bytesMerge_ne_mf14 (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.bytesMergeRawSpec A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 16144#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ⌜Prost.BytesMergeCapOk cap' tail.length⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail,
      stackAt_sub_to_bytesMerge_mf14 (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_ne_mf14 (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    prostSSGXAt A0 ss (v.apply (GenFieldX.kyber i ct)) ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ i) ∗
      memRegion (ss + 324#64) 4 ∗ restX14 A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (prostSSGXAt_kyber_some_fold A0 ss cap' ptr' v i ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

private theorem sat_pure_true_mf14 {m : Memory} {φ : Prop} {X R : SepProp} (hφ : φ)
    (h : m ⊨ (X ∗ emp) ∗ R) : m ⊨ (⌜φ⌝ ∗ X) ∗ R := by
  rw [sepConj_emp] at h
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, h⟩

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX14
