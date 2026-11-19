/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# `SessionStructure::merge_field` on Tag 14 (`pending_kyber_pre_key`)

Verifies `mergeField14KyberWA_ok`, `mergeField14KyberW_ok` (over `kyberAt14`), `mergeField14WA_ok`,
and `mergeField14W_ok` (over `prostSSGXNoPqAt_x14`) on `SP2Ext` at `mergeFieldStackX = 32768` with
slice length `< 2 ^ 62`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq
attribute [local wp_norm] kyberB0_signExtend_getLsbD_63 kyberB0_signExtend_getLsbD_63_beq

private theorem decode_kyber_result_mf14A (A : RustAlloc) {ct : List (BitVec 8)}
    (_hct : ct.length = 1569) (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A ret (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)
      (decodeVarint (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber]; dsimp only [Prost.varintSliceResultAt]
  have : (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = 2 := by simp only [List.length_cons]; omega
  rw [this]

private theorem decode_kyber_ne_result_mf14A (A : RustAlloc) (i : BitVec 32) {ct : List (BitVec 8)}
    (_hct : ct.length = 1569) (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A ret (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)
      (decodeVarint (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) =
      (ret ↦₆₄ 0#64) ∗
        ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber_ne]; dsimp only [Prost.varintSliceResultAt]
  have : (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail).length -
      (8#8 :: kyberIdBytes i ct tail).length = 2 := by simp only [List.length_cons]; omega
  rw [this]

private theorem post_of_decode_mf14WA (A : RustAlloc) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A).post
        ⟨sp0 - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_result_mf14A A hct, hsp, bytes_kyber_split_mf14, pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega]
  simp only [sepConj_assoc]

private theorem post_of_bytesMerge_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]; dsimp only
  rw [hsp, sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_kyber_mf14WA (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
      A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A ss (v.apply (GenFieldX.kyber 0#32 ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Q :=
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail)) ∗
    A.pool ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A ss cap' ptr' v 0#32 ct) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

private theorem post_of_decode_ne_mf14WA (A : RustAlloc) (i : BitVec 32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A).post
        ⟨sp0 - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_ne_result_mf14A A i hct, hsp, bytes_kyber_ne_split_mf14,
      pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega]
  simp only [sepConj_assoc]

private theorem pre_to_int32Merge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (Fr : SepProp) :
    ((ss + 320#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗ A.pool ∗
      memRegion (sp0 - 240#64 - 32528#64) 7872 ∗
      stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr ⊢
    (memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW) ∗
    (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ Fr) := by
  rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail]
  have hpt32 : ((ss + 320#64) ↦₃₂ 0#32) ⊢ memRegion (ss + 320#64) 4 := by
    rw [ProofLib.memRegion_four]; exact Entails.sepExists_right 0#32 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hpt32) ?_
  apply Entails.of_eq
  rw [← sepConj_assoc (memRegion (sp0 - 240#64 - 32528#64) 7872),
      decode_to_int32Merge_stack_mf14W (sp0 - 240#64)]
  ac_rfl

private theorem post_of_int32Merge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.int32MergeSpecW A).post
        ⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ((ss + 320#64) ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ kyberPtr2 ptr i) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) Prost.X.int32MergeStackW ∗ Fr := by
  dsimp only [Prost.X.int32MergeSpecW]
  rw [mergeUint32_kyberIdBytes i tail]; dsimp only
  rw [hsp, sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail]
  simp only [sepConj_assoc]; ac_rfl

private theorem post_of_bytesMerge_ne_mf14WA (A : RustAlloc) (ss bufRef slot ptr sp0 : BitVec 64)
    (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]; dsimp only
  rw [hsp, sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_ne_kyber_mf14WA (A : RustAlloc) (ss cap' ptr' : BitVec 64)
    (v : SSGX) (bufRef slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
      A.pool ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A ss (v.apply (GenFieldX.kyber i ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Q :=
    (vecU8At A (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ i) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail)) ∗
    A.pool ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A ss cap' ptr' v i ct) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

end Symbolic.Swarm.TRREF.B3DeserQ
