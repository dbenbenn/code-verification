/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# `SessionStructure::merge_field` on Tag 9P (`pending_pre_key`)

Verifies `mergeField9PW_spk_none_ok`, `mergeField9PW_spk_some_ok`, `mergeField9PPendingW_ok`
(over `pendingAt9P`), and `mergeField9PW_ok` (over `prostSSGXNoPqAt_x9pW`) on `SP2Ext` at
`mergeFieldStackX = 32768` with slice length `< 2 ^ 62`.
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
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Payload and cursor helpers for `pendingSpk none` and `pendingSpk (some i)` -/

theorem pendingSpk_none_payload_eq_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload =
      BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ::
        18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody none k spk =
      18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
    unfold pendingSpkBody optUint32Field; rw [hl, hs]; simp
  have hblen : (pendingSpkBody none k spk).length =
      36 + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p (n := 36 + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_none_payload_length_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload.length =
      37 + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem pendingSpk_some_payload_eq_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload =
      BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length) ::
        8#8 :: (encodeVarint (i.setWidth 64) ++
          (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody (some i) k spk =
      8#8 :: (encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
    unfold pendingSpkBody optUint32Field
    rw [hl, hs]
    simp [encodeKey, encodeVarint, encodeVarintAux, WireType.toNat]
  have hblen : (pendingSpkBody (some i) k spk).length =
      37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p
    (n := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_some_payload_length_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload.length =
      38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem sliceCursorAt_unfold_spk_none_x9p (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length +
        tail.length)) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenFieldX.pendingSpk none k spk).payload ++ tail).length =
      37 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk]
  rw [hlen, pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

theorem sliceCursorAfter_fold_spk_none_x9p (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗
      ((ptr + 36#64) ↦₈ 24#8) ∗
      ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.pendingSpk none k spk).payload ++ tail).length - tail.length =
      37 + (encodeVarint (spk.signExtend 64)).length := by
    rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk]; omega
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have h37 : BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length) =
      37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [BitVec.ofNat_add]
  have hptr : ptr + BitVec.ofNat 64 (37 + (encodeVarint (spk.signExtend 64)).length) =
      ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [h37]; bv_lin
  rw [hsub, hptr, pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin,
    show ptr + 3#64 + BitVec.ofNat 64 33 = ptr + 36#64 by bv_lin,
    show ptr + 36#64 + 1#64 = ptr + 37#64 by bv_lin]
  ac_rfl

theorem sliceCursorAt_unfold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32)
    {k : List (BitVec 8)} (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32)
    (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length + tail.length)) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ (encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))))) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail).length =
      38 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length + tail.length := by
    rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk]
  rw [hlen, pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

theorem sliceCursorAfter_fold_spk_some_x9p (slot ptr : BitVec 64) (i : BitVec 32)
    {k : List (BitVec 8)} (hk : k.length = 33) {spk : BitVec 32} (hspk : spk ≠ 0#32)
    (tail : List (BitVec 8)) :
    (slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter pendingPtr2
  have hsub : ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail).length - tail.length =
      38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
    rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk]; omega
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have h38 : BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length) =
      2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin
  have hptr : ptr + BitVec.ofNat 64 (38 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length) =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length := by
    rw [h38]; bv_lin
  rw [hsub, hptr, pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.cons_append, List.append_assoc, pointsToBytes_cons, pointsToBytes_append, hk,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 1#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 2#64 + BitVec.ofNat 64 33 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 by bv_lin,
    show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 35#64 + 1#64 =
      ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length + 36#64 by bv_lin]
  ac_rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

private theorem final_post_entails_spk_none_x9pWA (A : RustAlloc) (ss cap' ptr' v24 : BitVec 64)
    (v : SSGX) (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗ bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗ (ptr + 2#64) ↦ₛ (33#8 :: k) ∗ (ptr + 36#64) ↦₈ 24#8 ∗
        ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64) ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
          (ptr + 1#64) ↦₈ 18#8 ∗ (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗
          (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗
          (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
          (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160))) ⊢
    pendingAt9P A ss (v.apply (.pendingSpk none k spk)) ∗ bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_none_x9p slot ptr hk hspk tail]
  refine Entails.trans (Entails.trans (Q :=
    (vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& 18446744069414584320#64 ||| 0#64)) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗ memRegion (ss + 0x124#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    (((slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗ ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗ ((ptr + 36#64) ↦₈ 24#8) ∗
      ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗ A.pool) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl)
    (sepConj_mono (pendingAt9P_post_fold_spk_none A ss cap' ptr' v24 v k spk)
      (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
        r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)))
    (by apply Entails.of_eq; ac_rfl)

private theorem final_post_entails_spk_some_x9pWA (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗ bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗ A.pool ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A (ss + 248#64) cap' ptr' k ∗ (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗ (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗ memRegion (ss + 292#64) 4 ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗ (ptr + 1#64) ↦₈ 8#8 ∗
            (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
            (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
            (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
            (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160)))) ⊢
    pendingAt9P A ss (v.apply (.pendingSpk (some i) k spk)) ∗ bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
      A.pool ∗ stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Entails.trans (Q :=
    (vecU8At A (ss + 0xf8#64) cap' ptr' k ∗ ((ss + 0x110#64) ↦₃₂ 1#32) ∗
      ((ss + 0x114#64) ↦₃₂ i) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4) ∗ (bufRef ↦₆₄ slot) ∗
    (((slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗ ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗ (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗ ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗ A.pool) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗ (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗ (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl)
    (sepConj_mono (pendingAt9P_post_fold_spk_some A ss cap' ptr' v i k spk)
      (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
        r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)))
    (by apply Entails.of_eq; ac_rfl)

end Symbolic.Swarm.TRREF.B3DeserQ
