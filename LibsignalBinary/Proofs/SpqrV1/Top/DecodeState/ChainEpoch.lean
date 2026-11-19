/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainEpochPB` Field Merge Helpers (`0x53860..0x53928`)

Verifies the per-field handlers inside the inlined `ChainEpochPB::merge` loop of `spqr::decode_state`:
tag 1 (`send`, `0x538f0`), tag 2 (`recv`, `0x538b8`), and unknown-tag `skip_field(depth=98)` (`0x53860`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Panic-Aware Call Wrapper for `EpochDirection::merge` (`0x4f544`) -/

theorem optEpochDirectionPB_none_split48 (a : BitVec 64) :
    memRegion (a + 8#64) 48 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₃₂ w6) ∗
        memRegion (a + 52#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 8#64) 8 16 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 8 8 (by decide)
  have hs6 := ProofLib.memRegion_split ((((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 4 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6
  rw [hs1, hs2, hs3, hs4, hs5, hs6,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64),
    ProofLib.memRegion_eight (a + 32#64),
    ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_four (a + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem optEpochDirectionPBCapOkAt_some (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    optEpochDirectionPBCapOkAt A a remLen (some d) = epochDirectionPBCapOkAt A a remLen d := rfl

theorem optEpochDirectionPBCapOkAt_none (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optEpochDirectionPBCapOkAt A a remLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

theorem optEpochDirectionPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

@[expose] def epochDirectionPBCapOkRestAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (cap1 : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  (∃∗ ptr1 : BitVec 64,
    ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
    vecU8Heap A cap1 ptr1 d.next) ∗
  vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 0x34#64) 4

theorem epochDirectionPBCapOkAt_expose_cap (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢
      ∃∗ cap1 : BitVec 64,
        ⌜BytesMergeCapOk cap1 remLen ∧ cap1.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap1) ∗
        epochDirectionPBCapOkRestAt A a remLen cap1 d := by
  unfold epochDirectionPBCapOkAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap1
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  simp only [sepConj_assoc]
  have hlt_ent := vecU8Heap_cap_lt A cap1 ptr1 d.next
  have hreord1 :
      (a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8Heap A cap1 ptr1 d.next ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 =
      vecU8Heap A cap1 ptr1 d.next ∗
        ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
          ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono_left hlt_ent) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  apply Entails.pure_right ⟨hcap, hcap_lt⟩
  unfold epochDirectionPBCapOkRestAt
  have hreord2 :
      vecU8Heap A cap1 ptr1 d.next ∗ ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) =
      (a ↦₆₄ cap1) ∗
        (((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8Heap A cap1 ptr1 d.next) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 := by ac_rfl
  rw [hreord2]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right ptr1 (Entails.refl _)))

attribute [local irreducible] skipField Proto.mergeMessage Proto.spqrDecodeState

theorem epochDirectionPBCapOkAt_fold_cap (A : RustAlloc) (a cap1 : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) (hcap : BytesMergeCapOk cap1 remLen) :
    (a ↦₆₄ cap1) ∗ epochDirectionPBCapOkRestAt A a remLen cap1 d ⊢
      epochDirectionPBCapOkAt A a remLen d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBCapOkRestAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 ?_)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_right hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  exact Entails.of_eq (by ac_rfl)

theorem chainEpochPBCapOkAt_eq (A : RustAlloc) (sp : BitVec 64) (remLen : Nat) (ep : ChainEpochPB) :
    chainEpochPBCapOkAt A (sp - 688#64) remLen ep =
      optEpochDirectionPBCapOkAt A (sp - 688#64) remLen ep.send ∗
      optEpochDirectionPBCapOkAt A (sp - 632#64) remLen ep.recv := by
  unfold chainEpochPBCapOkAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

theorem chainEpochPBAt_eq (A : RustAlloc) (sp : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A (sp - 688#64) ep =
      optEpochDirectionPBAt A (sp - 688#64) ep.send ∗
      optEpochDirectionPBAt A (sp - 632#64) ep.recv := by
  unfold chainEpochPBAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

theorem epochLoop_cursor_to_epochErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remSt remEp : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) remEp curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommon, decodeStateEpochErrFrame, decodeStateEpochErrTailFrame]
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have h3 := chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) remEp curEpoch
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  have hreord :
      (memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesAt b ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesAt b ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem epochLoop_calleeErr_to_epochErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (remSt : Nat) (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateEpochErrFrame H_inner b A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommon, decodeStateEpochErrFrame, decodeStateEpochErrTailFrame]
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hst := Entails.trans (sepConj_mono_left h1) (vecArg_join_bytes A x.st)
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesAt b ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesAt b ∗
        (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
            ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
          vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono h2
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

end CryptoVerification.SpqrV1.Top.DecodeState
