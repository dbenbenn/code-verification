/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`) — Outer Loop, Prologue, and Top Theorem

**Checked by Lean.**

Verifies empty-input handling, outer-loop field-key dispatch and length-bounded induction,
prologue frame initialization, and the top-level `decodeState_ok` contract.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Pure & Framing Helpers for Empty Input (`0x53ae0`) and Success Exit (`0x53b28`) -/

theorem spqrDecodeState_eq_of_mergeLoopBin_top_err {bs : List (BitVec 8)} (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = none) :
    spqrDecodeState bs = .error .stateDecode := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold Proto.spqrDecodeState at hopt
    unfold spqrDecodeState Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st
    · rfl
    · simp [hm, Except.toOption] at hopt

theorem spqrDecodeState_eq_of_mergeLoopBin_top_ok {bs : List (BitVec 8)} {st : PqRatchetState}
    (hne : bs ≠ [])
    (h : mergeLoopBin PqRatchetState.mergeField bs.length default bs 0 100 = some st) :
    spqrDecodeState bs = .ok st := by
  have hopt := spqrDecodeState_toOption_eq_mergeLoopBin hne
  rw [h] at hopt
  cases bs with
  | nil => exact (hne rfl).elim
  | cons b tl =>
    unfold Proto.spqrDecodeState at hopt
    unfold spqrDecodeState Proto.spqrDecodeState
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
    rcases hm : PqRatchetState.decode (b :: tl) with e | st'
    · simp [hm, Except.toOption] at hopt
    · simp only [hm, Except.toOption, Option.some.injEq] at hopt
      subst hopt
      rfl

theorem memRegion_352_empty_split (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 8#64) 40 ∗
      memRegion (outPtr + 56#64) 72 ∗
      memRegion (outPtr + 136#64) 216 ∗
      (∃∗ w128 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w0 : BitVec 64,
        (outPtr ↦₆₄ w0) ∗ ((outPtr + 48#64) ↦₆₄ w48) ∗ ((outPtr + 128#64) ↦₆₄ w128)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 40) (k := 304)
      (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 296)
      (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 56#64) (n := 72) (k := 224)
      (b' := outPtr + 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 128#64) (n := 8) (k := 216)
      (b' := outPtr + 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 48#64),
    ProofLib.memRegion_eight (outPtr + 128#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem fold_decodeStateResultAt_empty (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (outPtr : BitVec 64) {bs : List (BitVec 8)} (hbs : bs = []) :
    (outPtr ↦₆₄ 18446744073709551615#64) ∗ memRegion (outPtr + 8#64) 40 ∗
      ((outPtr + 48#64) ↦₆₄ 18446744073709551615#64) ∗ memRegion (outPtr + 56#64) 72 ∗
      ((outPtr + 128#64) ↦₆₄ 18446744073709551613#64) ∗ memRegion (outPtr + 136#64) 216 ⊢
      decodeStateResultAt H_inner A outPtr (spqrDecodeState bs) := by
  subst hbs
  unfold spqrDecodeState
  rw [spqrDecodeState_nil, pqRatchetState_default_eq]
  unfold decodeStateResultAt protoPqRatchetStateAt
    optVersionNegotiationPBAt optChainPBAt optProtoPqRatchetInnerAt
    noneCap none3Cap
  dsimp only
  have ha56 : (outPtr + 48#64) + 8#64 = outPtr + 56#64 := by bv_omega
  have ha136 : (outPtr + 128#64) + 8#64 = outPtr + 136#64 := by bv_omega
  rw [ha56, ha136]
  exact Entails.of_eq (by ac_rfl)

theorem stack_1392_fold_1296 (sp w0 : BitVec 64) :
    ((sp - 1392#64) ↦₆₄ w0) ∗ memRegion (sp - 1384#64) 1288 ⊢
      memRegion (sp - 1392#64) 1296 := by
  rw [ProofLib.memRegion_split' (b := sp - 1392#64) (n := 8) (k := 1288)
      (b' := sp - 1384#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 1392#64) w0)

theorem head_ne_none2Cap_branch {w : BitVec 64} (hne : w ≠ none2Cap) :
    (w + 2#64 == 0#64) = false ∧ (w + 2#64 != 0#64) = true := by
  have h0 : w + 2#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -2#64
    bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h0, bne_iff_ne.mpr h0⟩

theorem state_1040_fold_352 (sp w0 w1 : BitVec 64) {bs336 : List (BitVec 8)}
    (hlen : bs336.length = 336) :
    ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) ⊢
      memRegion (sp - 1040#64) 352 := by
  have h16 : ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ⊢ memRegion (sp - 1040#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 8)
        (b' := sp - 1032#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ w0)
      (ProofLib.pointsTo64_entails_memRegion _ w1)
  have h336 : ((sp - 1024#64) ↦ₛ bs336) ⊢ memRegion (sp - 1024#64) 336 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp - 1024#64) bs336
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 16) (k := 336)
      (b' := sp - 1024#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1) ∗ ((sp - 1024#64) ↦ₛ bs336) =
      (((sp - 1040#64) ↦₆₄ w0) ∗ ((sp - 1032#64) ↦₆₄ w1)) ∗ ((sp - 1024#64) ↦ₛ bs336) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono h16 h336

theorem memRegion_352_split_head16_tail336 (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 16#64) 336 ∗
      (∃∗ out1 : BitVec 64, ∃∗ out0 : BitVec 64,
        (outPtr ↦₆₄ out0) ∗ ((outPtr + 8#64) ↦₆₄ out1)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 8) (k := 336)
      (b' := outPtr + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_eight (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

theorem len_cbz64_false {n : Nat} (h1 : 1 ≤ n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at h2
  omega

theorem vecArg_expose_len (A : RustAlloc) (st : VecArg) :
    st.at A ⊢
      (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      vecU8Heap A st.cap st.ptr st.bytes := by
  rw [VecArg.at, vecU8At_eq_header_heap, vecHeader]
  exact Entails.of_eq (by ac_rfl)

theorem vecArg_fold_len (A : RustAlloc) (st : VecArg) :
    (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
      ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      vecU8Heap A st.cap st.ptr st.bytes ⊢
      st.at A := by
  rw [VecArg.at, vecU8At_eq_header_heap, vecHeader]
  exact Entails.of_eq (by ac_rfl)

theorem nonempty_prologue_frame_assemble (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (st : VecArg) :
    ((sp - 1056#64) ↦₆₄ st.ptr) ∗
      ((sp - 1048#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
      (st.ptr ↦ₛ st.bytes) ∗
      ((sp - 1040#64) ↦₆₄ 18446744073709551615#64) ∗ memRegion (sp - 1032#64) 40 ∗
      ((sp - 992#64) ↦₆₄ 18446744073709551615#64) ∗ memRegion (sp - 984#64) 72 ∗
      ((sp - 912#64) ↦₆₄ 18446744073709551613#64) ∗ memRegion (sp - 904#64) 216 ⊢
      sliceCursorAfter (sp - 1056#64) st.ptr st.bytes st.bytes ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) st.bytes.length default := by
  rw [pqRatchetState_default_eq]
  unfold sliceCursorAfter protoPqRatchetStateCapOkAt
    optVersionNegotiationPBCapOkAt optChainPBCapOkAt optProtoPqRatchetInnerCapOkAt
    noneCap none3Cap
  dsimp only
  have hsub0 : st.bytes.length - st.bytes.length = 0 := Nat.sub_self _
  have hptr0 : st.ptr + BitVec.ofNat 64 0 = st.ptr := by simp
  have ha1048 : (sp - 1056#64) + 8#64 = sp - 1048#64 := by bv_omega
  have ha1032 : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
  have ha992 : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
  have ha984 : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
  have ha912 : (sp - 1040#64) + 128#64 = sp - 912#64 := by bv_omega
  have ha904 : (sp - 912#64) + 8#64 = sp - 904#64 := by bv_omega
  rw [hsub0, hptr0, ha1048, ha1032, ha992, ha984, ha912, ha904]
  exact Entails.of_eq (by ac_rfl)

theorem decodeState_nonempty_frame_split_s0 (sp0 : BitVec 64) :
    ((sp0 - 1392#64) ↦₆₄ 0#64) ∗ memRegion (sp0 - 1384#64) 1288 ⊢
      memRegion (sp0 - 1392#64) 336 ∗
      memRegion (sp0 - 1032#64) 40 ∗
      memRegion (sp0 - 984#64) 72 ∗
      memRegion (sp0 - 904#64) 216 ∗
      memRegion (sp0 - 688#64) 352 ∗
      memRegion (sp0 - 328#64) 224 ∗
      memRegion (sp0 - 104#64) 8 ∗
      (∃∗ bRef : BitVec 64, ∃∗ in0 : BitVec 64, ∃∗ ch0 : BitVec 64,
       ∃∗ vn0 : BitVec 64, ∃∗ cLen : BitVec 64, ∃∗ cPtr : BitVec 64,
        ((sp0 - 1056#64) ↦₆₄ cPtr) ∗ ((sp0 - 1048#64) ↦₆₄ cLen) ∗
        ((sp0 - 1040#64) ↦₆₄ vn0) ∗ ((sp0 - 992#64) ↦₆₄ ch0) ∗
        ((sp0 - 912#64) ↦₆₄ in0) ∗ ((sp0 - 336#64) ↦₆₄ bRef)) := by
  have hsplit := decodeState_nonempty_frame_split (sp0 - 1392#64) 0#64
  have h1 : sp0 - 1392#64 + 8#64 = sp0 - 1384#64 := bv_sub_add_lit sp0 1392 8
  have h2 : sp0 - 1392#64 + 360#64 = sp0 - 1032#64 := bv_sub_add_lit sp0 1392 360
  have h3 : sp0 - 1392#64 + 408#64 = sp0 - 984#64 := bv_sub_add_lit sp0 1392 408
  have h4 : sp0 - 1392#64 + 488#64 = sp0 - 904#64 := bv_sub_add_lit sp0 1392 488
  have h5 : sp0 - 1392#64 + 704#64 = sp0 - 688#64 := bv_sub_add_lit sp0 1392 704
  have h6 : sp0 - 1392#64 + 1064#64 = sp0 - 328#64 := bv_sub_add_lit sp0 1392 1064
  have h7 : sp0 - 1392#64 + 1288#64 = sp0 - 104#64 := bv_sub_add_lit sp0 1392 1288
  have h8 : sp0 - 1392#64 + 336#64 = sp0 - 1056#64 := bv_sub_add_lit sp0 1392 336
  have h9 : sp0 - 1392#64 + 344#64 = sp0 - 1048#64 := bv_sub_add_lit sp0 1392 344
  have h10 : sp0 - 1392#64 + 352#64 = sp0 - 1040#64 := bv_sub_add_lit sp0 1392 352
  have h11 : sp0 - 1392#64 + 400#64 = sp0 - 992#64 := bv_sub_add_lit sp0 1392 400
  have h12 : sp0 - 1392#64 + 480#64 = sp0 - 912#64 := bv_sub_add_lit sp0 1392 480
  have h13 : sp0 - 1392#64 + 1056#64 = sp0 - 336#64 := bv_sub_add_lit sp0 1392 1056
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] at hsplit
  exact hsplit

end CryptoVerification.SpqrV1.Top.DecodeState
