/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainEpochPB` Error Drop & Unwind Blocks

**Checked by Lean.** Verifies the error-unwinding and `ChainEpochPB` drop blocks (`0x53bec..0x53c7c`,
`0x53f30..0x53f4c`, `0x53fd4..0x5403c`) for the nested `ChainEpochPB` merge loop.
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

/-! ## `EpochDirectionPB` / `ChainEpochPB` Drop Memory Helpers -/

theorem optEpochDirectionPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

theorem optEpochDirectionPBAt_some (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

theorem rustBytesVecAt_unfold_drop (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    rustBytesVecAt A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold rustBytesVecAt vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  change
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢ _
  have hreord :
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by ac_rfl
  rw [hreord]
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  apply Entails.pure_right ⟨hle, hlt, hptr⟩
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    have hsplit : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      rw [← ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
      congr 1
      omega
    rw [hsplit]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)))))

theorem epochDirection_send_raw_to_48 (sp ptr1 len1 cap2 ptr2 len2 : BitVec 64) (ctr : BitVec 32) :
    ((sp - 680#64) ↦₆₄ ptr1) ∗ ((sp - 672#64) ↦₆₄ len1) ∗
      ((sp - 664#64) ↦₆₄ cap2) ∗ ((sp - 656#64) ↦₆₄ ptr2) ∗ ((sp - 648#64) ↦₆₄ len2) ∗
      ((sp - 640#64) ↦₃₂ ctr) ∗ memRegion (sp - 636#64) 4 ⊢
      memRegion (sp - 680#64) 48 := by
  have h1 : memRegion (sp - 680#64) 48 =
      memRegion (sp - 680#64) 8 ∗ memRegion (sp - 672#64) 40 :=
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 8) (k := 40) (b' := sp - 672#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 672#64) 40 =
      memRegion (sp - 672#64) 8 ∗ memRegion (sp - 664#64) 32 :=
    ProofLib.memRegion_split' (b := sp - 672#64) (n := 8) (k := 32) (b' := sp - 664#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 664#64) 32 =
      memRegion (sp - 664#64) 8 ∗ memRegion (sp - 656#64) 24 :=
    ProofLib.memRegion_split' (b := sp - 664#64) (n := 8) (k := 24) (b' := sp - 656#64) rfl (by bv_omega) (by decide)
  have h4 : memRegion (sp - 656#64) 24 =
      memRegion (sp - 656#64) 8 ∗ memRegion (sp - 648#64) 16 :=
    ProofLib.memRegion_split' (b := sp - 656#64) (n := 8) (k := 16) (b' := sp - 648#64) rfl (by bv_omega) (by decide)
  have h5 : memRegion (sp - 648#64) 16 =
      memRegion (sp - 648#64) 8 ∗ memRegion (sp - 640#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 648#64) (n := 8) (k := 8) (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  have h6 : memRegion (sp - 640#64) 8 =
      memRegion (sp - 640#64) 4 ∗ memRegion (sp - 636#64) 4 :=
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 4) (k := 4) (b' := sp - 636#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, h4, h5, h6]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap2)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr2)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len2)
            (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ ctr))))))

theorem epochDirection_recv_raw_to_56 (sp cap1 ptr1 len1 cap2 ptr2 len2 : BitVec 64) (ctr : BitVec 32) :
    ((sp - 632#64) ↦₆₄ cap1) ∗ ((sp - 624#64) ↦₆₄ ptr1) ∗ ((sp - 616#64) ↦₆₄ len1) ∗
      ((sp - 608#64) ↦₆₄ cap2) ∗ ((sp - 600#64) ↦₆₄ ptr2) ∗ ((sp - 592#64) ↦₆₄ len2) ∗
      ((sp - 584#64) ↦₃₂ ctr) ∗ memRegion (sp - 580#64) 4 ⊢
      memRegion (sp - 632#64) 56 := by
  have h0 : memRegion (sp - 632#64) 56 =
      memRegion (sp - 632#64) 8 ∗ memRegion (sp - 624#64) 48 :=
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 48) (b' := sp - 624#64) rfl (by bv_omega) (by decide)
  have h1 : memRegion (sp - 624#64) 48 =
      memRegion (sp - 624#64) 8 ∗ memRegion (sp - 616#64) 40 :=
    ProofLib.memRegion_split' (b := sp - 624#64) (n := 8) (k := 40) (b' := sp - 616#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 616#64) 40 =
      memRegion (sp - 616#64) 8 ∗ memRegion (sp - 608#64) 32 :=
    ProofLib.memRegion_split' (b := sp - 616#64) (n := 8) (k := 32) (b' := sp - 608#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 608#64) 32 =
      memRegion (sp - 608#64) 8 ∗ memRegion (sp - 600#64) 24 :=
    ProofLib.memRegion_split' (b := sp - 608#64) (n := 8) (k := 24) (b' := sp - 600#64) rfl (by bv_omega) (by decide)
  have h4 : memRegion (sp - 600#64) 24 =
      memRegion (sp - 600#64) 8 ∗ memRegion (sp - 592#64) 16 :=
    ProofLib.memRegion_split' (b := sp - 600#64) (n := 8) (k := 16) (b' := sp - 592#64) rfl (by bv_omega) (by decide)
  have h5 : memRegion (sp - 592#64) 16 =
      memRegion (sp - 592#64) 8 ∗ memRegion (sp - 584#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 592#64) (n := 8) (k := 8) (b' := sp - 584#64) rfl (by bv_omega) (by decide)
  have h6 : memRegion (sp - 584#64) 8 =
      memRegion (sp - 584#64) 4 ∗ memRegion (sp - 580#64) 4 :=
    ProofLib.memRegion_split' (b := sp - 584#64) (n := 4) (k := 4) (b' := sp - 580#64) rfl (by bv_omega) (by decide)
  rw [h0, h1, h2, h3, h4, h5, h6]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len1)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ cap2)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptr2)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ len2)
              (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ ctr)))))))

theorem epochDirection_recv_none_to_56 (sp w : BitVec 64) :
    ((sp - 632#64) ↦₆₄ w) ∗ memRegion (sp - 624#64) 48 ⊢
      memRegion (sp - 632#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp - 632#64) (n := 8) (k := 48) (b' := sp - 624#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 632#64) w)

theorem epoch_regions_to_err_frame (sp : BitVec 64) :
    memRegion (sp - 680#64) 48 ∗ memRegion (sp - 632#64) 56 ∗ memRegion (sp - 576#64) 240 ⊢
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
  have h1 : memRegion (sp - 680#64) 48 =
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 8 :=
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8) (b' := sp - 640#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 640#64) 304 =
      memRegion (sp - 640#64) 8 ∗ memRegion (sp - 632#64) 296 :=
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296) (b' := sp - 632#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 632#64) 296 =
      memRegion (sp - 632#64) 56 ∗ memRegion (sp - 576#64) 240 :=
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240) (b' := sp - 576#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact Entails.of_eq (by ac_rfl)

/-- Common stack/heap frame during `ChainEpochPB` error drop (excluding `[sp + 0x2c0..0x330]` =
    `s0.sp - 688#64 .. s0.sp - 576#64`, which holds the `112`-byte `ChainEpochPB`). -/
abbrev decodeStateEpochErrTailFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  x.st.at A ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 576#64) 240 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Complete `ChainEpochPB` error frame: `chainEpochPBAt A (s0.sp - 688#64) curEpoch` +
    `decodeStateEpochErrTailFrame H_inner b A x curSt s0`. -/
abbrev decodeStateEpochErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) (curSt : PqRatchetState) (curEpoch : ChainEpochPB)
    (s0 : State) : SepProp :=
  chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
  decodeStateEpochErrTailFrame H_inner b A x curSt s0

/-! ## `ChainEpochPB` Error Drop Path (`0x53c5c..0x53c98`, `0x53c28..0x53c58`, `0x53c18..0x53c24`, `0x54014..0x54024`) -/

theorem scratch_336_split_e8_40 (sp : BitVec 64) :
    memRegion (sp - 336#64) 240 ⊢
      memRegion (sp - 336#64) 8 ∗
      memRegion (sp - 320#64) 40 ∗
      memRegion (sp - 280#64) 184 ∗
      (∃∗ w_e8 : BitVec 64, (sp - 328#64) ↦₆₄ w_e8) := by
  have h1 : memRegion (sp - 336#64) 240 =
      memRegion (sp - 336#64) 8 ∗ memRegion (sp - 328#64) 232 :=
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232) (b' := sp - 328#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 328#64) 232 =
      memRegion (sp - 328#64) 8 ∗ memRegion (sp - 320#64) 224 :=
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 8) (k := 224) (b' := sp - 320#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 320#64) 224 =
      memRegion (sp - 320#64) 40 ∗ memRegion (sp - 280#64) 184 :=
    ProofLib.memRegion_split' (b := sp - 320#64) (n := 40) (k := 184) (b' := sp - 280#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3, ProofLib.memRegion_eight (sp - 328#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_336_fold_e8_40 (sp w_e8 : BitVec 64) :
    memRegion (sp - 336#64) 8 ∗
      ((sp - 328#64) ↦₆₄ w_e8) ∗
      memRegion (sp - 320#64) 40 ∗
      memRegion (sp - 280#64) 184 ⊢
      memRegion (sp - 336#64) 240 := by
  have h1 : memRegion (sp - 336#64) 240 =
      memRegion (sp - 336#64) 8 ∗ memRegion (sp - 328#64) 232 :=
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232) (b' := sp - 328#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 328#64) 232 =
      memRegion (sp - 328#64) 8 ∗ memRegion (sp - 320#64) 224 :=
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 8) (k := 224) (b' := sp - 320#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 320#64) 224 =
      memRegion (sp - 320#64) 40 ∗ memRegion (sp - 280#64) 184 :=
    ProofLib.memRegion_split' (b := sp - 320#64) (n := 40) (k := 184) (b' := sp - 280#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 328#64) w_e8))

theorem scratch_320_split_8 (sp : BitVec 64) :
    memRegion (sp - 320#64) 40 ⊢
      memRegion (sp - 312#64) 32 ∗
      (∃∗ w1 : BitVec 64, (sp - 320#64) ↦₆₄ w1) := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 8] at s1
  rw [s1, ProofLib.memRegion_eight (sp - 320#64)]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_320_fold_8 (sp w1 : BitVec 64) :
    ((sp - 320#64) ↦₆₄ w1) ∗ memRegion (sp - 312#64) 32 ⊢ memRegion (sp - 320#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 8] at s1
  rw [s1]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 320#64) w1)

theorem scratch_320_split_1_1 (sp : BitVec 64) :
    memRegion (sp - 320#64) 40 ⊢
      memRegion (sp - 318#64) 38 ∗
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        ((sp - 320#64) ↦₈ b0) ∗ ((sp - 319#64) ↦₈ b1)) := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 319#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 319 1] at s2
  rw [s1, s2, ProofLib.memRegion_one (sp - 320#64), ProofLib.memRegion_one (sp - 319#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_320_fold_1_1 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 320#64) ↦₈ b0) ∗ ((sp - 319#64) ↦₈ b1) ∗ memRegion (sp - 318#64) 38 ⊢
      memRegion (sp - 320#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 320#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 320 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 319#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 319 1] at s2
  rw [s1, s2]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

end CryptoVerification.SpqrV1.Top.DecodeState
