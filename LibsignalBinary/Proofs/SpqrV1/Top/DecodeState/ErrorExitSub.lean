/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Outer Loop & `ChainPB` Error Exit Paths for `spqr::decode_state` (`0x5349c`)

Proves error-exit blocks for `v1::State::merge` (`0x53bc0..0x53bd4`), outer `PqRatchetState`
`decode_key` and `skip_field` failures (`0x53af8..0x53b24`), and nested `ChainPB` field and
wire-type errors.
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

/-! ## 1. Shared Error Precondition Frame & `[sp + 0x2c8]` (`s0.sp - 680#64`) Helpers -/

/-- Shared separation-logic frame for error exit blocks when `protoPqRatchetStateAt` is intact at
    `s0.sp - 1040#64` and `[sp + 0x2c0]` (`s0.sp - 688#64`) is split out. -/
abbrev decodeStateErrFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  x.st.at A ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 352 ∗
  protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
  memRegion (s0.sp - 680#64) 40 ∗
  memRegion (s0.sp - 640#64) 304 ∗
  memRegion (s0.sp - 336#64) 240 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

theorem bv_sub_688_add_8 (sp : BitVec 64) :
    sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega

theorem scratch_680_split_8 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ⊢
      memRegion (sp - 672#64) 32 ∗
      (∃∗ w1 : BitVec 64, (sp - 680#64) ↦₆₄ w1) := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 8] at s1
  rw [s1, ProofLib.memRegion_eight (sp - 680#64)]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_680_fold_8 (sp w1 : BitVec 64) :
    ((sp - 680#64) ↦₆₄ w1) ∗ memRegion (sp - 672#64) 32 ⊢ memRegion (sp - 680#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 8 32 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 8] at s1
  rw [s1]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 680#64) w1)

theorem scratch_680_split_1_1 (sp : BitVec 64) :
    memRegion (sp - 680#64) 40 ⊢
      memRegion (sp - 678#64) 38 ∗
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        ((sp - 680#64) ↦₈ b0) ∗ ((sp - 679#64) ↦₈ b1)) := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 679#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 679 1] at s2
  rw [s1, s2, ProofLib.memRegion_one (sp - 680#64), ProofLib.memRegion_one (sp - 679#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_680_fold_1_1 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 680#64) ↦₈ b0) ∗ ((sp - 679#64) ↦₈ b1) ∗ memRegion (sp - 678#64) 38 ⊢
      memRegion (sp - 680#64) 40 := by
  have s1 := ProofLib.memRegion_split (sp - 680#64) 1 39 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 680 1] at s1
  have s2 := ProofLib.memRegion_split (sp - 679#64) 1 38 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 679 1] at s2
  rw [s1, s2]
  exact sepConj_mono (pointsTo8_entails_memRegion1 _ b0)
    (sepConj_mono (pointsTo8_entails_memRegion1 _ b1) (Entails.refl _))

/-! ## 2. `v1::State::merge` Error Push (`0x53bc0`) -/

end CryptoVerification.SpqrV1.Top.DecodeState
