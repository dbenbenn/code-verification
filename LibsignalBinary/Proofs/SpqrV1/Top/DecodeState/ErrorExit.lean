/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.VarintBridge -- shake: keep

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`) — Stack Frame & Error Exits

**Checked by Lean.**

Defines callee-saved register save-slot layouts and stack-frame splits, proves the shared
epilogue (`0x53e60..0x53e7c`) and `DecodeError` drop/unwind tail (`0x53df4..0x53e5c`), and
establishes panic-aware `DecodeError::push` and `DecodeError::from` error-exit paths.
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Callee-Saved Register Slots & Stack Frame Splits -/

/-- Callee-saved register save slots `[sp0 - 96, sp0)` (`0x60` bytes) for `spqr::decode_state`. -/
@[expose] def decodeStateSavedAt (sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s29) ∗ ((sp0 - 88#64) ↦₆₄ s30) ∗
    ((sp0 - 80#64) ↦₆₄ s28) ∗ ((sp0 - 72#64) ↦₆₄ s27) ∗
    ((sp0 - 64#64) ↦₆₄ s26) ∗ ((sp0 - 56#64) ↦₆₄ s25) ∗
    ((sp0 - 48#64) ↦₆₄ s24) ∗ ((sp0 - 40#64) ↦₆₄ s23) ∗
    ((sp0 - 32#64) ↦₆₄ s22) ∗ ((sp0 - 24#64) ↦₆₄ s21) ∗
    ((sp0 - 16#64) ↦₆₄ s20) ∗ ((sp0 - 8#64) ↦₆₄ s19)

theorem stackAt_decodeState_entry_split (sp0 : BitVec 64) :
    stackAt sp0 decodeStateStackX =
      stackAt (sp0 - 1392#64) v1StateMergeStack ∗
      memRegion (sp0 - 1384#64) 1288 ∗
      (∃∗ s19 : BitVec 64, ∃∗ s20 : BitVec 64, ∃∗ s21 : BitVec 64, ∃∗ s22 : BitVec 64,
       ∃∗ s23 : BitVec 64, ∃∗ s24 : BitVec 64, ∃∗ s25 : BitVec 64, ∃∗ s26 : BitVec 64,
       ∃∗ s27 : BitVec 64, ∃∗ s28 : BitVec 64, ∃∗ s30 : BitVec 64, ∃∗ s29 : BitVec 64,
       ∃∗ w0 : BitVec 64,
        ((sp0 - 1392#64) ↦₆₄ w0) ∗
        decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19) := by
  have h1 : stackAt sp0 decodeStateStackX =
      stackAt (sp0 - 1392#64) v1StateMergeStack ∗ memRegion (sp0 - 1392#64) 1392 := by
    unfold stackAt decodeStateStackX
    have h100 : BitVec.ofNat 64 (0x570 + v1StateMergeStack) =
        1392#64 + BitVec.ofNat 64 v1StateMergeStack := by decide
    have hbase : sp0 - 1392#64 =
        sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack) + BitVec.ofNat 64 v1StateMergeStack := by
      rw [h100]; bv_omega
    have hsub : sp0 - 1392#64 - BitVec.ofNat 64 v1StateMergeStack =
        sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack) := by
      rw [h100]; bv_omega
    rw [hsub]
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 (0x570 + v1StateMergeStack))
      (n := v1StateMergeStack) (k := 1392) (b' := sp0 - 1392#64) (by decide) hbase (by decide)
  rw [h1]
  rw [ProofLib.memRegion_split' (b := sp0 - 1392#64) (n := 8) (k := 1384)
      (b' := sp0 - 1384#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 1384#64) (n := 1288) (k := 96)
      (b' := sp0 - 96#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 96#64) (n := 8) (k := 88)
      (b' := sp0 - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 88#64) (n := 8) (k := 80)
      (b' := sp0 - 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 80#64) (n := 8) (k := 72)
      (b' := sp0 - 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 72#64) (n := 8) (k := 64)
      (b' := sp0 - 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 64#64) (n := 8) (k := 56)
      (b' := sp0 - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 56#64) (n := 8) (k := 48)
      (b' := sp0 - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 48#64) (n := 8) (k := 40)
      (b' := sp0 - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 40#64) (n := 8) (k := 32)
      (b' := sp0 - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 32#64) (n := 8) (k := 24)
      (b' := sp0 - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 24#64) (n := 8) (k := 16)
      (b' := sp0 - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp0 - 16#64) (n := 8) (k := 8)
      (b' := sp0 - 8#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (sp0 - 1392#64), ProofLib.memRegion_eight (sp0 - 96#64),
    ProofLib.memRegion_eight (sp0 - 88#64), ProofLib.memRegion_eight (sp0 - 80#64),
    ProofLib.memRegion_eight (sp0 - 72#64), ProofLib.memRegion_eight (sp0 - 64#64),
    ProofLib.memRegion_eight (sp0 - 56#64), ProofLib.memRegion_eight (sp0 - 48#64),
    ProofLib.memRegion_eight (sp0 - 40#64), ProofLib.memRegion_eight (sp0 - 32#64),
    ProofLib.memRegion_eight (sp0 - 24#64), ProofLib.memRegion_eight (sp0 - 16#64),
    ProofLib.memRegion_eight (sp0 - 8#64)]
  unfold decodeStateSavedAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; ac_rfl

theorem decodeState_stack_restore_1296 (sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 : BitVec 64) :
    stackAt (sp0 - 1392#64) v1StateMergeStack ∗
      memRegion (sp0 - 1392#64) 1296 ∗
      decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 ⊢
      stackAt sp0 decodeStateStackX := by
  rw [ProofLib.memRegion_split' (b := sp0 - 1392#64) (n := 8) (k := 1288)
      (b' := sp0 - 1384#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp0 - 1392#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w0
  rw [stackAt_decodeState_entry_split sp0]
  refine sepConj_mono_right ?_
  have hassoc :
      (sp0 - 1392#64) ↦₆₄ w0 ∗ memRegion (sp0 - 1384#64) 1288 ∗
        decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19 =
      memRegion (sp0 - 1384#64) 1288 ∗
        ((sp0 - 1392#64) ↦₆₄ w0 ∗
          decodeStateSavedAt sp0 s29 s30 s28 s27 s26 s25 s24 s23 s22 s21 s20 s19) := by ac_rfl
  rw [hassoc]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right s19 (Entails.sepExists_right s20 (Entails.sepExists_right s21
    (Entails.sepExists_right s22 (Entails.sepExists_right s23 (Entails.sepExists_right s24
    (Entails.sepExists_right s25 (Entails.sepExists_right s26 (Entails.sepExists_right s27
    (Entails.sepExists_right s28 (Entails.sepExists_right s30 (Entails.sepExists_right s29
    (Entails.sepExists_right w0 (Entails.refl _)))))))))))))

/-- Split `stackAt sp v1StateMergeStack` for a callee requiring stack budget `M ≤ v1StateMergeStack`. -/
theorem stackAt_to_callee (sp : BitVec 64) (M : Nat) (hM : M ≤ v1StateMergeStack) :
    stackAt sp v1StateMergeStack ⊢
      memRegion (sp - BitVec.ofNat 64 v1StateMergeStack) (v1StateMergeStack - M) ∗ stackAt sp M := by
  have h100 : v1StateMergeStack < 2 ^ 64 := by decide
  have heq := ProofLib.stackAt_split_bottom sp M (v1StateMergeStack - M) (by omega)
  have hadd : M + (v1StateMergeStack - M) = v1StateMergeStack := by omega
  rw [hadd] at heq; exact Entails.of_eq heq

/-- Restore `stackAt sp v1StateMergeStack` after a callee requiring stack budget `M ≤ v1StateMergeStack`. -/
theorem stackAt_of_callee (sp : BitVec 64) (M : Nat) (hM : M ≤ v1StateMergeStack) :
    memRegion (sp - BitVec.ofNat 64 v1StateMergeStack) (v1StateMergeStack - M) ∗ stackAt sp M ⊢
      stackAt sp v1StateMergeStack := by
  have h100 : v1StateMergeStack < 2 ^ 64 := by decide
  have heq := ProofLib.stackAt_split_bottom sp M (v1StateMergeStack - M) (by omega)
  have hadd : M + (v1StateMergeStack - M) = v1StateMergeStack := by omega
  rw [hadd] at heq; exact Entails.of_eq heq.symm

/-- On the non-empty input path, fold `(sp ↦₆₄ w0)` with `memRegion (sp + 8#64) 1288` and split
    into the disjoint stack frame regions of `spqr::decode_state`:
    - `memRegion sp 336` (`[sp, sp + 0x150)`)
    - `(sp + 0x150#64) ↦₆₄ cPtr ∗ (sp + 0x158#64) ↦₆₄ cLen` (`16`B cursor)
    - `(sp + 0x160#64) ↦₆₄ vn0 ∗ memRegion (sp + 0x168#64) 40` (`48`B `VersionNegotiationPB`)
    - `(sp + 0x190#64) ↦₆₄ ch0 ∗ memRegion (sp + 0x198#64) 72` (`80`B `ChainPB`)
    - `(sp + 0x1e0#64) ↦₆₄ in0 ∗ memRegion (sp + 0x1e8#64) 216` (`224`B `Inner`)
    - `memRegion (sp + 0x2c0#64) 352` (`352`B scratch)
    - `(sp + 0x420#64) ↦₆₄ bRef` (`8`B `bufRef` at `x29 - 0xf0`)
    - `memRegion (sp + 0x428#64) 224` (`224`B scratch at `x29 - 0xe8`)
    - `memRegion (sp + 0x508#64) 8` (`8`B padding before `x29`). -/
theorem decodeState_nonempty_frame_split (sp w0 : BitVec 64) :
    (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 1288 ⊢
      memRegion sp 336 ∗
      memRegion (sp + 0x168#64) 40 ∗
      memRegion (sp + 0x198#64) 72 ∗
      memRegion (sp + 0x1e8#64) 216 ∗
      memRegion (sp + 0x2c0#64) 352 ∗
      memRegion (sp + 0x428#64) 224 ∗
      memRegion (sp + 0x508#64) 8 ∗
      (∃∗ bRef : BitVec 64, ∃∗ in0 : BitVec 64, ∃∗ ch0 : BitVec 64,
       ∃∗ vn0 : BitVec 64, ∃∗ cLen : BitVec 64, ∃∗ cPtr : BitVec 64,
        ((sp + 0x150#64) ↦₆₄ cPtr) ∗ ((sp + 0x158#64) ↦₆₄ cLen) ∗
        ((sp + 0x160#64) ↦₆₄ vn0) ∗ ((sp + 0x190#64) ↦₆₄ ch0) ∗
        ((sp + 0x1e0#64) ↦₆₄ in0) ∗ ((sp + 0x420#64) ↦₆₄ bRef)) := by
  have h1296 : (sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 1288 ⊢ memRegion sp 1296 := by
    rw [ProofLib.memRegion_split' (b := sp) (n := 8) (k := 1288)
        (b' := sp + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion sp w0)
  refine Entails.trans h1296 ?_
  rw [ProofLib.memRegion_split' (b := sp) (n := 336) (k := 960)
      (b' := sp + 0x150#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x150#64) (n := 8) (k := 952)
      (b' := sp + 0x158#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x158#64) (n := 8) (k := 944)
      (b' := sp + 0x160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x160#64) (n := 8) (k := 936)
      (b' := sp + 0x168#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x168#64) (n := 40) (k := 896)
      (b' := sp + 0x190#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x190#64) (n := 8) (k := 888)
      (b' := sp + 0x198#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x198#64) (n := 72) (k := 816)
      (b' := sp + 0x1e0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x1e0#64) (n := 8) (k := 808)
      (b' := sp + 0x1e8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x1e8#64) (n := 216) (k := 592)
      (b' := sp + 0x2c0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x2c0#64) (n := 352) (k := 240)
      (b' := sp + 0x420#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x420#64) (n := 8) (k := 232)
      (b' := sp + 0x428#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x428#64) (n := 224) (k := 8)
      (b' := sp + 0x508#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp + 0x150#64),
    ProofLib.memRegion_eight (sp + 0x158#64),
    ProofLib.memRegion_eight (sp + 0x160#64),
    ProofLib.memRegion_eight (sp + 0x190#64),
    ProofLib.memRegion_eight (sp + 0x1e0#64),
    ProofLib.memRegion_eight (sp + 0x420#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

/-- Fold the 7 stack frame regions (`336 + 16 + 352 + 352 + 8 + 224 + 8 = 1296` bytes)
    back into `memRegion sp 1296` before the epilogue `0x53e60`. -/
theorem decodeState_frame_fold (sp bRef : BitVec 64) :
    memRegion sp 336 ∗
      memRegion (sp + 0x150#64) 16 ∗
      memRegion (sp + 0x160#64) 352 ∗
      memRegion (sp + 0x2c0#64) 352 ∗
      ((sp + 0x420#64) ↦₆₄ bRef) ∗
      memRegion (sp + 0x428#64) 224 ∗
      memRegion (sp + 0x508#64) 8 ⊢
      memRegion sp 1296 := by
  have hb : ((sp + 0x420#64) ↦₆₄ bRef) ⊢ memRegion (sp + 0x420#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + 0x420#64) bRef
  rw [ProofLib.memRegion_split' (b := sp) (n := 336) (k := 960)
      (b' := sp + 0x150#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x150#64) (n := 16) (k := 944)
      (b' := sp + 0x160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x160#64) (n := 352) (k := 592)
      (b' := sp + 0x2c0#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x2c0#64) (n := 352) (k := 240)
      (b' := sp + 0x420#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x420#64) (n := 8) (k := 232)
      (b' := sp + 0x428#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp + 0x428#64) (n := 224) (k := 8)
      (b' := sp + 0x508#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hb))))

/-! ## 2. Output Buffer Error Split & Callee Address Helpers -/

theorem memRegion_352_err_split (outPtr : BitVec 64) :
    memRegion outPtr 352 ⊢
      memRegion (outPtr + 9#64) 343 ∗
      (∃∗ b8 : BitVec 8, ∃∗ w0 : BitVec 64,
        (outPtr ↦₆₄ w0) ∗ ((outPtr + 8#64) ↦₈ b8)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 344)
      (b' := outPtr + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 1) (k := 343)
      (b' := outPtr + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight outPtr,
    ProofLib.memRegion_one (outPtr + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem fold_decodeStateResultAt_err (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (outPtr : BitVec 64) {res : Except Error PqRatchetState}
    (hres : res = .error .stateDecode) :
    (outPtr ↦₆₄ 18446744073709551614#64) ∗ ((outPtr + 8#64) ↦₈ 0#8) ∗ memRegion (outPtr + 9#64) 343 ⊢
      decodeStateResultAt H_inner A outPtr res := by
  subst hres
  exact Entails.refl _

abbrev decodeStatePost (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev decodeStatePanicPost (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (decodeStateSpecX H_inner b A).onPanic x s0 sf ∗ R)

@[simp, arm64_norm]
abbrev TraceVRegs (s s0 : State) : Prop :=
  s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem TraceVRegs.step {s0 s sm : State} (htr : TraceVRegs s s0)
    (htrm : sm.trace = s.trace) (hcsm : CalleeSavedPreserved s sm) :
    TraceVRegs sm s0 :=
  ⟨htrm.trans htr.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩

theorem allocFailedIn_trans {s0 sm sf : State} (htr : TraceVRegs sm s0)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr.1] using h

theorem sp_sub_1392_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 1392#64) &&& 15#64 == 0#64) = true := by

  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

/-! ## 3. Shared Epilogue `0x53e60..0x53e7c` and Error Tail `0x53df4..0x53e5c` -/

theorem decodeErrorWith_unfold (A : RustAlloc) (e : BitVec 64) (n : Nat) :
    decodeErrorAtStackLen A e n ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ w : BitVec 64,
        ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0 ∧ KindNoHeap w⌝ ∗
        A.live e 72 8 ∗
        (e ↦₆₄ cap) ∗ ((e + 8#64) ↦₆₄ ptr) ∗ ((e + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        ((e + 24#64) ↦₆₄ w) ∗ memRegion (e + 32#64) 40 ∗
        (if cap = 0 then emp else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) := by
  simp only [decodeErrorAtStackLen, vecOf, vecAt, vecHeader, vecBuf, List.length_replicate,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.sepExists_right w ?_))
  have hreord :
      A.live e 72 8 ∗
        ((e ↦₆₄ cap ∗ (e + 8#64) ↦₆₄ ptr ∗ (e + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
          ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          if cap = 0 then emp
          else A.live ptr (cap.toNat * 32) 8 ∗
            arrayAt stackEntryAt 32 ptr (List.replicate n ()) ∗
            memRegion (ptr + BitVec.ofNat 64 (n * 32)) ((cap.toNat - n) * 32)) ∗
        (⌜KindNoHeap w⌝ ∗ (e + 24#64) ↦₆₄ w) ∗ memRegion (e + 32#64) 40 =
      ⌜n ≤ cap.toNat ∧ cap.toNat * 32 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ ⌜KindNoHeap w⌝ ∗
        A.live e 72 8 ∗ e ↦₆₄ cap ∗ (e + 8#64) ↦₆₄ ptr ∗ (e + 16#64) ↦₆₄ BitVec.ofNat 64 n ∗
        (e + 24#64) ↦₆₄ w ∗ memRegion (e + 32#64) 40 ∗
        (if cap = 0 then emp
          else A.live ptr (cap.toNat * 32) 8 ∗
            arrayAt stackEntryAt 32 ptr (List.replicate n ()) ∗
            memRegion (ptr + BitVec.ofNat 64 (n * 32)) ((cap.toNat - n) * 32)) := by ac_rfl
  refine Entails.trans (Entails.of_eq hreord) ?_
  apply Entails.pure_left; rintro ⟨hn, hcap, hptr⟩
  apply Entails.pure_left; intro hw
  apply Entails.pure_right ⟨hn, hcap, hptr, hw⟩
  by_cases hc : cap = 0
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte, stackVec_buf_memRegion hn hcap]
    exact Entails.refl _

theorem protoPqRatchetState_to_memcpy (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (src dst : BitVec 64) (st : PqRatchetState) :
    protoPqRatchetStateAt H_inner A src st ∗ memRegion dst 352 ⊢
      ∃∗ srcBs : List (BitVec 8),
        ⌜srcBs.length = 352⌝ ∗
        (src ↦ₛ srcBs) ∗ memRegion dst srcBs.length ∗
        (relocProtoPqRatchetStateAt H_inner A st).1 srcBs := by
  refine Entails.trans (sepConj_mono_left ((relocProtoPqRatchetStateAt H_inner A st).2.to_bytes src)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro srcBs
  refine Entails.sepExists_right srcBs ?_
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hsrc
  refine Entails.pure_right hsrc ?_
  rw [hsrc]
  exact Entails.of_eq (by ac_rfl)

theorem protoPqRatchetState_of_memcpy (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (src dst : BitVec 64) (st : PqRatchetState) {srcBs : List (BitVec 8)} (hsrc : srcBs.length = 352) :
    (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs ⊢
      protoPqRatchetStateAt H_inner A dst st ∗ memRegion src 352 := by
  have h1 := (relocProtoPqRatchetStateAt H_inner A st).2.of_bytes dst srcBs hsrc
  have h2 : (src ↦ₛ srcBs) ⊢ memRegion src 352 := by
    rw [← hsrc]; exact pointsToBytes_entails_memRegion src srcBs
  have hreord :
      (dst ↦ₛ srcBs) ∗ (src ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs =
      ((dst ↦ₛ srcBs) ∗ (relocProtoPqRatchetStateAt H_inner A st).1 srcBs) ∗ (src ↦ₛ srcBs) := by ac_rfl
  rw [hreord]
  exact sepConj_mono h1 h2

theorem frame_4chunks_to_1296 (sp : BitVec 64) :
    memRegion (sp - 1392#64) 352 ∗
      memRegion (sp - 1040#64) 352 ∗
      memRegion (sp - 688#64) 352 ∗
      memRegion (sp - 336#64) 240 ⊢
      memRegion (sp - 1392#64) 1296 := by
  have h1 : memRegion (sp - 1392#64) 1296 =
      memRegion (sp - 1392#64) 352 ∗ memRegion (sp - 1040#64) 944 :=
    ProofLib.memRegion_split' (b := sp - 1392#64) (n := 352) (k := 944)
      (b' := sp - 1040#64) rfl (by bv_omega) (by decide)
  have h2 : memRegion (sp - 1040#64) 944 =
      memRegion (sp - 1040#64) 352 ∗ memRegion (sp - 688#64) 592 :=
    ProofLib.memRegion_split' (b := sp - 1040#64) (n := 352) (k := 592)
      (b' := sp - 688#64) rfl (by bv_omega) (by decide)
  have h3 : memRegion (sp - 688#64) 592 =
      memRegion (sp - 688#64) 352 ∗ memRegion (sp - 336#64) 240 :=
    ProofLib.memRegion_split' (b := sp - 688#64) (n := 352) (k := 240)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide)
  rw [h1, h2, h3]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_split_8 (sp : BitVec 64) :
    memRegion (sp - 688#64) 352 ⊢
      memRegion (sp - 680#64) 344 ∗
      (∃∗ w0 : BitVec 64, (sp - 688#64) ↦₆₄ w0) := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 688#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_fold_8 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 344 ⊢
      memRegion (sp - 688#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w0)

theorem scratch_688_split_48 (sp : BitVec 64) :
    memRegion (sp - 688#64) 352 ⊢
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 ∗
      (∃∗ w0 : BitVec 64, (sp - 688#64) ↦₆₄ w0) := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 688#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem scratch_688_fold_48 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      memRegion (sp - 688#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 344)
      (b' := sp - 680#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w0)

theorem SepWPp.call_decodeErrorPush {H_inner : V1InnerHeapPred} {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorPushSpec A))
    (d e : BitVec 64) (n : Nat) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = d)
    (hn : n < 2 ^ 32)
    (hP : P = ((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e n ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPp prog ret sf
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (d, e, n)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorPushSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hn⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorPushSpec] at hpost
    exact allowPanic_not_exited hpost
  · intro sm _ hm'
    dsimp only [decodeStatePanicPost, decodeStateSpecX, decodeErrorPushSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorPushSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [hsp] at hspm
    have hpost1 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        (((d ↦₆₄ e) ∗ decodeErrorAtStackLen A e (n + 1) ∗ A.pool ∗
          stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide))))))) hpost1
    exact hnext sm hpcm hrunm hspm (htr.step htrm hcsm) hcsm R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem SepWPp.call_decodeErrorFrom {H_inner : V1InnerHeapPred} {b : BitVec 64} {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (decodeErrorFromSpec A))
    (k w : BitVec 64) {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = k)
    (hw : KindNoHeap w)
    (hP : P = ((k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hnext : ∀ (sf : State) (v_k : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 →
      SepWPp prog ret sf
        ((decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPost H_inner b A x_outer s0 R)) :
    SepWPp prog ret s P Q (decodeStatePanicPost H_inner b A x_outer s0 R) := by
  let sp_cur := s0.sp - 1392#64
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - decodeErrorHookStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  refine SepWPp.call (x := (k, w)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [decodeErrorFromSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hw⟩, ?_⟩
    rw [hP] at hm
    have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (stackAt_to_callee sp_cur decodeErrorHookStack (by decide))))))) hm
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    dsimp only [sp_cur, F_ext]; ac_rfl
  · intro sm _ R' _ hpost
    dsimp only [decodeErrorFromSpec] at hpost
    exact allowPanic_not_exited hpost
  · intro sm _ hm'
    dsimp only [decodeStatePanicPost, decodeStateSpecX, decodeErrorFromSpec] at hm' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [decodeErrorFromSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0_ne, htrm⟩, hpost⟩
    rw [hsp] at hspm
    rw [ProofLib.memRegion_split' (b := k) (n := 8) (k := 40)
        (b' := k + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight k] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨v_k, hpost⟩
    have hpost1 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - decodeErrorHookStack) ∗
            stackAt sp_cur decodeErrorHookStack)) ∗ F) ∗ R' := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    have hpost2 : sm.mem ⊨
        ((decodeErrorAtStackLen A (sm.readReg64 .x0) 0 ∗ (k ↦₆₄ v_k) ∗ memRegion (k + 8#64) 40 ∗
          A.pool ∗ stackAt sp_cur v1StateMergeStack) ∗ F) ∗ R' :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur decodeErrorHookStack (by decide)))))))) hpost1
    exact hnext sm v_k hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne R' hpost2 hL
  · intro sm R' _ hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

end CryptoVerification.SpqrV1.Top.DecodeState
