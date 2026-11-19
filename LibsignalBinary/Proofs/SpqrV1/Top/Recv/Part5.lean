/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Version Dispatch

**Checked by Lean.** Version-branch continuation contracts (`V0ChainTail`, `InitInnerTail`,
`V1RatchetTailI`) and full `spqr::decode_state` + version dispatch (`+312..+496`, `+744..+952`)
for `spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Continuation Contracts for the Three Version Branches (`+496`, `+1076`, `+1532`) -/

theorem version_eq_zero_of_lt_one {v : BitVec 8} (h : v < 1#8) : v = 0#8 := by
  revert v h; bv_kernel

theorem version_trichotomy (v : BitVec 8) : v < 1#8 ∨ v = 1#8 ∨ v > 1#8 := by
  by_cases hlt : v < 1#8
  · exact Or.inl hlt
  · by_cases heq : v = 1#8
    · exact Or.inr (Or.inl heq)
    · refine Or.inr (Or.inr ?_)
      revert v hlt heq; bv_kernel

theorem pqRatchetStateToPb_inner_none {pre_pb : PqRatchetState} (h : pre_pb.inner = none) :
    (pqRatchetStateToPb pre_pb).inner = none := by
  unfold pqRatchetStateToPb; simp [h]

theorem pqRatchetStateToPb_inner_some {pre_pb : PqRatchetState} {pb : V1State}
    (h : pre_pb.inner = some (.v1 pb)) :
    (pqRatchetStateToPb pre_pb).inner = some pb := by
  unfold pqRatchetStateToPb; simp [h]

theorem pqRatchetStateToPb_vn {pre_pb : PqRatchetState} :
    (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl

theorem frame_pure_pre {P P_pre P_frame : SepProp} {φ : Prop}
    (hφ : φ) (hfocus : P = P_pre ∗ P_frame) :
    P ⊢ (⌜φ⌝ ∗ P_pre) ∗ P_frame := by
  rw [hfocus]
  exact sepConj_mono_left (Entails.pure_right hφ (Entails.refl _))

theorem cset_ne_eq (b : Bool) :
    (if b = true then 0#64 else 1#64) = (if (!b) = true then 1#64 else 0#64) := by
  cases b <;> rfl

theorem zeroExtend32_bne_zero_of_ne {v : BitVec 8} (h : v ≠ 0#8) :
    (BitVec.zeroExtend 32 v != 0#32) = true := by
  revert v h; bv_kernel

theorem one_ule_zeroExtend64_of_gt {v : BitVec 8} (h : v > 1#8) :
    (1#64).ule (BitVec.zeroExtend 64 v) = true := by
  revert v h; bv_kernel

theorem zeroExtend32_bne_one_of_gt {v : BitVec 8} (h : v > 1#8) :
    (BitVec.zeroExtend 32 v != 1#32) = true := by
  revert v h; bv_kernel

theorem ule_zeroExtend64_iff_not_lt {a b : BitVec 8} :
    ((BitVec.zeroExtend 64 b).ule (BitVec.zeroExtend 64 a) = true) ↔ ¬(a < b) := by
  constructor <;> intro h <;> (revert a b h; bv_kernel)

theorem ule_zeroExtend64_false_of_lt {a b : BitVec 8} (h : a < b) :
    (BitVec.zeroExtend 64 b).ule (BitVec.zeroExtend 64 a) = false := by
  revert a b h; bv_kernel

theorem ult_zeroExtend64_true_of_lt {a b : BitVec 8} (h : a < b) :
    (BitVec.zeroExtend 64 a).ult (BitVec.zeroExtend 64 b) = true := by
  revert a b h; bv_kernel

theorem ult_zeroExtend64_false_of_ge {a b : BitVec 8} (h : ¬(a < b)) :
    (BitVec.zeroExtend 64 a).ult (BitVec.zeroExtend 64 b) = false := by
  revert a b h; bv_kernel

theorem ule_zeroExtend64_true_of_ge {a b : BitVec 8} (h : ¬(a < b)) :
    (BitVec.zeroExtend 64 b).ule (BitVec.zeroExtend 64 a) = true := by
  revert a b h; bv_kernel

theorem ule_one_zeroExtend64_false_of_gt {v : BitVec 8} (h : v > 1#8) :
    (BitVec.zeroExtend 64 v).ule 1#64 = false := by
  revert v h; bv_kernel

theorem ugt_zeroExtend32_one_of_gt {v : BitVec 8} (h : v > 1#8) :
    (1#64).ult (BitVec.zeroExtend 64 v) = true := by
  revert v h; bv_kernel

theorem optVersionNegotiationPBTailAt_some_expose_minVersion (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) ⊢
      ((sp0 - 4952#64) ↦₈ vn.minVersion.truncate 8) ∗
      (∃∗ P_vn : SepProp,
        ⌜((sp0 - 4952#64) ↦₈ vn.minVersion.truncate 8) ∗ P_vn ⊢
          optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn)⌝ ∗ P_vn) := by
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  have h40 : (sp0 - 4992#64) + 40#64 = sp0 - 4952#64 := bv_sub_add_lit sp0 4992 40
  dsimp only [optVersionNegotiationPBTailAt]
  rw [← h16]
  refine Entails.trans (sepConj_mono_left (versionNegotiationPBTailAt_expose_minVersion (sp0 - 4992#64) vn)) ?_
  rw [h16, h40, sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro P_tail
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hP_tail
  refine Entails.sepExists_right (P_tail ∗ vecU8Heap A w0 w1 vn.authKey) ?_
  apply Entails.pure_right
  · rw [← sepConj_assoc]
    exact sepConj_mono_left hP_tail
  · exact Entails.refl _

theorem optVersionNegotiationPBTailAt_none_eq (A : RustAlloc) (w0 w1 a : BitVec 64) :
    optVersionNegotiationPBTailAt A w0 w1 a none ⊢
      ⌜w0 = noneCap⌝ ∗ optVersionNegotiationPBTailAt A noneCap w1 a none := by
  dsimp only [optVersionNegotiationPBTailAt]
  apply Entails.pure_left; intro hw0; subst hw0
  exact Entails.pure_right rfl (Entails.pure_right rfl (Entails.refl _))

theorem optVersionNegotiationPBTailAt_some_cap_lt (A : RustAlloc) (w0 w1 a : BitVec 64)
    (vn : VersionNegotiationPB) :
    optVersionNegotiationPBTailAt A w0 w1 a (some vn) ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗ optVersionNegotiationPBTailAt A w0 w1 a (some vn) := by
  dsimp only [optVersionNegotiationPBTailAt]
  refine Entails.trans (sepConj_mono_right (vecU8Heap_cap_lt A w0 w1 vn.authKey)) ?_
  rw [← sepConj_assoc, sepConj_comm (versionNegotiationPBTailAt a vn) ⌜_⌝, sepConj_assoc]
  exact Entails.refl _

end CryptoVerification.SpqrV1.Top.Recv

