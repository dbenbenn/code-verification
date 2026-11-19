/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsa -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part B0

Shared error epilogues (`+4392`, `+4396`), bad-`ptsNeeded` cleanup (`+604..+688`), and
`Unchunked::EkSent` validation error cleanup (`+4660..+4748`).
-/

public section

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append



/-! ## `+4396 -> s0.x30` and `+4392 -> s0.x30` Shared Epilogues -/

theorem v2hs_memRegion_976_56_to_1032 (fsp : BitVec 64) :
    memRegion fsp 976 ∗ memRegion (fsp + 976#64) 56 ⊢ memRegion fsp 1032 :=
  collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _

theorem v2hs_memRegion_896_ucWords_to_976
    (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64) :
    memRegion fsp 896 ∗ v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ⊢
      memRegion fsp 976 := by
  have h80 := v2hs_ucWordsAt_entails_80 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
  have h976 : memRegion fsp 896 ∗ memRegion (fsp + 896#64) 80 ⊢ memRegion fsp 976 :=
    collapse_top <| collapse_step0 (Entails.refl _) <| Entails.refl _
  exact Entails.trans (sepConj_mono_right h80) h976

theorem v2hs_vecU8Payload_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  dsimp only [vecU8Payload, vecCapPtrDealloc]
  apply Entails.pure_left
  rintro ⟨hle, hcap_lt, _⟩
  refine Entails.pure_right hcap_lt ?_
  by_cases hcap : cap = 0#64
  · have hbeq : (cap == 0#64) = true := by simp [hcap]
    simp only [hcap, hbeq, ↓reduceIte]
    exact Entails.refl emp
  · have hbeq : (cap == 0#64) = false := by simp [hcap]
    simp only [hcap, hbeq, Bool.false_eq_true, ↓reduceIte]
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    have hbound : bs.length + (cap.toNat - bs.length) ≤ 2 ^ 64 := by omega
    have hmr : memRegion ptr cap.toNat =
        memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
      conv_lhs => rw [hsplit]
      exact memRegion_split ptr bs.length (cap.toNat - bs.length) hbound
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))) ?_
    rw [hmr]
    exact Entails.of_eq (by ac_rfl)

theorem v2hs_optProtoUcHeap_some_none_dealloc (A : RustAlloc) (dk : List (BitVec 8))
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 epoch : BitVec 64) :
    v4b_vecU8Heap A dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A none u32 u40 u48 u56 u64 u72 ∗ ⌜u80 = epoch⌝ ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u32 = noneCap⌝ ∗ vecCapPtrDealloc A u8 u16 := by
  dsimp only [v4b_vecU8Heap, v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (v2hs_vecU8Payload_entails_dealloc A u8 u16 dk))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu8_lt⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜u32 = noneCap⌝]
  apply Entails.pure_left; intro hu32
  rw [sepConj_comm (vecCapPtrDealloc A u8 u16) ⌜u80 = epoch⌝]
  apply Entails.pure_left; intro _
  exact Entails.pure_right ⟨hu8_lt, hu32⟩ (Entails.refl _)

theorem v2hs_optProtoUcHeap_some_some_dealloc (A : RustAlloc) (dk : List (BitVec 8))
    (auth : ProtoAuthenticator)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 epoch : BitVec 64) :
    v4b_vecU8Heap A dk u8 u16 u24 ∗
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ∗ ⌜u80 = epoch⌝ ⊢
      ⌜u8.toNat < 2 ^ 63 ∧ u32.toNat < 2 ^ 63⌝ ∗
      vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 := by
  dsimp only [v4b_vecU8Heap, v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (v2hs_vecU8Payload_entails_dealloc A u8 u16 dk))
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono
      (v2hs_vecU8Payload_entails_dealloc A u32 u40 auth.rootKey)
      (v2hs_vecU8Payload_entails_dealloc A u56 u64 auth.macKey))))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨_, hu8_lt⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜_⌝]
  apply Entails.pure_left; rintro ⟨hu32_lt, _, _⟩
  rw [sepConj_left_comm (vecCapPtrDealloc A u8 u16) ⌜_⌝]
  apply Entails.pure_left; intro _
  have hcomm :
      vecCapPtrDealloc A u8 u16 ∗ (vecCapPtrDealloc A u32 u40 ∗
        (⌜u56.toNat < 2 ^ 63⌝ ∗ (vecCapPtrDealloc A u56 u64 ∗ ⌜u80 = epoch⌝))) =
      ⌜u56.toNat < 2 ^ 63⌝ ∗ (⌜u80 = epoch⌝ ∗
        (vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64)) := by
    ac_rfl
  rw [hcomm]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.pure_right ⟨hu8_lt, hu32_lt⟩ (Entails.refl _)

theorem v2hs_optProtoAuthHeap_some_dealloc (A : RustAlloc) (auth : ProtoAuthenticator)
    (u32 u40 u48 u56 u64 u72 : BitVec 64) :
    v1_optProtoAuthHeap A (some auth) u32 u40 u48 u56 u64 u72 ⊢
      ⌜u32.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 := by
  dsimp only [v1_optProtoAuthHeap]
  refine Entails.trans (sepConj_mono_right (sepConj_mono
    (v2hs_vecU8Payload_entails_dealloc A u32 u40 auth.rootKey)
    (v2hs_vecU8Payload_entails_dealloc A u56 u64 auth.macKey))) ?_
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hu32_lt, _, _⟩
  apply Entails.pure_left; intro _
  rw [sepConj_left_comm (vecCapPtrDealloc A u32 u40) ⌜_⌝]
  apply Entails.pure_left; intro _
  exact Entails.pure_right hu32_lt (Entails.refl _)

end CryptoVerification.SpqrV1.States.FromPb
