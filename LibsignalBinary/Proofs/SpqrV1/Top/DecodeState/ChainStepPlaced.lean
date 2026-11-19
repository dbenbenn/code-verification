/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` `ChainPB` Field Merge Handlers for `spqr::decode_state` (Block `325`)

Proves the per-field handlers (Tags 1, 2, 4, 5, 6, and `skip_field`) inside the inlined
`ChainPB::merge` loop of `spqr::decode_state` under `LibsignalPlacement`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Layout Unfolding Helpers for `Some ch` at `s0.sp - 1040#64` -/

theorem protoPqRatchetStateCapOkAt_some_ch_eq_placed (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ =
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt optChainPBCapOkAt chainPBCapOkAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  have hc1 : sp - 992#64 + 0x18#64 = sp - 968#64 := by bv_omega
  have hc2 : sp - 992#64 + 0x30#64 = sp - 944#64 := by bv_omega
  have hc3 : sp - 992#64 + 0x38#64 = sp - 936#64 := by bv_omega
  have hc4 : sp - 992#64 + 0x40#64 = sp - 928#64 := by bv_omega
  have hc5 : sp - 992#64 + 0x4c#64 = sp - 916#64 := by bv_omega
  rw [ha1, ha2, hc1, hc2, hc3, hc4, hc5]

private abbrev protoPqRatchetStateCapOkAt_some_ch_eq := @protoPqRatchetStateCapOkAt_some_ch_eq_placed

private theorem protoPqRatchetStateAt_some_ch_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateAt H_inner A (sp - 1040#64) ⟨optVn, some ch, inner⟩ =
      optVersionNegotiationPBAt A (sp - 1040#64) optVn ∗
        (chainLinksVecAt A (sp - 992#64) ch.links ∗
          rustBytesVecAt A (sp - 968#64) ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerAt H_inner A (sp - 912#64) inner := by
  unfold protoPqRatchetStateAt optChainPBAt chainPBAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  have hc1 : sp - 992#64 + 0x18#64 = sp - 968#64 := by bv_omega
  have hc2 : sp - 992#64 + 0x30#64 = sp - 944#64 := by bv_omega
  have hc3 : sp - 992#64 + 0x38#64 = sp - 936#64 := by bv_omega
  have hc4 : sp - 992#64 + 0x40#64 = sp - 928#64 := by bv_omega
  have hc5 : sp - 992#64 + 0x4c#64 = sp - 916#64 := by bv_omega
  rw [ha1, ha2, hc1, hc2, hc3, hc4, hc5]

private theorem optChainParamsPBAt_some_ch_eq (sp : BitVec 64) (cp : ChainParamsPB) :
    optChainParamsPBAt (sp - 928#64) (some cp) =
      ((sp - 928#64) ↦₃₂ 1#32) ∗ chainParamsPBAt (sp - 924#64) cp := by
  unfold optChainParamsPBAt
  dsimp only
  have ha : sp - 928#64 + 4#64 = sp - 924#64 := by bv_omega
  rw [ha]

private theorem chainLinks_bound_mono {len rem1 rem2 : Nat} (hle : rem2 ≤ rem1) (Q : SepProp) :
    (⌜len + rem1 ≤ 2 ^ 54⌝ : SepProp) ∗ Q ⊢ ⌜len + rem2 ≤ 2 ^ 54⌝ ∗ Q := by
  apply Entails.pure_left; intro h
  exact Entails.pure_right (by omega) (Entails.refl _)

private theorem chainLinks_bound_drop (len rem : Nat) (Q : SepProp) :
    (⌜len + rem ≤ 2 ^ 54⌝ : SepProp) ∗ Q ⊢ Q := by
  apply Entails.pure_left; intro _
  exact Entails.refl _

/-! ## 2. `ChainPB` Field Merge Handlers (Placed) -/

end CryptoVerification.SpqrV1.Top.DecodeState
