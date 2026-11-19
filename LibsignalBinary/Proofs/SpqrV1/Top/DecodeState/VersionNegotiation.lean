/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `VersionNegotiationPB` Framing & Tag Body Helpers for `spqr::decode_state` (`0x5349c`)

Defines `VersionNegotiationPB` stack-frame layout and initialization helpers and proves the
per-field body lemmas (Tags 1..4 and `skip_field`) for the inlined `VersionNegotiationPB::merge`
loop.
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

/-! ## 1. `VersionNegotiationPB` Framing and Initialization Helpers -/

theorem optChainParamsPBAt_none_to_init (a : BitVec 64) :
    (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 32, (a + 8#64) ↦₃₂ w1) := by
  have h1 : (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢ memRegion a 4 ∗ memRegion (a + 4#64) 8 :=
    sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion a 0#32)
  have h2 : memRegion a 4 ∗ memRegion (a + 4#64) 8 = memRegion a 12 :=
    (ProofLib.memRegion_split a 4 8 (by decide)).symm
  have h3 : memRegion a 12 = memRegion a 8 ∗ memRegion (a + 8#64) 4 :=
    ProofLib.memRegion_split a 8 4 (by decide)
  rw [h2, h3, ProofLib.memRegion_eight a, ProofLib.memRegion_four (a + 8#64)] at h1
  exact h1

theorem optVersionNegotiationPB_none_split40 (a : BitVec 64) :
    memRegion (a + 8#64) 40 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 32, ∃∗ w4 : BitVec 64,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₃₂ w3) ∗
        memRegion (a + 28#64) 8 ∗ ((a + 36#64) ↦₆₄ w4) ∗ memRegion (a + 44#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 24 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 4 20 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 4#64) 8 12 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 4#64) + 8#64) 8 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5
  rw [hs1, hs2, hs3, hs4, hs5,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_four (a + 24#64),
    ProofLib.memRegion_eight (a + 36#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem protoPqRatchetStateCapOkAt_some_vn_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (vn : VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨some vn, optCh, inner⟩ =
      (vecU8CapOkAt A (sp - 1040#64) remLen vn.authKey ∗
        optChainParamsPBAt (sp - 1016#64) vn.chainParams ∗
        ((sp - 1004#64) ↦₃₂ vn.direction) ∗
        ((sp - 1000#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp - 996#64) 4) ∗
      optChainPBCapOkAt A (sp - 992#64) remLen optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt optVersionNegotiationPBCapOkAt versionNegotiationPBCapOkAt
  dsimp only
  have ha18 : sp - 1040#64 + 0x18#64 = sp - 1016#64 := by bv_omega
  have ha24 : sp - 1040#64 + 0x24#64 = sp - 1004#64 := by bv_omega
  have ha28 : sp - 1040#64 + 0x28#64 = sp - 1000#64 := by bv_omega
  have ha2c : sp - 1040#64 + 0x2c#64 = sp - 996#64 := by bv_omega
  have ha30 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha80 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha18, ha24, ha28, ha2c, ha30, ha80]

theorem protoPqRatchetStateAt_some_vn_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (vn : VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateAt H_inner A (sp - 1040#64) ⟨some vn, optCh, inner⟩ =
      (rustBytesVecAt A (sp - 1040#64) vn.authKey ∗
        optChainParamsPBAt (sp - 1016#64) vn.chainParams ∗
        ((sp - 1004#64) ↦₃₂ vn.direction) ∗
        ((sp - 1000#64) ↦₃₂ vn.minVersion) ∗
        memRegion (sp - 996#64) 4) ∗
      optChainPBAt A (sp - 992#64) optCh ∗
      optProtoPqRatchetInnerAt H_inner A (sp - 912#64) inner := by
  unfold protoPqRatchetStateAt optVersionNegotiationPBAt versionNegotiationPBAt
  dsimp only
  have ha18 : sp - 1040#64 + 0x18#64 = sp - 1016#64 := by bv_omega
  have ha24 : sp - 1040#64 + 0x24#64 = sp - 1004#64 := by bv_omega
  have ha28 : sp - 1040#64 + 0x28#64 = sp - 1000#64 := by bv_omega
  have ha2c : sp - 1040#64 + 0x2c#64 = sp - 996#64 := by bv_omega
  have ha30 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha80 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha18, ha24, ha28, ha2c, ha30, ha80]

theorem optChainParamsPBAt_some_eq (sp : BitVec 64) (cp : ChainParamsPB) :
    optChainParamsPBAt (sp - 1016#64) (some cp) =
      ((sp - 1016#64) ↦₃₂ 1#32) ∗ chainParamsPBAt (sp - 1012#64) cp := by
  unfold optChainParamsPBAt
  dsimp only
  have ha : sp - 1016#64 + 4#64 = sp - 1012#64 := by bv_omega
  rw [ha]

theorem errFrame_parts_fold (A : RustAlloc) (x : DecodeStateGhost) (s0 : State)
    {cur : List (BitVec 8)} (hle : cur.length ≤ x.st.bytes.length)
    (hsuf : IsDropSuffix x.st.bytes cur) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      vecArgRestAt A x.st ∗
      memRegion (s0.sp - 1392#64) 336 ∗
      ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
      memRegion (s0.sp - 328#64) 224 ∗
      memRegion (s0.sp - 104#64) 8 ⊢
    x.st.at A ∗ memRegion (s0.sp - 1392#64) 352 ∗ memRegion (s0.sp - 336#64) 240 := by
  have hs := pointsToBytes_prefix_join (ptr := x.st.ptr) hle hsuf
  have hst := Entails.trans (sepConj_mono_left hs) (vecArg_join_bytes A x.st)
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        vecArgRestAt A x.st ∗
        memRegion (s0.sp - 1392#64) 336 ∗
        ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
        memRegion (s0.sp - 328#64) 224 ∗
        memRegion (s0.sp - 104#64) 8 =
      (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        vecArgRestAt A x.st) ∗
      (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
      (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
        memRegion (s0.sp - 328#64) 224 ∗
        memRegion (s0.sp - 104#64) 8) := by ac_rfl
  rw [hreord]
  exact sepConj_mono hst (sepConj_mono hlow hup)

theorem wireType_ofNat64_ne_zero_of_ne_varint {iwt : WireType} (h : iwt ≠ .varint) :
    BitVec.ofNat 64 iwt.toNat ≠ 0#64 := by
  cases iwt <;> first | contradiction | decide

/-! ## 2. `VersionNegotiationPB` Tag Body Helpers -/

end CryptoVerification.SpqrV1.Top.DecodeState
