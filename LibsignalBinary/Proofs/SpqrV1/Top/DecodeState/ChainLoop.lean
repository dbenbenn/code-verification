/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainPush
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiation
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainPB` Merge Loop & Outer Tag-2 Handler

**Checked by Lean.** Verifies `ChainPB` tag dispatch (`0x536cc`), single loop iteration (`0x536a4`),
inductive `ChainPB` merge loop (`0x53698`), length-delimited `ChainPB::merge` (`0x535b8`), and
outer `PqRatchetState::chain` tag-2 handler (`0x53590`).
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

attribute [local simp, local arm64_norm] truncate32_zeroExtend64_lsr3

/-! ## `ChainPB` Tag Dispatch (`0x536cc`, `+560`) -/

theorem optChainPB_none_split72 (a : BitVec 64) :
    memRegion (a + 8#64) 72 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 32, ∃∗ w9 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₃₂ w8) ∗
        memRegion (a + 68#64) 8 ∗ ((a + 76#64) ↦₃₂ w9) := by
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 56) (k := 16)
      (b' := a + 64#64) rfl (by bv_omega) (by decide),
    memRegion_56_eq_quads7At (a + 8#64),
    ProofLib.memRegion_split' (b := a + 64#64) (n := 4) (k := 12)
      (b' := a + 68#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 68#64) (n := 8) (k := 4)
      (b' := a + 76#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_four (a + 64#64),
    ProofLib.memRegion_four (a + 76#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; rintro ⟨w1, w2, w3, w4, w5, w6, w7⟩
  dsimp only [quads7At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.sepExists_right w7 (Entails.sepExists_right w8
          (Entails.sepExists_right w9 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

theorem chainLinksVecAt_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  exact Entails.pure_right (by omega) (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

theorem chainLinksVecAt_header_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
    chainLinksVecAt A a xs := by
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

end CryptoVerification.SpqrV1.Top.DecodeState
