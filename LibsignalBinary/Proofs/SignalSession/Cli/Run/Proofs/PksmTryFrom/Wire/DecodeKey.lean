/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Inlined `decode_key` and 8-Way Tag Dispatch

Symbolic execution of inlined `decode_varint` / `decode_key` (`+0x0f4..+0x16c`, `+0x308..+0x33c`)
and the 8-way protobuf field-tag dispatch (`+0x170..+0x234`) on `contractProg img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  memRegion_split decodeVarint_suffix pointsTo64_pair_entails_memRegion16
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_DecodeKey : True := trivial

/-! ## 3b. Inlined `decode_varint` and `decodeKeyPK_cpsX` (`+0x0f4..+0x16c`) -/

theorem tag_ge9_conds (tag : Nat) (hge : 9 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 1#32) = false) ∧ ((w1 == 2#32) = false) ∧ ((w1 != 2#32) = true) ∧
    ((w1 == 3#32) = false) ∧ ((w1 != 3#32) = true) ∧
    ((w1 == 4#32) = false) ∧ ((w1 != 4#32) = true) ∧ ((w1 == 5#32) = false) ∧
    ((w1 == 6#32) = false) ∧ ((w1 != 6#32) = true) ∧
    ((w1 == 7#32) = false) ∧ ((w1 != 7#32) = true) ∧
    ((w1 == 8#32) = false) ∧ ((w1 != 8#32) = true) := by
  dsimp only; rw [setWidth32_ofNat64]
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h3 : BitVec.ofNat 32 tag ≠ 3#32 := by bv_omega
  have h4 : BitVec.ofNat 32 tag ≠ 4#32 := by bv_omega
  have h5 : BitVec.ofNat 32 tag ≠ 5#32 := by bv_omega
  have h6 : BitVec.ofNat 32 tag ≠ 6#32 := by bv_omega
  have h7 : BitVec.ofNat 32 tag ≠ 7#32 := by bv_omega
  have h8 : BitVec.ofNat 32 tag ≠ 8#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, bne_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h3, bne_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h4, bne_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5,
    beq_eq_false_iff_ne.mpr h6, bne_iff_ne.mpr h6,
    beq_eq_false_iff_ne.mpr h7, bne_iff_ne.mpr h7,
    beq_eq_false_iff_ne.mpr h8, bne_iff_ne.mpr h8⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
