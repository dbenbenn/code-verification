/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArms -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: `int32::merge` Field Arms

Symbolic execution of the four `prost::encoding::int32::merge` field arms (`pre_key_id`,
`registration_id`, `signed_pre_key_id`, `kyber_pre_key_id`) and their unified CPS wrapper
`int32ArmPK_cps`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_104 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 104) = sp' + 408#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_100 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 100) = sp' + 412#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_96 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 96) = sp' + 416#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_92 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 92) = sp' + 420#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_88 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 88) = sp' + 424#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_84 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 84) = sp' + 428#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_80 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 80) = sp' + 432#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_76 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 76) = sp' + 436#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_72 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_64 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_56 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 56) = sp' + 456#64 := by bv_omega

theorem L1_IS5Wire_Int32Arms : True := trivial

/-! ## 1. Shared Callee, Decomposition & Error-Tail Helpers -/

@[expose] def wirePreKeyVecsOf (A : RustAlloc) (a : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  ∃∗ g : WirePreKeyGhost,
    optVecU8At A g.kyberCt a m.kyberCiphertext ∗
    optVecU8At A g.baseKey (a + 0x18#64) m.baseKey ∗
    optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
    optVecU8At A g.message (a + 0x48#64) m.message

theorem wirePreKeyOf_eq_vecs_u32s (A : RustAlloc) (a : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A a m =
      wirePreKeyVecsOf A a m ∗ optU32At (a + 0x60#64) m.registrationId ∗
      optU32At (a + 0x68#64) m.preKeyId ∗ optU32At (a + 0x70#64) m.signedPreKeyId ∗
      optU32At (a + 0x78#64) m.kyberPreKeyId := by
  unfold wirePreKeyOf wirePreKeyAt wirePreKeyVecsOf
  simp only [sepExists_sepConj_left, sepConj_assoc]

@[expose] def wirePreKeyRest1 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_preKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 416#64) m.preKeyId ∗ wirePreKeyRest1 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest1
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_preKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 416#64) o ∗ wirePreKeyRest1 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with preKeyId := o } := by
  rw [wirePreKeyOf_eq_preKeyId A sp' { m with preKeyId := o }]; rfl

/-! ## 2. Tag 1 (`pre_key_id`, `+0x260..+0x27c` / `+0x3f0..+0x410`, `off = 0x68`) -/

@[expose] def wirePreKeyRest5 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 416#64) m.preKeyId ∗
  optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_regId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 408#64) m.registrationId ∗ wirePreKeyRest5 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest5
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_regId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 408#64) o ∗ wirePreKeyRest5 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with registrationId := o } := by
  rw [wirePreKeyOf_eq_regId A sp' { m with registrationId := o }]; rfl

@[expose] def wirePreKeyRest6 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 424#64) m.signedPreKeyId ∗ wirePreKeyRest6 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest6
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 424#64) o ∗ wirePreKeyRest6 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with signedPreKeyId := o } := by
  rw [wirePreKeyOf_eq_signedPreKeyId A sp' { m with signedPreKeyId := o }]; rfl

@[expose] def wirePreKeyRest7 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 424#64) m.signedPreKeyId

theorem wirePreKeyOf_eq_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 432#64) m.kyberPreKeyId ∗ wirePreKeyRest7 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest7
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 432#64) o ∗ wirePreKeyRest7 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with kyberPreKeyId := o } := by
  rw [wirePreKeyOf_eq_kyberPreKeyId A sp' { m with kyberPreKeyId := o }]; rfl

/-- Descriptor for the 4 `int32` arms of `PreKeySignalMessage::try_from`. -/
inductive Int32FieldPK where
  | preKeyId | registrationId | signedPreKeyId | kyberPreKeyId

/-- Entry offset of each `int32` arm in `PreKeySignalMessage::try_from`. -/
@[expose] def Int32FieldPK.entryOff : Int32FieldPK → BitVec 64
  | .preKeyId => 0x260#64 | .registrationId => 0x280#64
  | .signedPreKeyId => 0x1d0#64 | .kyberPreKeyId => 0x2c8#64

/-- Field update for each `int32` arm of `ProtoPreKeySignalMessage`. -/
@[expose] def Int32FieldPK.set (f : Int32FieldPK) (m : ProtoPreKeySignalMessage) (v : BitVec 32) :
    ProtoPreKeySignalMessage :=
  match f with
  | .preKeyId => { m with preKeyId := some v }
  | .registrationId => { m with registrationId := some v }
  | .signedPreKeyId => { m with signedPreKeyId := some v }
  | .kyberPreKeyId => { m with kyberPreKeyId := some v }

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
