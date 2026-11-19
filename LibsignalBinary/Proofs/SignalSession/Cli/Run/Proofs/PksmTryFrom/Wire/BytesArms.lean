/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option maxRecDepth 400000

/-!
# `PreKeySignalMessage::try_from`: `bytes::merge` Arms and `DecodeError::push` Tails

Symbolic execution of the four `prost::encoding::bytes::merge` field arms (`kyber_ciphertext`,
`base_key`, `identity_key`, `message`) and their `DecodeError::push` error tails
(`+0x340..+0x45c → +0x460`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

theorem L1_BytesArms : True := trivial

@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_216 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 216) = sp' + 296#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_200 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 200) = sp' + 312#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_176 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 176) = sp' + 336#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_152 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 152) = sp' + 360#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_128 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 128) = sp' + 384#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_72 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_64 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Basic register / memory helpers -/

theorem wirePreKeyAt_entails_of (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g a m ⊢ wirePreKeyOf A a m := by
  unfold wirePreKeyOf; exact Entails.sepExists_intro (P := fun g => wirePreKeyAt A g a m) g

/-! ## Caller-relative `bytes::merge` & `DecodeError::push` wrappers and shared tail (`+0x458..+0x460`) -/

@[expose] def wirePreKeyU32s (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  optU32At (sp' + 408#64) m.registrationId ∗
    optU32At (sp' + 416#64) m.preKeyId ∗
    optU32At (sp' + 424#64) m.signedPreKeyId ∗
    optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyAt_split_kyberCt (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
      (optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem vecU8At_kyberCt_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 312#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with kyberCiphertext := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with kyberCt := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with kyberCiphertext := some v0 })
  rw [wirePreKeyAt_split_kyberCt A { g with kyberCt := ⟨cap0, ptr0⟩ } sp' { m with kyberCiphertext := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_baseKey (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_baseKey_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 336#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with baseKey := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with baseKey := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with baseKey := some v0 })
  rw [wirePreKeyAt_split_baseKey A { g with baseKey := ⟨cap0, ptr0⟩ } sp' { m with baseKey := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_identityKey (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_identityKey_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 360#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with identityKey := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with identityKey := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with identityKey := some v0 })
  rw [wirePreKeyAt_split_identityKey A { g with identityKey := ⟨cap0, ptr0⟩ } sp' { m with identityKey := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_message (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.message (sp' + 384#64) m.message ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_message_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 384#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with message := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with message := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with message := some v0 })
  rw [wirePreKeyAt_split_message A { g with message := ⟨cap0, ptr0⟩ } sp' { m with message := some v0 }]
  exact Entails.refl _

/-! ## Tag 8 (`kyber_ciphertext`, `+0x238..+0x25c` / `+0x36c..+0x380` → `+0x3e0..+0x3ec`, `off = 0x00`) -/

inductive BytesArmFieldPK where
  | kyberCt
  | baseKey
  | identityKey
  | message
  deriving DecidableEq

@[expose, simp]
def BytesArmFieldPK.off : BytesArmFieldPK → BitVec 64
  | .kyberCt => 0x00#64
  | .baseKey => 0x18#64
  | .identityKey => 0x30#64
  | .message => 0x48#64

@[expose, simp]
def BytesArmFieldPK.entryOff : BytesArmFieldPK → BitVec 64
  | .kyberCt => 0x238#64
  | .baseKey => 0x190#64
  | .identityKey => 0x2a0#64
  | .message => 0x200#64

@[expose, simp]
def BytesArmFieldPK.set : BytesArmFieldPK → ProtoPreKeySignalMessage → List (BitVec 8) → ProtoPreKeySignalMessage
  | .kyberCt, m, v => { m with kyberCiphertext := some v }
  | .baseKey, m, v => { m with baseKey := some v }
  | .identityKey, m, v => { m with identityKey := some v }
  | .message, m, v => { m with message := some v }

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
