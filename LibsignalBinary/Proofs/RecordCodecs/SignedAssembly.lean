/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Epilogue

/-!
# Signed and Kyber Pre-Key Record Decoder Assembly

Connects `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` and
`signal_session::stores::decode_kyber_pre_key` to top-level `Program.ofImage`, X-form
(`AllocContractsX`), and relocatable `[LibsignalPlacement]` (Block `595`) specifications:
* `kyberDeserialize_eq`, `signedDeserialize_eq`: relate the record deserializers to
  `SignedPreKeyRecordStructure.decode`.
* `decodeSignedPreKeySpec_eq`, `decodeSignedPreKeyPlacedSpec_eq`: establish that the signed and
  Kyber pre-key wrapper contracts coincide (LLVM shares one compiled function for both).
* `decodeKyberPreKey_run`, `decodeSignedPreKey_run`, `decodeKyberPreKey_placed_ok`,
  `decodeSignedPreKey_placed_ok`: lift the proved wrapper to image and block-placed entrypoints.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.RecordCodecsBinary.SignedAssembly

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs

theorem kyberDeserialize_eq (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

theorem signedDeserialize_eq (bs : List (BitVec 8)) :
    SignedPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold SignedPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

/-- Both result predicates hold the same bytes for the same input. -/
theorem signedPreKeyResultAt_deserialize (A : RustAlloc) (r : BitVec 64) (bs : List (BitVec 8)) :
    signedPreKeyResultAt A r (SignedPreKeyRecord.deserialize bs) =
      kyberPreKeyResultAt A r (KyberPreKeyRecord.deserialize bs) := by
  rw [signedDeserialize_eq, kyberDeserialize_eq]
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

section XForm

open ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers

attribute [local irreducible] Program.fetch Program.externAt?

private theorem kpkStack_smallRoot_split_x (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ∗
        memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
  have h1 := Wire.stackAt_sub_split sp 128 smallRootStack
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) kpkSubStack =
      stackAt (sp - 128#64) kpkSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 128#64 - BitVec.ofNat 64 kpkSubStack := by
      change sp - 65536#64 = sp - 128#64 - 65408#64
      bv_omega
    rw [ha]
  have h3 := Wire.stackAt_sub_split (sp - 128#64) signedDecodeStackX kpkSubStack
  have h4 : stackAt sp 128 =
      memRegion (sp - 128#64) 8 ∗
        memRegion (sp - 128#64 + 8#64) 88 ∗
        memRegion (sp - 128#64 + 96#64) 32 := by
    unfold stackAt
    rw [show (128 : Nat) = 8 + (88 + 32) by decide,
      ProofLib.memRegion_split (sp - 128#64) 8 120 (by decide),
      ProofLib.memRegion_split (sp - 128#64 + 8#64) 88 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h1, h2, h3, h4]
  ac_rfl

private theorem kpkStack_exit_pack_x (sp c0 c1 c2 c3 : BitVec 64) :
    memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 128#64 + 8#64) 88 ∗
      ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
      ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
      ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
      ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
      stackAt (sp - 128#64) signedDecodeStackX ∗
      memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack := by
  rw [kpkStack_smallRoot_split_x sp]
  have hf32 := kpkFrame32_pack (sp - 128#64) c0 c1 c2 c3
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hf32))))
  apply entails_of_eq; ac_rfl

private theorem kpkDecodeStack_drop_split_x (sp' : BitVec 64) :
    stackAt sp' signedDecodeStackX =
      stackAt sp' Prost.dropDecodeErrorStackX ∗
        memRegion (sp' - BitVec.ofNat 64 signedDecodeStackX)
          (signedDecodeStackX - Prost.dropDecodeErrorStackX) := by
  have hs := Wire.stackAt_sub_split sp' Prost.dropDecodeErrorStackX signedDecodeStackX
  rw [hs]
  ac_rfl

private theorem okExit_pack_x (A : RustAlloc) (sp ret bytesA : BitVec 64) (bytes : List (BitVec 8))
    (pubCap pubPtr privCap privPtr sigCap sigPtr c0 c1 c2 c3 : BitVec 64) (pad32 : BitVec 32)
    (m : SignedPreKeyRecordStructure) :
    words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      signedPreKeyBufs A pubCap pubPtr privCap privPtr sigCap sigPtr m ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.ok ⟨m⟩) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := words88Sp_pack (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
    sigCap sigPtr (BitVec.ofNat 64 m.signature.length) m.timestamp (pad32 ++ m.id)
  have hret := signedPreKeyStructAt_ret_pack A ret pubCap pubPtr privCap privPtr sigCap sigPtr pad32 m
  have hstk := kpkStack_exit_pack_x sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp (pad32 ++ m.id) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  rw [← sepConj_assoc (words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
      privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
      sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
      m.timestamp (pad32 ++ m.id))]
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

private theorem errExit_pack_x (A : RustAlloc) (sp ret bytesA e c0 c1 c2 c3 : BitVec 64)
    (bytes : List (BitVec 8)) :
    ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (ret + 16#64) 72) ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX)) ∗
      A.pool ⊢
      kyberPreKeyResultAt A ret (.error .invalidProtobufEncoding) ∗
        (bytesA ↦ₛ bytes) ∗
        stackAt sp smallRootStack ∗
        A.pool := by
  have hsp88 := errLocal88_pack (sp - 128#64) e
  have hret := kyberErr88_pack A ret
  have hstk := kpkStack_exit_pack_x sp c0 c1 c2 c3
  have hstk' :
      memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStackX ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStackX) ⊢
      stackAt sp smallRootStack :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hsp88)) hstk
  exact sepConj_mono hret (sepConj_mono_right (sepConj_mono_left hstk'))

end XForm

section Placed

open CryptoVerification.RecordCodecs.Placed

/-- The image-free signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyRawSpec_eq (A : RustAlloc) :
    decodeSignedPreKeyRawSpec A = decodeKyberPreKeyRawSpec A := by
  simp only [decodeSignedPreKeyRawSpec, decodeKyberPreKeyRawSpec, signedPreKeyResultAt_deserialize]

/-- The relocatable `[LibsignalPlacement]` signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyPlacedSpec_eq [LibsignalPlacement] (A : RustAlloc) :
    decodeSignedPreKeyPlacedSpec A = decodeKyberPreKeyPlacedSpec A := by
  simp only [decodeSignedPreKeyPlacedSpec, decodeKyberPreKeyPlacedSpec, decodeSignedPreKeyRawSpec_eq]

/-- `decode_kyber_pre_key` (block `595`) under `[LibsignalPlacement]` meets
`decodeKyberPreKeyPlacedSpec A` from `SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeKyberPreKey_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeKyberPreKeyPlacedSpec A) :=
  DecodeKyberPreKey.decodeKyberPreKey_placed_ok_of_decode
    (SignedPreKeyDecode.signedDecode_placed_ok_of_deps hH d) d.dropDecodeError3

/-- `decode_kyber_pre_key` as `decode_signed_pre_key` (block `595`, LLVM keeps one function
for both) under `[LibsignalPlacement]` meets `decodeSignedPreKeyPlacedSpec A` from
`SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeSignedPreKey_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeSignedPreKeyPlacedSpec A) := by
  rw [decodeSignedPreKeyPlacedSpec_eq]
  exact decodeKyberPreKey_placed_ok hH d

end Placed

end CryptoVerification.RecordCodecsBinary.SignedAssembly
