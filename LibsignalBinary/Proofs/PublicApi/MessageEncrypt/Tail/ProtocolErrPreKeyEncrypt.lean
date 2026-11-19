/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `MessageEncrypt` `T5` Kyber Error Tail (`tailPreKeyEncryptErr_ok`)

Steps `+0xc38..+0xc64`: copies staged error words `w3..w5` from `sp + 0xb00` to `sp + 0x9d0`,
deallocates the optional Kyber ciphertext box at `sp + 0x8a0` when non-empty (`__rust_dealloc`),
and branches to `tailDropRecord_ok` at `+0x46c`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

theorem kyberSome_entails (a ptr n : BitVec 64) (id : BitVec 32) :
    (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ n) ∗ ((a + 0x10#64) ↦₃₂ id) ∗ memRegion (a + 0x14#64) 4 ⊢
      memRegion a 24 := by
  rw [memRegion_cut a 24 8 16 rfl (by decide),
    memRegion_cut (a + BitVec.ofNat 64 8) 16 8 8 rfl (by decide),
    memRegion_cut (a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) 8 4 4 rfl (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (Entails.refl _)))

theorem kyberNone_entails (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 16 ⊢ memRegion a 24 := by
  rw [memRegion_cut a 24 8 16 rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

theorem kyberPost_two {a1 a2 a3 b1 b2 b3 k1 k2 P S F X Y : SepProp} (hb : b1 ∗ b2 ∗ b3 ⊢ X)
    (hk : k1 ∗ k2 ⊢ Y) :
    a1 ∗ a2 ∗ a3 ∗ b1 ∗ b2 ∗ b3 ∗ k1 ∗ k2 ∗ P ∗ S ∗ F ⊢ a1 ∗ a2 ∗ a3 ∗ X ∗ Y ∗ P ∗ S ∗ F := by
  have e : b1 ∗ b2 ∗ b3 ∗ k1 ∗ k2 ∗ P ∗ S ∗ F = (b1 ∗ b2 ∗ b3) ∗ (k1 ∗ k2) ∗ P ∗ S ∗ F := by
    simp only [sepConj_assoc]
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hb (sepConj_mono_left hk))))

theorem kyberPost_four {a1 a2 a3 b1 b2 b3 k1 k2 k3 k4 P S F X Y : SepProp} (hb : b1 ∗ b2 ∗ b3 ⊢ X)
    (hk : k1 ∗ k2 ∗ k3 ∗ k4 ⊢ Y) :
    a1 ∗ a2 ∗ a3 ∗ b1 ∗ b2 ∗ b3 ∗ k1 ∗ k2 ∗ k3 ∗ k4 ∗ P ∗ S ∗ F ⊢
      a1 ∗ a2 ∗ a3 ∗ X ∗ Y ∗ P ∗ S ∗ F := by
  have e : b1 ∗ b2 ∗ b3 ∗ k1 ∗ k2 ∗ k3 ∗ k4 ∗ P ∗ S ∗ F =
      (b1 ∗ b2 ∗ b3) ∗ (k1 ∗ k2 ∗ k3 ∗ k4) ∗ P ∗ S ∗ F := by
    simp only [sepConj_assoc]
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hb (sepConj_mono_left hk))))

theorem kyberPost_four' {a1 a2 a3 b1 b2 b3 k1 k2 k3 k4 P S F X Y : SepProp} (hb : b1 ∗ b2 ∗ b3 ⊢ X)
    (hk : k1 ∗ k2 ∗ k3 ∗ k4 ⊢ Y) :
    P ∗ S ∗ a1 ∗ a2 ∗ a3 ∗ b1 ∗ b2 ∗ b3 ∗ k1 ∗ k2 ∗ k3 ∗ k4 ∗ F ⊢
      a1 ∗ a2 ∗ a3 ∗ X ∗ Y ∗ P ∗ S ∗ F :=
  Entails.trans (Entails.of_eq (by ac_rfl)) (kyberPost_four hb hk)

theorem kyberPoll_eq (sp : BitVec 64) :
    memRegion (sp + 0x8b8#64) 0x248 =
      memRegion (sp + 0x8b8#64) 0x118 ∗ memRegion (sp + 0x9d0#64) 24 ∗
        memRegion (sp + 0x9e8#64) 0x118 := by
  rw [memRegion_cut _ 0x248 0x118 0x130 rfl (by decide),
    memRegion_cut _ 0x130 24 0x118 rfl (by decide),
    addr_ofNat_add sp 0x8b8 0x118 0x9d0 rfl, addr_ofNat_add sp 0x9d0 24 0x9e8 rfl]

theorem kyberDropRecordPoll_eq (sp w3 w4 w5 : BitVec 64) :
    pollWith sp 0x9d0 [w3, w4, w5] =
      words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
        (memRegion (sp + 0x46a#64) 0x436 ∗ memRegion (sp + 0x8a0#64) 24 ∗
          memRegion (sp + 0x8b8#64) 0x118) ∗
        (memRegion (sp + 0x9e8#64) 0x118 ∗ memRegion (sp + 0xb00#64) 24 ∗
          memRegion (sp + 0xb18#64) 0x68) := by
  rw [pollWith_9d0_eq', memRegion_cut (sp + 0x46a#64) 0x566 0x436 0x130 rfl (by decide),
    memRegion_cut _ 0x130 24 0x118 rfl (by decide),
    addr_ofNat_add sp 0x46a 0x436 0x8a0 rfl, addr_ofNat_add sp 0x8a0 24 0x8b8 rfl,
    memRegion_cut (sp + 0x9e8#64) 0x198 0x118 0x80 rfl (by decide),
    memRegion_cut _ 0x80 24 0x68 rfl (by decide),
    addr_ofNat_add sp 0x9e8 0x118 0xb00 rfl, addr_ofNat_add sp 0xb00 24 0xb18 rfl]
  ac_rfl

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
