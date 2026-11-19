/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Specs
public import LibsignalBinary.Proofs.E2E.Bin.SegCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Bin.CalleeProofs
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsEpilogue -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsStoreSession -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsStoresInitSaveIdentity -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib
open ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

/-! ## `.rodata` Role Strings (`0x87888`, `0x878ac`) -/

section PqxdhNameRoDataFacts
set_option maxRecDepth 2000000

end PqxdhNameRoDataFacts

/-! ## 36-Byte Word Decompositions and `meBytes` Clamping -/

theorem exists_words4_word32_of_length_36 {bs : List (BitVec 8)} (h : bs.length = 36) :
    ∃ (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗
          ((a + 24#64) ↦₆₄ᵣ w3) ∗ ((a + 32#64) ↦₃₂ᵣ w4)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₃₂ w4)) := by
  have hle : ∀ k, k ≤ 36 → k ≤ bs.length := fun k hk => h ▸ hk
  refine ⟨pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
            (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8),
          pack64 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)
            (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8),
          pack64 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)
            (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8),
          pack64 (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8)
            (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8) (bs.getD 31 0#8),
          pack32 (bs.getD 32 0#8) (bs.getD 33 0#8) (bs.getD 34 0#8) (bs.getD 35 0#8),
          fun a => ?_, fun a => ?_⟩
  · change (a ↦ᵣ bs.drop 0) = _
    rw [pointsToBytesRO_drop_split a bs 0 8 (hle 8 (by decide)),
        pointsToBytesRO_drop_split _ bs 8 8 (hle 16 (by decide)),
        pointsToBytesRO_drop_split _ bs 16 8 (hle 24 (by decide)),
        pointsToBytesRO_drop_split _ bs 24 8 (hle 32 (by decide)),
        pointsToBytesRO_drop_split _ bs 32 4 (hle 36 (by decide))]
    have hdrop36 : bs.drop 36 = [] := by simp [h]
    rw [hdrop36, pointsToBytesRO_nil, sepConj_emp,
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 0 (hle 8 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 8 (hle 16 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 16 (hle 24 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 24 (hle 32 (by decide)),
        pointsToBytesRO_take4_eq_pointsTo32RO _ bs 32 (hle 36 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    rw [h8]
    simp only [pack32, BitVec.add_assoc, BitVec.reduceAdd]
  · change (a ↦ₛ bs.drop 0) = _
    rw [pointsToBytes_drop_split a bs 0 8 (hle 8 (by decide)),
        pointsToBytes_drop_split _ bs 8 8 (hle 16 (by decide)),
        pointsToBytes_drop_split _ bs 16 8 (hle 24 (by decide)),
        pointsToBytes_drop_split _ bs 24 8 (hle 32 (by decide)),
        pointsToBytes_drop_split _ bs 32 4 (hle 36 (by decide))]
    have hdrop36 : bs.drop 36 = [] := by simp [h]
    rw [hdrop36, pointsToBytes_nil, sepConj_emp,
        pointsToBytes_take8_eq_pointsTo64 _ bs 0 (hle 8 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 8 (hle 16 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 16 (hle 24 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 24 (hle 32 (by decide)),
        pointsToBytes_take4_eq_pointsTo32 _ bs 32 (hle 36 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    rw [h8]
    simp only [pack32, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_36_words4_word32_split (a : BitVec 64) :
    memRegion a 36 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 32, (a + 32#64) ↦₃₂ d4) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 4)
        (b' := a + 32#64) rfl (by bv_omega) (by decide),
      memRegion_32_four_64 a,
      memRegion_four (a + 32#64)]
  simp only [sepConj_assoc]

theorem pointsToBytes_meBytes_split (a : BitVec 64) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) :
    (a ↦ₛ meBytes) =
      (a ↦ₛ meBytes.take 32) ∗ ((a + 32#64) ↦₃₂ meRegId meBytes) := by
  have hle : ∀ k, k ≤ 36 → k ≤ meBytes.length := fun k hk => hlen ▸ hk
  change (a ↦ₛ meBytes.drop 0) = _
  rw [pointsToBytes_drop_split a meBytes 0 32 (hle 32 (by decide)),
      pointsToBytes_drop_split _ meBytes 32 4 (hle 36 (by decide))]
  have hdrop36 : meBytes.drop 36 = [] := by simp [hlen]
  rw [hdrop36, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ meBytes 32 (hle 36 (by decide))]
  rfl

def meSkVec (meBytes : List (BitVec 8)) (hlen : meBytes.length = 36) : List.Vector (BitVec 8) 32 :=
  ⟨meBytes.take 32, by simp [hlen]⟩

def meClampedVec (meBytes : List (BitVec 8)) (hlen : meBytes.length = 36) : List.Vector (BitVec 8)
  32 :=
  Ratchet.clampScalar (meSkVec meBytes hlen)

theorem clampScalar_idem (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  apply Subtype.ext
  change [(b0 &&& 0xf8#8) &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
    b15,
          b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
          (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8] =
         [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
          b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
          (b31 &&& 0x7f#8) ||| 0x40#8]
  have h0 : (b0 &&& 0xf8#8) &&& 0xf8#8 = b0 &&& 0xf8#8 := by
    rw [BitVec.and_assoc]; rfl
  have h31 : (((b31 &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b31 &&& 0x7f#8) ||| 0x40#8 := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc,
      show (0x7f#8 : BitVec 8) &&& 0x7f#8 = 0x7f#8 from rfl,
      show (0x40#8 : BitVec 8) &&& 0x7f#8 = 0x40#8 from rfl,
      BitVec.or_assoc,
      show (0x40#8 : BitVec 8) ||| 0x40#8 = 0x40#8 from rfl]
  rw [h0, h31]

theorem meKeyPairBytes_eq_of_length_36 (pubKey : PubKeyFn) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) :
    meKeyPairBytes pubKey meBytes =
      (pubKey (meClampedVec meBytes hlen)).toList ++ (meClampedVec meBytes hlen).toList := by
  have h32 : (meBytes.take 32).length = 32 := by simp [hlen]
  unfold meKeyPairBytes meClampedVec meSkVec
  simp only [h32, ↓reduceDIte]

theorem pointsToBytes_meKeyPairBytes_eq (pubKey : PubKeyFn) {meBytes : List (BitVec 8)}
    (hlen : meBytes.length = 36) (a : BitVec 64) :
    ((a ↦ₛ (pubKey (Ratchet.clampScalar (meClampedVec meBytes hlen))).toList) ∗
     ((a + 32#64) ↦ₛ (meClampedVec meBytes hlen).toList)) =
      (a ↦ₛ meKeyPairBytes pubKey meBytes) := by
  rw [meKeyPairBytes_eq_of_length_36 pubKey hlen]
  unfold meClampedVec
  rw [clampScalar_idem (meSkVec meBytes hlen), pointsToBytes_append,
      List.Vector.toList_length]

/-! ## `<IdentityKey>::decode` (`0x0ae58`) -/

@[expose] def pkTryFromLen33AnySpec : Spec (BitVec 64 × BitVec 64 × IdentityKey) where
  pre := fun (out, keyPtr, k) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: k.publicKey.bytes.toList)) ∗ memRegion out 40
  post := fun (out, keyPtr, k) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: k.publicKey.bytes.toList)) ∗
      (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (out + 33#64) 7

private def remoteKeyChunksAny (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem exists_remoteKeyChunksAny_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = remoteKeyChunksAny a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8),
    pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (hle 4 (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (hle 5 (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (hle 6 (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (hle 7 (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (hle 9 (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (hle 13 (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (hle 15 (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (hle 23 (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (hle 31 (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (hle 32 (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (hle 4 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (hle 5 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (hle 6 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (hle 7 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (hle 9 (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (hle 13 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (hle 15 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (hle 23 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (hle 31 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (hle 32 (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [remoteKeyChunksAny, pack32, BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunksAny_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunksAny (ret + 8#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗
      ((ret + 15#64) ↦₁₆ v7) ∗ ((ret + 17#64) ↦₃₂ v9) ∗ ((ret + 21#64) ↦₁₆ v13) ∗
      ((ret + 23#64) ↦₆₄ v15) ∗ ((ret + 31#64) ↦₆₄ v23) ∗ ((ret + 39#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunksAny]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunksAny_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunksAny (sp - 87#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗
      ((sp - 80#64) ↦₁₆ v7) ∗ ((sp - 78#64) ↦₃₂ v9) ∗ ((sp - 74#64) ↦₁₆ v13) ∗
      ((sp - 72#64) ↦₆₄ v15) ∗ ((sp - 64#64) ↦₆₄ v23) ∗ ((sp - 56#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunksAny]
  have h83 : sp - 87#64 + 4#64 = sp - 83#64 := by bv_omega
  have h82 : sp - 87#64 + 5#64 = sp - 82#64 := by bv_omega
  have h81 : sp - 87#64 + 6#64 = sp - 81#64 := by bv_omega
  have h80 : sp - 87#64 + 7#64 = sp - 80#64 := by bv_omega
  have h78 : sp - 87#64 + 9#64 = sp - 78#64 := by bv_omega
  have h74 : sp - 87#64 + 13#64 = sp - 74#64 := by bv_omega
  have h72 : sp - 87#64 + 15#64 = sp - 72#64 := by bv_omega
  have h64 : sp - 87#64 + 23#64 = sp - 64#64 := by bv_omega
  have h56 : sp - 87#64 + 31#64 = sp - 56#64 := by bv_omega
  rw [h83, h82, h81, h80, h78, h74, h72, h64, h56]

private theorem sevenLo_sp_87_any (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗ rest) =
      (((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
       ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 87#64) (sp - 86#64) (sp - 85#64) (sp - 84#64)
    (sp - 83#64) (sp - 82#64) (sp - 81#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_8_any (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗ rest) =
      (((ret + 8#64) ↦₈ b0) ∗ ((ret + 9#64) ↦₈ b1) ∗ ((ret + 10#64) ↦₈ b2) ∗
       ((ret + 11#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 8#64) (ret + 9#64) (ret + 10#64) (ret + 11#64)
    (ret + 12#64) (ret + 13#64) (ret + 14#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sp_88_four_bytes_any (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
    rest) =
      (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗ rest) := by
  have h87 : sp - 87#64 = sp - 88#64 + 1#64 := by bv_omega
  have h86 : sp - 86#64 = sp - 88#64 + 2#64 := by bv_omega
  have h85 : sp - 85#64 = sp - 88#64 + 3#64 := by bv_omega
  rw [h87, h86, h85, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sp_84_split_16_any (sp : BitVec 64) (b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) =
      (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5)) ∗ rest) := by
  have h82 : sp - 82#64 = sp - 84#64 + 2#64 := by bv_omega
  rw [h82, ← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16,
    ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_40_identityKeyDecode_split_any (ret : BitVec 64) :
    memRegion ret 40 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 32, (ret + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (ret + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (ret + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (ret + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 16, (ret + 15#64) ↦₁₆ r15) ∗
      (∃∗ r17 : BitVec 32, (ret + 17#64) ↦₃₂ r17) ∗
      (∃∗ r21 : BitVec 16, (ret + 21#64) ↦₁₆ r21) ∗
      (∃∗ r23 : BitVec 64, (ret + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 64, (ret + 31#64) ↦₆₄ r31) ∗
      (∃∗ r39 : BitVec 8, (ret + 39#64) ↦₈ r39) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 32)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 28)
        (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 27)
        (b' := ret + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 26)
        (b' := ret + 14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 25)
        (b' := ret + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 2) (k := 23)
        (b' := ret + 17#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 4) (k := 19)
        (b' := ret + 21#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 21#64) (n := 2) (k := 17)
        (b' := ret + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 23#64) (n := 8) (k := 9)
        (b' := ret + 31#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 31#64) (n := 8) (k := 1)
        (b' := ret + 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret, memRegion_four (ret + 8#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_two (ret + 15#64), memRegion_four (ret + 17#64), memRegion_two (ret + 21#64),
      ProofLib.memRegion_eight (ret + 23#64), ProofLib.memRegion_eight (ret + 31#64),
        memRegion_one (ret + 39#64)]

private theorem stackAt_identityKeyDecode_split_any (sp : BitVec 64) :
    stackAt sp 0x60 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s56 : BitVec 8, (sp - 40#64) ↦₈ s56) ∗
      memRegion (sp - 39#64) 7 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ s88 : BitVec 32, (sp - 8#64) ↦₃₂ s88) ∗
      (∃∗ s92 : BitVec 16, (sp - 4#64) ↦₁₆ s92) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x60 = 96#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 40) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 1) (k := 39)
        (b' := sp - 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 48#64), memRegion_one (sp - 40#64),
      (ProofLib.memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem memRegion_sp_88_40_split_any (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ k0 : BitVec 32, (sp - 88#64) ↦₃₂ k0) ∗
      (∃∗ k4 : BitVec 16, (sp - 84#64) ↦₁₆ k4) ∗
      (∃∗ k6 : BitVec 16, (sp - 82#64) ↦₁₆ k6) ∗
      (∃∗ k8 : BitVec 16, (sp - 80#64) ↦₁₆ k8) ∗
      (∃∗ k10 : BitVec 32, (sp - 78#64) ↦₃₂ k10) ∗
      (∃∗ k14 : BitVec 16, (sp - 74#64) ↦₁₆ k14) ∗
      (∃∗ k16 : BitVec 64, (sp - 72#64) ↦₆₄ k16) ∗
      (∃∗ k24 : BitVec 64, (sp - 64#64) ↦₆₄ k24) ∗
      (∃∗ k32 : BitVec 8, (sp - 56#64) ↦₈ k32) ∗
      memRegion (sp - 55#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 36)
        (b' := sp - 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 2) (k := 34)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 2) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 2) (k := 30)
        (b' := sp - 78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 4) (k := 26)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 7)
        (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 88#64), memRegion_two (sp - 84#64), memRegion_two (sp - 82#64),
      memRegion_two (sp - 80#64), memRegion_four (sp - 78#64), memRegion_two (sp - 74#64),
      ProofLib.memRegion_eight (sp - 72#64), ProofLib.memRegion_eight (sp - 64#64),
        memRegion_one (sp - 56#64)]

structure OpenEmptyGhostP where
  outPtr  : BitVec 64
  who     : BitVec 32
  mePtr   : BitVec 64
  meBytes : List (BitVec 8)
  tlsInit : Option (BitVec 64 × BitVec 64)

theorem emptyHashMapAt_eq_words64At (ctrlPtr out k0 k1 : BitVec 64) :
    emptyHashMapAt ctrlPtr out k0 k1 = words64At out [ctrlPtr, 0#64, 0#64, 0#64, k0, k1] := by
  unfold emptyHashMapAt StoreNew.emptyHashMapAt StoreNew.emptyRawTableAt StoreNew.randomStateAt
  dsimp only [words64At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  ac_rfl

/-- Callee-saved registers `x19..x26, x28..x29` and link register `x30` spilled at the top of
`libsignal_pqxdh_e2e::open`'s `0x4b0`-byte stack frame (`s0.sp - 0x60#64 .. s0.sp`,
with unused 8-byte slot at `s0.sp - 0x48#64` since `x27` is untouched). -/
@[expose] def openPqxdhSavedRegsAt (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗ (∃∗ d27 : BitVec 64, (s0.sp - 0x48#64) ↦₆₄ d27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

theorem openPqxdhSavedRegsAt_entails_cells (s0 : State) :
    Entails (openPqxdhSavedRegsAt s0) (cells (s0.sp - 0x60#64) 12) := by
  dsimp only [openPqxdhSavedRegsAt]
  apply cells_sub_succ_entails 96 12
  apply cells_sub_succ_entails 88 11
  apply cells_sub_succ_entails 80 10
  rw [ProofLib.cells_sub_succ s0.sp 72 9 (by decide) (by decide), ← sepExists_sepConj_left]
  refine sepConj_mono_right ?_
  apply cells_sub_succ_entails 64 8
  apply cells_sub_succ_entails 56 7
  apply cells_sub_succ_entails 48 6
  apply cells_sub_succ_entails 40 5
  apply cells_sub_succ_entails 32 4
  apply cells_sub_succ_entails 24 3
  apply cells_sub_succ_entails 16 2
  rw [ProofLib.cells_sub_succ s0.sp 8 1 (by decide) (by decide), ProofLib.cells_zero]
  exact Entails.sepExists_right _ (by rw [sepConj_emp]; exact Entails.refl _)

end CryptoVerification.E2E.Pqxdh.WireEntries
