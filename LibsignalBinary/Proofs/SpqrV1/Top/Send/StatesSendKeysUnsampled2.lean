/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Sub-Step (`+684..+2588`)

**Checked by Lean.**

Verifies `step_keysUnsampled_684_to_2588`: calls `Authenticator::mac_hdr`, sets up
`ekSentInlineWordsAt`, reserves 32 bytes via `do_reserve_and_handle [local#2]`, and
appends the 32-byte MAC to `hdr`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

theorem vecU8_len32_expose {A : RustAlloc} (a : BitVec 64) (mac : Bytes) (hlen : mac.length = 32) :
    vecU8 A a mac ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧ (cap == 0#64) = false⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗
      memRegion (ptr + 32#64) (cap.toNat - 32) := by
  unfold vecU8 vecU8At vecHeader
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  by_cases hc : cap = 0#64
  · subst hc
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte, sepConj_emp, hlen,
      show BitVec.ofNat 64 32 = 32#64 from rfl, sepConj_assoc]
    have hcomm0 :
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         ⌜32 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝) =
        (⌜32 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64)) := by ac_rfl
    rw [hcomm0]
    exact Entails.pure_left fun h => nomatch h.1
  · have hc0 : ¬ (cap = 0) := hc
    have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    simp only [hc0, ↓reduceIte, hlen, show BitVec.ofNat 64 32 = 32#64 from rfl, sepConj_assoc]
    have hcomm :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) =
        (⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
         (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
         A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ mac) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    exact Entails.pure_right ⟨hle, hlt, hp, hcb⟩ (Entails.refl _)

/-- Four consecutive 64-bit words (`32` bytes) at `a`. -/
@[expose] def words4At (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)

theorem memRegion_32_eq_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]

theorem words4At_entails_memRegion (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    words4At a w0 w1 w2 w3 ⊢ memRegion a 32 := by
  unfold words4At
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (ProofLib.pointsTo64_entails_memRegion _ _)))

theorem memRegion_24_eq_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]

theorem words3_entails_memRegion (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _))

/-- Inline 13-word (104-byte) layout of `unchunkedEkSentCt1ReceivedAt` at `a`:
    - `+0..+48`: `auth` (`48`B)
    - `+48..+72`: `ek` Vec header (`cap, ptr, len`)
    - `+72..+96`: `dk` Vec header (`cap, ptr, len`)
    - `+96..+104`: `epoch` (`8`B) -/
@[expose] def ekSentInlineWordsAt (a : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (ekCap ekPtr ekLen dkCap dkPtr dkLen epoch : BitVec 64) : SepProp :=
  authInlineWordsAt g a auth ∗
  ((a + 48#64) ↦₆₄ ekCap) ∗ ((a + 56#64) ↦₆₄ ekPtr) ∗ ((a + 64#64) ↦₆₄ ekLen) ∗
  ((a + 72#64) ↦₆₄ dkCap) ∗ ((a + 80#64) ↦₆₄ dkPtr) ∗ ((a + 88#64) ↦₆₄ dkLen) ∗
  ((a + 96#64) ↦₆₄ epoch)

theorem memRegion_104_eq_words13 (a : BitVec 64) :
    memRegion a 104 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (a + 64#64) ↦₆₄ d8) ∗
      (∃∗ d9 : BitVec 64, (a + 72#64) ↦₆₄ d9) ∗
      (∃∗ d10 : BitVec 64, (a + 80#64) ↦₆₄ d10) ∗
      (∃∗ d11 : BitVec 64, (a + 88#64) ↦₆₄ d11) ∗
      (∃∗ d12 : BitVec 64, (a + 96#64) ↦₆₄ d12) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide),
      memRegion_48_eq_words6 a,
      memRegion_48_eq_words6 (a + 48#64),
      ProofLib.memRegion_eight (a + 96#64),
      show (a + 48#64) + 8#64 = a + 56#64 by bv_omega,
      show (a + 48#64) + 16#64 = a + 64#64 by bv_omega,
      show (a + 48#64) + 24#64 = a + 72#64 by bv_omega,
      show (a + 48#64) + 32#64 = a + 80#64 by bv_omega,
      show (a + 48#64) + 40#64 = a + 88#64 by bv_omega]
  ac_rfl

theorem ekSentInlineWordsAt_entails_memRegion (a : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (ekCap ekPtr ekLen dkCap dkPtr dkLen epoch : BitVec 64) :
    ekSentInlineWordsAt a g auth ekCap ekPtr ekLen dkCap dkPtr dkLen epoch ⊢
    memRegion a 104 := by
  unfold ekSentInlineWordsAt
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 48) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 40) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 32) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 24) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 8) (k := 16) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (authInlineWordsAt_entails_memRegion g a auth)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (ProofLib.pointsTo64_entails_memRegion _ _)))))))

/-- Sixteen consecutive 64-bit words (`128` bytes) at `a`. -/
@[expose] def words16At (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) : SepProp :=
  words8At a w0 w1 w2 w3 w4 w5 w6 w7 ∗
  words8At (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15

theorem memRegion_128_eq_words16 (a : BitVec 64) :
    memRegion a 128 =
      ((∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
       (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
       (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
       (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
       (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
       (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
       (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
       (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7)) ∗
      ((∃∗ d8 : BitVec 64, (a + 64#64) ↦₆₄ d8) ∗
       (∃∗ d9 : BitVec 64, ((a + 64#64) + 8#64) ↦₆₄ d9) ∗
       (∃∗ d10 : BitVec 64, ((a + 64#64) + 16#64) ↦₆₄ d10) ∗
       (∃∗ d11 : BitVec 64, ((a + 64#64) + 24#64) ↦₆₄ d11) ∗
       (∃∗ d12 : BitVec 64, ((a + 64#64) + 32#64) ↦₆₄ d12) ∗
       (∃∗ d13 : BitVec 64, ((a + 64#64) + 40#64) ↦₆₄ d13) ∗
       (∃∗ d14 : BitVec 64, ((a + 64#64) + 48#64) ↦₆₄ d14) ∗
       (∃∗ d15 : BitVec 64, ((a + 64#64) + 56#64) ↦₆₄ d15)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 64) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 a,
      memRegion_64_eq_words8 (a + 64#64)]

theorem words16At_entails_memRegion (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64) :
    words16At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
    memRegion a 128 := by
  unfold words16At
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 64) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono
    (words8At_entails_memRegion a w0 w1 w2 w3 w4 w5 w6 w7)
    (words8At_entails_memRegion (a + 64#64) w8 w9 w10 w11 w12 w13 w14 w15)

@[simp]
theorem reserveCap_64_64_32 : reserveCap 64 64 32 = 128 := by decide

@[simp]
theorem bytesAt_false_eq (a : BitVec 64) (bs : Bytes) :
    bytesAt false a bs = (a ↦ₛ bs) := rfl

/-! ## Tail Layout Lemmas -/

theorem chunkedStatesTail920At_keysSampled_eq {F : ShaCompress} (A : RustAlloc) (a : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesTail920At A a (.keysSampled st) =
      chunkedKeysSampledAt A a st ∗ memRegion (a + 504#64) 416 :=
  rfl

theorem authInlineWordsAt_352_entails_memRegion_400
    (g : AuthenticatorGhost) (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ memRegion (a + 48#64) 352 ⊢ memRegion a 400 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 352) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (authInlineWordsAt_entails_memRegion g a auth)

theorem hdr_mac_len_96 (K : MlKem) (seed : List.Vector (BitVec 8) 64) {mac : Bytes}
    (hmac_len : mac.length = 32) :
    ((K.fromSeed seed).1.toList ++ mac).length = 96 := by
  rw [List.length_append, List.Vector.toList_length, hmac_len]

theorem encodeBytesResult_hdr_mac (K : MlKem) (seed : List.Vector (BitVec 8) 64) {mac : Bytes}
    (hmac_len : mac.length = 32) :
    ∃ enc : PolyEncoder,
      encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63"
        ((K.fromSeed seed).1.toList ++ mac) = .ok enc := by
  have h96 := hdr_mac_len_96 K seed hmac_len
  obtain ⟨enc, h1, h2, _⟩ := encodeBytesResult_of_len_even_le
    (msg := (K.fromSeed seed).1.toList ++ mac) (by omega) (by omega)
  exact ⟨enc, h1, h2⟩

/-! ## Sub-Step 1c (`+684 -> +2588`) -/

@[simp]
theorem macHdrUnchecked_length (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (hdr : Bytes) :
    (auth.macHdrUnchecked F ep hdr).length = 32 := by
  rw [MacHdrFacts.macHdrUnchecked_eq_hmacWith, LibsignalSpqrV1.length_hmacWith]

theorem hdr_data_len_105 (K : MlKem) (seed : List.Vector (BitVec 8) 64) (ep : Epoch) :
    (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ (K.fromSeed seed).1.toList).length = 105 := by
  simp only [List.length_append, MacHdrFacts.hdrLabel_length,
    toBEBytes_8_length, List.Vector.toList_length]

theorem memRegion_504_expose_chunk_slot (sp : BitVec 64) :
    memRegion (sp + 4192#64) 504 =
      (∃∗ d0 : BitVec 64, (sp + 4192#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 4200#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4208#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 4216#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 16, (sp + 4224#64) ↦₁₆ d4) ∗
      memRegion (sp + 4226#64) 470 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 8) (k := 496) (b' := sp + 4200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4200#64) (n := 8) (k := 488) (b' := sp + 4208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4208#64) (n := 8) (k := 480) (b' := sp + 4216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4216#64) (n := 8) (k := 472) (b' := sp + 4224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4224#64) (n := 2) (k := 470) (b' := sp + 4226#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4192#64),
      ProofLib.memRegion_eight (sp + 4200#64),
      ProofLib.memRegion_eight (sp + 4208#64),
      ProofLib.memRegion_eight (sp + 4216#64),
      ProofLib.memRegion_two (sp + 4224#64)]

theorem chunkAt_and_470_entails_memRegion_504 (sp : BitVec 64) (c : Chunk) :
    chunkAt (sp + 4192#64) c ∗ memRegion (sp + 4226#64) 470 ⊢ memRegion (sp + 4192#64) 504 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 34) (k := 470) (b' := sp + 4226#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (chunkAt_entails_memRegion (sp + 4192#64) c)

theorem memRegion_4704_2400_split_macHdr (sp : BitVec 64) :
    memRegion (sp + 4704#64) 2400 =
      memRegion (sp + 4704#64) 128 ∗
      memRegion (sp + 4832#64) 24 ∗
      memRegion (sp + 4856#64) 2248 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 128) (k := 2272) (b' := sp + 4832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4832#64) (n := 24) (k := 2248) (b' := sp + 4856#64) rfl (by bv_omega) (by decide)]

theorem macHdr_ok_elim {F : ShaCompress} {auth : Authenticator} {ep : Epoch} {hdr mac : Bytes}
    (h : auth.macHdr F ep hdr = .ok mac) :
    mac = auth.macHdrUnchecked F ep hdr ∧
    auth.macKey.length < 2 ^ 32 ∧
    (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ hdr).length < 2 ^ 32 := by
  unfold Authenticator.macHdr at h
  dsimp only at h
  split_ifs at h with hlt
  exact ⟨(Except.ok.inj h).symm, hlt.1, hlt.2⟩

theorem authMacHdrPinned_onPanic_of_ok {F : ShaCompress} {A : RustAlloc}
    (x : AuthMacHdrPinnedGhost) {mac : Bytes}
    (h : x.auth.macHdr F x.ep x.hdr = .ok mac) (s0 sf : State) :
    (authMacHdrPinnedSpec F A).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  obtain ⟨_, hk, hd⟩ := macHdr_ok_elim h
  dsimp only [authMacHdrPinnedSpec]
  have h1 : ¬ (2 ^ 32 ≤ x.auth.macKey.length) := by omega
  have h2 : ¬ (2 ^ 32 ≤ (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 x.ep ++ x.hdr).length) := by omega
  simp only [h1, h2, or_false]

theorem send_hdr_chunk_ok_elim {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    {tape tape' : Bytes}
    {outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    (hsend : st.send_hdr_chunk K spqrPolyApi tape = .ok (outSt, chunk, tape')) :
    ∃ (h64 : 64 ≤ tape.length) (sending_hdr : PolyEncoder),
      let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
      let mac := st.uc.auth.macHdrUnchecked F st.uc.epoch (K.fromSeed seed).1.toList
      st.uc.auth.macHdr F st.uc.epoch (K.fromSeed seed).1.toList = .ok mac ∧
      encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok sending_hdr ∧
      sending_hdr.nextChunk = .ok (outSt.sending_hdr, chunk) ∧
      outSt.uc = { epoch := st.uc.epoch, auth := st.uc.auth,
                   ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList } ∧
      tape' = tape.drop 64 := by
  have h64 : 64 ≤ tape.length := by
    by_contra hlt
    rw [send_hdr_chunk_of_lt_64 K st (by omega)] at hsend
    cases hsend
  refine ⟨h64, ?_⟩
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
  cases hmac : st.uc.auth.macHdr F st.uc.epoch (K.fromSeed seed).1.toList with
  | error p =>
    rw [send_hdr_chunk_of_macHdr_err K st h64 hmac] at hsend
    cases hsend
  | ok mac =>
    obtain ⟨rfl, _, _⟩ := macHdr_ok_elim hmac
    obtain ⟨sending_hdr, henc_res, henc_exp⟩ :=
      encodeBytesResult_hdr_mac K seed (macHdrUnchecked_length F st.uc.auth st.uc.epoch _)
    refine ⟨sending_hdr, hmac, henc_res, ?_⟩
    cases hnc : sending_hdr.nextChunk with
    | error p =>
      rw [send_hdr_chunk_of_nextChunk_err K st h64 hmac henc_exp hnc] at hsend
      cases hsend
    | ok pair =>
      rcases pair with ⟨sending_hdr', chunk'⟩
      have hok := send_hdr_chunk_of_ok K st h64 hmac henc_exp hnc
      dsimp only at hok
      rw [hok] at hsend
      injection hsend with htuple
      injection htuple with hout hrest
      injection hrest with hch htp
      have hsnd : sending_hdr' = outSt.sending_hdr :=
        congrArg Chunked.SendEk.KeysSampled.sending_hdr hout
      have huc : { epoch := st.uc.epoch, auth := st.uc.auth,
                   ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList } = outSt.uc :=
        congrArg Chunked.SendEk.KeysSampled.uc hout
      rw [← hsnd, ← huc, ← hch, ← htp]
      exact ⟨rfl, rfl, rfl⟩

theorem fold_vecU8_of_inline {A : RustAlloc} (a cap ptr len : BitVec 64) (bs : Bytes)
    (hlen : BitVec.ofNat 64 bs.length = len) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
    RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader RustHeap.vecU8Buf
  rw [hlen]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem fold_authenticatorAt_of_inline {A : RustAlloc} (g : AuthenticatorGhost)
    (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ authHeapBufs A g auth ⊢
    authenticatorAt A a auth := by
  rw [← authenticatorPinAt_eq_inline_heap A g a auth]
  unfold authenticatorAt authenticatorPinAt vecU8
  exact sepConj_mono
    (Entails.sepExists_right g.rootKey.cap (Entails.sepExists_right g.rootKey.ptr (Entails.refl _)))
    (Entails.sepExists_right g.macKey.cap (Entails.sepExists_right g.macKey.ptr (Entails.refl _)))

theorem fold_chunkedKeysSampledAt {F : ShaCompress} {A : RustAlloc}
    (a : BitVec 64) (g : AuthenticatorGhost)
    (outSt : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (auth : Authenticator) (epoch : Epoch) (ek dk : Bytes)
    (ek_ptr dk_ptr : BitVec 64)
    (huc : outSt.uc = { epoch := epoch, auth := auth, ek := ek, dk := dk })
    (hek : BitVec.ofNat 64 ek.length = 1152#64)
    (hdk : BitVec.ofNat 64 dk.length = 2400#64) :
    polyEncoderAt A a outSt.sending_hdr ∗
    ekSentInlineWordsAt (a + 400#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
    authHeapBufs A g auth ∗
    RustHeap.vecU8Buf A 1152#64 ek_ptr ek ∗
    RustHeap.vecU8Buf A 2400#64 dk_ptr dk ⊢
    chunkedKeysSampledAt A a outSt := by
  unfold chunkedKeysSampledAt unchunkedHeaderSentAt
  rw [huc]
  dsimp only [ekSentInlineWordsAt]
  have h1 := fold_authenticatorAt_of_inline (A := A) g (a + 400#64) auth
  have h2 := fold_vecU8_of_inline (A := A) ((a + 400#64) + 48#64) 1152#64 ek_ptr 1152#64 ek hek
  have h3 := fold_vecU8_of_inline (A := A) ((a + 400#64) + 72#64) 2400#64 dk_ptr 2400#64 dk hdk
  rw [show ((a + 400#64) + 48#64) + 8#64 = (a + 400#64) + 56#64 by bv_omega,
      show ((a + 400#64) + 48#64) + 16#64 = (a + 400#64) + 64#64 by bv_omega] at h2
  rw [show ((a + 400#64) + 72#64) + 8#64 = (a + 400#64) + 80#64 by bv_omega,
      show ((a + 400#64) + 72#64) + 16#64 = (a + 400#64) + 88#64 by bv_omega] at h3
  have hlhs :
      polyEncoderAt A a outSt.sending_hdr ∗
      (authInlineWordsAt g (a + 400#64) auth ∗
       ((a + 400#64 + 48#64) ↦₆₄ 1152#64) ∗ ((a + 400#64 + 56#64) ↦₆₄ ek_ptr) ∗ ((a + 400#64 + 64#64) ↦₆₄ 1152#64) ∗
       ((a + 400#64 + 72#64) ↦₆₄ 2400#64) ∗ ((a + 400#64 + 80#64) ↦₆₄ dk_ptr) ∗ ((a + 400#64 + 88#64) ↦₆₄ 2400#64) ∗
       ((a + 400#64 + 96#64) ↦₆₄ epoch)) ∗
      authHeapBufs A g auth ∗
      RustHeap.vecU8Buf A 1152#64 ek_ptr ek ∗
      RustHeap.vecU8Buf A 2400#64 dk_ptr dk =
      polyEncoderAt A a outSt.sending_hdr ∗
      ((authInlineWordsAt g (a + 400#64) auth ∗ authHeapBufs A g auth) ∗
       (((a + 400#64 + 48#64) ↦₆₄ 1152#64) ∗ ((a + 400#64 + 56#64) ↦₆₄ ek_ptr) ∗
        ((a + 400#64 + 64#64) ↦₆₄ 1152#64) ∗ RustHeap.vecU8Buf A 1152#64 ek_ptr ek) ∗
       (((a + 400#64 + 72#64) ↦₆₄ 2400#64) ∗ ((a + 400#64 + 80#64) ↦₆₄ dk_ptr) ∗
        ((a + 400#64 + 88#64) ↦₆₄ 2400#64) ∗ RustHeap.vecU8Buf A 2400#64 dk_ptr dk) ∗
       ((a + 400#64 + 96#64) ↦₆₄ epoch)) := by ac_rfl
  rw [hlhs]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

theorem memRegion_4704_2400_split_nextChunk (sp : BitVec 64) :
    memRegion (sp + 4704#64) 2400 =
      memRegion (sp + 4704#64) 504 ∗
      memRegion (sp + 5208#64) 34 ∗
      memRegion (sp + 5242#64) 1862 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 504) (k := 1896) (b' := sp + 5208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5208#64) (n := 34) (k := 1862) (b' := sp + 5242#64) rfl (by bv_omega) (by decide)]

theorem encodeBytes_onPanic_of_ok {A : RustAlloc} (x : EncodeBytesGhost) {enc : PolyEncoder}
    (_h : encodeBytesResult x.msg = .ok enc) (s0 sf : State) :
    (encodeBytesSpecX A).onPanic x s0 sf =
      (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) := by
  dsimp only [encodeBytesSpecX, encodeBytesSpec]

theorem pointsToBytes_and_tail_entails_memRegion (ptr : BitVec 64) (bs : Bytes)
    (len cap : Nat) (hlen : bs.length = len) (hle : len ≤ cap) (hlt : cap < 2 ^ 64) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 len) (cap - len) ⊢
    memRegion ptr cap := by
  have h1 := pointsToBytes_entails_memRegion ptr bs
  rw [hlen] at h1
  rw [ProofLib.memRegion_split' (b := ptr) (n := len) (k := cap - len)
      (b' := ptr + BitVec.ofNat 64 len) (by omega) rfl (by omega)]
  exact sepConj_mono_left h1

end CryptoVerification.SpqrV1.Top.Send

