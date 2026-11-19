/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict

/-!
# `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (`0x29b30`) — Success Path

Proves the Segment 4 `.ok` branch (`0x2a3a8 .. 0x2a4a4` → `0x2a034`) when
`SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg`, and combines it with
`post_seg4_err_wp` into `post_seg4_after_signal_wp`.
-/

public section

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm]
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48
  bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_80 bv_add_neg_87
  bv_add_neg_88 bv_add_neg_96 bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136
  bv_add_neg_152 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186
  bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216
  bv_add_neg_512
  bv_sub_add_lit' bv_sub_sub_lit
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

/-! ## Cleanup Tail `0x2a4a0 .. 0x2a4a4` (`+2416 .. +2420` → `+1284`) -/

theorem msgHeapAt_pqCap_lt (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (addrW0 addrW1 : BitVec 64) :
    msgHeapAt A g m addrW0 addrW1 ⊢
      ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗ msgHeapAt A g m addrW0 addrW1 := by
  unfold msgHeapAt vecU8Heap
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hbnd => ?_
  refine Entails.pure_left fun ⟨hlen, hlt, hptr⟩ => ?_
  rw [pure_true_emp hlt, emp_sepConj,
    pure_true_emp hbnd, emp_sepConj,
    pure_true_emp ⟨hlen, hlt, hptr⟩, emp_sepConj]
  exact Entails.refl _

theorem memRegion120_words15 (r : BitVec 64) :
    memRegion r 120 =
      (∃∗ s0 : BitVec 64, r ↦₆₄ s0) ∗
      (∃∗ s1 : BitVec 64, (r + 8#64) ↦₆₄ s1) ∗
      (∃∗ s2 : BitVec 64, (r + 16#64) ↦₆₄ s2) ∗
      (∃∗ s3 : BitVec 64, (r + 24#64) ↦₆₄ s3) ∗
      (∃∗ s4 : BitVec 64, (r + 32#64) ↦₆₄ s4) ∗
      (∃∗ s5 : BitVec 64, (r + 40#64) ↦₆₄ s5) ∗
      (∃∗ s6 : BitVec 64, (r + 48#64) ↦₆₄ s6) ∗
      (∃∗ s7 : BitVec 64, (r + 56#64) ↦₆₄ s7) ∗
      (∃∗ s8 : BitVec 64, (r + 64#64) ↦₆₄ s8) ∗
      (∃∗ s9 : BitVec 64, (r + 72#64) ↦₆₄ s9) ∗
      (∃∗ s10 : BitVec 64, (r + 80#64) ↦₆₄ s10) ∗
      (∃∗ s11 : BitVec 64, (r + 88#64) ↦₆₄ s11) ∗
      (∃∗ s12 : BitVec 64, (r + 96#64) ↦₆₄ s12) ∗
      (∃∗ s13 : BitVec 64, (r + 104#64) ↦₆₄ s13) ∗
      (∃∗ s14 : BitVec 64, (r + 112#64) ↦₆₄ s14) := by
  rw [show (120 : Nat) = 48 + (48 + (8 + (8 + 8))) by decide,
    memRegion_split r 48 72 (by decide),
    memRegion_split (r + 48#64) 48 24 (by decide),
    memRegion_split (r + 48#64 + 48#64) 8 16 (by decide),
    memRegion_split (r + 48#64 + 48#64 + 8#64) 8 8 (by decide),
    memRegion48_words6 r,
    memRegion48_words6 (r + 48#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64 + 8#64),
    ProofLib.memRegion_eight (r + 48#64 + 48#64 + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion48_mid_eq (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ p0 : BitVec 32, a ↦₃₂ p0) ∗
      (∃∗ p1 : BitVec 32, (a + 4#64) ↦₃₂ p1) ∗
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
      (∃∗ w32 : BitVec 64, (a + 32#64) ↦₆₄ w32) ∗
      (∃∗ k40 : BitVec 32, (a + 40#64) ↦₃₂ k40) ∗
      memRegion (a + 44#64) 4 := by
  rw [show (48 : Nat) = 4 + (4 + (32 + (4 + 4))) by decide,
    memRegion_split a 4 44 (by decide),
    memRegion_split (a + 4#64) 4 40 (by decide),
    memRegion_split (a + 4#64 + 4#64) 32 8 (by decide),
    memRegion_split (a + 4#64 + 4#64 + 32#64) 4 4 (by decide),
    ProofLib.memRegion_four a, ProofLib.memRegion_four (a + 4#64),
    memRegion32_words4 (a + 4#64 + 4#64),
    ProofLib.memRegion_four (a + 4#64 + 4#64 + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion48_tail_eq (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w8 : BitVec 64, (a + 8#64) ↦₆₄ w8) ∗
      (∃∗ w16 : BitVec 64, (a + 16#64) ↦₆₄ w16) ∗
      (∃∗ w24 : BitVec 64, (a + 24#64) ↦₆₄ w24) ∗
      (∃∗ u32 : BitVec 32, (a + 32#64) ↦₃₂ u32) ∗
      (∃∗ u36 : BitVec 32, (a + 36#64) ↦₃₂ u36) ∗
      (∃∗ b40 : BitVec 8, (a + 40#64) ↦₈ b40) ∗
      memRegion (a + 41#64) 7 := by
  rw [show (48 : Nat) = 32 + (4 + (4 + (1 + 7))) by decide,
    memRegion_split a 32 16 (by decide),
    memRegion_split (a + 32#64) 4 12 (by decide),
    memRegion_split (a + 32#64 + 4#64) 4 8 (by decide),
    memRegion_split (a + 32#64 + 4#64 + 4#64) 1 7 (by decide),
    memRegion32_words4 a,
    ProofLib.memRegion_four (a + 32#64),
    ProofLib.memRegion_four (a + 32#64 + 4#64),
    ProofLib.memRegion_one (a + 32#64 + 4#64 + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion248_sret_split (r : BitVec 64) :
    memRegion r 248 =
      memRegion (r + 168#64) 32 ∗
      memRegion r 120 ∗
      memRegion (r + 120#64) 48 ∗
      memRegion (r + 200#64) 48 := by
  rw [show (248 : Nat) = 120 + (48 + (32 + 48)) by decide,
    memRegion_split r 120 128 (by decide),
    memRegion_split (r + 120#64) 48 80 (by decide),
    memRegion_split (r + 120#64 + 48#64) 32 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem memRegion112_words14 (a : BitVec 64) :
    memRegion a 112 =
      (∃∗ w1 : BitVec 64, a ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 8#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 16#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 24#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 32#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (a + 40#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (a + 48#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (a + 56#64) ↦₆₄ w8) ∗
      (∃∗ w9 : BitVec 64, (a + 64#64) ↦₆₄ w9) ∗
      (∃∗ w10 : BitVec 64, (a + 72#64) ↦₆₄ w10) ∗
      (∃∗ w11 : BitVec 64, (a + 80#64) ↦₆₄ w11) ∗
      (∃∗ w12 : BitVec 64, (a + 88#64) ↦₆₄ w12) ∗
      (∃∗ w13 : BitVec 64, (a + 96#64) ↦₆₄ w13) ∗
      (∃∗ w14 : BitVec 64, (a + 104#64) ↦₆₄ w14) := by
  rw [show (112 : Nat) = 48 + (48 + (8 + 8)) by decide,
    memRegion_split a 48 64 (by decide),
    memRegion_split (a + 48#64) 48 16 (by decide),
    memRegion_split (a + 48#64 + 48#64) 8 8 (by decide),
    memRegion48_words6 a,
    memRegion48_words6 (a + 48#64),
    ProofLib.memRegion_eight (a + 48#64 + 48#64),
    ProofLib.memRegion_eight (a + 48#64 + 48#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words14_entails_memRegion112
    (a w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗
    ((a + 24#64) ↦₆₄ w4) ∗ ((a + 32#64) ↦₆₄ w5) ∗ ((a + 40#64) ↦₆₄ w6) ∗
    ((a + 48#64) ↦₆₄ w7) ∗ ((a + 56#64) ↦₆₄ w8) ∗ ((a + 64#64) ↦₆₄ w9) ∗
    ((a + 72#64) ↦₆₄ w10) ∗ ((a + 80#64) ↦₆₄ w11) ∗ ((a + 88#64) ↦₆₄ w12) ∗
    ((a + 96#64) ↦₆₄ w13) ∗ ((a + 104#64) ↦₆₄ w14) ⊢
      memRegion a 112 := by
  rw [memRegion112_words14 a]
  exact sepConj_mono (Entails.sepExists_intro w1)
    (sepConj_mono (Entails.sepExists_intro w2)
      (sepConj_mono (Entails.sepExists_intro w3)
        (sepConj_mono (Entails.sepExists_intro w4)
          (sepConj_mono (Entails.sepExists_intro w5)
            (sepConj_mono (Entails.sepExists_intro w6)
              (sepConj_mono (Entails.sepExists_intro w7)
                (sepConj_mono (Entails.sepExists_intro w8)
                  (sepConj_mono (Entails.sepExists_intro w9)
                    (sepConj_mono (Entails.sepExists_intro w10)
                      (sepConj_mono (Entails.sepExists_intro w11)
                        (sepConj_mono (Entails.sepExists_intro w12)
                          (sepConj_mono (Entails.sepExists_intro w13)
                            (Entails.sepExists_intro w14)))))))))))))

theorem sevenBytesHead_tail_assoc (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (R : SepProp) :
    (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗
      ((a + 6#64) ↦₈ b6) ∗ R =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
      ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ R := by
  have h := congrArg (· ∗ R) (sevenBytesHeadAt_eq_tailAt a b0 b1 b2 b3 b4 b5 b6)
  dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at h
  simpa only [sepConj_assoc] using h

theorem preKeyResultAt_ok_intro (A : RustAlloc) (x : PreKeyTryFromArgs)
    (innerMsg : SignalMessage)
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (msgG : SignalMessageGhost) (serBoxPtr kyberBoxPtr : BitVec 64)
    (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
    (ik0 ik1 ik2 ik3 : BitVec 64)
    (opkVal : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3)) :
    (msgWords15At x.sret
      msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
      msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
      msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
      rk0 rk1 rk2 rk3 addrW0 addrW1
      (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
    (((x.sret + 120#64) ↦₃₂ opkTag x) ∗ ((x.sret + 124#64) ↦₃₂ opkVal)) ∗
    (((x.sret + 128#64) ↦₆₄ serBoxPtr) ∗
      ((x.sret + 136#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
      boxU8Buf A serBoxPtr x.bytes) ∗
    (((x.sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
      ((x.sret + 152#64) ↦₆₄ 1569#64) ∗
      boxU8Buf A kyberBoxPtr x.kyberBytes ∗
      ((x.sret + 160#64) ↦₃₂ x.kpkId) ∗
      memRegion (x.sret + 164#64) 4) ∗
    pkLayoutAt (x.sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
    (((x.sret + 200#64) ↦₆₄ ik0) ∗ ((x.sret + 208#64) ↦₆₄ ik1) ∗
      ((x.sret + 216#64) ↦₆₄ ik2) ∗ ((x.sret + 224#64) ↦₆₄ ik3)) ∗
    ((x.sret + 232#64) ↦₃₂ x.regId) ∗
    ((x.sret + 236#64) ↦₃₂ x.spkId) ∗
    ((x.sret + 240#64) ↦₈ 4#8) ∗
    memRegion (x.sret + 241#64) 7 ⊢
      preKeyResultAt A x.sret x := by
  unfold preKeyResultAt
  rw [hsig]
  refine Entails.trans ?_ (Entails.sepExists_intro ⟨msgG, serBoxPtr, kyberBoxPtr⟩)
  unfold preKeyMsgAt PreKeyTryFromArgs.toModel optKyberAt
  dsimp only
  have hmsg := signalMessageAt_pack A msgG x.sret innerMsg rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 hrk
  have hopk' := pointsTo32_pair_entails_optU32At (x.sret + 120#64) x opkVal hopk
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hopk'
  refine Entails.trans (sepConj_mono hmsg (sepConj_mono_left hopk')) ?_
  rw [boxU8At_eq_boxU8Buf A (x.sret + 0x80#64) serBoxPtr x.bytes,
      boxU8At_eq_boxU8Buf A (x.sret + 0x90#64) kyberBoxPtr x.kyberBytes,
      PreKeyTryFromArgs.kyberBytes_length,
      hpk, ← pkLayoutAt_eq_pointsToBytes (x.sret + 0xa8#64),
      hik (x.sret + 0xc8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-! ## `post_seg4_ok_pack_wp` (`+2236 .. +2420` → `+1284`) -/

theorem opkTag_mask64_truncate32 (x : PreKeyTryFromArgs) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (opkTag x) &&& 1#64) = opkTag x := by
  unfold opkTag
  cases x.opkId <;> simp

end CryptoVerification.E2E.Pqxdh.ResponderWire
