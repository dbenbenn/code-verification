/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import ProofLib.RegChain
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segPreKey` `PreKeySignalMessage` Construction (`+0x8c8..+0xa70`)

On the `Ok sm` return of `OTR::encrypt` at `+0x8c8` (`PreKeyEncryptRetState`), relocates the inner
`SignalMessage`, optional Kyber payload, base key, and local identity key, invokes
`PreKeySignalMessage::new` (`+0x98c`), and copies the 248-byte result to `sp + 0x370` to establish
`CmState` at `+0xa70`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Word and `memRegion` Decomposition Helpers -/

theorem words64At_append : ∀ (ws1 ws2 : List (BitVec 64)) (a : BitVec 64),
    words64At a (ws1 ++ ws2) =
      words64At a ws1 ∗ words64At (a + BitVec.ofNat 64 (8 * ws1.length)) ws2
  | [], ws2, a => by
    simp only [List.nil_append, words64At, List.length_nil, Nat.mul_zero,
      BitVec.add_zero, emp_sepConj]
  | w :: ws1, ws2, a => by
    simp only [List.cons_append, words64At, List.length_cons,
      words64At_append ws1 ws2 (a + 8#64), sepConj_assoc]
    have h : a + 8#64 + BitVec.ofNat 64 (8 * ws1.length) =
        a + BitVec.ofNat 64 (8 * (ws1.length + 1)) := by bv_omega
    rw [h]

theorem memRegion_24_exists_words3 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ w0 w1 w2 : BitVec 64, m ⊨ words64At a [w0, w1, w2] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := SegFrom.memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, hws⟩
  · nomatch hlen

theorem memRegion_32_exists_words4 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ w0 w1 w2 w3 : BitVec 64, m ⊨ words64At a [w0, w1, w2, w3] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := SegFrom.memRegion_exists_words64At 4 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w3, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, hws⟩
  · nomatch hlen

theorem memRegion_120_exists_words15 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 120 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 : BitVec 64,
      m ⊨ words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗ R := by
  rw [memRegion_split a 32 88 (by decide),
      memRegion_split (a + 32#64) 32 56 (by decide),
      memRegion_split (a + 32#64 + 32#64) 32 24 (by decide)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm
  obtain ⟨d0, d1, d2, d3, hm⟩ := memRegion_32_exists_words4 a hm
  have hm1 : m ⊨ memRegion (a + 32#64) 32 ∗
      (memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 24 ∗
        words64At a [d0, d1, d2, d3] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d4, d5, d6, d7, hm1⟩ := memRegion_32_exists_words4 (a + 32#64) hm1
  have hm2 : m ⊨ memRegion (a + 64#64) 32 ∗
      (memRegion (a + 96#64) 24 ∗
        words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm1
  obtain ⟨d8, d9, d10, d11, hm2⟩ := memRegion_32_exists_words4 (a + 64#64) hm2
  have hm3 : m ⊨ memRegion (a + 96#64) 24 ∗
      (words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗
        words64At (a + 64#64) [d8, d9, d10, d11] ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm2
  obtain ⟨d12, d13, d14, hm3⟩ := memRegion_24_exists_words3 (a + 96#64) hm3
  refine ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, ?_⟩
  have hcomb :
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] =
      words64At a [d0, d1, d2, d3] ∗ words64At (a + 32#64) [d4, d5, d6, d7] ∗
        words64At (a + 64#64) [d8, d9, d10, d11] ∗ words64At (a + 96#64) [d12, d13, d14] := by
    rw [show [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] =
        [d0, d1, d2, d3] ++ ([d4, d5, d6, d7] ++ ([d8, d9, d10, d11] ++ [d12, d13, d14])) from rfl,
      words64At_append, words64At_append, words64At_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd]
  rw [hcomb]
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm3

theorem memRegion_248_exists_words31 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 248 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14
      d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 : BitVec 64,
      m ⊨ words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
        d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] ∗ R := by
  rw [memRegion_split a 120 128 (by decide),
      memRegion_split (a + 120#64) 120 8 (by decide),
      ProofLib.memRegion_eight (a + 120#64 + 120#64)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨d30, hm⟩ := hm
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, hm⟩ :=
    memRegion_120_exists_words15 a hm
  have hm1 : m ⊨ memRegion (a + 120#64) 120 ∗
      (words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
        ((a + 240#64) ↦₆₄ d30) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
  obtain ⟨d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, hm1⟩ :=
    memRegion_120_exists_words15 (a + 120#64) hm1
  refine ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, ?_⟩
  have hcomb :
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
        d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] =
      words64At a [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ∗
        words64At (a + 120#64) [d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29] ∗
        ((a + 240#64) ↦₆₄ d30) := by
    rw [show [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
          d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30] =
        [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14] ++
          ([d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29] ++ [d30]) from rfl,
      words64At_append, words64At_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, words64At, sepConj_emp, sepConj_assoc]
  rw [hcomb]
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm1

/-! ## Representation Relocation Helpers -/

theorem pqCap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

theorem words64At_2 (a w0 w1 : BitVec 64) :
    words64At a [w0, w1] = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) := by
  simp only [words64At, sepConj_emp]

theorem words64At_3 (a w0 w1 w2 : BitVec 64) :
    words64At a [w0, w1, w2] = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes32_exists_words64At {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a [w0, w1, w2, w3] := by
  obtain ⟨w0, w1, w2, w3, _, heq⟩ := exists_unpack64_of_length_32 h
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [heq a]
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

@[expose] def otrRestAt (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A o pqCap pqPtr ot.pqrState ∗
    ((o + 0x18#64) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
    ((o + 0x38#64) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
    ((o + 0x78#64) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
    ((o + 0x98#64) ↦ₛ chainKeyBytes ot.senderChainKey) ∗
    ((o + 0xbc#64) ↦₃₂ ot.previousCounter) ∗
    memRegion (o + 0xc1#64) 7

theorem otrAt_eq_ik_ver_rest (A : RustAlloc) (sp pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) (ik0 ik1 ik2 ik3 : BitVec 64)
    (hik : ∀ a : BitVec 64,
      (a ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) = words64At a [ik0, ik1, ik2, ik3]) :
    otrAt A (sp + 0x288#64) pqCap pqPtr ot =
      words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
      ((sp + 0x348#64) ↦₈ ot.sessionVersion) ∗
      otrRestAt A (sp + 0x288#64) pqCap pqPtr ot := by
  unfold otrAt otrRestAt
  have h2e0 : sp + 0x288#64 + 0x58#64 = sp + 0x2e0#64 := by bv_omega
  have h348 : sp + 0x288#64 + 0xc0#64 = sp + 0x348#64 := by bv_omega
  rw [h2e0, h348, hik (sp + 0x2e0#64)]
  ac_rfl

theorem signalMessageWordsAt_eq_words64At (g : SignalMessageGhost) (m : SignalMessage)
    (a m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt g m a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [g.pqCap, g.pqPtr, BitVec.ofNat 64 m.pqRatchet.length,
        g.ctPtr, BitVec.ofNat 64 m.ciphertext.length,
        g.serPtr, BitVec.ofNat 64 m.serialized.length,
        m7, m8, m9, m10, m11, m12, m.previousCounter ++ m.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem signalMessageHeap_serialized_lt (A : RustAlloc) (g : SignalMessageGhost) (m : SignalMessage)
    (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14 ⊢
      ⌜m.serialized.length < 2 ^ 40⌝ ∗ signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14 := by
  unfold signalMessageHeap
  refine Entails.pure_left fun h => ?_
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

theorem signalMessageAt_relocate (A : RustAlloc) (g : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A g src sm ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      w0 + 1#64 ≠ 0#64 ∧
      sm.serialized.length < 2 ^ 40 ∧
      (m ⊨ words64At src [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗ H ⊢
          signalMessageAt A g dst sm) := by
  have hm1 := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A g src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨hpqCap, hm1⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨m7, m8, m9, m10, m11, m12, m14, hm1⟩
  have hm2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (signalMessageHeap_serialized_lt A g sm m7 m8 m9 m10 m11 m12 m14))) hm1
  have hm3 : m ⊨ ⌜sm.serialized.length < 2 ^ 40⌝ ∗
      (signalMessageWordsAt g sm src m7 m8 m9 m10 m11 m12 m14 ∗
        signalMessageHeap A g sm m7 m8 m9 m10 m11 m12 m14 ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm2
  rw [satisfies_pure_sepConj, signalMessageWordsAt_eq_words64At] at hm3
  rcases hm3 with ⟨hser, hm3⟩
  refine ⟨g.pqCap, g.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length,
    g.ctPtr, BitVec.ofNat 64 sm.ciphertext.length,
    g.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A g sm m7 m8 m9 m10 m11 m12 m14,
    pqCap_add_one_ne_zero hpqCap, hser, hm3, ?_⟩
  intro dst
  rw [← signalMessageWordsAt_eq_words64At]
  exact signalMessageAt_pack A g dst sm m7 m8 m9 m10 m11 m12 m14

theorem optKyberAt_relocate (A : RustAlloc) (src ptr : BitVec 64) (kp : Option KyberPayload)
    {m : Memory} {R : SepProp}
    (hm : m ⊨ optKyberAt A src ptr kp ∗ R) :
    ∃ (k0 k1 k2 : BitVec 64) (H : SepProp),
      (m ⊨ words64At src [k0, k1, k2] ∗ H ∗ R) ∧
      (∀ dst : BitVec 64, words64At dst [k0, k1, k2] ∗ H ⊢ optKyberAt A dst ptr kp) := by
  cases kp with
  | none =>
    dsimp only [optKyberAt] at hm
    rw [memRegion_split (src + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight (src + 8#64),
        ProofLib.memRegion_eight (src + 8#64 + 8#64)] at hm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm
    rcases hm with ⟨k2, k1, hm⟩
    refine ⟨0#64, k1, k2, emp, ?_, ?_⟩
    · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
        emp_sepConj]
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    · intro dst
      dsimp only [optKyberAt]
      rw [sepConj_emp]
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
      rw [memRegion_split (dst + 8#64) 8 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (sepConj_mono
        (pointsTo64_entails_memRegion (dst + 8#64) k1)
        (pointsTo64_entails_memRegion (dst + 16#64) k2))
  | some k =>
    dsimp only [optKyberAt] at hm
    rw [boxU8At_eq_header_sep_buf, ProofLib.memRegion_four (src + 0x14#64)] at hm
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      sepConj_assoc] at hm
    obtain ⟨hi, hm⟩ := hm
    have hpair : ∀ a : BitVec 64,
        ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((a + 0x14#64) ↦₃₂ hi) =
          ((a + 16#64) ↦₆₄ (hi ++ k.preKeyId)) := by
      intro a
      have hp := pointsTo32_pair (a + 16#64) k.preKeyId hi
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
    refine ⟨ptr, BitVec.ofNat 64 k.ciphertext.length, hi ++ k.preKeyId,
      Encrypt.boxU8Buf A ptr k.ciphertext, ?_, ?_⟩
    · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      rw [← hpair src]
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    · intro dst
      dsimp only [optKyberAt]
      rw [boxU8At_eq_header_sep_buf]
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      rw [← hpair dst]
      have hhi := pointsTo32_entails_memRegion (dst + 0x14#64) hi
      have hrearr :
          ((dst ↦₆₄ ptr) ∗ ((dst + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
            (((dst + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((dst + 0x14#64) ↦₃₂ hi)) ∗
            Encrypt.boxU8Buf A ptr k.ciphertext) =
          ((dst ↦₆₄ ptr) ∗ ((dst + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
            Encrypt.boxU8Buf A ptr k.ciphertext ∗
            ((dst + 0x10#64) ↦₃₂ k.preKeyId) ∗ ((dst + 0x14#64) ↦₃₂ hi)) := by
        ac_rfl
      rw [hrearr]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hhi)))

theorem optU32At_pack64 (b : BitVec 64) (opt : Option (BitVec 32)) (val : BitVec 32) :
    (⌜optU32ValProp opt val⌝ ∗ (b ↦₆₄ (val ++ (if opt.isSome then 1#32 else 0#32)))) ⊢
      optU32At b opt := by
  refine Entails.pure_left fun hval => ?_
  rw [← pointsTo32_pair]
  cases opt with
  | none =>
    unfold optU32At
    exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
  | some v =>
    unfold optU32At
    rw [hval v rfl]
    exact Entails.refl _

theorem preKeyMsgAt_relocate (A : RustAlloc) (g : PreKeyMsgGhost) (src : BitVec 64)
    (psm : PreKeySignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ preKeyMsgAt A g src psm ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
        w25 w26 w27 w28 w29 w30 : BitVec 64) (H : SepProp),
      w0 + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ∗ H ⊢
        preKeyMsgAt A g dst psm) := by
  obtain ⟨w21, w22, w23, w24, hbk⟩ :=
    bytes32_exists_words64At (bs := psm.baseKey.bytes.toList) (List.Vector.toList_length _)
  obtain ⟨w25, w26, w27, w28, hik⟩ :=
    bytes32_exists_words64At (bs := psm.identityKey.publicKey.bytes.toList) (List.Vector.toList_length _)
  unfold preKeyMsgAt at hm
  rw [sepConj_assoc] at hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    H_sm, hw0, _, hm, hpack_sm⟩ := signalMessageAt_relocate A g.msg src psm.message hm
  let W15 := [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
  let F_tail := boxU8At A (src + 0x80#64) g.serPtr psm.serialized ∗
    ((src + 0xa8#64) ↦ₛ psm.baseKey.bytes.toList) ∗
    ((src + 0xc8#64) ↦ₛ psm.identityKey.publicKey.bytes.toList) ∗
    ((src + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((src + 0xec#64) ↦₃₂ psm.signedPreKeyId)
  have hm_ky : m ⊨ optKyberAt A (src + 0x90#64) g.kyberPtr psm.kyberPayload ∗
      (words64At src W15 ∗ H_sm ∗ optU32At (src + 0x78#64) psm.preKeyId ∗ F_tail ∗
        ((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7 ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by dsimp only [W15, F_tail]; ac_rfl)) hm
  obtain ⟨w18, w19, w20, H_ky, hm_ky, hpack_ky⟩ :=
    optKyberAt_relocate A (src + 0x90#64) g.kyberPtr psm.kyberPayload hm_ky
  have hpk_unp := optU32At_unpack64 (src + 0x78#64) psm.preKeyId
  have hver_unp : ((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7 ⊢
      ∃∗ w30 : BitVec 64, ⌜versionPadProp psm.messageVersion w30⌝ ∗ ((src + 0xf0#64) ↦₆₄ w30) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using versionPad_unpack (src + 0xf0#64) psm.messageVersion
  have hm_sub : m ⊨ (optU32At (src + 0x78#64) psm.preKeyId ∗
      (((src + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (src + 0xf1#64) 7)) ∗
      (words64At src W15 ∗ words64At (src + 0x90#64) [w18, w19, w20] ∗ F_tail ∗ H_sm ∗ H_ky ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_ky
  have hm_sub' := Satisfies.mono (sepConj_mono_left (sepConj_mono hpk_unp hver_unp)) hm_sub
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc] at hm_sub'
  rcases hm_sub' with ⟨w30, pkVal, hm_sub'⟩
  have hm_pure : m ⊨ ⌜optU32ValProp psm.preKeyId pkVal⌝ ∗ ⌜versionPadProp psm.messageVersion w30⌝ ∗
      (((src + 0x78#64) ↦₆₄ (pkVal ++ (if psm.preKeyId.isSome then 1#32 else 0#32))) ∗
        ((src + 0xf0#64) ↦₆₄ w30) ∗ words64At src W15 ∗
        words64At (src + 0x90#64) [w18, w19, w20] ∗ F_tail ∗ H_sm ∗ H_ky ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_sub'
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hpkVal, hvp, hm_pure⟩
  let w15 := pkVal ++ (if psm.preKeyId.isSome then 1#32 else 0#32)
  let w16 := g.serPtr
  let w17 := BitVec.ofNat 64 psm.serialized.length
  let w29 := psm.signedPreKeyId ++ psm.registrationId
  have hpair29 : ∀ a : BitVec 64,
      ((a + 0xe8#64) ↦₃₂ psm.registrationId) ∗ ((a + 0xec#64) ↦₃₂ psm.signedPreKeyId) =
        ((a + 0xe8#64) ↦₆₄ w29) := fun a => by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, w29] using
      pointsTo32_pair (a + 0xe8#64) psm.registrationId psm.signedPreKeyId
  have hwords31 : ∀ a : BitVec 64,
      words64At a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] =
      words64At a W15 ∗ ((a + 0x78#64) ↦₆₄ w15) ∗ ((a + 0x80#64) ↦₆₄ w16) ∗ ((a + 0x88#64) ↦₆₄ w17) ∗
        words64At (a + 0x90#64) [w18, w19, w20] ∗ words64At (a + 0xa8#64) [w21, w22, w23, w24] ∗
        words64At (a + 0xc8#64) [w25, w26, w27, w28] ∗
        ((a + 0xe8#64) ↦₆₄ w29) ∗ ((a + 0xf0#64) ↦₆₄ w30) := by
    intro a
    rw [show [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] =
        W15 ++ ([w15, w16, w17] ++ ([w18, w19, w20] ++ ([w21, w22, w23, w24] ++
          ([w25, w26, w27, w28] ++ [w29, w30])))) from rfl,
      words64At_append, words64At_append, words64At_append, words64At_append, words64At_append]
    simp only [W15, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, words64At_3 (a + 120#64), words64At_2 (a + 232#64),
      sepConj_assoc]
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    H_sm ∗ Encrypt.boxU8Buf A g.serPtr psm.serialized ∗ H_ky, hw0, ?_, ?_⟩
  · dsimp only [F_tail] at hm_pure
    rw [boxU8At_eq_header_sep_buf, hbk (src + 0xa8#64), hik (src + 0xc8#64), hpair29 src] at hm_pure
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_pure
    rw [hwords31 src]
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_pure
  · intro dst
    unfold preKeyMsgAt
    rw [hwords31 dst, boxU8At_eq_header_sep_buf, hbk (dst + 0xa8#64), hik (dst + 0xc8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [← sepConj_assoc ((dst + 0xe8#64) ↦₃₂ psm.registrationId), hpair29 dst]
    have hpk_pack : ((dst + 0x78#64) ↦₆₄ w15) ⊢ optU32At (dst + 0x78#64) psm.preKeyId :=
      Entails.trans (Entails.pure_right hpkVal (Entails.refl _))
        (optU32At_pack64 (dst + 0x78#64) psm.preKeyId pkVal)
    have hver_pack : ((dst + 0xf0#64) ↦₆₄ w30) ⊢
        ((dst + 0xf0#64) ↦₈ psm.messageVersion) ∗ memRegion (dst + 0xf1#64) 7 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        Entails.trans (Entails.pure_right hvp (Entails.refl _))
          (versionPad_pack (dst + 0xf0#64) psm.messageVersion w30)
    refine Entails.trans (Entails.of_eq (show _ =
        (words64At dst W15 ∗ H_sm) ∗ ((dst + 0x78#64) ↦₆₄ w15) ∗
          (((dst + 0x80#64) ↦₆₄ w16) ∗ ((dst + 0x88#64) ↦₆₄ w17) ∗
            Encrypt.boxU8Buf A g.serPtr psm.serialized) ∗
          (words64At (dst + 0x90#64) [w18, w19, w20] ∗ H_ky) ∗
          words64At (dst + 0xa8#64) [w21, w22, w23, w24] ∗
          words64At (dst + 0xc8#64) [w25, w26, w27, w28] ∗
          ((dst + 0xe8#64) ↦₆₄ w29) ∗ ((dst + 0xf0#64) ↦₆₄ w30) by ac_rfl)) ?_
    exact sepConj_mono (hpack_sm dst)
      (sepConj_mono hpk_pack (sepConj_mono (Entails.refl _)
        (sepConj_mono (hpack_ky (dst + 0x90#64))
          (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
            (sepConj_mono_right hver_pack))))))

/-! ## Frame Unpack and Pack Helpers -/

@[expose] def buildPreKeyMsgScratchRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8#64) 0xc ∗ memRegion (sp + 0x18#64) 0xc ∗ memRegion (sp + 0x28#64) 0xc ∗
    ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
    ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

theorem preKeyEncryptScratch'_unpack (sp : BitVec 64) (regId spk pkVal : BitVec 32)
    {m : Memory} {R : SepProp} (hm : m ⊨ preKeyEncryptScratch' sp regId spk pkVal ∗ R) :
    ∃ u0 : BitVec 64,
      m ⊨ ((sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
        ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal)) ∗ buildPreKeyMsgScratchRest sp ∗ R := by
  dsimp only [preKeyEncryptScratch', buildPreKeyMsgScratchRest] at hm ⊢
  rw [memRegion_split sp 8 0xc (by decide), ProofLib.memRegion_eight sp] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨u0, hm⟩ := hm
  exact ⟨u0, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm⟩

theorem preKeyEncryptScratch'_to_cmScratch (sp u0 : BitVec 64) (regId spk pkVal : BitVec 32) :
    (sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
      ((sp + 0x24#64) ↦₃₂ spk) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp ⊢ cmScratch sp := by
  unfold buildPreKeyMsgScratchRest cmScratch
  have h38 : memRegion sp 0x38 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 0xc ∗ memRegion (sp + 0x14#64) 4 ∗
        memRegion (sp + 0x18#64) 0xc ∗ memRegion (sp + 0x24#64) 4 ∗
        memRegion (sp + 0x28#64) 0xc ∗ memRegion (sp + 0x34#64) 4 := by
    rw [memRegion_split sp 8 0x30 (by decide), mr_cut_add sp 8 0xc 0x24 (by decide),
        mr_cut_add sp 0x14 4 0x20 (by decide), mr_cut_add sp 0x18 0xc 0x14 (by decide),
        mr_cut_add sp 0x24 4 0x10 (by decide), mr_cut_add sp 0x28 0xc 4 (by decide)]
  rw [h38]
  refine Entails.trans (Entails.of_eq (show _ =
      ((sp ↦₆₄ u0) ∗ memRegion (sp + 8#64) 0xc ∗ ((sp + 0x14#64) ↦₃₂ regId) ∗
        memRegion (sp + 0x18#64) 0xc ∗ ((sp + 0x24#64) ↦₃₂ spk) ∗
        memRegion (sp + 0x28#64) 0xc ∗ ((sp + 0x34#64) ↦₃₂ pkVal)) ∗
        ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono (pointsTo64_entails_memRegion sp u0)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x14#64) regId)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x24#64) spk)
              (sepConj_mono (Entails.refl _)
                (pointsTo32_entails_memRegion (sp + 0x34#64) pkVal)))))))
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x48#64) (sp + 0xc0#64)) (Entails.refl _))))

theorem words64At_entails_mr (a : BitVec 64) (ws : List (BitVec 64)) (n : Nat)
    (hn : 8 * ws.length = n) (hb : n ≤ 2 ^ 64) :
    words64At a ws ⊢ memRegion a n :=
  hn ▸ Pf.SegFrom.words64At_entails_memRegion ws a (hn.symm ▸ hb)

theorem bytes32_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) ⊢ memRegion a 32 := by
  obtain ⟨w0, w1, w2, w3, heq⟩ := bytes32_exists_words64At h
  rw [heq a]
  exact words64At_entails_mr a [w0, w1, w2, w3] 32 rfl (by decide)

theorem kyber_ciphertext_length_lt {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} (hr : RecordInScopeEnc r) (hcur : r.currentSession = some sess) :
    ∀ k, (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) = some k →
      k.ciphertext.length < 2 ^ 32 := by
  intro k hk
  rw [Option.map_eq_some_iff] at hk
  rcases hk with ⟨pk, hpk_some, rfl⟩
  exact (hr sess hcur).2.2.2 pk hpk_some

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
