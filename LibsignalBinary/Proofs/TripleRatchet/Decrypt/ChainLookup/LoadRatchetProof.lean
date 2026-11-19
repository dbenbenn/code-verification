/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym -- proof-setup: allow-public-import
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main

/-!
# Segment S1 (`LoadRatchet`) Proofs for `try_decrypt_with_state`

Verifies Segment S1 (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`), calling
`TripleRatchet::from_session_state` and either returning an error via the epilogue
(`missingRemoteIdentity`) or copying `TripleRatchet` (`264` B) into the stack frame to enter
`FindChainState`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem loadRatchet_err_stack_recombine (sp remA tag w0 w1 w2 w3 w4 : BitVec 64) :
    (memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x38#64) 0x158 ∗
     ((sp + 0x190#64) ↦₆₄ errTag) ∗
     ((sp + 0x198#64) ↦₆₄ tag) ∗
     words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x1c8#64) 208 ∗
     memRegion (sp + 0x298#64) 0x268 ∗
     ((sp + 0x500#64) ↦₆₄ tag) ∗
     words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion sp 1408 := by
  sep_interval

/-- All fields of `signalMessageAt A g a m` except the 32-bit `counter` at `a + 0x68`. -/

@[expose] def signalMessageNoCounterAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_eq_counter_rest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x68#64) ↦₃₂ m.counter) ∗ signalMessageNoCounterAt A g a m := by
  unfold signalMessageAt signalMessageNoCounterAt; sep_ac_rfl

theorem exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) ∧
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) := by
  obtain ⟨bs, H_tr, hlen, hm', hent⟩ := relocBytes_trBodyAt trG tr hpad p R m hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, by rwa [← hwords p], fun q => ?_⟩
  rw [← hwords q]
  exact hent q

theorem exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion p 256 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64,
      m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R := by
  rw [memRegion_eq_exists_bytes p 256 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    by rwa [← hwords p]⟩

namespace ChainLookupFacts

theorem elim_exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R)
    (k : ∀ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) →
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) → P) : P :=
  let ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, hm_w, hent_tr⟩ := exists_words32_of_trBodyAt hpad hm
  k w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr

theorem elim_exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨ memRegion p 256 ∗ R)
    (k : ∀ (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64),
      (m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R) → P) : P :=
  let ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hm'⟩ :=
    exists_words32_of_memRegion_256 hm
  k d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm'

end ChainLookupFacts

theorem loadRatchet_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R) :
    ∃ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗ memRegion (sp + 0x530#64) 0x50) ∗ R := by
  let F_rem := memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗
    memRegion (sp + 0x2ad#64) 0x253 ∗ memRegion (sp + 0x530#64) 0x50
  have hsplit :
      memRegion sp 0x30 ∗ memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 =
      (∃∗ t5 : BitVec 64, (sp + 0x528#64) ↦₆₄ t5) ∗
      (∃∗ t4 : BitVec 64, (sp + 0x520#64) ↦₆₄ t4) ∗
      (∃∗ t3 : BitVec 64, (sp + 0x518#64) ↦₆₄ t3) ∗
      (∃∗ t2 : BitVec 64, (sp + 0x510#64) ↦₆₄ t2) ∗
      (∃∗ t1 : BitVec 64, (sp + 0x508#64) ↦₆₄ t1) ∗
      (∃∗ t0 : BitVec 64, (sp + 0x500#64) ↦₆₄ t0) ∗
      (∃∗ g2ac : BitVec 8, (sp + 0x2ac#64) ↦₈ g2ac) ∗
      (∃∗ g2a0 : BitVec 64, (sp + 0x2a0#64) ↦₆₄ g2a0) ∗
      (∃∗ d_cap : BitVec 64, (sp + 0x38#64) ↦₆₄ d_cap) ∗
      (∃∗ g28 : BitVec 32, (sp + 0x28#64) ↦₃₂ g28) ∗
      (∃∗ g20 : BitVec 64, (sp + 0x20#64) ↦₆₄ g20) ∗
      memRegion (sp + 0x40#64) 256 ∗ F_rem := by
    dsimp only [F_rem]; sep_interval_eq
  rw [hsplit] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨g20, g28, d_cap, g2a0, g2ac, t0, t1, t2, t3, t4, t5, hm⟩
  have hm4 : m ⊨ memRegion (sp + 0x40#64) 256 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗ ((sp + 0x508#64) ↦₆₄ t1) ∗
       ((sp + 0x510#64) ↦₆₄ t2) ∗ ((sp + 0x518#64) ↦₆₄ t3) ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗ F_rem ∗ R) := by
    convert hm using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_memRegion_256 hm4
    fun d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm4 => ?_
  have h500 : words4At (sp + 0x500#64) t0 t1 t2 t3 =
      ((sp + 0x500#64) ↦₆₄ t0) ∗ ((sp + 0x508#64) ↦₆₄ t1) ∗
      ((sp + 0x510#64) ↦₆₄ t2) ∗ ((sp + 0x518#64) ↦₆₄ t3) := by
    sep_interval_eq
  refine ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, ?_⟩
  rw [h500]; dsimp only [F_rem] at hm4; convert hm4 using 1; sep_ac_rfl

namespace ChainLookupFacts

theorem elim_s1_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R)
    (k : ∀ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      (m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗
         ((sp + 0x28#64) ↦₃₂ g28) ∗
         ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
         ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
         ((sp + 0x520#64) ↦₆₄ t4) ∗
         ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗
         memRegion (sp + 0x2c#64) 4 ∗
         memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗
         memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗
         memRegion (sp + 0x530#64) 0x50) ∗ R) → P) : P :=
  let ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, hm_stk2⟩ := loadRatchet_ok_stack_extract hm
  k g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
    g28 g2ac hm_stk2

end ChainLookupFacts

theorem loadRatchet_ok_stack_recombine (sp cap remA : BitVec 64) (b2ac : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₆₄ cap) ∗
     words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
     memRegion (sp + 0x298#64) 8 ∗
     ((sp + 0x2a0#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x2a8#64) 4 ∗
     ((sp + 0x2ac#64) ↦₈ b2ac) ∗
     memRegion (sp + 0x2ad#64) 0x253 ∗
     words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
     ((sp + 0x520#64) ↦₆₄ w4) ∗
     ((sp + 0x528#64) ↦₆₄ w5) ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion (sp + 0x140#64) 0x440 := by
  sep_interval

private abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

theorem LoadRatchetStatePlaced.to_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetStatePlaced (blkPl_131).base A ctl x R s0 s) :
    LoadRatchetState_placed A ctl x R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1, h.2.1.2.2.2.2.1,
          h.2.1.2.2.2.2.2.1, h.2.1.2.2.2.2.2.2.1.1, h.2.1.2.2.2.2.2.2.2⟩,
    h.2.2⟩, h.2.1.2.2.2.2.2.2.1.2⟩

theorem FindChainStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainState_placed A ctl x trG tr st1 R s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    FindChainStatePlaced (blkPl_131).base A ctl x trG tr st1 R s0 s :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1, h.2.1.2.2.2.2.1,
         h.2.1.2.2.2.2.2.1, ⟨h.2.1.2.2.2.2.2.2.1, hro⟩, h.2.1.2.2.2.2.2.2.2⟩,
   h.2.2⟩

theorem loadRatchet_after_call_ok_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
      (fun s' => ∃ trG, FindChainState_placed A ctl x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨ trAt A (sp + 0x190#64) trG tr ∗
    (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
     memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A trG tr ∗
      (((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗ trBodyAt (sp + 0x198#64) trG tr ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 0x198#64) trG tr ∗
      (trHeapAt A trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 0x30 ∗ memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8) ∗
      (words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗ trHeapAt A trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 g28 g2ac hm_stk2 => ?_
  unfold tryDecryptCommonHeap at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗ trHeapAt A trG tr ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
    memRegion (sp + 0x530#64) 0x50 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢; convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_wp_placed (H := H)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    hcap hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx22 hx23 hx25
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨b2ac, hPf, hwpInv_f, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hcl_f hmf
  subst hPf
  refine ⟨trG, hpcf, hwpInv_f.to_midMeta_placed hcl_f, hx0_f, hx1_f, hx8_f,
    hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
    hx25_f, hx27_f, hx28_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [trAt_eq_cap_body_heap, show sp + 0x38#64 + 8#64 = sp + 0x40#64 by bv_omega,
      signalMessageAt_eq_counter_rest]
  have hmf_re : sf.mem ⊨
      (words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       memRegion (sp + 0x298#64) 8 ∗ ((sp + 0x2a0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x2a8#64) 4 ∗
       ((sp + 0x2ac#64) ↦₈ b2ac) ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       trHeapAt A trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R) := by
    dsimp only [F_ok, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_tr (sp + 0x40#64))
      (sepConj_mono_left
        (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
