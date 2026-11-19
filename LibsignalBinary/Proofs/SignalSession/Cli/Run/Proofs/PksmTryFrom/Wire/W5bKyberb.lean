/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyber -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `PreKeySignalMessage::try_from`: Kyber Error Allocation, Panic Tails, and Mismatched-Field Error

Proves `.rodata` error-string allocation helpers (`freshString_entails_pksmErrE`), OOM
panic tails (`+0xa74`, `+0xa80`), the Kyber buffer deallocation step (`+0xa1c → +0xa24`),
and the 68-byte mismatched-Kyber error branch (`kyber_half_err_wpE`, `+0x6c8 → +0xa24`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp
open CryptoVerification.SignalSession.Cli

private abbrev SepWPp := Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
private abbrev SepWPp.panic := @Wire.SepWPp.panic
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre

private theorem bv_sub_add_lit_k (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_lit_k (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
theorem L1_PksmWire_W5bKyberb : True := trivial

/-! ## 1. Callee Wrappers, ADRP Normalization, `.rodata` Helpers, & `freshString_entails_pksmErrE` -/

theorem stackAt_skipFieldStackX_ext (sp' : BitVec 64) :
    stackAt sp' (Prost.skipFieldStackX 100) =
      memRegion (sp' - BitVec.ofNat 64 (Prost.skipFieldStackX 100))
        (Prost.skipFieldStackX 100 - extHookStack) ∗ stackAt sp' extHookStack :=
  stackAt_sub_split sp' extHookStack (Prost.skipFieldStackX 100)

theorem ule_64_vb_eq_true {vb : BitVec 8} (hvb_ge : 0x40 ≤ vb.toNat) :
    (64#64).ule (vb.zeroExtend 64) = true := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_true (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

theorem freshBuf_entails_vecU8 (A : RustAlloc) (v ptr : BitVec 64) (n : Nat)
    (hn_pos : 0 < n) (hn_lt : n < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.live ptr n 1 ∗ memRegion ptr n ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A v bs := by
  rw [ProofLib.memRegion_eq_exists_bytes ptr n (by omega)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  refine Entails.trans
    (Q := ⌜bs.length = n⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 n) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.live ptr n 1 ∗ (ptr ↦ₛ bs)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Entails.pure_left fun hlen => ?_
  subst hlen
  refine Entails.sepExists_right bs ?_
  dsimp only [vecU8]
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) (Entails.sepExists_right ptr ?_)
  have hcap_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have := congrArg BitVec.toNat h0
    rw [hcap_nat, hz] at this
    omega
  dsimp only [vecU8At, vecHeader]
  simp only [hcap_ne, ↓reduceIte, hcap_nat, Nat.sub_self, memRegion_zero, sepConj_emp]
  rw [pure_true_emp ⟨Nat.le_refl _, hn_lt, hptr⟩, emp_sepConj]
  apply entails_of_eq; ac_rfl

/-- (`ErrAt.pksm0c_errCells_invalidMessage_preKey_words`): keeps the freshly allocated
`n`-byte `String` (`A.live ptr n 1 ∗ memRegion ptr n`) inside `speAt` as `vecU8 A (sret + 16) bs`,
absorbing only read-only `.rodata` frame `Pro` into `anyHeap`. -/
theorem freshString_entails_pksmErrE (A : RustAlloc) (sret ptr w5 w6 : BitVec 64) (n : Nat)
    (Pro : SepProp) (hn_pos : 0 < n) (hn_lt : n < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hw5 : w5.truncate 8 = 3#8) :
    (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
      ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ ((sret + 24#64) ↦₆₄ ptr) ∗
      ((sret + 32#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗
      memRegion (sret + 56#64) 192 ∗
      A.live ptr n 1 ∗ memRegion ptr n ∗ Pro ⊢
      pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap := by
  have hvec := freshBuf_entails_vecU8 A (sret + 16#64) ptr n hn_pos hn_lt hptr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
  refine Entails.trans
    (Q := (((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ ((sret + 24#64) ↦₆₄ ptr) ∗
        ((sret + 32#64) ↦₆₄ BitVec.ofNat 64 n) ∗ A.live ptr n 1 ∗ memRegion ptr n) ∗
      ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
        ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗ memRegion (sret + 56#64) 192) ∗
      Pro)
    (by apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono hvec (sepConj_mono_right (entails_anyHeap Pro))) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  refine Entails.trans
    (Q := ((sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗ vecU8 A (sret + 16#64) bs ∗
        ((sret + 40#64) ↦₆₄ w5) ∗ ((sret + 48#64) ↦₆₄ w6) ∗ memRegion (sret + 56#64) 192) ∗
      anyHeap)
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left (pksm0c_errCells_invalidMessage_preKey_words A [] sret w5 w6 bs hw5)

theorem bf_low8_eq_3 (w : BitVec 64) :
    (w &&& bv% (2 ^ 64 - 256) ||| 3#64).truncate 8 = 3#8 := by
  bv_bits

theorem memRegion68_unpack (p : BitVec 64) :
    memRegion p 68 ⊢
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (p + 48#64) ↦₆₄ w6) ∗ (∃∗ w7 : BitVec 64, (p + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 32, (p + 64#64) ↦₃₂ w8) := by
  rw [show (68 : Nat) = 48 + (8 + (8 + 4)) by decide,
    Prost.memRegion_split p 48 20 (by decide),
    Prost.memRegion_split (p + 48#64) 8 12 (by decide),
    Prost.memRegion_split (p + 48#64 + 8#64) 8 4 (by decide),
    memRegion48_words6 p,
    ProofLib.memRegion_eight (p + 48#64),
    ProofLib.memRegion_eight (p + 48#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (memRegion_four_entails (p + 64#64)))))))))

theorem memRegion68_pack (p w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (w8 : BitVec 32) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
      ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
      ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₃₂ w8) ⊢ memRegion p 68 := by
  rw [show (68 : Nat) = 48 + (8 + (8 + 4)) by decide,
    Prost.memRegion_split p 48 20 (by decide),
    Prost.memRegion_split (p + 48#64) 8 12 (by decide),
    Prost.memRegion_split (p + 48#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (Q := ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
        ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5)) ∗
      ((p + 48#64) ↦₆₄ w6) ∗ ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₃₂ w8))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono (words6_entails_memRegion48 p w0 w1 w2 w3 w4 w5)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 48#64) w6)
      (sepConj_mono (pointsTo64_entails_memRegion (p + 56#64) w7)
        (pointsTo32_entails_memRegion (p + 64#64) w8)))

theorem memRegion54_unpack (p : BitVec 64) :
    memRegion p 54 =
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      memRegion (p + 48#64) 6 := by
  rw [show (54 : Nat) = 48 + 6 by decide,
    Prost.memRegion_split p 48 6 (by decide),
    memRegion48_words6 p]
  simp only [sepConj_assoc]

theorem memRegion54_pack (p w0 w1 w2 w3 w4 w46 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
      ((p + 32#64) ↦₆₄ w4) ∗ memRegion (p + 40#64) 6 ∗ ((p + 46#64) ↦₆₄ w46) ⊢
      memRegion p 54 := by
  rw [show (54 : Nat) = 8 + (8 + (8 + (8 + (8 + (6 + 8))))) by decide,
    Prost.memRegion_split p 8 46 (by decide),
    Prost.memRegion_split (p + 8#64) 8 38 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64) 8 30 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64) 8 22 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64) 8 14 (by decide),
    Prost.memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 6 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion p w0)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 8#64) w1)
      (sepConj_mono (pointsTo64_entails_memRegion (p + 16#64) w2)
        (sepConj_mono (pointsTo64_entails_memRegion (p + 24#64) w3)
          (sepConj_mono (pointsTo64_entails_memRegion (p + 32#64) w4)
            (sepConj_mono_right (pointsTo64_entails_memRegion (p + 46#64) w46))))))

theorem shift_window_40_to_46 (p w40 : BitVec 64) :
    ((p + 40#64) ↦₆₄ w40) ∗ memRegion (p + 48#64) 6 ⊢
      memRegion (p + 40#64) 6 ∗ (∃∗ w46 : BitVec 64, (p + 46#64) ↦₆₄ w46) := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (p + 40#64) w40)) ?_
  have hsplit : memRegion (p + 40#64) 8 ∗ memRegion (p + 48#64) 6 =
      memRegion (p + 40#64) 6 ∗ (∃∗ w46 : BitVec 64, (p + 46#64) ↦₆₄ w46) := by
    rw [show p + 48#64 = p + 40#64 + BitVec.ofNat 64 8 by bv_omega,
      ← Prost.memRegion_split (p + 40#64) 8 6 (by decide),
      show (8 + 6 : Nat) = 6 + 8 by decide,
      Prost.memRegion_split (p + 40#64) 6 8 (by decide),
      ProofLib.memRegion_eight (p + 40#64 + BitVec.ofNat 64 6),
      show p + 40#64 + BitVec.ofNat 64 6 = p + 46#64 by bv_omega]
  exact entails_of_eq hsplit

theorem cap_sub1_add2_hi_of_pos_lt {cap : BitVec 64} (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (cap - bv% (2 ^ 64 - 1)).ult (cap - 1#64) = false := by
  rw [BitVec.ult_eq_decide]
  exact decide_eq_false (by bv_omega)

/-! ## 2. Panic Tails (`kyber_a74_panic_wp`, `kyber_a80_panic_wp`) & Dealloc (`kyber_a1c_to_a24_wp`) -/

theorem sepConj_rot3_kyber (P1 P2 P3 F : SepProp) :
    (P1 ∗ P2 ∗ P3) ∗ F = P3 ∗ P1 ∗ P2 ∗ F := by ac_rfl

/-- Pure `pksmParse` corollary (`(kpkOpt.isSome != kyberOpt.isSome) = true`):
when `Pksm.decodeProto body = some m` has mismatched `kyberPreKeyId` / `kyberCiphertext`
presence, `Pksm.pksmParse (vb :: body) = none`. -/
theorem pksmParse_eq_none_of_kyber_half {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (hhalf : (m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true) :
    Pksm.pksmParse (vb :: body) = none :=
  pksmParse_kyberBad hd (kyberOk_false_of_half (bne_iff_ne.mp hhalf))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
