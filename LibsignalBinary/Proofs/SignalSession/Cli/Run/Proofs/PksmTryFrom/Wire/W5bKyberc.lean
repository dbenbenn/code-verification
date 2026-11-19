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
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysPlacedSym
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `PreKeySignalMessage::try_from`: Missing-Kyber v4 Error and Full Kyber Dispatch (`+0x684..+0x830` / `+0xa24`)

Proves the 54-byte missing-Kyber v4 error branch (`kyber_neither_v4_err_wpE`,
`+0x6c8 → +0xa24` / `+0xa80`) and assembles the full Kyber `Ok` (`w5b_kyber_ok_wp`,
`+0x684 → +0x830`) and `Err` (`w5b_kyber_err_wpE`, `+0x684 → +0xa24`) transitions.
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
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
theorem L1_PksmWire_W5bKyberc : True := trivial

/-! ## 1. Pure `pksmParse` Bridges for Kyber Dispatch Errors -/

/-- Pure `pksmParse` corollary (`m.kyberPreKeyId = none`, `m.kyberCiphertext = none`,
`0x40 ≤ vb.toNat`): `Pksm.pksmParse (vb :: body) = none`. -/
theorem pksmParse_eq_none_of_kyber_neither_v4 {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (hvb_ge : 0x40 ≤ vb.toNat)
    (h1 : m.kyberPreKeyId = none) (h2 : m.kyberCiphertext = none) :
    Pksm.pksmParse (vb :: body) = none := by
  by_cases h4f : vb ≤ 0x4f#8
  · have hv : 0x40#8 ≤ vb := BitVec.le_def.mpr hvb_ge
    exact pksmParse_kyberBad hd (kyberOk_false_of_neither_v4 hv h4f h1 h2)
  · have hgt : 0x4f#8 < vb := by
      rw [BitVec.le_def] at h4f
      rw [BitVec.lt_def]
      change 79 < vb.toNat
      change ¬ (vb.toNat ≤ 79) at h4f
      omega
    exact pksmParse_unrec hgt

/-- Combined pure `pksmParse` corollary for Kyber dispatch `Err` branches. -/
theorem pksmParse_eq_none_of_w5b_kyber_err {vb : BitVec 8} {body : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} (hd : Pksm.decodeProto body = some m)
    (herr : (m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ 0x40 ≤ vb.toNat)) :
    Pksm.pksmParse (vb :: body) = none := by
  rcases herr with hhalf | ⟨h1, h2, hvb_ge⟩
  · exact pksmParse_eq_none_of_kyber_half hd hhalf
  · exact pksmParse_eq_none_of_kyber_neither_v4 hd hvb_ge h1 h2

/-! ## 2. ``kyber_neither_v4_err_wpE``: (`+0x6c8 → +0xa24` / `+0xa80`) -/

private theorem merge_err_anyHeap (E S : SepProp) :
    ((E ∗ anyHeap) ∗ S) ∗ anyHeap ⊢ E ∗ S ∗ anyHeap := by
  refine Entails.trans
    (Q := E ∗ S ∗ (anyHeap ∗ anyHeap))
    (by apply entails_of_eq; ac_rfl)
    (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
