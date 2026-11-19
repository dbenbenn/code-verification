/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOk
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEnc
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 4): `h45_SegExitVT_trap` and `SegSignal` (`h45_segSignal_okVT_trap`) on `trTrapProgAt`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

section SegSignal

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem h45_pqCap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem h45_segSignal_list_len3 {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

private theorem h45_signalMessageWordsAt_eq_words64At (gm : SignalMessageGhost) (sm : SignalMessage)
    (a : BitVec 64) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt gm sm a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [gm.pqCap, gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
        BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
        m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem h45_signalMessageAt_relocate (A : RustAlloc) (gm : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A gm src sm ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) := by
  have hm' := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A gm src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨hpq, hm'⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨m7, m8, m9, m10, m11, m12, m14, hm'⟩ := hm'
  rw [h45_signalMessageWordsAt_eq_words64At, sepConj_assoc] at hm'
  refine ⟨gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
    BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A gm sm m7 m8 m9 m10 m11 m12 m14,
    h45_pqCap_add_one_ne_zero hpq, hm', ?_⟩
  intro dst
  rw [← h45_signalMessageWordsAt_eq_words64At]
  exact signalMessageAt_pack A gm dst sm m7 m8 m9 m10 m11 m12 m14

end SegSignal

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
