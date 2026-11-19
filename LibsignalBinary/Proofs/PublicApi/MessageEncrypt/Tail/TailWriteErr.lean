/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem resStaged_of_speStaged {A : RustAlloc} {ret : BitVec 64} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {jws : List (BitVec 64)} {H : SepProp}
    (hst : SpeStaged A ret e [w0, w1, w2, w3, w4, w5] H) (hjws : jws.length = 24) :
    ResStaged A ret (.error e) [errTag, w0, w1, w2] (unpack64List (w3 :: w4 :: w5 :: jws)) H := by
  rcases hst with ⟨hne, _, hent⟩
  refine ⟨fun h => hne (Except.error.inj h), rfl, ?_, ?_⟩
  · simp [hjws]
  · rw [apiEncResultAt_error, ← words64At_eq_pointsToBytes (ret + 0x20#64)]
    have hsplit :
        words64At ret [errTag, w0, w1, w2] ∗
          words64At (ret + 0x20#64) (w3 :: w4 :: w5 :: jws) ∗ H =
        (ret ↦₆₄ errTag) ∗
          (words64At (ret + 8#64) [w0, w1, w2, w3, w4, w5] ∗ H) ∗
          words64At (ret + 56#64) jws := by
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl
    rw [hsplit]
    have hj_mem : words64At (ret + 56#64) jws ⊢ memRegion (ret + 56#64) 192 := by
      have h192 : (192 : Nat) = 8 * jws.length := by omega
      rw [h192]
      exact words64At_entails_memRegion (ret + 56#64) jws (by omega)
    exact sepConj_mono_right (sepConj_mono hent hj_mem)

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
