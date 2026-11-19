/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.CodeLayout

/-!
# Model Equivalence for `spqr::recv` Panics After `consume_message_key`

Proves `model_of_recvPanics` and `tryDecrypt_onPanicTight_of_afterCmk`: once `fromSessionState`,
`ensureReceiverChain`, and `consumeMessageKey` succeed, `S.recvPanics` implies
`(x.model C S parse).1 = .error .panic`, so `tryDecryptSpec.onPanic` collapses to
`tryDecryptOnPanicTight`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.Model

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

/-- S5 `spqr.recv` panic branch: when `fromSessionState = (.ok tr, st1)`,
`ensureReceiverChain = (.ok ck, r1)`, `consumeMessageKey = (.ok mkg, r2)`, and
`S.recvPanics x.st.pqRatchetState x.msg.pqRatchet`, the model panics. -/
theorem model_of_recvPanics {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (hp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) :
    (x.model C S uuidTryParse).1 = .error .panic := by
  have hpq : tr.pqrState = x.st.pqRatchetState := (fromSessionState_ok_inv htr).2.2.1
  rw [model_unfold, htr]
  dsimp only
  unfold TripleRatchet.decrypt
  rw [exec_bind, onRatchet_eq, herc]
  dsimp only
  rw [exec_bind, onRatchet_eq]
  dsimp only
  rw [hcmk]
  dsimp only
  rw [exec_bind, exec_get]
  dsimp only [SpqrModel.spqr]
  simp only [hpq, hp, ↓reduceIte]
  rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
