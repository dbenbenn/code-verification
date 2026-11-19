/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Pure Model, Panic Bridge, and Borrowed-Input Helpers for `segSignal_ok`

Pure `messageEncrypt` unfolding on the `pendingPreKey = none` error and RNG-draw paths,
`OTR::encrypt` panic bridge (`segSignal_panic_bridge`), and borrowed-input frame `sgEnv`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Pure Model and Panic Bridge -/

theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem execOk_of_exec_error {α : Type} {m : Mut (OutgoingTripleRatchet (List (BitVec 8))) α}
    {o : OutgoingTripleRatchet (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec m o).1 = .error e) : execOk m o = .error e := by
  unfold execOk
  rcases hm : Mut.exec m o with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

theorem execOk_of_exec_ok {α : Type} {m : Mut (OutgoingTripleRatchet (List (BitVec 8))) α}
    {o : OutgoingTripleRatchet (List (BitVec 8))} {a : α}
    (h : (Mut.exec m o).1 = .ok a) : execOk m o = .ok (a, (Mut.exec m o).2) := by
  unfold execOk
  rcases hm : Mut.exec m o with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

/-- With `sess.pendingPreKey = none` and `OTR::encrypt = .error p`, `messageEncrypt` returns
`.error (.ofProtocol p)` after `load_session`. -/
theorem segSignal_model_err {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {p : SignalProtocolError}
    (hcur : r.currentSession = some sess) (hnone : sess.pendingPreKey = none)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (henc : execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr
      = .error p) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol p), [.loadSession x.rem.val]) := by
  simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers, hcur, hfrom,
    hrem, hnone, henc]

theorem segSignal_sendState {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {c : IdentityChange}
    (hcur : r.currentSession = some sess) (hnone : sess.pendingPreKey = none)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) :
    x.sendState (okAnswers r c) = some otr.pqrState ∧
      x.draws S (okAnswers r c) = S.draws otr.pqrState x.rest := by
  constructor
  · simp [EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom, hrem, hnone]
  · simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom, hrem,
      hnone]

@[expose] def segSignalEncGhost (sp pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (x : WithStoresEncGhost) : OtrEncryptGhost :=
  ⟨sp + 0x580#64, sp + 0x288#64, pqCap, pqPtr, otr, x.ptA, x.ptext, 0#64, none, x.remA, x.rem,
    x.cur, x.rest⟩

theorem segSignalEncGhost_model (C : Crypto) (S : SpqrModel)
    (sp pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (x : WithStoresEncGhost) :
    (segSignalEncGhost sp pqCap pqPtr otr x).model C S uuidTryParse =
      Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr :=
  rfl

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
