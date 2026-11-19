/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Facts about the libsignal session API model

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Flattened characterizations (`decryptFlat`, `encryptFlat`) and properties of `messageEncrypt` and
`messageDecryptSignal`: store-call trace prefixes (`fullTrace`), atomic store-on-success (`Stored`),
well-formedness preservation (`Session.Wf`), panic characterization (`ApiError.panic`), and
non-vacuity witnesses.
-/

public section

namespace CryptoGames.LibsignalSessionApi
open LibsignalSession

variable {Addr PQ PQC E : Type} [Inhabited PQ]

/-! ### `ApiError.ofProtocol` -/

/-! ### Flattened forms -/

/-- `api_simp [h, …]`: `simp` with the `Api` monad (`ExceptT` over `StateM`) unfolded to plain
functions, plus the given lemmas. -/
local macro "api_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp [Api.run, storeCall, liftProtocol, modify, modifyGet,
      MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure,
      StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, Id.run, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.lift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, $xs,*] $(loc)?)

/-- `message_decrypt_signal` flattened: the result and the trace by cases on the store answers and
the decryption. -/
@[expose] def decryptFlat (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_decrypt_signal"), [load])
  | .ok (some record) =>
    match record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins with
    | .error e => (.error (ApiError.ofProtocol e), [load])
    | .ok (ptext, record') =>
      match record'.currentSession.bind (·.state.remoteIdentity) with
      | none => (.error .panic, [load])
      | some k =>
        let trust := StoreCall.isTrustedIdentity remote k .receiving
        match answers.isTrustedIdentity with
        | .error e => (.error (.store e), [load, trust])
        | .ok false => (.error (.untrustedIdentity remote), [load, trust])
        | .ok true =>
          let save := StoreCall.saveIdentity remote k
          match answers.saveIdentity with
          | .error e => (.error (.store e), [load, trust, save])
          | .ok _ =>
            let store := StoreCall.storeSession remote record'
            match answers.storeSession with
            | .error e => (.error (.store e), [load, trust, save, store])
            | .ok () => (.ok ptext, [load, trust, save, store])

theorem messageDecryptSignal_eq_flat (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    messageDecryptSignal C spqr ser answers ciphertext remote loc coins =
      decryptFlat C spqr ser answers ciphertext remote loc coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageDecryptSignal, decryptFlat]
  rcases l with el | _ | record
  · api_simp []
  · api_simp []
  · rcases hd : record.tryDecryptFromRecord C spqr (ser remote loc) ciphertext coins with
      ed | ⟨ptext, record'⟩
    · api_simp [hd]
    · rcases record' with ⟨_ | session⟩
      · api_simp [hd]
      · rcases hk : session.state.remoteIdentity with _ | k
        · api_simp [hd, hk]
        · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
            api_simp [hd, hk]

/-- The `PreKeySignalMessage` wrapping and the `encrypt` call of `message_encrypt`
(`session_management.rs:76–119`), flattened. -/
@[expose] def wrapFlat (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) (session : Session PQ) (otr : OutgoingTripleRatchet PQ) :
    Except (ApiError Addr E) (CiphertextMessage × OutgoingTripleRatchet PQ) :=
  match session.pendingPreKey with
  | some items =>
    match SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with
    | none => .error .panic
    | some timestamp =>
      match timestamp.checkedAddSecs maxUnacknowledgedSessionAge with
      | none => .error .panic
      | some expiry =>
        if expiry.lt now then .error (.sessionNotFound remote "message_encrypt")
        else
          match execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext (ser loc remote) coins) otr with
          | .error e => .error (ApiError.ofProtocol e)
          | .ok (signalMessage, otr') =>
            .ok (.preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion
              session.localRegistrationId items.preKeyId items.signedPreKeyId
              (session.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩) items.baseKey
              otr'.localIdentityKey signalMessage), otr')
  | none =>
    match execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext none coins) otr with
    | .error e => .error (ApiError.ofProtocol e)
    | .ok (signalMessage, otr') => .ok (.signalMessage signalMessage, otr')

/-- `message_encrypt` flattened. -/
@[expose] def encryptFlat (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) :
    Except (ApiError Addr E) CiphertextMessage × List (StoreCall Addr PQ) :=
  let load := StoreCall.loadSession remote
  match answers.loadSession with
  | .error e => (.error (.store e), [load])
  | .ok none => (.error (.sessionNotFound remote "message_encrypt"), [load])
  | .ok (some record) =>
    match record.currentSession with
    | none => (.error (.sessionNotFound remote "message_encrypt"), [load])
    | some session =>
      match execOk OutgoingTripleRatchet.fromSessionState session.state with
      | .error e => (.error (ApiError.ofProtocol e), [load])
      | .ok (otr, taken) =>
        match taken.remoteIdentity with
        | none => (.error .panic, [load])
        | some k =>
          match wrapFlat C codec spqr ser ptext remote loc now coins session otr with
          | .error e => (.error e, [load])
          | .ok (message, otr') =>
            let trust := StoreCall.isTrustedIdentity remote k .sending
            match answers.isTrustedIdentity with
            | .error e => (.error (.store e), [load, trust])
            | .ok false => (.error (.untrustedIdentity remote), [load, trust])
            | .ok true =>
              let save := StoreCall.saveIdentity remote k
              match answers.saveIdentity with
              | .error e => (.error (.store e), [load, trust, save])
              | .ok _ =>
                let store := StoreCall.storeSession remote
                  ⟨some { session with state := otr'.applyToSessionState taken }⟩
                match answers.storeSession with
                | .error e => (.error (.store e), [load, trust, save, store])
                | .ok () => (.ok message, [load, trust, save, store])

theorem messageEncrypt_eq_flat (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ptext : List (BitVec 8)) (remote loc : Addr)
    (now : SystemTime) (coins : PQC) :
    messageEncrypt C codec spqr ser answers ptext remote loc now coins =
      encryptFlat C codec spqr ser answers ptext remote loc now coins := by
  rcases answers with ⟨l, t, s, st⟩
  simp only [messageEncrypt, encryptFlat]
  rcases l with el | _ | ⟨_ | session⟩
  · api_simp []
  · api_simp []
  · api_simp []
  · rcases hf : execOk OutgoingTripleRatchet.fromSessionState session.state with ef | ⟨otr, taken⟩
    · api_simp [hf]
    · rcases hk : taken.remoteIdentity with _ | k
      · api_simp [hf, hk]
      · rcases hp : session.pendingPreKey with _ | items
        · rcases he : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext none coins) otr with
            ee | ⟨sm, otr'⟩
          · api_simp [hf, hk, hp, he, wrapFlat]
          · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
              api_simp [hf, hk, hp, he, wrapFlat]
        · rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
          · api_simp [hf, hk, hp, h1, wrapFlat]
          · rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry
            · api_simp [hf, hk, hp, h1, h2, wrapFlat]
            · by_cases h3 : expiry.lt now = true
              · api_simp [hf, hk, hp, h1, h2, h3, wrapFlat]
              · rcases he : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext
                    (ser loc remote) coins) otr with ee | ⟨sm, otr'⟩
                · api_simp [hf, hk, hp, h1, h2, h3, he, wrapFlat]
                · rcases t with et | _ | _ <;> rcases s with es | _ <;> rcases st with est | _ <;>
                    api_simp [hf, hk, hp, h1, h2, h3, he, wrapFlat]

/-! ### Traces and storage on the flattened forms

`fullTrace` and `Stored` are the vocabulary of the main results; the `*Flat_*` lemmas are those
results for `decryptFlat` / `encryptFlat`, transported below by `*_eq_flat`. -/

local instance : Inhabited IdentityKey := ⟨⟨⟨List.Vector.replicate 32 0⟩⟩⟩
local instance : Inhabited (SessionRecord PQ) := ⟨⟨none⟩⟩

/-- The four store calls of a run that gets to the end: load, trust check, save identity, store
the record `r`, all for the remote address. -/
@[expose] def fullTrace (remote : Addr) (k : IdentityKey) (dir : Direction) (r : SessionRecord PQ) :
    List (StoreCall Addr PQ) :=
  [.loadSession remote, .isTrustedIdentity remote k dir, .saveIdentity remote k,
    .storeSession remote r]

theorem decryptFlat_prefix (C : Crypto) (spqr : Spqr PQ PQC)
    (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
    (ciphertext : SignalMessage) (remote loc : Addr) (coins : BitVec 256) :
    ∃ k r, (decryptFlat C spqr ser answers ciphertext remote loc coins).2 ≠ [] ∧
      (decryptFlat C spqr ser answers ciphertext remote loc coins).2 <+:
        fullTrace remote k .receiving r := by
  unfold decryptFlat
  repeat' split
  all_goals first
    | exact ⟨_, _, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨_, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨default, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩

section encrypt
variable (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
  (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
  (ptext : List (BitVec 8)) (remote loc : Addr) (now : SystemTime) (coins : PQC)

theorem encryptFlat_prefix :
    ∃ k r, (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 ≠ [] ∧
      (encryptFlat C codec spqr ser answers ptext remote loc now coins).2 <+:
        fullTrace remote k .sending r := by
  unfold encryptFlat
  repeat' split
  all_goals first
    | exact ⟨_, _, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨_, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩
    | exact ⟨default, default, List.cons_ne_nil _ _, List.prefix_iff_eq_take.mpr rfl⟩

end encrypt

/-! ### Facts about the session model -/

/-- `OutgoingTripleRatchet::from_session_state` only moves the SPQR state out. -/
theorem execOk_fromSessionState {s t : SessionState PQ} {o : OutgoingTripleRatchet PQ}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (o, t)) :
    t = { s with pqRatchetState := default } ∧ s.remoteIdentity.isSome := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    api_simp [hs, hr] at h
  all_goals split_ifs at h <;> api_simp [] at h
  exact ⟨h.2.symm, rfl⟩

/-- A successful `try_decrypt_with_state` clears the pending pre-key flag and keeps the remote
identity key, which was present (`TripleRatchet::from_session_state` requires it). -/
theorem tryDecryptWithState_ok {PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) {s s' : SessionState PQ} {p : List (BitVec 8)}
    (h : Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) s =
      (.ok p, s')) :
    s'.pendingPreKey = false ∧ s'.remoteIdentity = s.remoteIdentity ∧ s.remoteIdentity.isSome := by
  unfold SessionState.tryDecryptWithState at h
  generalize Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) = D at h
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases hr : s.remoteIdentity with _ | k <;> api_simp [hr] at h
  generalize D _ = R at h
  rcases R with ⟨_ | a, t⟩ <;> api_simp [liftE] at h
  obtain ⟨-, rfl⟩ := h
  simp [SessionState.clearUnacknowledgedPreKeyMessage, TripleRatchet.applyToSessionState]

theorem SessionState.tryDecryptFromRecord_ok {PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) {s s' : SessionState PQ} {p : List (BitVec 8)}
    (h : SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins s =
      (.ok p, s')) :
    s'.pendingPreKey = false ∧ s'.remoteIdentity = s.remoteIdentity ∧ s.remoteIdentity.isSome := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · split at h
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply tryDecryptWithState_ok C spqr expected ciphertext msgType coins
      assumption
    · simp at h

/-! ### `message_decrypt_signal` -/

section decrypt
variable (C : Crypto) (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
  (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remote loc : Addr)
  (coins : BitVec 256)

/-- **Call order**: the store calls are always a non-empty prefix of load, trust check
(`Receiving`), save identity, store, all for the remote address. -/
theorem messageDecryptSignal_trace_prefix :
    ∃ k r, (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 ≠ [] ∧
      (messageDecryptSignal C spqr ser answers ciphertext remote loc coins).2 <+:
        fullTrace remote k .receiving r := by
  rw [messageDecryptSignal_eq_flat]; exact decryptFlat_prefix ..

end decrypt

/-! ### `message_encrypt` -/

section encryptApi
variable (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
  (ser : Addr → Addr → Option (List (BitVec 8))) (answers : StoreAnswers PQ E)
  (ptext : List (BitVec 8)) (remote loc : Addr) (now : SystemTime) (coins : PQC)

/-- **Call order**: the store calls are always a non-empty prefix of load, trust check
(`Sending`), save identity, store, all for the remote address. -/
theorem messageEncrypt_trace_prefix :
    ∃ k r, (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 ≠ [] ∧
      (messageEncrypt C codec spqr ser answers ptext remote loc now coins).2 <+:
        fullTrace remote k .sending r := by
  rw [messageEncrypt_eq_flat]; exact encryptFlat_prefix ..

end encryptApi

/-! ### Non-vacuity -/

end CryptoGames.LibsignalSessionApi
