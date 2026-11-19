/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.V1.ParamsEWith -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.TripleRatchet.Seeds.Model

/-!
# Session-model step, epoch, and wire-length lemmas for arbitrary SPQR models

Generalizes the reachable-state step lemmas (`SessRepr`, `SeedsLen32`, receiver-chain bounds, and
identity preservation across `messageEncrypt`, `TripleRatchet.decrypt`, and `tryDecryptFromRecord`),
epoch transition lemmas (`send_epochs_gen`, `recv_epochs_gen`), and wire-length bound
(`send_wire_len_gen`) from `spqrOffB` to an arbitrary `S : Spqr Bytes PQC`.
-/

public section

namespace CryptoVerification.E2E.V1

set_option autoImplicit false

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.Record CryptoVerification.E2E.Reach
open CryptoVerification.E2E.Epochs CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Seeds

attribute [local simp] exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet exec_liftE
  exec_bind exec_onRatchet

/-! ## Session-state step lemmas for arbitrary `Spqr` models -/

section Steps

variable {PQC : Type}

/-- `SessionState.messageEncrypt` preserves `SessRepr` for any SPQR model `S`. -/
theorem sessRepr_messageEncrypt_gen (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr Bytes PQC)
    (addresses : Option Bytes) (ptext : Bytes) (coins : PQC) (st st' : SessionState Bytes)
    (msg : SignalMessage) (hrep : SessRepr st)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
    SessRepr st' := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure] at h
        unfold OutgoingTripleRatchet.encrypt at h
        simp only [exec_bind, exec_get] at h
        cases hpan : S.sendPanics st.pqRatchetState coins
        case true => simp [hpan] at h
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
        rcases hs : S.send st.pqRatchetState coins with _ | ⟨pq', key, pm⟩
        · simp [hs] at h
        · simp only [hs] at h
          rcases hn : sc.chainKey.nextChainKey C.F with _ | next
          · simp [hn] at h
          · simp only [hn, exec_bind, exec_liftE, exec_set, exec_pure, Prod.mk.injEq,
              Except.ok.injEq] at h
            rcases h with ⟨_, rfl⟩
            refine ⟨hrep.1, ?_⟩
            intro sc' hsc'
            simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_some,
              Option.some.injEq] at hsc'
            subst hsc'
            exact hrep.2 sc hsc

/-- `SessionState.tryDecryptFromRecord` preserves `SessRepr` for any SPQR model `S`. -/
theorem sessRepr_tryDecryptFromRecord_gen (C : Crypto) (S : Spqr Bytes PQC)
    (expected : Option Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState Bytes) (pt : Bytes) (hrep : SessRepr st)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    SessRepr st' := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          unfold TripleRatchet.decrypt at hdec
          rw [exec_bind, exec_onRatchet] at hdec
          have hr0 : RatchetRepr
              ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ :=
            hrep
          have hr1 := ensureReceiverChain_ratchetRepr C m.senderRatchetKey coins _ hr0
          rcases he : Mut.exec (RatchetState.ensureReceiverChain C m.senderRatchetKey coins)
              ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ with
            ⟨e | ck, r1⟩
          · simp [he] at hdec
          · rw [he] at hdec hr1
            simp only [exec_bind, exec_onRatchet] at hdec
            have hr2 := consumeMessageKey_ratchetRepr C.F m.senderRatchetKey ck m.counter msgType r1 hr1
            rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType) r1 with
              ⟨e | mkg, r2⟩
            · simp [hc] at hdec
            · rw [hc] at hdec hr2
              simp only [exec_get] at hdec
              cases hpan : S.recvPanics st.pqRatchetState m.pqRatchet
              case true => simp [hpan] at hdec
              simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hdec
              rcases hspqr : S.recv st.pqRatchetState m.pqRatchet with ⟨_ | _⟩ | ⟨pq', key⟩
              · simp [hspqr] at hdec
              · simp [hspqr] at hdec
              · simp only [hspqr, exec_bind, exec_pure] at hdec
                split at hdec
                · simp at hdec
                · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F key).cipherKey
                      (mkg.generateKeys C.F key).iv m.ciphertext with _ | ptext'
                  · simp [haes] at hdec
                  · simp only [haes] at hdec
                    rcases hdec with ⟨_, rfl⟩
                    exact hr2

/-- `SessionState.messageEncrypt` preserves `SeedsLen32`, the receiver-chain bound, and party
identities, updating `pqRatchetState` and `msg.pqRatchet` via `S.send`. -/
theorem messageEncrypt_ok_props_gen (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr Bytes PQC)
    (addresses : Option Bytes) (ptext : Bytes) (coins : PQC) (st st' : SessionState Bytes)
    (msg : SignalMessage) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity ∧
      ∃ key pm, S.send st.pqRatchetState coins = some (st'.pqRatchetState, key, pm) ∧
        msg.pqRatchet = pm := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure] at h
        unfold OutgoingTripleRatchet.encrypt at h
        simp only [exec_bind, exec_get] at h
        cases hpan : S.sendPanics st.pqRatchetState coins
        case true => simp [hpan] at h
        simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
        rcases hs : S.send st.pqRatchetState coins with _ | ⟨pq', key, pm⟩
        · simp [hs] at h
        · simp only [hs] at h
          rcases hn : sc.chainKey.nextChainKey C.F with _ | next
          · simp [hn] at h
          · simp only [hn, exec_bind, exec_liftE, exec_set, exec_pure, Prod.mk.injEq,
              Except.ok.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp [OutgoingTripleRatchet.applyToSessionState, SeedsLen32] at hseeds ⊢
            exact ⟨hseeds, hlen, rfl⟩

/-- `TripleRatchet.decrypt` preserves the receiver-chain bound and updates `pqrState` via `S.recv`
on `m.pqRatchet`. -/
theorem tr_decrypt_ok_props_gen (C : Crypto) (S : Spqr Bytes PQC) (expected : Option Bytes)
    (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (t t' : TripleRatchet Bytes) (pt : Bytes)
    (hlen : t.ratchet.receiverChains.length ≤ maxReceiverChains)
    (h : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins) t = (.ok pt, t')) :
    t'.ratchet.receiverChains.length ≤ maxReceiverChains ∧
      ∃ key, S.recv t.pqrState m.pqRatchet = .ok (t'.pqrState, key) := by
  unfold TripleRatchet.decrypt at h
  rw [exec_bind, exec_onRatchet] at h
  have h1 := ensureReceiverChain_receiverChains_le C m.senderRatchetKey coins t.ratchet hlen
  rcases he : Mut.exec (RatchetState.ensureReceiverChain C m.senderRatchetKey coins) t.ratchet with
    ⟨e | ck, r1⟩
  · simp [he] at h
  · rw [he] at h h1
    simp only [exec_bind, exec_onRatchet] at h
    have h2 := consumeMessageKey_receiverChains_length C.F m.senderRatchetKey ck m.counter msgType r1
    rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F m.senderRatchetKey ck m.counter msgType) r1 with
      ⟨e | mkg, r2⟩
    · simp [hc] at h
    · rw [hc] at h h2
      simp only [exec_get] at h
      cases hpan : S.recvPanics t.pqrState m.pqRatchet
      case true => simp [hpan] at h
      simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
      rcases hspqr : S.recv t.pqrState m.pqRatchet with ⟨_ | _⟩ | ⟨pq', key⟩
      · simp [hspqr] at h
      · simp [hspqr] at h
      · simp only [hspqr, exec_bind, exec_pure] at h
        split at h
        · simp at h
        · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F key).cipherKey
              (mkg.generateKeys C.F key).iv m.ciphertext with _ | ptext
          · simp [haes] at h
          · simp only [haes] at h
            rcases h with ⟨_, rfl⟩
            exact ⟨h2.trans_le h1, key, rfl⟩

/-- `SessionState.tryDecryptFromRecord` preserves `SeedsLen32`, the receiver-chain bound, and party
identities, updating `pqRatchetState` via `S.recv` on `m.pqRatchet`. -/
theorem tryDecryptFromRecord_ok_props_gen (C : Crypto) (S : Spqr Bytes PQC)
    (expected : Option Bytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState Bytes) (pt : Bytes) (hseeds : SeedsLen32 st)
    (hlen : st.receiverChains.length ≤ maxReceiverChains)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    SeedsLen32 st' ∧ st'.receiverChains.length ≤ maxReceiverChains ∧
      st'.localIdentity = st.localIdentity ∧ st'.remoteIdentity = st.remoteIdentity ∧
      ∃ key, S.recv st.pqRatchetState m.pqRatchet = .ok (st'.pqRatchetState, key) := by
  have hseeds' : SeedsLen32 st' := by
    have := tryDecryptFromRecord_preserves C S expected m msgType coins st hseeds
    simpa [h] using this
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [exec_liftE, exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          obtain ⟨hlen', key, hk⟩ := tr_decrypt_ok_props_gen C S expected m msgType coins _ tr' pt' hlen hdec
          exact ⟨hseeds', hlen', rfl, rfl, key, hk⟩

end Steps

/-! ## Epoch and wire-length lemmas for arbitrary `Spqr` models and coin types -/

private theorem addrsE_length' (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidTryParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidTryParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidTryParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

/-! ## Specializations to `spqrOffB` -/

end CryptoVerification.E2E.V1
