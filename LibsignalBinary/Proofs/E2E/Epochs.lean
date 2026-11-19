/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
import LibsignalBinary.Proofs.E2E.Record.Support.Phi
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionSMProofDefs

/-!
# End-to-End Epoch Ghost Agreement and Wire Length Bound

**Checked by Lean.**

Connects the pure `SessionState` protocol model to `EpochGhost` and the `2^32`-byte wire length
filter `shortCiphertext`:
* `send_epochs_proof` / `recv_epochs_proof`: `EpochGhost.ofGhost` commutes with `EpochGhost.send`
  and `EpochGhost.recv`.
* `send_wire_len_proof`: ciphertexts emitted by `(spqrOffSessionParams C).send` for plaintexts of
  length `< 2^31` have byte length `< 2^32`.
-/

public section

namespace CryptoVerification.E2E.Epochs

open CryptoGames CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.HMAC CryptoGames.CBC CryptoGames.LibsignalAead
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E CryptoVerification.E2E.Record

/-! ## `Mut.exec` simp lemmas -/

@[local simp] theorem exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

@[local simp] theorem exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] theorem exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] theorem exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

@[local simp] theorem exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] theorem exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] theorem exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

@[local simp] theorem exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

@[local simp] theorem exec_map {σ α β : Type} (f : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (f <$> m) s =
      match Mut.exec m s with
      | (.ok a, s') => (.ok (f a), s')
      | (.error e, s') => (.error e, s') := by
  rw [map_eq_bind_pure_comp]
  simp only [exec_bind, Function.comp_apply, exec_pure]

@[local simp] theorem exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

/-! ## Receiver-chain ratchet-key preservation -/

theorem fromSessionState_outgoing_receiverChains {PQ : Type} [Inhabited PQ] (record : SessionState PQ) :
    (Mut.exec OutgoingTripleRatchet.fromSessionState record).2.receiverChains =
      record.receiverChains := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
  rcases hsc : record.senderChain with _ | sc
  · simp [hsc]
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet]
    split_ifs
    · rfl
    · rcases hrem : record.remoteIdentity with _ | remote <;> simp

theorem messageEncrypt_receiverChains {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (addresses : Option (List (BitVec 8))) (ptext : List (BitVec 8)) (coins : PQC)
    (record : SessionState PQ) :
    (SessionState.messageEncrypt C codec spqr addresses ptext coins record).2.receiverChains =
      record.receiverChains := by
  unfold SessionState.messageEncrypt
  have hf := fromSessionState_outgoing_receiverChains record
  rcases h1 : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨e | session, taken⟩
  · simp
  · rw [h1] at hf
    dsimp only
    rcases h2 : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext
        (record.encryptAddresses addresses) coins) session with ⟨e | message, session'⟩
    · simp
    · simpa [OutgoingTripleRatchet.applyToSessionState] using hf

theorem map_set_eq_self {α β : Type} (f : α → β) (l : List α) (idx : ℕ) {c c' : α}
    (hget : l[idx]? = some c) (hf : f c' = f c) :
    (l.set idx c').map f = l.map f := by
  induction l generalizing idx with
  | nil => simp at hget
  | cons a as ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, hf]
    | succ idx =>
      simp only [List.getElem?_cons_succ] at hget
      simp [List.set, ih idx hget]

theorem takeSkippedKey_map_senderRatchetKey (their : PublicKey) (counter : BitVec 32)
    (r : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.takeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · rcases h3 : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with _ | pos
      · simp [h1, h2, h3]
      · rcases h4 : c.messageKeys[pos]? with _ | key
        · simp [h1, h2, h3, h4]
        · simp only [h1, h2, h3, h4, exec_bind, exec_get, exec_set, exec_pure]
          apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
          rfl

theorem storeSkippedKey_map_senderRatchetKey (their : PublicKey) (key : MessageKeyGenerator)
    (r : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.storeSkippedKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
      rfl

theorem setReceiverChainKey_map_senderRatchetKey (their : PublicKey) (ck : ChainKey)
    (r : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.setReceiverChainKey
  rcases h1 : r.findReceiverChainIndex their with _ | chainIdx
  · simp [h1]
  · rcases h2 : r.receiverChains[chainIdx]? with _ | c
    · simp [h1, h2]
    · simp only [h1, h2, exec_bind, exec_get, exec_set]
      apply map_set_eq_self (·.senderRatchetKey) r.receiverChains chainIdx h2
      rfl

theorem advanceChain_map_senderRatchetKey (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) (fuel : ℕ) (ck : ChainKey) (r : RatchetState) :
    (Mut.exec (RatchetState.advanceChain F their counter fuel ck) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  induction fuel generalizing ck r with
  | zero => rfl
  | succ fuel ih =>
    unfold RatchetState.advanceChain
    split
    · rw [exec_bind]
      have h1 := storeSkippedKey_map_senderRatchetKey their (ck.messageKeys F) r
      rcases hs : Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) r with
        ⟨e | _, r1⟩
      · rw [hs] at h1
        exact h1
      · rw [hs] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck.nextChainKey F with _ | ck'
        · exact h1
        · exact (ih ck' r1).trans h1
    · rfl

theorem consumeMessageKey_map_senderRatchetKey (F : ShaCompress) (their : PublicKey)
    (ck : ChainKey) (counter : BitVec 32) (msgType : MessageType) (r : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r).2.receiverChains.map
      (·.senderRatchetKey) =
    r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte, exec_bind]
    have h1 := takeSkippedKey_map_senderRatchetKey their counter r
    rcases ht : Mut.exec (RatchetState.takeSkippedKey their counter) r with ⟨e | opt, r1⟩
    · rw [ht] at h1
      exact h1
    · rw [ht] at h1
      cases opt <;> simpa using h1
  · simp only [hlt, ↓reduceIte, exec_bind, exec_get]
    split
    · rfl
    · rw [exec_bind]
      have h1 := advanceChain_map_senderRatchetKey F their counter (counter - ck.index).toNat ck r
      rcases ha : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r
        with ⟨e | ck1, r1⟩
      · rw [ha] at h1
        exact h1
      · rw [ha] at h1
        simp only [exec_bind, exec_liftE]
        rcases hn : ck1.nextChainKey F with _ | ck2
        · exact h1
        · simp only [exec_pure]
          have h2 := setReceiverChainKey_map_senderRatchetKey their ck2 r1
          rcases hs : Mut.exec (RatchetState.setReceiverChainKey their ck2) r1 with ⟨e | _, r2⟩ <;>
            · rw [hs] at h2
              exact h2.trans h1

theorem dhRatchetStep_ok_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey)
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) =
      (r.receiverChains.map (·.senderRatchetKey) ++ [their]).drop
        ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey at h
  simp only [exec_bind, exec_get] at h
  rcases hsc : r.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_modifyGet, exec_liftE] at h
    rcases hrc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
      _ | ⟨newRootKey, receiverChainKey⟩
    · simp [hrc1] at h
    · simp only [hrc1, exec_modify, exec_pure] at h
      rcases hrc2 : rootCreateChain C newRootKey their (KeyPair.generate C coins).privateKey with
        _ | ⟨finalRootKey, senderChainKey⟩
      · simp [hrc2] at h
      · simp only [hrc2, Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨_, rfl⟩
        simp [RatchetState.evictReceiverChains, List.map_drop, List.map_append]

theorem ensureReceiverChain_ok_some_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey) (i : ℕ)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = some i)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) = r.receiverChains.map (·.senderRatchetKey) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  rcases hget : r.receiverChains[i]? with _ | c
  · simp [hget] at h
  · rcases hck : c.chainKey with _ | ck'
    · simp [hget, hck] at h
    · simp only [hget, hck, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl

theorem ensureReceiverChain_ok_none_map_senderRatchetKey (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r r1 : RatchetState) (ck : ChainKey)
    (hidx : r.receiverChains.findIdx? (·.senderRatchetKey == their) = none)
    (h : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    r1.receiverChains.map (·.senderRatchetKey) =
      (r.receiverChains.map (·.senderRatchetKey) ++ [their]).drop
        ((r.receiverChains.length + 1) - maxReceiverChains) := by
  unfold RatchetState.ensureReceiverChain RatchetState.findReceiverChainKey
    RatchetState.findReceiverChainIndex at h
  simp only [exec_bind, exec_get, hidx, exec_liftE] at h
  exact dhRatchetStep_ok_map_senderRatchetKey C their coins r r1 ck h

theorem tryDecryptFromRecord_ok_ratchet {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option Bytes) (msg : SignalMessage)
    (msgType : MessageType) (coins : BitVec 256) (st st' : SessionState PQ) (pt : Bytes)
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    ∃ ck r1 mkg r2,
      Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ =
        (.ok ck, r1) ∧
      Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType) r1 =
        (.ok mkg, r2) ∧
      st'.receiverChains = r2.receiverChains := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, hst'⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, exec_bind, exec_modifyGet, exec_get, exec_pure] at hd
        unfold TripleRatchet.decrypt at hd
        rw [exec_bind, exec_onRatchet] at hd
        rcases he : Mut.exec (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)
            ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ with
          ⟨e | ck, r1⟩
        · simp [he] at hd
        · simp only [he, exec_bind, exec_onRatchet] at hd
          rcases hc : Mut.exec (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck
              msg.counter msgType) r1 with ⟨e | mkg, r2⟩
          · simp [hc] at hd
          · simp only [hc, exec_get] at hd
            cases hpan : spqr.recvPanics st.pqRatchetState msg.pqRatchet
            case true => simp [hpan] at hd
            simp only [hpan, Bool.false_eq_true, ↓reduceIte] at hd
            rcases hspqr : spqr.recv st.pqRatchetState msg.pqRatchet with ⟨_ | _⟩ | ⟨newPqrState, pqrKey⟩
            · simp [hspqr] at hd
            · simp [hspqr] at hd
            · simp only [hspqr, exec_pure, exec_bind] at hd
              split_ifs at hd
              · simp at hd
              · rcases haes : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv msg.ciphertext with _ | pt'
                · simp [haes] at hd
                · have hupd : updated.receiverChains = r2.receiverChains := by
                    simpa [haes, TripleRatchet.applyToSessionState,
                      SessionState.clearUnacknowledgedPreKeyMessage] using
                      congrArg (fun x => x.2.receiverChains) hd.symm
                  refine ⟨ck, r1, mkg, r2, rfl, hc, ?_⟩
                  rw [← hst']
                  exact hupd

theorem findIdx?_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).findIdx? p = l.findIdx? (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.findIdx?_cons, ih]

theorem find?_zip_of_findIdx?_none {α β : Type} (p : α → Bool)
    (ks : List α) (es : List β) (hnone : ks.findIdx? p = none) :
    (ks.zip es).find? (fun x => p x.1) = none := by
  induction ks generalizing es with
  | nil => rfl
  | cons k ks ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [List.findIdx?_cons] at hnone
      cases hk : p k with
      | true => simp [hk] at hnone
      | false =>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hnone
        simp [List.zip_cons_cons, hk, ih es hnone]

theorem find?_zip_of_findIdx?_some {α : Type} (p : α → Bool)
    (ks : List α) (es : List ℕ) (i : ℕ)
    (hlen : ks.length = es.length)
    (hsome : ks.findIdx? p = some i) :
    ∃ k, (ks.zip es).find? (fun x => p x.1) = some (k, es.getD i 0) := by
  induction ks generalizing es i with
  | nil => simp at hsome
  | cons k ks ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.findIdx?_cons] at hsome
      cases hk : p k with
      | true =>
        simp only [hk, ↓reduceIte, Option.some.injEq] at hsome
        subst hsome
        exact ⟨k, by simp [List.zip_cons_cons, hk, List.getD]⟩
      | false =>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hsome
        rcases hsome with ⟨j, hj, rfl⟩
        rcases ih es j hlen hj with ⟨k', hk'⟩
        refine ⟨k', ?_⟩
        simpa [List.zip_cons_cons, List.find?_cons, hk, List.getD] using hk'

theorem zip_drop {α β : Type} (as : List α) (bs : List β) (k : ℕ) :
    (as.drop k).zip (bs.drop k) = (as.zip bs).drop k := by
  induction k generalizing as bs with
  | zero => rfl
  | succ k ih =>
    cases as with
    | nil => simp
    | cons a as =>
      cases bs with
      | nil => simp
      | cons b bs => simp [List.drop_succ_cons, List.zip_cons_cons, ih]

theorem zip_append_singleton {α β : Type} (as : List α) (bs : List β) (a : α) (b : β)
    (hlen : as.length = bs.length) :
    (as ++ [a]).zip (bs ++ [b]) = (as.zip bs) ++ [(a, b)] := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases bs with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp [List.zip_cons_cons, ih ys hlen]

/-! ## `send_epochs_proof` and `recv_epochs_proof` -/

/-! ## `send_wire_len_proof` -/

private theorem addrsE_length' (s r : Party) (a : List (BitVec 8))
    (h : serializedPartyAddresses uuidTryParse s r = some a) : a.length = 36 := by
  unfold serializedPartyAddresses at h
  cases hs : serviceIdParse uuidTryParse (utf8 (partyAddressName s)) <;>
    cases hr : serviceIdParse uuidTryParse (utf8 (partyAddressName r)) <;> simp_all [addrBytes]
  subst h
  simp

end CryptoVerification.E2E.Epochs
