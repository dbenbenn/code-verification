/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI `SegFrom` Proof (`Cur` → `Otr`)

Proves `segFrom_okV` (`+0x20c..+0x2c8`), calling `OutgoingTripleRatchet::from_session_state` on
the current `SessionState` and branching to `Otr` (`+0x2c8`) on `Ok` or the error tail (`+0x49c`)
on `Err`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

private theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

private theorem fromSessionState_error_ne_invalidState
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    e ≠ .invalidState ∧ e ≠ .panic := by
  unfold Mut.exec OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq, Except.error.injEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.error.injEq] at h) <;>
    (subst h; decide)

private theorem execOk_fromSessionState_of_error
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    execOk OutgoingTripleRatchet.fromSessionState st = .error e := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem execOk_fromSessionState_of_ok
    {st : SessionState (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .ok otr) :
    execOk OutgoingTripleRatchet.fromSessionState st =
      .ok (otr, (Mut.exec OutgoingTripleRatchet.fromSessionState st).2) := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem model_of_fromSessionState_error
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp only [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, liftM, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, List.nil_append]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem list_len6 {α : Type} (ws : List α) (h : ws.length = 6) :
    ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
  rcases ws with _ | ⟨w0, ws⟩; · nomatch h
  rcases ws with _ | ⟨w1, ws⟩; · nomatch h
  rcases ws with _ | ⟨w2, ws⟩; · nomatch h
  rcases ws with _ | ⟨w3, ws⟩; · nomatch h
  rcases ws with _ | ⟨w4, ws⟩; · nomatch h
  rcases ws with _ | ⟨w5, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
  · nomatch h

private theorem memRegion_24_exists_words (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ w0 w1 w2 : BitVec 64,
      m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨w0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨w2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hws
    exact ⟨w0, w1, w2, Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hws⟩
  · nomatch hlen

private theorem words_entails_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ⊢ memRegion a 24 := by
  have h := words64At_entails_memRegion [w0, w1, w2] a
    (by simp only [List.length_cons, List.length_nil]; decide)
  simpa only [words64At, List.length_cons, List.length_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

private theorem memRegion_200_exists_otrWords25 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 200 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
        BitVec 64,
      m ⊨ otrWords25 a d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20
        d21 d22 d23 d24 ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 25 a (by decide) hm
  rcases ws with _ | ⟨d0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d3, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d4, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d5, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d6, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d7, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d8, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d9, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d10, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d11, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d12, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d13, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d14, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d15, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d16, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d17, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d18, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d19, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d20, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d21, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d22, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d23, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨d24, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · rw [← otrWords25_eq_words64At] at hws
    exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24, hws⟩
  · nomatch hlen

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
