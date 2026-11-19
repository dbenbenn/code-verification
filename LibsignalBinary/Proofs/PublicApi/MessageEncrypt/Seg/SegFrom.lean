/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromFetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

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

theorem fromSessionState_error_ne_invalidState_shared_lb
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

theorem execOk_fromSessionState_of_error_shared_lb
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    execOk OutgoingTripleRatchet.fromSessionState st = .error e := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

theorem execOk_fromSessionState_of_ok_shared_lb
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
    execOk_fromSessionState_of_error_shared_lb herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState_shared_lb herr).2
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

theorem pqCap_add_one_ne_zero_shared_lb {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

theorem otrAt_relocate (A : RustAlloc) (src : BitVec 64) (pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) {m : Memory} {R : SepProp}
    (hm : m ⊨ otrAt A src pqCap pqPtr ot ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
        BitVec 64) (H : SepProp),
      pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ otrWords25 src pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
        w19 w20 w21 w22 w23 w24 ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        otrWords25 dst pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
          w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pqCap pqPtr ot) := by
  obtain ⟨w3, w4, w5, w6, _, heq1⟩ :=
    exists_unpack64_of_length_32 (bs := ot.senderRatchetKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w7, w8, w9, w10, _, heq2⟩ :=
    exists_unpack64_of_length_32 (bs := ot.senderRatchetKey.privateKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w11, w12, w13, w14, _, heq3⟩ :=
    exists_unpack64_of_length_32 (bs := ot.localIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w15, w16, w17, w18, _, heq4⟩ :=
    exists_unpack64_of_length_32 (bs := ot.remoteIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨w19, w20, w21, w22, _, heq5⟩ :=
    exists_unpack64_of_length_32 (bs := keyToBytes32 ot.senderChainKey.key)
      (length_keyToBytes32 _)
  have hbody : ∀ o : BitVec 64,
      otrAt A o pqCap pqPtr ot =
        ((o ↦₆₄ pqCap) ∗ ((o + 0x08#64) ↦₆₄ pqPtr) ∗
          ((o + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
          ((o + 0x18#64) ↦₆₄ w3) ∗ ((o + 0x20#64) ↦₆₄ w4) ∗
          ((o + 0x28#64) ↦₆₄ w5) ∗ ((o + 0x30#64) ↦₆₄ w6) ∗
          ((o + 0x38#64) ↦₆₄ w7) ∗ ((o + 0x40#64) ↦₆₄ w8) ∗
          ((o + 0x48#64) ↦₆₄ w9) ∗ ((o + 0x50#64) ↦₆₄ w10) ∗
          ((o + 0x58#64) ↦₆₄ w11) ∗ ((o + 0x60#64) ↦₆₄ w12) ∗
          ((o + 0x68#64) ↦₆₄ w13) ∗ ((o + 0x70#64) ↦₆₄ w14) ∗
          ((o + 0x78#64) ↦₆₄ w15) ∗ ((o + 0x80#64) ↦₆₄ w16) ∗
          ((o + 0x88#64) ↦₆₄ w17) ∗ ((o + 0x90#64) ↦₆₄ w18) ∗
          ((o + 0x98#64) ↦₆₄ w19) ∗ ((o + 0xa0#64) ↦₆₄ w20) ∗
          ((o + 0xa8#64) ↦₆₄ w21) ∗ ((o + 0xb0#64) ↦₆₄ w22) ∗
          ((o + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index))) ∗
        (((o + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (o + 0xc1#64) 7) ∗
        vecU8Buf A pqCap pqPtr ot.pqrState := by
    intro o
    unfold otrAt
    rw [vecU8At_eq_header_sep_buf, vecHeader, chainKeyBytes_split,
        heq1 (o + 0x18#64), heq2 (o + 0x38#64), heq3 (o + 0x58#64),
        heq4 (o + 0x78#64), heq5 (o + 0x98#64)]
    have hpair :
        (((o + 0x98#64 + 32#64) ↦₃₂ ot.senderChainKey.index) ∗
          ((o + 0xbc#64) ↦₃₂ ot.previousCounter)) =
        ((o + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index)) := by
      have hp := pointsTo32_pair (o + 0xb8#64) ot.senderChainKey.index ot.previousCounter
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpair ⊢
    rw [← hpair]
    ac_rfl
  rw [hbody src] at hm
  have hv_unp :
      ((src + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (src + 0xc1#64) 7 ⊢
        ∃∗ w24 : BitVec 64, ⌜versionPadProp ot.sessionVersion w24⌝ ∗ ((src + 0xc0#64) ↦₆₄ w24) := by
    have hv := versionPad_unpack (src + 0xc0#64) ot.sessionVersion
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hv
  have hm' := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono (Entails.refl _)
        (sepConj_mono hv_unp (vecU8Buf_pqCap_lt A pqCap pqPtr ot.pqrState)))) hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm'
  obtain ⟨w24, hm'⟩ := hm'
  have hm_pure : m ⊨ ⌜versionPadProp ot.sessionVersion w24⌝ ∗ ⌜pqCap.toNat < 2 ^ 63⌝ ∗
      (otrWords25 src pqCap pqPtr (BitVec.ofNat 64 ot.pqrState.length)
        w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
        (ot.previousCounter ++ ot.senderChainKey.index) w24 ∗
      vecU8Buf A pqCap pqPtr ot.pqrState ∗ R) := by
    unfold otrWords25
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm'
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hvp, hpq, hm_out⟩
  refine ⟨pqPtr, BitVec.ofNat 64 ot.pqrState.length,
    w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, ot.previousCounter ++ ot.senderChainKey.index, w24,
    vecU8Buf A pqCap pqPtr ot.pqrState,
    pqCap_add_one_ne_zero_shared_lb hpq, hm_out, ?_⟩
  intro dst
  rw [hbody dst]
  have hv_pack : ((dst + 0xc0#64) ↦₆₄ w24) ⊢
      ((dst + 0xc0#64) ↦₈ ot.sessionVersion) ∗ memRegion (dst + 0xc1#64) 7 := by
    have hp := Entails.trans (Entails.pure_right hvp (Entails.refl _))
      (versionPad_pack (dst + 0xc0#64) ot.sessionVersion w24)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp
  unfold otrWords25
  rw [show ((dst ↦₆₄ pqCap) ∗ ((dst + 0x08#64) ↦₆₄ pqPtr) ∗
      ((dst + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      ((dst + 0x18#64) ↦₆₄ w3) ∗ ((dst + 0x20#64) ↦₆₄ w4) ∗
      ((dst + 0x28#64) ↦₆₄ w5) ∗ ((dst + 0x30#64) ↦₆₄ w6) ∗
      ((dst + 0x38#64) ↦₆₄ w7) ∗ ((dst + 0x40#64) ↦₆₄ w8) ∗
      ((dst + 0x48#64) ↦₆₄ w9) ∗ ((dst + 0x50#64) ↦₆₄ w10) ∗
      ((dst + 0x58#64) ↦₆₄ w11) ∗ ((dst + 0x60#64) ↦₆₄ w12) ∗
      ((dst + 0x68#64) ↦₆₄ w13) ∗ ((dst + 0x70#64) ↦₆₄ w14) ∗
      ((dst + 0x78#64) ↦₆₄ w15) ∗ ((dst + 0x80#64) ↦₆₄ w16) ∗
      ((dst + 0x88#64) ↦₆₄ w17) ∗ ((dst + 0x90#64) ↦₆₄ w18) ∗
      ((dst + 0x98#64) ↦₆₄ w19) ∗ ((dst + 0xa0#64) ↦₆₄ w20) ∗
      ((dst + 0xa8#64) ↦₆₄ w21) ∗ ((dst + 0xb0#64) ↦₆₄ w22) ∗
      ((dst + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index)) ∗
      ((dst + 0xc0#64) ↦₆₄ w24)) ∗ vecU8Buf A pqCap pqPtr ot.pqrState =
    ((dst ↦₆₄ pqCap) ∗ ((dst + 0x08#64) ↦₆₄ pqPtr) ∗
      ((dst + 0x10#64) ↦₆₄ BitVec.ofNat 64 ot.pqrState.length) ∗
      ((dst + 0x18#64) ↦₆₄ w3) ∗ ((dst + 0x20#64) ↦₆₄ w4) ∗
      ((dst + 0x28#64) ↦₆₄ w5) ∗ ((dst + 0x30#64) ↦₆₄ w6) ∗
      ((dst + 0x38#64) ↦₆₄ w7) ∗ ((dst + 0x40#64) ↦₆₄ w8) ∗
      ((dst + 0x48#64) ↦₆₄ w9) ∗ ((dst + 0x50#64) ↦₆₄ w10) ∗
      ((dst + 0x58#64) ↦₆₄ w11) ∗ ((dst + 0x60#64) ↦₆₄ w12) ∗
      ((dst + 0x68#64) ↦₆₄ w13) ∗ ((dst + 0x70#64) ↦₆₄ w14) ∗
      ((dst + 0x78#64) ↦₆₄ w15) ∗ ((dst + 0x80#64) ↦₆₄ w16) ∗
      ((dst + 0x88#64) ↦₆₄ w17) ∗ ((dst + 0x90#64) ↦₆₄ w18) ∗
      ((dst + 0x98#64) ↦₆₄ w19) ∗ ((dst + 0xa0#64) ↦₆₄ w20) ∗
      ((dst + 0xa8#64) ↦₆₄ w21) ∗ ((dst + 0xb0#64) ↦₆₄ w22) ∗
      ((dst + 0xb8#64) ↦₆₄ (ot.previousCounter ++ ot.senderChainKey.index))) ∗
      ((dst + 0xc0#64) ↦₆₄ w24) ∗ vecU8Buf A pqCap pqPtr ot.pqrState by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_left hv_pack)

@[expose] def sessionPure (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

theorem sessionRecordAt_cur_some (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess) {m : Memory} {R : SepProp}
    (hm : m ⊨ sessionRecordAt A (sp + 0x110#64) g r ∗ R) :
    ∃ G : SessionGhost,
      g.cur = some G ∧ sessionPure G sess ∧
      (m ⊨ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G sess.state ∗ R) := by
  unfold sessionRecordAt at hm
  rw [hcur] at hm
  cases hgc : g.cur with
  | none =>
    rw [hgc] at hm
    dsimp only at hm
    have hfalse : m ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    exact False.elim ((satisfies_pure_sepConj _ _ _).1 hfalse).1
  | some G =>
    rw [hgc] at hm
    dsimp only at hm
    unfold sessionStateReprAt at hm
    have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
    rw [heq] at hm
    have hpure : m ⊨ ⌜sessionPure G sess⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗ R) := by
      unfold sessionPure
      exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    rw [satisfies_pure_sepConj] at hpure
    exact ⟨G, rfl, hpure.1, hpure.2⟩

theorem sessionRecordAt_taken_fold (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (G G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hpure : sessionPure G sess) (hagr : G.AgreeExceptPq G') :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G' st' ⊢
      sessionRecordAt A (sp + 0x110#64) { g with cur := some G' } (takenRecord sess st') := by
  unfold sessionRecordAt takenRecord sessionStateReprAt
  dsimp only
  have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [heq]
  unfold SessionGhost.AgreeExceptPq at hagr
  have hpure' : sessionPure G' { sess with state := st' } := by
    rw [hagr]
    exact hpure
  exact sepConj_mono_right (Entails.pure_right hpure' (Entails.refl _))

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem words64At_entails_memRegion : ∀ (ws : List (BitVec 64)) (a : BitVec 64),
    8 * ws.length ≤ 2 ^ 64 →
    words64At a ws ⊢ memRegion a (8 * ws.length)
  | [], a, _ => by
    simp only [words64At, List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero]
    exact Entails.refl _
  | w :: ws, a, h => by
    simp only [words64At, List.length_cons] at h ⊢
    rw [show 8 * (ws.length + 1) = 8 + 8 * ws.length by omega,
        memRegion_split a 8 (8 * ws.length) (by omega)]
    exact sepConj_mono (pointsTo64_entails_memRegion a w)
      (words64At_entails_memRegion ws (a + 8#64) (by omega))

theorem memRegion_exists_words64At : ∀ (n : Nat) (a : BitVec 64) {m : Memory} {R : SepProp},
    8 * n ≤ 2 ^ 64 →
    (m ⊨ memRegion a (8 * n) ∗ R) →
    ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ R)
  | 0, a, m, R, _, hm => by
    rw [Nat.mul_zero, ProofLib.memRegion_zero, emp_sepConj] at hm
    exact ⟨[], rfl, by simpa [words64At] using hm⟩
  | n + 1, a, m, R, h, hm => by
    rw [show 8 * (n + 1) = 8 + 8 * n by omega,
        memRegion_split a 8 (8 * n) (by omega),
        ProofLib.memRegion_eight a] at hm
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
    obtain ⟨w, hm⟩ := hm
    have hm' : m ⊨ memRegion (a + 8#64) (8 * n) ∗ ((a ↦₆₄ w) ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At n (a + 8#64) (by omega) hm'
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    simp only [words64At]
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hws

theorem otrWords25_eq_words64At (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) :
    otrWords25 o w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
      w23 w24 =
    words64At o [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, w22, w23, w24] := by
  simp only [otrWords25, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem otrWords25_entails_memRegion (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) :
    otrWords25 o w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22
      w23 w24 ⊢ memRegion o 200 := by
  rw [otrWords25_eq_words64At]
  exact words64At_entails_memRegion
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
      w18, w19, w20, w21, w22, w23, w24] o (by simp only [List.length_cons, List.length_nil]; decide)

theorem spAligned_of_sp_eq {s sm : State} (hal : s.spAligned = true) (hsp : sm.sp = s.sp) :
    sm.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [hsp]
  exact hal

theorem list_len6_shared_lb {α : Type} (ws : List α) (h : ws.length = 6) :
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

theorem memRegion_24_exists_words_shared_lb (a : BitVec 64) {m : Memory} {R : SepProp}
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

theorem words_entails_memRegion_24_shared_lb (a w0 w1 w2 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) ⊢ memRegion a 24 := by
  have h := words64At_entails_memRegion [w0, w1, w2] a
    (by simp only [List.length_cons, List.length_nil]; decide)
  simpa only [words64At, List.length_cons, List.length_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem memRegion_200_exists_otrWords25_shared_lb (a : BitVec 64) {m : Memory} {R : SepProp}
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
