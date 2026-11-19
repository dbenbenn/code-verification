/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentityFetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem taken_remoteIdentity_eq_some
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    taken.remoteIdentity = some otr.remoteIdentityKey := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h)
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem exists_pointsTo16_of_memRegion2 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 2 ∗ R) :
    ∃ v : BitVec 16, m ⊨ (a ↦₁₆ v) ∗ R := by
  rw [memRegion_split a 1 1 (by decide), ProofLib.memRegion_one a,
      ProofLib.memRegion_one (a + 1#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨b0, b1, hm⟩ := hm
  rw [pointsTo8_pair] at hm
  exact ⟨_, hm⟩

private theorem pointsTo16_entails_memRegion2 (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 := by
  rw [pointsTo16_split8 a v, memRegion_split a 1 1 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

private theorem exists_pointsTo32_of_memRegion4 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 4 ∗ R) :
    ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [ProofLib.memRegion_four a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem exists_pointsTo64_of_memRegion8 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 8 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem list_len2 {α : Type} (ws : List α) (h : ws.length = 2) :
    ∃ b0 b1, ws = [b0, b1] := by
  rcases ws with _ | ⟨b0, ws⟩; · nomatch h
  rcases ws with _ | ⟨b1, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨b0, b1, rfl⟩
  · nomatch h

private theorem list_len4 {α : Type} (ws : List α) (h : ws.length = 4) :
    ∃ b0 b1 b2 b3, ws = [b0, b1, b2, b3] := by
  rcases ws with _ | ⟨b0, ws⟩; · nomatch h
  rcases ws with _ | ⟨b1, ws⟩; · nomatch h
  rcases ws with _ | ⟨b2, ws⟩; · nomatch h
  rcases ws with _ | ⟨b3, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨b0, b1, b2, b3, rfl⟩
  · nomatch h

theorem exists_ikChunks6_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (c0 : BitVec 32) (c4 : BitVec 16) (c6 c14 c22 : BitVec 64) (c30 : BitVec 16),
      ∀ o : BitVec 64, (o ↦ₛ bs) = ikChunks6 o c0 c4 c6 c14 c22 c30 := by
  have s22 : bs.drop 22 = (bs.drop 22).take 8 ++ bs.drop 30 := by
    have := (List.take_append_drop 8 (bs.drop 22)).symm
    rwa [List.drop_drop] at this
  have s14 : bs.drop 14 = (bs.drop 14).take 8 ++ bs.drop 22 := by
    have := (List.take_append_drop 8 (bs.drop 14)).symm
    rwa [List.drop_drop] at this
  have s6 : bs.drop 6 = (bs.drop 6).take 8 ++ bs.drop 14 := by
    have := (List.take_append_drop 8 (bs.drop 6)).symm
    rwa [List.drop_drop] at this
  have s4 : bs.drop 4 = (bs.drop 4).take 2 ++ bs.drop 6 := by
    have := (List.take_append_drop 2 (bs.drop 4)).symm
    rwa [List.drop_drop] at this
  have s0 : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  have hsplit : bs = bs.take 4 ++ ((bs.drop 4).take 2 ++ ((bs.drop 6).take 8 ++
      ((bs.drop 14).take 8 ++ ((bs.drop 22).take 8 ++ bs.drop 30)))) :=
    s0.trans (congrArg (bs.take 4 ++ ·)
      (s4.trans (congrArg ((bs.drop 4).take 2 ++ ·)
        (s6.trans (congrArg ((bs.drop 6).take 8 ++ ·)
          (s14.trans (congrArg ((bs.drop 14).take 8 ++ ·) s22)))))))
  have hl4 : (bs.take 4).length = 4 := by simp [h]
  have hl2 : ((bs.drop 4).take 2).length = 2 := by simp [h]
  have hl6 : ((bs.drop 6).take 8).length = 8 := by simp [h]
  have hl14 : ((bs.drop 14).take 8).length = 8 := by simp [h]
  have hl22 : ((bs.drop 22).take 8).length = 8 := by simp [h]
  have hl30 : (bs.drop 30).length = 2 := by simp [h]
  obtain ⟨b0, b1, b2, b3, h4⟩ := list_len4 (bs.take 4) hl4
  obtain ⟨b4, b5, h2⟩ := list_len2 ((bs.drop 4).take 2) hl2
  obtain ⟨b30, b31, h30⟩ := list_len2 (bs.drop 30) hl30
  obtain ⟨c6, hc6⟩ := exists_unpack64_of_length_8 hl6
  obtain ⟨c14, hc14⟩ := exists_unpack64_of_length_8 hl14
  obtain ⟨c22, hc22⟩ := exists_unpack64_of_length_8 hl22
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4, c6, c14, c22, b31 ++ b30, ?_⟩
  intro o
  conv_lhs => rw [hsplit]
  rw [h4, h2, hc6, hc14, hc22, h30]
  simp only [pointsToBytes_append, List.length_cons, List.length_nil, unpack64_length,
    pointsToBytes4_eq_pointsTo32, pointsToBytes2_eq_pointsTo16,
    ← pointsTo64_eq_pointsToBytes]
  unfold ikChunks6
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]

theorem ikChunks6_entails_memRegion (o : BitVec 64) (c0 : BitVec 32) (c4 : BitVec 16)
    (c6 c14 c22 : BitVec 64) (c30 : BitVec 16) :
    ikChunks6 o c0 c4 c6 c14 c22 c30 ⊢ memRegion o 32 := by
  unfold ikChunks6
  rw [memRegion_split o 4 28 (by decide),
      memRegion_split (o + 4#64) 2 26 (by decide),
      memRegion_split (o + 4#64 + 2#64) 8 18 (by decide),
      memRegion_split (o + 4#64 + 2#64 + 8#64) 8 10 (by decide),
      memRegion_split (o + 4#64 + 2#64 + 8#64 + 8#64) 8 2 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion2 _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo16_entails_memRegion2 _ _)))))

theorem exists_ikChunks6_of_memRegion32 (o : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion o 32 ∗ R) :
    ∃ (d0 : BitVec 32) (d4 : BitVec 16) (d6 d14 d22 : BitVec 64) (d30 : BitVec 16),
      m ⊨ ikChunks6 o d0 d4 d6 d14 d22 d30 ∗ R := by
  rw [memRegion_eq_exists_bytes o 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨bs, hm⟩ := hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨d0, d4, d6, d14, d22, d30, heq⟩ := exists_ikChunks6_of_length_32 hlen
  exact ⟨d0, d4, d6, d14, d22, d30, (heq o) ▸ hm⟩

@[expose] def sessionPure (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat

@[expose] def sessionRecordWithoutRemIk (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ⌜sessionPure G { sess with state := st }⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.localIk (sp + 0x128#64) ∗
  vecU8At A ((sp + 0x128#64) + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) ((sp + 0x128#64) + 0x48#64) G.chainsCap G.chainsPtr
    (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice ((sp + 0x128#64) + 0x60#64) ∗
  vecU8At A ((sp + 0x128#64) + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A ((sp + 0x128#64) + 0x90#64) G.sender st.senderChain ∗
  optTailVecAt A 48 ((sp + 0x128#64) + 0xf8#64) G.pending ∗
  optTailVecAt A 32 ((sp + 0x128#64) + 0x128#64) G.kyber ∗
  (((sp + 0x128#64) + 0x148#64) ↦₃₂ st.sessionVersion) ∗
  (((sp + 0x128#64) + 0x14c#64) ↦₃₂ st.previousCounter) ∗
  (((sp + 0x128#64) + 0x150#64) ↦ₛ G.regIds)

theorem sessionRecordAt_taken_eq (A : RustAlloc) (sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    (hcur : g.cur = some G) :
    sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st) =
      vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
      sessionRecordWithoutRemIk A sp g G sess st := by
  unfold sessionRecordAt takenRecord
  rw [hcur]
  dsimp only
  unfold sessionStateReprAt sessionStateAt sessionRecordWithoutRemIk sessionPure
  have heq : (sp + 0x110#64) + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [heq]
  ac_rfl

theorem sessionRecordAt_taken_extract_remIk (A : RustAlloc) (sp : BitVec 64)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    {m : Memory} {R : SepProp}
    (hm : m ⊨ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st)) ∗ R) :
    ∃ (g : RecordGhost) (G : SessionGhost),
      g.cur = some G ∧
      (match st.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      (m ⊨ vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        sessionRecordWithoutRemIk A sp g G sess st ∗ R) := by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  cases hcur : g.cur with
  | none =>
    unfold sessionRecordAt takenRecord at hm
    rw [hcur] at hm
    dsimp only at hm
    have hfalse : m ⊨ ⌜False⌝ ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
    exact False.elim ((satisfies_pure_sepConj _ _ _).1 hfalse).1
  | some G =>
    rw [sessionRecordAt_taken_eq A sp g G sess st hcur] at hm
    have hm_copy := hm
    unfold sessionRecordWithoutRemIk at hm_copy
    have hm1 : m ⊨
        ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
          G.chains.length = st.receiverChains.length ∧
          G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
          G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
        (vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
          ⌜sessionPure G { sess with state := st }⌝ ∗
          vecGhostAt A G.localIk (sp + 0x128#64) ∗
          vecU8At A ((sp + 0x128#64) + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
          vecAt A 104 8 (chainAt A) ((sp + 0x128#64) + 0x48#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          vecGhostAt A G.alice ((sp + 0x128#64) + 0x60#64) ∗
          vecU8At A ((sp + 0x128#64) + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
          optSenderChainAt A ((sp + 0x128#64) + 0x90#64) G.sender st.senderChain ∗
          optTailVecAt A 48 ((sp + 0x128#64) + 0xf8#64) G.pending ∗
          optTailVecAt A 32 ((sp + 0x128#64) + 0x128#64) G.kyber ∗
          (((sp + 0x128#64) + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          (((sp + 0x128#64) + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          (((sp + 0x128#64) + 0x150#64) ↦ₛ G.regIds) ∗ R) :=
      Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_copy
    have hrem := ((satisfies_pure_sepConj _ _ _).1 hm1).1.2.1
    rw [sepConj_assoc] at hm
    exact ⟨g, G, hcur, hrem, hm⟩

theorem sessionRecordAt_taken_restore_remIk (A : RustAlloc) (sp : BitVec 64)
    (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8)))
    (hcur : g.cur = some G) :
    vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
      sessionRecordWithoutRemIk A sp g G sess st ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st) := by
  refine Entails.sepExists_right g ?_
  rw [sessionRecordAt_taken_eq A sp g G sess st hcur]
  exact Entails.refl _

open CryptoVerification.LibsignalPublicApi.StoreKit

theorem spAligned_of_sp_eq {s sm : State} (hal : s.spAligned = true) (hsp : sm.sp = s.sp) :
    sm.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [hsp]
  exact hal

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
