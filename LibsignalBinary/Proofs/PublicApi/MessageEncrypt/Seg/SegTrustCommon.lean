/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Helpers for `segTrust_ok`, `segSave_ok`, and `segApplyStore_ok`

`SegExit` combinators, allocation-panic bridges, `.rodata` vtable/literal helpers, future-box folding
lemmas, and `StoreAnswers` witnesses shared across the post-encryption store segments.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `SegExit` Combinators and Allocation Panic Bridge -/

theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem drop_ne (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    b + 0x42b28#64 ≠ 0#64 := by
  intro h
  rw [show b = 0#64 - 0x42b28#64 by rw [← h, BitVec.add_sub_cancel]] at hb
  exact absurd hb (by decide)

/-! ## `.rodata` Vtable and String Literal Lemmas -/

@[expose] def trustVtablesAt {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (b + ikit.trustShimOff)) ∗
  ((b + ikit.trustFutVtOff) ↦₆₄ᵣ (b + ikit.trustFutDropOff)) ∗
  ((b + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((b + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.trustPollOff))

@[expose] def saveVtablesAt {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : SepProp :=
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (b + ikit.saveShimOff)) ∗
  ((b + ikit.saveFutVtOff) ↦₆₄ᵣ (b + ikit.saveFutDropOff)) ∗
  ((b + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((b + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (b + ikit.savePollOff))

@[expose] def storeVtablesAt {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : SepProp :=
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (b + kit.storeShimOff)) ∗
  ((b + kit.storeFutVtOff) ↦₆₄ᵣ (b + kit.storeFutDropOff)) ∗
  ((b + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((b + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kit.storePollOff))

theorem encSubStackV_lt {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    {sp0 : BitVec 64} (hstk : sp0.toNat ≥ withStoresEncStackV kit ikit) :
    encSubStackV kit ikit < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hstk) sp0.isLt

theorem stackAt_encSubStack_split (sp : BitVec 64) (k : Nat) (hk : k ≤ encSubStack) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - k) ∗ stackAt sp k :=
  stackAt_sub sp encSubStack k hk (by decide)

theorem stackAt_encSubStackV_split {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    {sp0 : BitVec 64} (hstk : sp0.toNat ≥ withStoresEncStackV kit ikit)
    (sp : BitVec 64) (k : Nat) (hk : k ≤ encSubStackV kit ikit) :
    stackAt sp (encSubStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - k) ∗ stackAt sp k :=
  stackAt_sub sp (encSubStackV kit ikit) k hk (encSubStackV_lt kit ikit hstk)

theorem trustBox_fold (p u0 u1 u2 : BitVec 64) (b0 b1 : BitVec 8) :
    (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 0x10#64) ↦₆₄ u2) ∗ ((p + 0x18#64) ↦₈ b0) ∗
      ((p + 0x19#64) ↦₈ b1) ∗ memRegion (p + 0x1a#64) 6 ⊢ memRegion p 32 := by
  rw [memRegion_split p 8 24 (by decide), memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))))

theorem saveBox_fold (p u0 u1 u2 : BitVec 64) (b0 : BitVec 8) :
    (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 0x10#64) ↦₆₄ u2) ∗ ((p + 0x18#64) ↦₈ b0) ∗
      memRegion (p + 0x19#64) 7 ⊢ memRegion p 32 := by
  rw [memRegion_split p 8 24 (by decide), memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))

theorem spAligned_of_sp_eq {s sm : State} (hal : s.spAligned = true) (hsp : sm.sp = s.sp) :
    sm.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [hsp]
  exact hal

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

theorem pointsTo8_memRegion7_exists_word64 (a : BitVec 64) (d : BitVec 8) :
    ((a ↦₈ d) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ w : BitVec 64, ⌜w.setWidth 8 = d⌝ ∗ (a ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hpad => ?_
  have hlen : (d :: pad).length = 8 := by simp [hpad]
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 hlen
  refine Entails.sepExists_right w ?_
  have hd : w.setWidth 8 = d := by
    have h0 : (d :: pad).head? = (unpack64 w).head? := congrArg List.head? hw
    unfold unpack64 at h0
    simp only [List.head?_cons, Option.some.injEq] at h0
    rw [BitVec.setWidth_eq_extractLsb' (by decide), ← h0]
  refine Entails.pure_right hd ?_
  rw [← pointsToBytes_cons, hw, ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem pointsTo32_memRegion4_exists_word64 (a : BitVec 64) (d : BitVec 32) :
    ((a ↦₃₂ d) ∗ memRegion (a + 4#64) 4) ⊢
      ∃∗ w : BitVec 64, ⌜w.setWidth 32 = d⌝ ∗ (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun hi => ?_
  refine Entails.sepExists_right (hi ++ d) ?_
  have hd : (hi ++ d).setWidth 32 = d := by
    rw [BitVec.setWidth_eq_extractLsb' (by decide), BitVec.extractLsb'_append_eq_right]
  refine Entails.pure_right hd ?_
  rw [pointsTo64_split32, BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
  exact Entails.refl _

/-! ## `StepsThroughEncrypt` Model and RNG Draw Lemmas -/

theorem StepsThroughEncrypt.draws_eq {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr')
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (hload : answers.loadSession = .ok (some r)) :
    x.draws S answers = S.draws otr.pqrState x.rest := by
  rcases h15 with ⟨hcur, _, hfrom, hrem, hstep5⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession
  simp only [hload, hcur, hfrom, hrem, Option.isNone, Bool.false_eq_true, ↓reduceIte]
  unfold EncEncryptStep at hstep5
  cases hpk : sess.pendingPreKey with
  | none =>
    rfl
  | some items =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, _, _⟩
    simp only [hts, Option.bind_some, hexp, hlt, Bool.false_eq_true, ↓reduceIte]

@[expose] def answersOfTrust (r : SessionRecord (List (BitVec 8))) (ans : Except Unit Bool) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := .ok (some r)
    isTrustedIdentity := ans
    saveIdentity := .ok .newOrUnchanged
    storeSession := .ok () }

@[expose] def answersOfSaveErr (r : SessionRecord (List (BitVec 8))) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := .ok (some r)
    isTrustedIdentity := .ok true
    saveIdentity := .error ()
    storeSession := .ok () }

@[expose] def answersOfStoreErr (r : SessionRecord (List (BitVec 8))) (c : IdentityChange) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := .ok (some r)
    isTrustedIdentity := .ok true
    saveIdentity := .ok c
    storeSession := .error () }

theorem StepsThroughEncrypt.model_trust_err {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    x.model C S uuidTryParse (answersOfTrust r (.error ())) =
      (.error (.store ()),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending]) := by
  rcases h15 with ⟨hcur, _, hfrom, hrem, hstep5⟩
  unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol answersOfTrust
  unfold EncEncryptStep at hstep5
  cases hpk : sess.pendingPreKey with
  | none =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, henc, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw]
  | some items =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, hts, hexp, hlt, henc, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe,
      MonadExceptOf.throw]

theorem StepsThroughEncrypt.model_trust_false {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    x.model C S uuidTryParse (answersOfTrust r (.ok false)) =
      (.error (.untrustedIdentity x.rem.val),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending]) := by
  rcases h15 with ⟨hcur, _, hfrom, hrem, hstep5⟩
  unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol answersOfTrust
  unfold EncEncryptStep at hstep5
  cases hpk : sess.pendingPreKey with
  | none =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, henc, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw]
  | some items =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, hts, hexp, hlt, henc, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe,
      MonadExceptOf.throw]

theorem StepsThroughEncrypt.model_save_err {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    x.model C S uuidTryParse (answersOfSaveErr r) =
      (.error (.store ()),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending,
          .saveIdentity x.rem.val k]) := by
  rcases h15 with ⟨hcur, _, hfrom, hrem, hstep5⟩
  unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol answersOfSaveErr
  unfold EncEncryptStep at hstep5
  cases hpk : sess.pendingPreKey with
  | none =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, henc, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw]
  | some items =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, hts, hexp, hlt, henc, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe,
      MonadExceptOf.throw]

theorem StepsThroughEncrypt.model_store_err {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (c : IdentityChange)
    (h15 : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    x.model C S uuidTryParse (answersOfStoreErr r c) =
      (.error (.store ()),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending,
          .saveIdentity x.rem.val k,
          .storeSession x.rem.val (storedRecord sess otr' taken)]) := by
  rcases h15 with ⟨hcur, _, hfrom, hrem, hstep5⟩
  unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol answersOfStoreErr
    storedRecord
  unfold EncEncryptStep at hstep5
  cases hpk : sess.pendingPreKey with
  | none =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, henc, ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw]
  | some items =>
    rw [hpk] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    simp [hcur, hfrom, hrem, hpk, hts, hexp, hlt, henc, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.lift, StateT.bind, pure, ExceptT.pure,
      StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe,
      MonadExceptOf.throw]

theorem StepsThroughEncrypt.tailModel_trust_err {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))} {s0 s : State}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr')
    (htrust : ikit.trustRel ist0 x.rem.val k .sending (.error ()))
    (htr : s.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        ikit.trustEvs x.rem.val k .sending (.error ()))) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfTrust r (.error ())) (.error (.store ())) s0 s := by
  unfold TailModel
  rw [StepsThroughEncrypt.model_trust_err h15, htr]
  exact ⟨⟨rfl, ⟨h15.2.1.2, trivial⟩, ⟨htrust, trivial⟩⟩,
    congrArg (s0.trace ++ ·) (ikit.traceOfWith_load_trust kit encRecord (answersOfTrust r (.error ())) x.rem.val k .sending).symm⟩

theorem StepsThroughEncrypt.tailModel_trust_false {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))} {s0 s : State}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr')
    (htrust : ikit.trustRel ist0 x.rem.val k .sending (.ok false))
    (htr : s.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        ikit.trustEvs x.rem.val k .sending (.ok false))) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfTrust r (.ok false))
      (.error (.untrustedIdentity x.rem.val)) s0 s := by
  unfold TailModel
  rw [StepsThroughEncrypt.model_trust_false h15, htr]
  exact ⟨⟨rfl, ⟨h15.2.1.2, trivial⟩, ⟨htrust, trivial⟩⟩,
    congrArg (s0.trace ++ ·) (ikit.traceOfWith_load_trust kit encRecord (answersOfTrust r (.ok false)) x.rem.val k .sending).symm⟩

theorem StepsThroughEncrypt.tailModel_save_err {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))} {s0 s : State}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr')
    (htrust : ikit.trustRel ist0 x.rem.val k .sending (.ok true))
    (hsave : ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.error ()))
    (htr : s.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k (.error ())))) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfSaveErr r) (.error (.store ())) s0 s := by
  unfold TailModel
  rw [StepsThroughEncrypt.model_save_err h15, htr]
  refine ⟨⟨rfl, ⟨h15.2.1.2, trivial⟩, ⟨htrust, hsave, trivial⟩⟩, ?_⟩
  rw [ikit.traceOfWith_load_trust_save kit encRecord (answersOfSaveErr r) x.rem.val k .sending]
  simp only [answersOfSaveErr, List.append_assoc]

theorem StepsThroughEncrypt.tailModel_store_err {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))} (c : IdentityChange) {s0 s : State}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr')
    (htrust : ikit.trustRel ist0 x.rem.val k .sending (.ok true))
    (hsave : ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c))
    (hstore : kit.storeRel st0 x.rem.val (storedRecord sess otr' taken) (.error ()))
    (htr : s.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k (.ok c)) ++
        kit.storeEvs encRecord x.rem.val (storedRecord sess otr' taken) (.error ()))) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfStoreErr r c) (.error (.store ())) s0 s := by
  unfold TailModel
  rw [StepsThroughEncrypt.model_store_err c h15, htr]
  refine ⟨⟨rfl, ⟨h15.2.1.2, hstore, trivial⟩, ⟨htrust, hsave, trivial⟩⟩, ?_⟩
  rw [ikit.traceOfWith_all4 kit encRecord (answersOfStoreErr r c) x.rem.val k .sending (storedRecord sess otr' taken)]
  simp only [answersOfStoreErr, List.append_assoc]
end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
