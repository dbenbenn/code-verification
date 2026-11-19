/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Stack -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Shared Helpers and Hook Bridges for `segPreKey`

Pure `SystemTime` comparison lemmas, callee/hook `subroutine_ok` projections at `encEntry img`,
`.rodata` `"message_encrypt"` literal lemmas, `SegExit` combinators, and error-answer witnesses for
`segPreKey`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure Model and `SystemTime` Lemmas -/

theorem checkedAddSecs_tvNsec {t ts : SystemTime} {s : Nat}
    (h : t.checkedAddSecs s = some ts) : ts.tvNsec = t.tvNsec := by
  unfold SystemTime.checkedAddSecs at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · simp at h

theorem unixEpoch_checkedAddSecs_tvNsec {s : Nat} {ts : SystemTime}
    (h : SystemTime.unixEpoch.checkedAddSecs s = some ts) :
    ts.tvNsec = 0#32 ∧ ts.tvNsec.toNat < 10 ^ 9 := by
  have h1 := checkedAddSecs_tvNsec h
  have h2 : SystemTime.unixEpoch.tvNsec = 0#32 := rfl
  rw [h2] at h1
  exact ⟨h1, by rw [h1]; decide⟩

theorem checkedAddSecs_tvNsec_lt_of_unixEpoch {s1 s2 : Nat} {ts expiry : SystemTime}
    (h1 : SystemTime.unixEpoch.checkedAddSecs s1 = some ts)
    (h2 : ts.checkedAddSecs s2 = some expiry) :
    expiry.tvNsec = 0#32 ∧ expiry.tvNsec.toNat < 10 ^ 9 := by
  have ⟨hts0, _⟩ := unixEpoch_checkedAddSecs_tvNsec h1
  have hexp := checkedAddSecs_tvNsec h2
  rw [hts0] at hexp
  exact ⟨hexp, by rw [hexp]; decide⟩

/-! ## `SystemTime.lt` Instruction Bridge (`+0x704..+0x71c`) -/

theorem systemTime_lt_cond_eq (a b : SystemTime) :
    (if a.tvSec == b.tvSec then a.tvNsec.ult b.tvNsec else a.tvSec.slt b.tvSec) = a.lt b := by
  unfold SystemTime.lt
  by_cases h : a.tvSec = b.tvSec
  · have hslt : b.tvSec.slt b.tvSec = false := by simp [BitVec.slt]
    simp [h, hslt, BitVec.ult, BitVec.lt_def]
  · have hbeq : (a.tvSec == b.tvSec) = false := beq_false_of_ne h
    simp [hbeq]

/-! ## Callee and Hook Address Projections -/

theorem SepWPp.of_sepWP_ret {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hpost⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.of_sepWP {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hcont R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.call_frame {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre_eq : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hf : P = T ∗ F)
    (hexit : ∀ code sf R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R')) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R' hm hL
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
    rw [hf, sepConj_assoc] at hm
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex_st, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpan sm hpan_st⟩)⟩
  · exact (hexit code sm R' hex_st hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R' hoom_st hpost⟩)⟩

/-! ## `SegExit` Combinators -/

@[expose] def preKeyErrAnswers (r : SessionRecord (List (BitVec 8))) :
    StoreAnswers (List (BitVec 8)) Unit :=
  okAnswers r .newOrUnchanged

theorem allocFailedIn_of_prefix {s0 s sf : State} (hpref : s0.trace <+: s.trace)
    (ha : allocFailedIn s sf) : allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := hpref
  unfold allocFailedIn at ha ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem model_of_unack_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = none) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts]

theorem model_of_timeAdd_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = none) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts, hexp]

theorem model_of_stale {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = true) :
    x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) ∧
    x.draws S (preKeyErrAnswers r) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte]
  · unfold EncryptGhost.draws EncryptGhost.sendState loadedSession preKeyErrAnswers okAnswers
    simp only [hcur, hfrom, hrem, Option.isNone, hpk, hts, hexp, hlt, Option.bind, ↓reduceIte,
      Bool.false_eq_true]

theorem sendState_of_not_stale {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false) :
    x.sendState (preKeyErrAnswers r) = some otr.pqrState := by
  unfold EncryptGhost.sendState loadedSession preKeyErrAnswers okAnswers
  simp only [hcur, hfrom, hrem, Option.isNone, hpk, hts, hexp, hlt, Option.bind, ↓reduceIte,
    Bool.false_eq_true]

theorem draws_of_not_stale {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false) :
    x.draws S (preKeyErrAnswers r) = S.draws otr.pqrState x.rest := by
  unfold EncryptGhost.draws
  rw [sendState_of_not_stale hcur hfrom hrem hpk hts hexp hlt]

@[expose] def preKeyOtrGhost (x : WithStoresEncGhost) (sp pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) : OtrEncryptGhost where
  ret := sp + 0x580#64
  o := sp + 0x288#64
  pqCap := pqCap
  pqPtr := pqPtr
  ot := otr
  ptA := x.ptA
  ptext := x.ptext
  locA := x.locA
  loc := some x.loc
  remA := x.remA
  rem := x.rem
  cur := x.cur
  rest := x.rest

theorem execOk_of_preKeyOtrGhost_error {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {sp pqCap pqPtr : BitVec 64}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {e : SignalProtocolError}
    (h : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error e) :
    execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
      (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr = .error e := by
  unfold execOk
  change (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).1 = .error e at h
  rcases hm : Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr with ⟨_ | _, _⟩ <;>
    simp_all

theorem execOk_of_preKeyOtrGhost_ok {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {sp pqCap pqPtr : BitVec 64}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (h : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm) :
    execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
      (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr =
      .ok (sm, ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2) := by
  unfold execOk
  change (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).1 = .ok sm at h
  change _ = Except.ok (sm, (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr).2)
  rcases hm : Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddrVals (serviceIdParse uuidTryParse) x.loc.val x.rem.val) x.rest) otr with ⟨_ | _, _⟩ <;>
    simp_all

theorem model_of_otr_panic {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64}
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hotr : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic) :
    (x.model C S uuidTryParse (preKeyErrAnswers r)).1 = .error .panic := by
  have hexec := execOk_of_preKeyOtrGhost_error hotr
  rw [EncryptGhost.model, messageEncrypt_eq_flat]
  simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
    hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec, ApiError.ofProtocol]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
