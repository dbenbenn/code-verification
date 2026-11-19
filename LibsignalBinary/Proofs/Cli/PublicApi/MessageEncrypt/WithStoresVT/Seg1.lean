/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
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
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFromFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentity
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentityFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import ProofLib.RegChain
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 1): `EncEnvT_trap`, `withStoresEncSpecVT_trap`, and
segments `SegIdentity`, `SegFrom`, `SegTrust`, `SegSave` on `trTrapProgAt`
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt



open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

@[expose, reducible] def h45_kitF {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False }

theorem h45_storeFinal_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitF, ih]

theorem h45_callsRel_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, h45_kitF, ih]

theorem h45_traceOfWith_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitF kit) encRecord ans calls = ikit.traceOfWith kit encRecord ans calls :=
  rfl

@[expose] def h45_ScopeNone (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  Scope r ∧ r.currentSession = none

@[expose, reducible] def h45_kitL {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False, loadRel := fun _ _ _ => False }

section SegIdentity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

end SegIdentity

section SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom


open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem h45_fromSessionState_error_ne_invalidState
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    e ≠ .invalidState ∧ e ≠ .panic := by
  unfold Mut.exec OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, Except.error.injEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.error.injEq] at h) <;>
    (subst h; decide)

private theorem h45_execOk_fromSessionState_of_error
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    execOk OutgoingTripleRatchet.fromSessionState st = .error e := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem h45_execOk_fromSessionState_of_ok
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

private theorem h45_model_of_fromSessionState_error
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    h45_execOk_fromSessionState_of_error herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (h45_fromSessionState_error_ne_invalidState herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp only [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, List.nil_append]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

end SegFrom

section SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust


open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

end SegTrust

/-! ## Ext Bridges (`CliEncHooksExt` / `CliExternsOk` / `EncCallees_ext` → `WithStoresVT.*Ext`) -/

theorem encHooksExt_of_cliEncHooksExt {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : CliEncHooksExt C A S ext) : WithStoresVT.EncHooksExt C A S ext where
  toTripleRatchetHooks := h.toTripleRatchetHooks
  shim := h.shim
  memcpy := h.memcpy
  memcpyRO := h.memcpyRO
  timeAdd := h.timeAdd
  durationSinceEpoch := h.durationSinceEpoch

theorem WithStoresVT.encHooksExt_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    WithStoresVT.EncHooksExt P.C A S ext :=
  encHooksExt_of_cliEncHooksExt (cliEncHooksExt_of_externsOk S hOk)

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
