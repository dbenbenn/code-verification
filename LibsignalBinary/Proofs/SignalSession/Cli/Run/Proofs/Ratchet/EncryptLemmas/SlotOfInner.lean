/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.PanicAndWire
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Outer Slot Reduction for `encrypt`

Discharges the `EncEnv` record-scope invariants (`w1_scopeIn`, `w1_scopeQ`, `w1_recOk`) for
`w1SessKit` and reduces `encSlotSpec` (`cliEncrypt_slot_of_inner` and its
`PEParams`/`RustAlloc`-generic counterparts) to the inner `withStoresEncSpecVT_cli` contract.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## Record-scope obligations (`scopeIn`, `scopeQ`, `recOk`) -/

private theorem fromSessionState_pqr_and_taken {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    otr.pqrState = s.pqRatchetState ∧ taken = { s with pqRatchetState := [] } := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨(congrArg OutgoingTripleRatchet.pqrState h.1).symm, h.2.symm⟩

private theorem otr_encrypt_send_step_aux {PQ PQC : Type} {C : Crypto} {codec : SignalMessageProtoCodec}
    {spqr : Spqr PQ PQC} {ptext : List (BitVec 8)} {ad : Option (List (BitVec 8))} {rest : PQC}
    {otr otr' : OutgoingTripleRatchet PQ} {sm : SignalMessage}
    (h : execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext ad rest) otr = .ok (sm, otr')) :
    ∃ salt pm, spqr.send otr.pqrState rest = some (otr'.pqrState, salt, pm) := by
  unfold execOk Mut.exec OutgoingTripleRatchet.encrypt at h
  dsimp only [ExceptT.run, ExceptT.mk, ExceptT.lift, StateT.run, StateT.bind, StateT.map,
    Functor.map, ExceptT.map, ExceptT.bind, ExceptT.bindCont, StateT.pure, ExceptT.pure,
    StateT.get, StateT.set, set, MonadStateOf.set, liftE, StateT.lift, liftM, monadLift,
    MonadLift.monadLift, MonadLiftT.monadLift, get, getThe, MonadStateOf.get, bind, pure,
    throw, throwThe, MonadExceptOf.throw] at h
  cases hpan : spqr.sendPanics otr.pqrState rest
  case true =>
    simp [hpan, ExceptT.bindCont, StateT.bind, StateT.pure, bind, pure] at h
  case false =>
    simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
    rcases hs : spqr.send otr.pqrState rest with _ | ⟨pq', salt, pm⟩
    · simp [hs, StateT.pure, pure] at h
    · simp only [hs] at h
      rcases hn : otr.senderChainKey.nextChainKey C.F with _ | next
      · simp [hn, StateT.bind, StateT.pure, ExceptT.bindCont, bind, pure] at h
      · simp only [hn, StateT.bind, StateT.pure, StateT.map, StateT.set, ExceptT.bindCont,
          bind, pure, Except.ok.injEq, Prod.mk.injEq] at h
        have hpq : pq' = otr'.pqrState := congrArg OutgoingTripleRatchet.pqrState h.2
        subst hpq
        exact ⟨salt, pm, rfl⟩

private theorem otr_encrypt_send_step {C : Crypto} {S : SpqrModel}
    {ptext : List (BitVec 8)} {ad : Option (List (BitVec 8))} {rest : List (BitVec 8)}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (h : execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr ptext ad rest) otr =
      .ok (sm, otr')) :
    ∃ salt pm, S.send otr.pqrState rest = some (otr'.pqrState, salt, pm) :=
  otr_encrypt_send_step_aux h

@[expose] def w1EncGhost (x : EncGhost) : WithStoresEncGhost where
  ret := x.ret
  ptA := x.ptA
  ptext := x.ptext
  remA := x.peerA
  rem := x.peer
  locA := x.meA
  loc := x.me
  now := unixEpoch
  cur := x.coinsP
  rest := x.coins
  ssA := x.stores + 0xf0#64
  idA := x.stores

/-! ## Outer `encSlotSpec` reduction -/

private theorem loadSession_some_of_model_ok {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {x : EncryptGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {cm : CiphertextMessage}
    (hok : (x.model C S uuidParse answers).1 = .ok cm) :
    ∃ r, answers.loadSession = .ok (some r) := by
  simp only [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat] at hok
  rcases hl : answers.loadSession with _ | (_ | r)
  · simp [hl] at hok
  · simp [hl] at hok
  · exact ⟨r, rfl⟩

private def w1SlotAnsOfRc (F : FsFiles)
    (rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))) : SlotAns CiphertextMessage :=
  match rc with
  | (.ok m, calls) => some (some (w1CliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

private theorem w1EncDef_eq_slotAnsOfRc (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (g : CryptoVerification.LibsignalPublicApi.EncryptGhost) (hnow : g.now = unixEpoch) :
    w1EncDef W Scope F g.rem.val g.loc.val g.ptext g.rest =
      w1SlotAnsOfRc F (g.model W.C (pqxdhSpqrModel W) uuidTryParse
        (w1CliAnswers Scope F g.rem.val (w1EncKey Scope F g.rem.val))) := by
  unfold w1EncDef w1SlotAnsOfRc CryptoVerification.LibsignalPublicApi.EncryptGhost.model
  rw [hnow]
  generalize LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
    (serializeAddrVals (serviceIdParse uuidTryParse))
    (w1CliAnswers Scope F g.rem.val (w1EncKey Scope F g.rem.val))
    g.ptext g.rem.val g.loc.val unixEpoch g.rest = rc
  rcases rc with ⟨err | _, _⟩
  · cases err <;> rfl
  · rfl

private theorem match_panic_eq_none (F : FsFiles)
    {rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))}
    (h : rc.1 = .error .panic) :
    w1SlotAnsOfRc F rc = none := by
  rcases rc with ⟨res, _⟩
  dsimp only at h
  subst h
  rfl

private theorem slotOut_of_rc_eq {F : FsFiles} {ans : SlotAns CiphertextMessage}
    {rc : Except (ApiError AddrVal Unit) CiphertextMessage ×
      List (StoreCall AddrVal (List (BitVec 8)))}
    {s0 sf : State}
    (hans : ans = w1SlotAnsOfRc F rc)
    (hnoPanic : rc.1 ≠ .error .panic)
    (hnoStore : rc.1 ≠ .error (.store ()))
    (hwrOk : ∀ v, rc.1 = .ok v → ∀ pw ∈ (w1CliFinal F rc.2).writes, cliWrOk pw.1) :
    slotOut ans (w1CliFinal F rc.2) rc.1 s0 sf := by
  refine ⟨hnoPanic, hnoStore, ?_⟩
  rcases rc with ⟨err | v, calls⟩
  · dsimp only [w1SlotAnsOfRc] at hnoPanic hans ⊢
    cases err <;> first | exact hans | exact False.elim (hnoPanic rfl)
  · dsimp only [w1SlotAnsOfRc] at hans
    exact ⟨hans, hwrOk v rfl⟩

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
