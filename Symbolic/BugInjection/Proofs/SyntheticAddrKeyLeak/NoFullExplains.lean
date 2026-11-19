/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.Shared.Composed.Runs
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Refutation of Full 2-Call `Explains` for `synthetic-addr-key-leak-cli`

Proves a parametric refutation `not_explains_init_send_invalidAddr` (and
`not_explains_single_invalidAddr`) for any 2-call `[.run ev₀, .run ev₁]` trace where `ev₀` exits
`0` and `ev₁` is an exit-`0` `.send` call whose `PreKeySignalMessage` stdout `out₁` satisfies the
fast outer-protobuf check `invalidPreKeySendAddr out₁ = true`, together with direct specializations
to both:
- the `(compI0, compHooks0)` carrier trace `ImplTrace.akCarrierTrace`, and
- the recorded witness trace `AddrKeyLeakCli.trace` (`akTrace`).

On Call 1 (`.send`, exit `0` with `0x03`-prefixed `PreKeySignalMessage` stdout `out₁`):
1. `Explains` requires a `.messageEncrypt` party step emitting a visible entry
   `v = ⟨.send, [ek, ct, msg], .preKeySend, none⟩ ∈ vis` where `msg = encMsg st coins pq m` and
   `parseTrSignalMsg msg = some (encSig st coins pq m)`.
2. `GhostWF` forces `(encSig st coins pq m).wire` to carry
   `g.addr wire = Cli.serializeAddresses ⟨Cli.aliceUuid, 1⟩ ⟨Cli.bobUuid, 1⟩` (36 bytes).
3. `SendMatches` + `decodePreKey_encode` + `gamma_trWireMsg` + `trWireBytes_canonical` force the
   38 bytes immediately preceding the 8-byte MAC of the inner `SignalMessage` in `out₁` to equal
   `encodeField 6 0 0 (.bytes (serializeAddresses alice bob))`, whereas the mutant placed the
   32-byte `mac_key` in protobuf field 6 (`addresses`) — concrete byte contradiction!
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoFullExplains

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Bytes Participant ExecTrace Trace Traceful ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.Spqr (spqrSend)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Refinement (encodeField canonicalVariation)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet
  (TRState messageVersion trMsgKeys computeMac kdfCk parseTrSignalMsg u32Max)
open DY.Libsignal.Composed (reachability)
open scoped DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   Explains MatchesEventsAt StepsWF RunMatches RunRejected OutputsMatch BytesMatchEntry
   SendMatches decodePreKey preKeyWire ecKey kyberKey runSteps stepView encDraws encSendEntry
   exposures pendingPreKey lastSent nextBundleIds runWrapped gamma trWireBytes_canonical
   gamma_trWireMsg)
open DY.Libsignal.Composed.Refinement.Cli (aliceUuid bobUuid serializeAddress serializeAddresses)
open Symbolic.BugInjection (PQXDHSpqrSetup compFitsPinned)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
  (length_le_preKeyWire PreKeyLengthsFit decodePreKey_encode)
open Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs
  (akSetup akTrace sentWire1 akEvents akEvents_eq akCarrierTrace c1Out)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next messageEncrypt_fail_not_ok)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd encSt encMsg encSig parse_encMsg RndE NetE EvT StT)
open Symbolic.Swarm.CREF.TR (gamma_concat gamma_trunc8 gamma_hmac length_hmacWith)

/-! ## 1. Protocol-Address Bytes & Fast Computable `invalidPreKeySendAddr` Check -/

private def aliceUuidChars : List Char :=
  ['8', 'a', '6', 'f', '1', 'c', '2', 'e', '-', '3', 'b', '4', 'd', '-',
   '4', 'e', '5', 'f', '-', '9', 'a', '0', 'b', '-', '1', 'c', '2', 'd',
   '3', 'e', '4', 'f', '5', 'a', '6', 'b']

private def bobUuidChars : List Char :=
  ['5', 'd', '3', 'e', '2', 'f', '1', '0', '-', '7', 'a', '8', 'b', '-',
   '4', 'c', '9', 'd', '-', '8', 'e', '0', 'f', '-', 'a', '1', 'b', '2',
   'c', '3', 'd', '4', 'e', '5', 'f', '6']

private theorem aliceUuid_eq_ofList : aliceUuid = String.ofList aliceUuidChars := rfl

private theorem bobUuid_eq_ofList : bobUuid = String.ofList bobUuidChars := rfl

/-- Explicit 36-byte serialization of `(⟨aliceUuid, 1⟩, ⟨bobUuid, 1⟩)`. -/
def expectedAddrFast : HwBytes :=
  [0x00#8,
   0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8,
   0x9a#8, 0x0b#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8,
   0x01#8,
   0x00#8,
   0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8,
   0x8e#8, 0x0f#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8,
   0x01#8]

theorem serializeAddresses_alice_bob_eq :
    serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ = expectedAddrFast := by
  rw [aliceUuid_eq_ofList, bobUuid_eq_ofList]
  unfold serializeAddresses serializeAddress DY.Libsignal.Composed.Refinement.Cli.parseUuidBytes
  dsimp only
  rw [String.toList_ofList, String.toList_ofList]
  rfl

private theorem expectedAddrFast_ne_nil : expectedAddrFast ≠ [] := by decide

/-- Expected 38-byte protobuf field 6 (`addresses`) on an honest `PreKeySignalMessage` send. -/
def expectedAddrField : HwBytes :=
  encodeField 6 0 0 (.bytes expectedAddrFast)

/-- Extract the last `n` bytes immediately preceding the 8-byte trailing MAC of `msg`. -/
def extractPreMacSuffix (n : Nat) (msg : HwBytes) : HwBytes :=
  let pre := msg.take (msg.length - 8)
  pre.drop (pre.length - n)

private theorem extractPreMacSuffix_eq (A B C : HwBytes) (hC : C.length = 8) :
    extractPreMacSuffix B.length ((A ++ B) ++ C) = B := by
  dsimp only [extractPreMacSuffix]
  have hlen1 : ((A ++ B) ++ C).length - 8 = (A ++ B).length := by
    rw [List.length_append, hC, Nat.add_sub_cancel]
  rw [hlen1, List.take_left]
  have hlen2 : (A ++ B).length - B.length = A.length := by
    rw [List.length_append, Nat.add_sub_cancel]
  rw [hlen2, List.drop_left]

/-- Fast outer-protobuf extraction of `message` from `preKeyWire` via `decodePreKey_encode`. -/
private theorem decodePreKey_preKeyWire_msg {preKeyId : Option (BitVec 32)}
    {spkId kpkId regId : BitVec 32} {ik ek ct msg b : HwBytes}
    (hb : b = preKeyWire preKeyId spkId kpkId regId ik ek ct msg)
    (hlen : b.length < 2 ^ 63) :
    (decodePreKey (b.drop 2)).bind (·.message) = some msg := by
  have ⟨hik_le, hek_le, hct_le, hmsg_le⟩ :=
    length_le_preKeyWire preKeyId spkId kpkId regId ik ek ct msg
  rw [← hb] at hik_le hek_le hct_le hmsg_le
  have hfit : PreKeyLengthsFit
      { registrationId := some regId, preKeyId, signedPreKeyId := some spkId,
        kyberPreKeyId := some kpkId, kyberCiphertext := some (kyberKey ct),
        baseKey := some (ecKey ek), identityKey := some ik, message := some msg } := by
    intro v hv; simp only [Option.some.injEq] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simp only [ecKey, List.length_cons]; omega
    · omega
    · omega
    · simp only [kyberKey, List.length_cons]; omega
  subst hb
  dsimp only [kyberKey, ecKey] at hfit
  simp only [preKeyWire, List.drop_succ_cons, List.drop_zero, decodePreKey_encode _ hfit]
  rfl

/-- Fast computable check that `w` is a `0x03`-framed `PreKeySignalMessage` of length `< 2 ^ 63`
whose outer-protobuf `message` field does NOT carry `expectedAddrField` immediately before its
8-byte trailing MAC. -/
def invalidPreKeySendAddr (w : HwBytes) : Bool :=
  (w.head? == some wirePrekeyTag) &&
  decide (w.length < 2 ^ 63) &&
  match (decodePreKey (w.drop 2)).bind (·.message) with
  | some pMsg => decide (extractPreMacSuffix expectedAddrField.length pMsg ≠ expectedAddrField)
  | none => false

/-! ## 2. Trace & `Step.messageEncrypt` Helpers -/

private theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_append_at {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

private theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

private def encTrGen (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : ExecTrace :=
  let m := rnd tr.length 32
  let coins := rnd (tr.length + 1) cl
  ((((((tr.append (RndE 32)).append (RndE cl)).append
    (NetE (spqrSend st.spqr coins).2.1)).append
    (EvT (.Sent me st.peer (dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

private theorem encTrGen_length (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : (encTrGen tr me stH cl st pq).length = tr.length + 7 := by
  dsimp only [encTrGen]; simp only [append_len]

private theorem Runs.messageEncryptGen {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} {pq : Bytes}
    (hst : tr.at? stH = some (StT me st))
    (hns : st.ns ≠ u32Max)
    (hpq : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)).at? pqH = some (NetE pq)) :
    Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pqH) tr (tr.length + 6)
      (encTrGen tr me stH cl st pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Runs.bind (Runs.getLocalState hst) ?_
  refine Runs.bind (Runs.guard _ hns) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.genRand _ _) ?_
  refine Runs.bind (Runs.sendMessage _ _) ?_
  have hpq' :
      (((tr.append (RndE 32)).append (RndE cl)).append
        (NetE (spqrSend st.spqr
          (rnd (tr.append (RndE 32)).length cl)).2.1)).at? pqH = some (NetE pq) := by
    rw [append_len]; exact hpq
  refine Runs.bind (Runs.receiveMessage hpq') ?_
  refine Runs.bind (Runs.logEvent _ _) ?_
  refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
  refine runs_cast (Runs.sendMessage _ _) ?_ ?_
  · simp only [NetE, EvT, StT, append_len, Nat.add_assoc]
  · simp only [encTrGen, encSt, encMsg, RndE, NetE, EvT, StT, append_len]
    dsimp only [kdfCk, spqrSend]

private theorem encTrGen_lastSent (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    lastSent tr (encTrGen tr me stH cl st pq) =
      some (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32)) := by
  unfold lastSent
  rw [encTrGen_length]
  have hlt : tr.length < tr.length + 7 := by omega
  have hsub : tr.length + 7 - 1 = tr.length + 6 := by omega
  simp only [hlt, ↓reduceIte, hsub, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have hat : ((encTrGen tr me stH cl st pq).at? (tr.length + 6) : Option DY.Network.ExecEntryT) =
      some (NetE (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
    dsimp only [encTrGen]
    exact at?_append_at _ _ (by simp only [append_len])
  simp [hat]

private theorem lastSent_messageEncrypt_of_ok {me : Participant} {stH cl pqH : Nat}
    {tr : ExecTrace}
    (hlok : (Step.messageEncrypt me stH cl pqH).LocalOk tr)
    (hok : (Step.messageEncrypt me stH cl pqH).ok tr = true) :
    ∃ st pq,
      lastSent tr ((Step.messageEncrypt me stH cl pqH).next tr) =
        some (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32)) := by
  have hpq_eq : pqH = tr.length + 2 := by
    rcases hlok.2 with h2 | h3
    · exact h2
    · exfalso
      rw [h3] at hok
      dsimp only [DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx] at hok
      rw [messageEncrypt_fail_not_ok] at hok
      cases hok
  subst hpq_eq
  have hok_run := hok
  unfold Step.ok Step.toInput at hok_run
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    (me, stH, cl, tr.length + 2) tr] at hok_run
  dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability] at hok_run
  unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok_run
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hok_run
  rcases hst : ((DY.PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 with
    _ | st
  · simp [hst] at hok_run
  · have hat_st : tr.at? stH = some (StT me st) :=
      Symbolic.Swarm.CREF.bks_stored_of_getLocalState hst
    rw [hst, Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd] at hok_run
    dsimp only at hok_run
    have hns : st.ns ≠ u32Max := by
      intro hmax
      have hf : ((failure : Traceful Unit).run tr).1 = none := by rw [DY.Traceful.run_failure]
      simp [_root_.guard, hmax, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hf] at hok_run
    let pqSalt := (spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1
    have hpq_at : (((tr.append (RndE 32)).append (RndE cl)).append (NetE pqSalt)).at?
        (tr.length + 2) = some (NetE pqSalt) :=
      at?_append_at _ _ (by simp only [append_len])
    have hruns := Runs.messageEncryptGen hat_st hns hpq_at
    have hnext_eq :
        (Step.messageEncrypt me stH cl (tr.length + 2)).next tr =
          encTrGen tr me stH cl st pqSalt := by
      dsimp only [Step.next, Step.toInput]
      rw [stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability
        (me, stH, cl, tr.length + 2) tr]
      dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability]
      exact hruns.2
    exact ⟨st, pqSalt, by rw [hnext_eq, encTrGen_lastSent]⟩

/-! ## 3. Visible-Entry Filtering & `MatchesEventsAt` Peeling -/

private theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

private theorem matchesEventsAt_run_peel {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {ev : RunEvent} {evs : List CliEvent}
    {vis visAll : List VisEntry}
    (hnotRej : ¬ RunRejected ev)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt interp r S g initIds tr ss (.run ev :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ tr' s ss' v vs,
      s.LocalOk tr' ∧
      StepsWF ss' (s.next tr') ∧
      RunMatches interp r S g tr' s ev v initIds ∧
      (∀ w ∈ v, w ∈ visAll) ∧
      (∀ w ∈ vs, w ∈ visAll) ∧
      MatchesEventsAt interp r S g (nextBundleIds initIds ev) (s.next tr') ss' evs vs := by
  cases hm with
  | run0 _ hrej _ => exact False.elim (hnotRej hrej)
  | run1 _ hrm hrest =>
    obtain ⟨_, hlok, hwf_tail⟩ := stepsWF_append_right _ hwf
    exact ⟨_, _, _, _, _, hlok, hwf_tail, hrm,
      fun w hw => hsub w (List.mem_append_left _ hw),
      fun w hw => hsub w (List.mem_append_right _ hw), hrest⟩

private theorem kind_ne_send_of_mem_encDraws {rs : List (Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws rs) : v.kind ≠ .send := by
  rcases Symbolic.Proofs.Swarm.UA.XlateSteps.encDraws_kind hv with hk | hk <;> rw [hk] <;> decide

private theorem kind_ne_send_of_mem_exposures {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') : v.kind ≠ .send := by
  rw [Symbolic.Proofs.Swarm.UA.XlateSteps.exposures_kind hv]; decide

private theorem stepView_send_preKeySend {s : Step} {tr : ExecTrace} {v : VisEntry}
    {peer : CryptoVerification.SignalSession.Address}
    (hfits : s.FitsCmd (.send peer))
    (hlok : s.LocalOk tr)
    (hok : s.ok tr = true)
    (hv : v ∈ stepView s tr true)
    (hkind : v.kind = .send) :
    ∃ ek ct st coins pq m,
      v = ⟨.send, [ek, ct, encMsg st coins pq m], .preKeySend, none⟩ := by
  cases s with
  | messageEncryptAbort me stH =>
    unfold stepView at hv
    simp only [List.mem_append] at hv
    rcases hv with hv_own | hv_exp
    · by_cases hok' : (Step.messageEncryptAbort me stH).ok tr = true
      · simp only [hok', ↓reduceIte] at hv_own
        exact False.elim (kind_ne_send_of_mem_encDraws hv_own hkind)
      · simp only [hok', Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hv_own
        exact False.elim (kind_ne_send_of_mem_encDraws hv_own.1 hkind)
    · exact False.elim (kind_ne_send_of_mem_exposures hv_exp hkind)
  | messageEncrypt _ stH cl _ =>
    obtain ⟨st, pq, hlast⟩ := lastSent_messageEncrypt_of_ok hlok hok
    unfold stepView at hv
    simp only [hok, ↓reduceIte, List.mem_append] at hv
    rcases hv with (hv_draws | hv_send) | hv_exp
    · exact False.elim (kind_ne_send_of_mem_encDraws hv_draws hkind)
    · unfold encSendEntry at hv_send
      rw [hlast] at hv_send
      rcases hppk : pendingPreKey tr stH with _ | ⟨ek, ct⟩
      · simp [hppk] at hv_send
      · simp only [hppk, List.mem_singleton] at hv_send
        exact ⟨ek, ct, st, rnd (tr.length + 1) cl, pq, rnd tr.length 32, hv_send⟩
    · exact False.elim (kind_ne_send_of_mem_exposures hv_exp hkind)
  | _ => cases hfits

/-! ## 4. Parametric Refutation of `Explains` on Any Invalid-`addresses` Call-1 Send -/

private theorem gamma_computeMac_length (interp : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (mk ikS ikR wire : Bytes) :
    (gamma interp S g (computeMac mk ikS ikR wire)).length = 8 := by
  unfold computeMac
  rw [gamma_trunc8, gamma_hmac, List.length_take, length_hmacWith]
  decide

/-- Parametric refutation of `Explains` on any 2-call `[.run ev₀, .run ev₁]` trace where `ev₀`
exits `0` and `ev₁` is an exit-`0` `.send` call whose stdout `out₁` satisfies
`invalidPreKeySendAddr out₁ = true`. -/
theorem not_explains_single_invalidAddr {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {ev₀ ev₁ : RunEvent} {peer₁ : CryptoVerification.SignalSession.Address}
    {out₀ out₁ : HwBytes}
    (hexit₀ : ev₀.exit = some (0, out₀))
    (hcmd₁ : ev₁.cmd = .send peer₁)
    (hexit₁ : ev₁.exit = some (0, out₁))
    (hbad₁ : invalidPreKeySendAddr out₁ = true) :
    ¬ Explains interp r S g ss vis [.run ev₀, .run ev₁] := by
  unfold invalidPreKeySendAddr at hbad₁
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad₁
  obtain ⟨⟨hhead₁, hlen_wire⟩, hp_bad⟩ := hbad₁
  rcases hdec : (decodePreKey (out₁.drop 2)).bind (·.message) with _ | pMsg
  · rw [hdec] at hp_bad; cases hp_bad
  · rw [hdec, decide_eq_true_eq] at hp_bad
    rintro ⟨_, hgwf, ⟨_, _, hswf0, _⟩, hm0⟩
    have hnotRej0 : ¬ RunRejected ev₀ := fun h => h out₀ hexit₀
    have hnotRej1 : ¬ RunRejected ev₁ := fun h => h out₁ hexit₁
    obtain ⟨_, _, _, _, _, _, hswf1, _, _, hsub1, hm1⟩ :=
      matchesEventsAt_run_peel hnotRej0 hswf0 hm0 (fun _ hw => hw)
    obtain ⟨tr1, s1, _, v1, _, hlok1, _, hrm1, hsub_v1, _, _⟩ :=
      matchesEventsAt_run_peel hnotRej1 hswf1 hm1 hsub1
    obtain ⟨_, _, hfits1, _, hok1, _, hvis1, inp, drs, outs, hv1_split, _, _, hout1, _, _⟩ := hrm1
    have hwrap1 : runWrapped ev₁ = true := by
      unfold runWrapped
      rw [hcmd₁, hexit₁]
      exact hhead₁
    rw [hwrap1] at hvis1
    rw [hcmd₁] at hfits1
    unfold OutputsMatch at hout1
    rw [hexit₁, hcmd₁] at hout1
    obtain ⟨v, rfl, hbme⟩ := hout1
    have hv_in_v1 : v ∈ v1 := by
      rw [hv1_split]
      exact List.mem_cons_of_mem inp (List.mem_append_right drs (List.mem_singleton.mpr rfl))
    have hv_in_vis : v ∈ vis := hsub_v1 v hv_in_v1
    have hv_in_stepView : v ∈ stepView s1 tr1 true := hvis1 ▸ hv_in_v1
    obtain ⟨ek, ct, st, coins, pq, m, hv_eq⟩ :=
      stepView_send_preKeySend hfits1 hlok1 hok1 hv_in_stepView hbme.1.symm
    subst hv_eq
    have haddr :
        g.addr (encSig st coins pq m).wire =
          serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ :=
      (hgwf.2.2 _ hv_in_vis rfl).1 rfl ek ct (encMsg st coins pq m) (encSig st coins pq m) rfl
        (parse_encMsg st coins pq m)
    rw [serializeAddresses_alice_bob_eq] at haddr
    dsimp only [BytesMatchEntry, SendMatches] at hbme
    obtain ⟨_, _, _, _, _, hwire⟩ := hbme
    have hp_msg : pMsg = gamma interp S g (encMsg st coins pq m) := by
      have hdec' := decodePreKey_preKeyWire_msg hwire hlen_wire
      rw [hdec] at hdec'
      injection hdec'
    let keys := trMsgKeys pq (kdfCk st.cks).2
    let wire := (encSig st coins pq m).wire
    let mac := computeMac keys.macKey st.myIk st.peerIk wire
    have henc_eq : encMsg st coins pq m = DY.Concat.concat wire mac := rfl
    have hwire_def :
        wire = DY.TrWire.trWireMsg messageVersion (dhPk st.dhs) st.ns st.pn
          (DY.SymEnc.symEnc keys.cipherKey keys.iv m) (spqrSend st.spqr coins).2.2
          canonicalVariation := rfl
    have hgamma_wire :
        ∃ preBytes, gamma interp S g wire = preBytes ++ expectedAddrField := by
      rw [hwire_def, gamma_trWireMsg, ← hwire_def, haddr, trWireBytes_canonical]
      simp only [expectedAddrFast_ne_nil, ↓reduceIte]
      exact ⟨_, rfl⟩
    obtain ⟨preBytes, hgw⟩ := hgamma_wire
    have hmac_len : (gamma interp S g mac).length = 8 :=
      gamma_computeMac_length interp S g keys.macKey st.myIk st.peerIk wire
    have hp_msg_split :
        pMsg = (preBytes ++ expectedAddrField) ++ gamma interp S g mac := by
      rw [hp_msg, henc_eq, gamma_concat, hgw]
    have hsuf : extractPreMacSuffix expectedAddrField.length pMsg = expectedAddrField := by
      rw [hp_msg_split]
      exact extractPreMacSuffix_eq preBytes expectedAddrField (gamma interp S g mac) hmac_len
    exact hp_bad hsuf

/-- Existential form `¬ (∃ g ss vis, Explains ...)` of `not_explains_single_invalidAddr`. -/
theorem not_explains_init_send_invalidAddr {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {ev₀ ev₁ : RunEvent}
    {peer₁ : CryptoVerification.SignalSession.Address} {out₀ out₁ : HwBytes}
    (hexit₀ : ev₀.exit = some (0, out₀))
    (hcmd₁ : ev₁.cmd = .send peer₁)
    (hexit₁ : ev₁.exit = some (0, out₁))
    (hbad₁ : invalidPreKeySendAddr out₁ = true) :
    ¬ (∃ g ss vis, Explains interp r S g ss vis [.run ev₀, .run ev₁]) := by
  rintro ⟨g, ss, vis, hex⟩
  exact not_explains_single_invalidAddr hexit₀ hcmd₁ hexit₁ hbad₁ hex

/-! ## 5. Concrete Instantiations on `ImplTrace.akCarrierTrace` and `AddrKeyLeakCli.trace` -/

/-- Recorded Call-1 (`send "attack-at-dawn"`) stdout from `AddrKeyLeakCli.trace` (1793 bytes). -/
abbrev c1RecordedOut : HwBytes := sentWire1

theorem invalidPreKeySendAddr_c1Out :
    invalidPreKeySendAddr c1Out = true := by
  decide +kernel

theorem invalidPreKeySendAddr_sentWire1 :
    invalidPreKeySendAddr sentWire1 = true := by
  decide +kernel

theorem invalidPreKeySendAddr_c1RecordedOut :
    invalidPreKeySendAddr c1RecordedOut = true :=
  invalidPreKeySendAddr_sentWire1

/-- Refutes `Explains` on `Defs.akEvents out1` whenever `invalidPreKeySendAddr out1 = true`. -/
theorem not_explains_akEvents_invalidAddr {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {out1 : HwBytes}
    (hbad : invalidPreKeySendAddr out1 = true) :
    ¬ (∃ g ss vis, Explains interp r S g ss vis (akEvents out1)) :=
  not_explains_init_send_invalidAddr rfl rfl rfl hbad

/-- Direct `¬ Explains` form on `Defs.akEvents out1`. -/
theorem not_explains_akEvents_single_invalidAddr {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step}
    {vis : List VisEntry} {out1 : HwBytes}
    (hbad : invalidPreKeySendAddr out1 = true) :
    ¬ Explains interp r S g ss vis (akEvents out1) :=
  not_explains_single_invalidAddr rfl rfl rfl hbad

/-- No model run and ghost can explain `ImplTrace.akCarrierTrace` under any `ExternInterpretation`,
`ProtocolSetup`, and `OpaqueSymbolSemantics`. -/
theorem not_explains_carrier_any {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} :
    ¬ (∃ g ss vis, Explains interp r S g ss vis akCarrierTrace) :=
  not_explains_init_send_invalidAddr rfl rfl rfl invalidPreKeySendAddr_c1Out

/-- Direct `¬ Explains` form on `ImplTrace.akCarrierTrace`. -/
theorem not_explains_carrier_single {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis akCarrierTrace :=
  not_explains_single_invalidAddr rfl rfl rfl invalidPreKeySendAddr_c1Out

/-- Refutation of full 2-call `Explains` on `ImplTrace.akCarrierTrace` at `compI0`. -/
theorem not_explains_akCarrierTrace {r : ProtocolSetup} {S : OpaqueSymbolSemantics} :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akCarrierTrace) :=
  not_explains_carrier_any

/-- Refutation of full 2-call `Explains` on `ImplTrace.akCarrierTrace` under `compI0`, assuming
`ProtocolSetupWF r` and `compFitsPinned akSetup compI0 r`. -/
theorem not_full_explains_carrier {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (_hwf : ProtocolSetupWF r) (_hfits : compFitsPinned akSetup compI0 r) :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akCarrierTrace) :=
  not_explains_carrier_any

/-- Refutation of full 2-call `Explains` on `ImplTrace.akCarrierTrace` under `compI0` from
`compFitsPinned akSetup compI0 r`. -/
theorem not_full_explains_carrier_of_fits {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (_hfits : compFitsPinned akSetup compI0 r) :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akCarrierTrace) :=
  not_explains_carrier_any

/-- No model run and ghost can explain `AddrKeyLeakCli.trace` (`akTrace`) under any
`ExternInterpretation`, `ProtocolSetup`, and `OpaqueSymbolSemantics`. -/
theorem not_explains_any_interp {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} :
    ¬ (∃ g ss vis, Explains interp r S g ss vis akTrace) := by
  rw [← akEvents_eq]
  exact not_explains_akEvents_invalidAddr invalidPreKeySendAddr_sentWire1

/-- Direct `¬ Explains` form on `AddrKeyLeakCli.trace` (`akTrace`). -/
theorem not_explains_akTrace_single {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis akTrace := by
  rw [← akEvents_eq]
  exact not_explains_akEvents_single_invalidAddr invalidPreKeySendAddr_sentWire1

/-- Refutation of full 2-call `Explains` on `akTrace` under `compI0`, assuming
`ProtocolSetupWF r` and `compFitsPinned akSetup compI0 r`. -/
theorem not_full_explains {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (_hwf : ProtocolSetupWF r) (_hfits : compFitsPinned akSetup compI0 r) :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akTrace) :=
  not_explains_any_interp

/-- Refutation of full 2-call `Explains` on `akTrace` under `compI0` from
`compFitsPinned akSetup compI0 r`. -/
theorem not_full_explains_of_fits {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (_hfits : compFitsPinned akSetup compI0 r) :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akTrace) :=
  not_explains_any_interp

/-- Alias without `hwf`/`hfits` guards for convenience in `Top.lean`. -/
theorem not_explains_akTrace {r : ProtocolSetup} {S : OpaqueSymbolSemantics} :
    ¬ (∃ g ss vis, Explains compI0 r S g ss vis akTrace) :=
  not_explains_any_interp

end Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoFullExplains
