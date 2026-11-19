/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Random
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Tests.CliNonvacuity.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Clean 3-Step Prefix (`bobStart` Completion) for Seed 7003 (`Clean3BobStart7003.lean`)

Extends `(gClean7003 mode cl₁ cl₃, ssClean2 cl₁, visClean2 cl₁)` with `m2Clean` (`bobStart`),
proving `Explains` on `[.run ev0, .run (ev1Of mode), .run (ev2Of mode)]` and closed-form
trace/state/salt/visibility projections on `t7Clean cl₁` and `visClean3 cl₁`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003

unseal DY.Bytes

open ByteSpecs (hmacWith)
open scoped DY.Libsignal.Composed
open DY (Traceful ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg RecvChain kdfCk trMsgKeys computeMac createChain
   consumeMessageKey setRecvChain maxReceiverChains parseTrSignalMsg spqrA2B spqrB2A)
open DY.Libsignal.Composed (reachability bobStart)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry VisEventKind
   PreKeyFields PreKeyRep
   gamma randTerm setupTrace runSteps runTrace newIndices newRandoms received receivedPlaintext
   rngEntry bobVis bobOpkPk exposures stepView honestKeysOf
   storedSecrets storedStates honestSaltsOf plaintextTerms
   GhostAndSemMatchSetup GhostWF ModelRunWF OpkNamed
   BytesMatchEntry DrawsMatch OutputsMatch RunMatches MatchesEventsAt Explains
   bobDoneBaseKeys)
open DY.Libsignal.Composed.Refinement.Cli (serializeAddresses aliceUuid bobUuid)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next stepIn_ok)
open Symbolic.Swarm.CREF (b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd RndE NetE EvP EvT EvC StP StT bobSt0 bobOut bobOutOpt
   bobAgreement_honest encMsg encSig parse_encMsg ratchetState recvSt skipTr
   mac_ok dec_ok createChain_comm)
open Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas (spqrRecv_init_pos)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (matchesEvents_run1)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of setupTrace_false_eq m0_ok_false m0_next_false vis_m0_false visStep modelRunWF_msPrefix2)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (length_append_entry_eq getEventAt_eq_at? getMessageSentAt_eq_at?)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003 (setup_ids_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
  (SemPinned2 if_pos' if_neg' getMessageSentAt_of_at?_net
   at?_append_other_eq at?_append_same_eq at?_nil_eq length_append_eq)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B (bobTr0)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
  (NoSkippedKeys noSkippedKeys_setupTr4 noSkippedKeys_aliceTr noSkippedKeys_encTrCl
   noSkippedKeys_bobTr0 bobTr0_bobDone_mem)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators (gamma_of_termAt)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
  (isAliceWire isAliceWire_tTrW_dhPk_rnd gClean7003 gClean7003_σ_length
   o1Pure o1_eq_pure stA0Pure stA0_eq_pure key0Pure spqrSend_stA0_key
   pqMsg1Pure stA1Pure encMsg1Pure encSig1Pure
   dhsBPure stB00Pure stB0'Pure cBPure cB'Pure stB1Pure CommonNodes mkCommonNodes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
  (ghostAndSemMatchSetup_gClean7003 pqSecrets7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith


/-! ## 1. Clean 3-Step Definitions & `m2Clean` (`bobStart`) Execution -/

def m2Clean : Step := .bobStart "bob" "alice" HonestSession.kh1 1 HonestSession.mh1 33 1
def ssClean3 (cl₁ : Nat) : List Step := [m0Of false, m1Clean cl₁, m2Clean]

def t7Clean (cl₁ : Nat) : ExecTrace :=
  bobTr0 (t6Clean cl₁) o1Pure.ek o1Pure.ct o1Pure.keys (encSig1Pure cl₁).2
    (kdfCk (cBPure cl₁).chainKey).2 key0Pure (tRnd 31 32) key0Pure
    (stB0'Pure cl₁) (stB1Pure cl₁) (cBPure cl₁)

def visClean3 (cl₁ : Nat) : List VisEntry :=
  visClean2 cl₁ ++ stepView m2Clean (t6Clean cl₁) true

theorem t6Clean_length (cl₁ : Nat) : (t6Clean cl₁).length = 38 := by
  rw [(m1Clean_props cl₁).2.2.2.1, HonestSession.t5_length]

theorem t7Clean_length (cl₁ : Nat) : (t7Clean cl₁).length = 47 := by
  simp only [t7Clean, bobTr0, length_append_entry_eq, t6Clean_length]

theorem t6Clean_le_t7Clean (cl₁ : Nat) : t6Clean cl₁ ≤ t7Clean cl₁ := by
  unfold t7Clean bobTr0; dsimp only
  iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
  exact DY.Trace.append_le _ _

theorem t7Clean_at_46_stB1 (cl₁ : Nat) :
    (t7Clean cl₁).at? 46 = some (StT "bob" (stB1Pure cl₁)) := by
  unfold t7Clean
  rw [TraceState7003.bobTr0_trState_eq, t6Clean_length, if_pos' rfl]

private theorem seedB0_pure_eq (cl₁ : Nat) :
    (kdfCk stA0Pure.cks).2 = (kdfCk (cBPure cl₁).chainKey).2 := by
  rw [Dag7003Nodes.cBPure_chainKey_eq]

theorem m2Clean_runs (cl₁ : Nat) :
    Runs (bobStart "bob" "alice" HonestSession.kh1 1 HonestSession.mh1 33 1)
      (t6Clean cl₁) 46 (t7Clean cl₁) := by
  have hset : setRecvChain (stB0'Pure cl₁).recv (cB'Pure cl₁) = [cB'Pure cl₁] := by
    simp [setRecvChain, stB0'Pure, ratchetState, cB'Pure, cBPure, stB00Pure, bobSt0, maxReceiverChains]
  have hrs : ratchetState (stB00Pure cl₁) (encSig1Pure cl₁).2.ratchetKey
      (rnd (t6Clean cl₁).length 32) = (stB0'Pure cl₁, cBPure cl₁) := by
    rw [t6Clean_length]; rfl
  have hle45 : HonestSession.t4 ≤ HonestSession.t5 := by
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.append_le _ _
  have hle56 : HonestSession.t5 ≤ t6Clean cl₁ := (m1Clean_props cl₁).2.2.2.2.1
  have hle46 : HonestSession.t4 ≤ t6Clean cl₁ := DY.Trace.le_trans _ _ _ hle45 hle56
  have ht4 : HonestSession.t4 = b1_setupTr4 "alice" "bob" :=
    setupTrace_false_eq.symm.trans (Symbolic.Swarm.CREF.b1_setupTrace_eq r0 (by show "alice" ≠ "bob"; decide))
  have hik : (t6Clean cl₁).at? HonestSession.kh1.ik =
      some (StP "bob" { kind := .identity, sk := randTerm 5 32 }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change HonestSession.t4.at? 9 = _; rw [ht4]
    unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1
    iterate 12 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact at?_append_eq_self _ _ (by simp [length_append_eq, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hspk : (t6Clean cl₁).at? HonestSession.kh1.spk =
      some (StP "bob" { kind := .signedPrekey, sk := randTerm 10 32 }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change HonestSession.t4.at? 13 = _; rw [ht4]
    unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1
    iterate 8 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact at?_append_eq_self _ _ (by simp [length_append_eq, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hpqk : (t6Clean cl₁).at? HonestSession.kh1.pqspk =
      some (StP "bob" { kind := .pqPrekey, sk := randTerm 16 64 }) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    change HonestSession.t4.at? 19 = _; rw [ht4]
    unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact at?_append_eq_self _ _ (by simp [length_append_eq, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hreg : (t6Clean cl₁).at? 1 =
      some (EvP (.IdentityRegistered "alice" (dhPk (randTerm 0 32)) (DY.Signature.vk (randTerm 0 32)) true)) := by
    refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle46 ?_
    rw [ht4]; unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1
    iterate 20 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    exact at?_append_eq_self _ _ (by simp [length_append_eq, Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hek : (t6Clean cl₁).at? HonestSession.mh1.ek = some (NetE o1Pure.ek) := by
    have hs := getMessageSentAt_le hle56 t5_sent_25_26.1
    rw [getMessageSentAt_eq_at?] at hs
    rcases hat : ((t6Clean cl₁).at? 25 : Option DY.Network.ExecEntryT) with _ | ⟨⟨m⟩⟩ <;> rw [hat] at hs
    · cases hs
    · injection hs with hx; subst hx; exact hat
  have hct : (t6Clean cl₁).at? HonestSession.mh1.ct = some (NetE o1Pure.ct) := by
    have hs := getMessageSentAt_le hle56 t5_sent_25_26.2
    rw [getMessageSentAt_eq_at?] at hs
    rcases hat : ((t6Clean cl₁).at? 26 : Option DY.Network.ExecEntryT) with _ | ⟨⟨m⟩⟩ <;> rw [hat] at hs
    · cases hs
    · injection hs with hx; subst hx; exact hat
  have hv_var : ∀ sk : DY.Bytes, ((dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hv_lit : ∀ sk : DY.Bytes, ((dhPk sk).view? DY.Literal.Literal.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hlow_dhPk : ∀ sk : DY.Bytes, DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false := fun sk => by
    simp only [DY.Libsignal.TripleRatchet.x25519LowOrder, DY.X25519.normalizeX25519Key,
      hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hcan : DY.Libsignal.PQXDH.isCanonicalKey o1Pure.ek = true := by
    simp only [DY.Libsignal.PQXDH.isCanonicalKey, o1Pure, hv_var,
      DY.Libsignal.PQXDH.x25519LowOrder, DY.X25519.normalizeX25519Key,
      DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]; rfl
  have hmsg : (t6Clean cl₁).at? HonestSession.mh1.msg = some (NetE (encMsg1Pure cl₁)) := by
    change (t6Clean cl₁).at? 37 = _
    unfold t6Clean Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003.encTrCl; dsimp only
    rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, HonestSession.t5_length])]
    have h32 : HonestSession.t5.length + 1 = 32 := by rw [HonestSession.t5_length]
    have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
    rw [h32, HonestSession.t5_length, hr, hr, spqrSend_stA0_key]; rfl
  have hpq : (((t6Clean cl₁).append (RndE 32)).append (NetE key0Pure)).at? 33 = some (NetE key0Pure) := by
    iterate 2 refine Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some (DY.Trace.append_le _ _) ?_
    have hs := (m1Clean_props cl₁).2.2.2.2.2.1
    have h32 : HonestSession.t5.length + 1 = 32 := by rw [HonestSession.t5_length]
    have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
    rw [h32, hr, spqrSend_stA0_key, getMessageSentAt_eq_at?] at hs
    rcases hat : ((t6Clean cl₁).at? 33 : Option DY.Network.ExecEntryT) with _ | ⟨⟨m⟩⟩ <;> rw [hat] at hs
    · cases hs
    · injection hs with hx; subst hx; rfl
  have hspqr_recv : DY.Spqr.spqrRecv (stB0'Pure cl₁).spqr (encSig1Pure cl₁).2.pqRatchet 1 =
      some (recvSt (DY.Spqr.spqrInit o1Pure.keys.pqr spqrB2A) (pqMsg1Pure cl₁), key0Pure) := by
    refine spqrRecv_init_pos o1Pure.keys.pqr (pqMsg1Pure cl₁) .b2a 1 (by decide) ?_
    have hl0 : ((pqMsg1Pure cl₁).view? DY.Literal.Literal.SubF) = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
    simp [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hl0]
  have hbs := Runs.bobStart (keys := o1Pure.keys) (msg := (encSig1Pure cl₁).2) (t := encMsg1Pure cl₁)
    (st' := stB0'Pure cl₁) (c := cBPure cl₁) (c' := cB'Pure cl₁)
    (seed := (kdfCk (cBPure cl₁).chainKey).2) (pq := key0Pure) (m := tRnd 31 32)
    hik hspk hpqk rfl hreg hek hct hcan
    (bobAgreement_honest (tRnd 0 32) (tRnd 22 32) (tRnd 5 32) (tRnd 10 32) (tRnd 16 64) (tRnd 23 32))
    hmsg (parse_encMsg _ _ _ _) rfl (hlow_dhPk (tRnd 24 32)) hrs rfl hspqr_recv hpq
    (mac_ok (seedB0_pure_eq cl₁) rfl rfl) (dec_ok (seedB0_pure_eq cl₁))
    (stOut := stB1Pure cl₁) (by rw [hset]; rfl)
  have hskip : ∀ (tr : ExecTrace) (n : Nat),
      skipTr tr ((stB0'Pure cl₁).sessionInfo "bob") (encSig1Pure cl₁).2.ratchetKey
        (cBPure cl₁) n (encSig1Pure cl₁).2.counter = tr :=
    fun tr _ => by change ((Pure.pure () : Traceful Unit).run tr).2.val = tr; rw [DY.Traceful.run_pure]
  dsimp only [] at hbs
  rw [hskip] at hbs
  have hcnt : (encSig1Pure cl₁).2.counter = 0 := rfl
  have hidx : (cBPure cl₁).index = 0 := rfl
  rw [hcnt, hidx] at hbs
  simp only [UInt32.toNat_zero, Nat.sub_zero, Nat.add_zero] at hbs
  refine ⟨hbs.1.trans (congrArg some ?_), hbs.2⟩
  simp only [length_append_entry_eq, t6Clean_length]

theorem m2Clean_ok (cl₁ : Nat) : m2Clean.ok (t6Clean cl₁) = true := by
  unfold m2Clean Step.ok Step.toInput
  erw [stepIn_ok, (m2Clean_runs cl₁).1]; rfl

theorem m2Clean_next (cl₁ : Nat) : m2Clean.next (t6Clean cl₁) = t7Clean cl₁ := by
  unfold m2Clean Step.next Step.toInput
  erw [stepIn_next]; exact (m2Clean_runs cl₁).2

theorem m2Clean_preCond (cl₁ : Nat) : m2Clean.PreCond (t6Clean cl₁) := by
  unfold m2Clean Step.PreCond Step.toInput; dsimp only
  exact (stepIn_preCond_iff DY.Libsignal.Composed.bobStart.reachability
    ("bob", "alice", HonestSession.kh1, 1, HonestSession.mh1, 33, 1) (t6Clean cl₁)).mpr trivial

theorem runTrace_ssClean3 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    runTrace r (ssClean3 cl₁) = t7Clean cl₁ := by
  unfold runTrace ssClean3
  rw [setupTrace_eq_t4 ha hb hopk]
  dsimp only [runSteps]
  rw [m0_next_false, (m1Clean_props cl₁).2.2.1, m2Clean_next]

/-! ## 2. Visibility, `GhostWF`, and `ModelRunWF` on `(ssClean3, visClean3)` -/

theorem exposures_t6Clean_t7Clean (cl₁ : Nat) : exposures (t6Clean cl₁) (t7Clean cl₁) = [] := by
  apply exposures_eq_nil_of_noNewExposures
  unfold t7Clean bobTr0; dsimp only
  iterate 9 refine (noNewExposures_append
      (by simp -failIfUnchanged only [length_append_entry_eq, t6Clean_length]; omega) rfl rfl ?_)
  exact noNewExposures_self (t6Clean cl₁)

theorem newRandoms_t6Clean_t7Clean (cl₁ : Nat) :
    newRandoms (t6Clean cl₁) (t7Clean cl₁) = [(randTerm 38 32, 32)] := by
  unfold t7Clean bobTr0; dsimp only
  repeat rw [newRandoms_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, t6Clean_length]; omega)]
  rw [newRandoms_self, t6Clean_length]
  simp only [length_append_entry_eq, t6Clean_length]; rfl

theorem received_t6Clean_mh1 (cl₁ : Nat) :
    received (t6Clean cl₁) [HonestSession.mh1.ek, HonestSession.mh1.ct, HonestSession.mh1.msg] =
      [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁] := by
  have hle56 : HonestSession.t5 ≤ t6Clean cl₁ := (m1Clean_props cl₁).2.2.2.2.1
  have h25 := getMessageSentAt_le hle56 t5_sent_25_26.1
  have h26 := getMessageSentAt_le hle56 t5_sent_25_26.2
  have h37 : (t6Clean cl₁).getMessageSentAt 37 = some (encMsg1Pure cl₁) := by
    have hls := lastSent_t5_t6Clean cl₁
    unfold DY.Libsignal.Composed.Refinement.lastSent at hls
    rw [t6Clean_length, if_pos' (by rw [HonestSession.t5_length]; omega)] at hls
    exact hls
  dsimp only [HonestSession.mh1, received, List.filterMap_cons, List.filterMap_nil]
  rw [h25, h26, h37]

private theorem t7Clean_trEvent_eq (cl₁ : Nat) (i : Nat) (hi : 38 ≤ i) :
    (t7Clean cl₁).getEventAt TREvent i =
    if i = 45 then
      some (.MessageKey ((stB0'Pure cl₁).sessionInfo "bob") .receiver
        (kdfCk (cBPure cl₁).chainKey).2 key0Pure 0 (cBPure cl₁).rIdx 46)
    else if i = 44 then
      some (.Received "bob" (stB0'Pure cl₁).peer (encSig1Pure cl₁).2.ratchetKey 0 (tRnd 31 32))
    else if i = 42 then
      some (.HonestDH ((stB0'Pure cl₁).sessionInfo "bob") (stB0'Pure cl₁).dhs ((stB0'Pure cl₁).rIdx - 2))
    else if i = 41 then
      some (.DHRatchet "bob" (stB0'Pure cl₁).peer (encSig1Pure cl₁).2.ratchetKey (dhPk (stB0'Pure cl₁).dhs))
    else none := by
  rw [getEventAt_eq_at?]
  unfold t7Clean bobTr0
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, t6Clean_length, Nat.add_assoc]
  have hnone : ((t6Clean cl₁).at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
    simp [DY.Trace.at?, t6Clean_length, show ¬ i < 38 by omega]
  rw [hnone]
  by_cases h45 : i = 45 <;> simp [h45, EvT]
  by_cases h44 : i = 44 <;> simp [h44]
  by_cases h42 : i = 42 <;> simp [h42]
  by_cases h41 : i = 41 <;> simp [h41]

theorem receivedPlaintext_t6Clean_t7Clean (cl₁ : Nat) :
    receivedPlaintext (t6Clean cl₁) (t7Clean cl₁) = some (tRnd 31 32) := by
  unfold receivedPlaintext newIndices
  rw [t6Clean_length, t7Clean_length]
  change (List.range' 38 9).findSome? _ = _
  dsimp only [List.range', List.findSome?]
  repeat rw [t7Clean_trEvent_eq cl₁ _ (by decide)]
  rfl

theorem vis_m2Clean (cl₁ : Nat) (w : Bool) :
    stepView m2Clean (t6Clean cl₁) w =
      [⟨.recv, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeyRecv, none⟩,
       rngEntry (randTerm 38 32),
       ⟨.accept, [tRnd 31 32], .single,
         DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone
           (t6Clean cl₁) (t7Clean cl₁)⟩] := by
  unfold stepView
  rw [m2Clean_ok]
  dsimp only [m2Clean, ↓reduceIte]
  change bobVis (t6Clean cl₁) (m2Clean.next (t6Clean cl₁)) HonestSession.mh1
      (bobOpkPk "bob" HonestSession.kh1 (t6Clean cl₁)) ++
      exposures (t6Clean cl₁) (m2Clean.next (t6Clean cl₁)) = _
  rw [m2Clean_next, exposures_t6Clean_t7Clean, List.append_nil]
  dsimp only [bobVis, bobOpkPk, HonestSession.kh1, Option.bind, Option.toList]
  rw [List.append_nil, received_t6Clean_mh1, newRandoms_t6Clean_t7Clean,
      receivedPlaintext_t6Clean_t7Clean]
  rfl

theorem ghostWF_clean3 (mode : Bool) (cl₁ cl₃ : Nat) :
    GhostWF (gClean7003 mode cl₁ cl₃) (visClean3 cl₁) := by
  have hg2 := ghostWF_clean2 mode cl₁ cl₃
  refine ⟨?_, hg2.2.1, ?_⟩
  · intro v hv hvk ts n hn hmem
    unfold visClean3 at hv
    rcases List.mem_append.mp hv with hv2 | hv3
    · exact hg2.1 v hv2 hvk ts n hn hmem
    · rw [vis_m2Clean] at hv3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
      rcases hv3 with rfl | rfl | rfl
      · cases hvk
      · simp only [rngEntry, List.mem_singleton] at hmem
        have hts := (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1
        exact gClean7003_σ_length (by omega) (by omega)
      · cases hvk
  · intro v hv hvk
    unfold visClean3 at hv
    rcases List.mem_append.mp hv with hv2 | hv3
    · exact hg2.2.2 v hv2 hvk
    · rw [vis_m2Clean] at hv3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
      rcases hv3 with rfl | rfl | rfl <;> cases hvk

theorem modelRunWF_clean3 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat)
    (hcl₁ : cl₁ = 0 ∨ cl₁ = 32 ∨ cl₁ = 64) :
    ModelRunWF r (ssClean3 cl₁) := by
  rw [modelRunWF_iff_r0 ha hb hopk]
  obtain ⟨hiscur0, hdom0, ⟨hm0_ok, hm0_loc, _⟩, _⟩ := modelRunWF_msPrefix2 false
  refine ⟨hiscur0, hdom0, ?_, ?_⟩
  · dsimp only [ssClean3, DY.Libsignal.Composed.Refinement.StepsWF]
    refine ⟨hm0_ok, hm0_loc, ?_⟩
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, m0_next_false]
    refine ⟨(m1Clean_props cl₁).1, ⟨hcl₁, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [HonestSession.t5_length])⟩, ?_⟩
    rw [(m1Clean_props cl₁).2.2.1]
    exact ⟨m2Clean_preCond cl₁, trivial, trivial⟩
  · intro i j si sj p k b hij hmi hmj hli _ hlj
    rcases i with _ | _ | _ | i
    · simp only [ssClean3, List.getElem?_cons_zero, Option.some.injEq] at hmi; subst hmi; cases hli
    · rcases j with _ | _ | _ | j <;> try omega
      · simp only [ssClean3, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmj
        subst hmj; cases hlj
      · simp [ssClean3] at hmj
    · simp only [ssClean3, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi; cases hli
    · simp [ssClean3] at hmi

/-! ## 3. Closed-Form Projections & `Explains` on `(ssClean3, visClean3)` -/

theorem storedSecrets_t7Clean (cl₁ : Nat) : storedSecrets (t7Clean cl₁) = pqSecrets7003 := by
  have hc : storedSecrets (t7Clean cl₁) = storedSecrets (t6Clean cl₁) := by
    unfold t7Clean bobTr0; simp only [storedSecrets_append]; repeat erw [List.append_nil]
  exact hc.trans (storedSecrets_t6Clean cl₁)

theorem storedStates_t7Clean {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    storedStates r (t7Clean cl₁) =
      [⟨"alice", stA0Pure⟩, ⟨"alice", stA1Pure cl₁⟩, ⟨"bob", stB1Pure cl₁⟩] := by
  have ht4 : (setupTrace r).length = 22 := by
    rw [setupTrace_eq_t4 ha hb hopk, HonestSession.t4_length]
  unfold t7Clean bobTr0; dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, ht4, t6Clean_length]; omega)]
  rw [storedStates_t6Clean ha hb hopk]
  rfl

theorem honestSaltsOf_ssClean3 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    honestSaltsOf r (ssClean3 cl₁) = [DY.Spqr.zeroKey, key0Pure] := by
  have h2 := honestSaltsOf_ssClean2 ha hb hopk cl₁
  unfold honestSaltsOf ssClean2 at h2
  unfold honestSaltsOf ssClean3
  dsimp only [honestKeysOf, m2Clean] at h2 ⊢
  rwa [List.append_nil]

theorem plaintextTerms_visClean3 (cl₁ : Nat) :
    plaintextTerms (visClean3 cl₁) = [tRnd 31 32] := by
  unfold plaintextTerms visClean3
  rw [List.filter_append, List.flatMap_append, vis_m2Clean]
  have hnil : ([⟨.recv, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeyRecv, none⟩,
       rngEntry (randTerm 38 32),
       ⟨.accept, [tRnd 31 32], .single,
         DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone
           (t6Clean cl₁) (t7Clean cl₁)⟩].filter (·.kind == .pt)) = [] := rfl
  rw [hnil, List.flatMap_nil, List.append_nil]
  exact plaintextTerms_visClean2 cl₁

theorem sendTerms_visClean3 (cl₁ : Nat) :
    (((visClean3 cl₁).filter (·.kind == .send)).flatMap (·.terms)) =
      [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁] := by
  unfold visClean3
  rw [List.filter_append, List.flatMap_append, vis_m2Clean]
  have hnil : ([⟨.recv, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeyRecv, none⟩,
       rngEntry (randTerm 38 32),
       ⟨.accept, [tRnd 31 32], .single,
         DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone
           (t6Clean cl₁) (t7Clean cl₁)⟩].filter (·.kind == .send)) = [] := rfl
  rw [hnil, List.flatMap_nil, List.append_nil]
  exact sendTerms_visClean2 cl₁

theorem noSkippedKeys_t7Clean (cl₁ : Nat) : NoSkippedKeys (t7Clean cl₁) := by
  have ht4 : HonestSession.t4 = b1_setupTr4 "alice" "bob" :=
    setupTrace_false_eq.symm.trans (Symbolic.Swarm.CREF.b1_setupTrace_eq r0 (by show "alice" ≠ "bob"; decide))
  unfold t7Clean t6Clean HonestSession.t5
  refine noSkippedKeys_bobTr0 (noSkippedKeys_encTrCl (noSkippedKeys_aliceTr ?_))
  rw [ht4]; exact noSkippedKeys_setupTr4

theorem bobDoneBaseKeys_t6Clean (cl₁ : Nat) : bobDoneBaseKeys (t6Clean cl₁) = [] := by
  have ht4 : HonestSession.t4 = b1_setupTr4 "alice" "bob" :=
    setupTrace_false_eq.symm.trans (Symbolic.Swarm.CREF.b1_setupTrace_eq r0 (by show "alice" ≠ "bob"; decide))
  unfold t6Clean HonestSession.t5
  rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B.encTrCl_bobDone_eq,
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B.aliceTr_bobDone_eq, ht4,
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003.setupTr4_bobDone_nil]

theorem pendingPreKey_t7Clean_46 (cl₁ : Nat) :
    DY.Libsignal.Composed.Refinement.pendingPreKey (t7Clean cl₁) 46 = none := by
  unfold DY.Libsignal.Composed.Refinement.pendingPreKey DY.ExecTrace.getLocalStateAt
  rw [t7Clean_at_46_stB1]
  dsimp only [Option.map, StT]
  have hdec : DY.Libsignal.Composed.Refinement.sessionHasDecrypted
      (t7Clean cl₁) ((stB1Pure cl₁).sessionInfo "bob") 46 = true := by
    unfold DY.Libsignal.Composed.Refinement.sessionHasDecrypted
    refine List.any_eq_true.mpr ⟨45, List.mem_range.mpr (by decide), ?_⟩
    rw [t7Clean_trEvent_eq cl₁ 45 (by decide), if_pos' rfl]
    exact decide_eq_true rfl
  rw [hdec]; rfl

theorem runMatches_clean2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    RunMatches compI7003 r S (gClean7003 mode cl₁ cl₃)
      ((m1Clean cl₁).next ((m0Of false).next (setupTrace r))) m2Clean (ev2Of mode)
      (stepView m2Clean (t6Clean cl₁) true) (some (none, 7#32, 9#32)) := by
  let g := gClean7003 mode cl₁ cl₃
  have cn := mkCommonNodes (mode := mode) (S := S) (pts := [tRnd 31 32]) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem2
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  have htr2 : (m1Clean cl₁).next ((m0Of false).next (setupTrace r)) = t6Clean cl₁ := by
    rw [setupTrace_eq_t4 ha hb hopk, m0_next_false, (m1Clean_props cl₁).2.2.1]
  have hx := xClean_mem mode cl₁ cl₃ hf hkpk hsem2
  rw [runTrace_ssClean2 ha hb hopk] at hx
  have hin2 : (ev2Of mode).input = out1Of mode := by
    cases mode with
    | false => dsimp [ev2Of, ev2_m1, out1Of]; exact out1M1Raw_eq
    | true => dsimp [ev2Of, ev2_m2, out1Of]; exact out1M2Raw_eq
  let inp2 : VisEntry := ⟨.recv, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeyRecv, none⟩
  let drs2 : List VisEntry := [rngEntry (randTerm 38 32)]
  let out2 : VisEntry :=
    ⟨.accept, [tRnd 31 32], .single,
      DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone
        (t6Clean cl₁) (t7Clean cl₁)⟩
  refine ⟨rfl, by cases mode <;> rfl, by cases mode <;> trivial, ha.symm,
    by rw [htr2]; exact m2Clean_ok cl₁,
    by cases mode with | false => exact ⟨pt1M1Raw, rfl⟩ | true => exact ⟨pt1M2Raw, rfl⟩,
    by rw [htr2, vis_m2Clean cl₁ (DY.Libsignal.Composed.Refinement.runWrapped (ev2Of mode)), vis_m2Clean cl₁ true],
    inp2, drs2, [out2], by rw [vis_m2Clean]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by cases mode <;> rfl, ?_⟩
    rw [hin2]
    refine ⟨hx.2.2.2.1, p1Of mode, parse_out1Of mode, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases mode <;> decide +kernel
  · have hc_eq : (ev2Of mode).coins = coins2Bytes := by
      cases mode with | false => exact coins2Raw_eq | true => exact coins2Raw_eq
    refine ⟨[bytesOf dhsBId], fun p hp => by rcases List.mem_singleton.mp hp with rfl; decide,
      by rw [hc_eq]; decide +kernel, List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil⟩
    dsimp only [rngEntry, List.map]
    exact congrArg (· :: []) (gamma_of_termAt cn.dhsB)
  · have hm0_gam : gamma compI7003 S g (tRnd 31 32) = (if mode then pt1M2Bytes else pt1M1Bytes) :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_randTerm_pos S g 31 32 (by decide)
    cases mode
    · dsimp only [OutputsMatch, ev2Of, ev2_m1]; rw [pt1M1Raw_eq]
      exact ⟨out2, rfl, rfl, congrArg (· :: []) hm0_gam⟩
    · dsimp only [OutputsMatch, ev2Of, ev2_m2]; rw [pt1M2Raw_eq]
      exact ⟨out2, rfl, rfl, congrArg (· :: []) hm0_gam⟩
  · rw [htr2, hin2]; exact hx
  · rw [htr2]; dsimp only [DY.Libsignal.Composed.Refinement.PathFaithfulAt, m2Clean]
    intro p _ ⟨ek, hek, _⟩; rw [bobDoneBaseKeys_t6Clean] at hek; cases hek

theorem explains_clean3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g₀ ss₀ vis₀ [.run ev0, .run (ev1Of mode), .run (ev2Of mode)])
    (hsem2 : SemPinned2 S cl₁) :
    Explains compI7003 r S (gClean7003 mode cl₁ cl₃) (ssClean3 cl₁) (visClean3 cl₁)
      [.run ev0, .run (ev1Of mode), .run (ev2Of mode)] := by
  obtain ⟨hgc, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 mode cl₁ cl₃ hf hex.1
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  refine ⟨hgc, ghostWF_clean3 mode cl₁ cl₃, modelRunWF_clean3 ha hb hopk cl₁ hsem2.1, ?_⟩
  unfold DY.Libsignal.Composed.Refinement.MatchesEvents ssClean3
  have hnb1 : DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) (ev1Of mode) =
      some (none, 7#32, 9#32) := by cases mode <;> rfl
  have hnil : MatchesEventsAt compI7003 r S (gClean7003 mode cl₁ cl₃)
      (DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) (ev2Of mode))
      (m2Clean.next ((m1Clean cl₁).next ((m0Of false).next (setupTrace r)))) [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h2 := matchesEvents_run1 (runMatches_clean2 mode cl₁ cl₃ hf hkpk hsem2) hnil
  rw [List.append_nil, ← hnb1] at h2
  have h1 := matchesEvents_run1 (runMatches_clean1 mode cl₁ cl₃ hf hkpk hsem2) h2
  rw [← ev0_nextBundleIds] at h1
  simpa [visClean3, visClean2, List.append_assoc] using
    matchesEvents_run1 (runMatches_clean0 mode cl₁ cl₃ hf hgc hkpk hsem2) h1

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003
