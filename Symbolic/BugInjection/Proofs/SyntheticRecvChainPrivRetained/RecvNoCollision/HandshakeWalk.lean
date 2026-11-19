/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.ShaMacLaws
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagTermAt
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
public import Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

/-!
# Setup Normalization and Handshake DAG Walk (`HandshakeWalk.lean`)

Provides:
1. Reduction of any `r : ProtocolSetup` satisfying `rcprCompFitsPinned` to `r0`, plus
   `not_implicitReject_o1`.
2. Certified `decide +kernel`-backed `TermAt` builders, `handshake_termAt`, and
   `pqSecrets_safeMemo` from `SetupAndCall0Pinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes ExecTrace Trace)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH
  (PQXDHState serializedIk agree pqxdhIkm pqxdhKdf pqxdhLabel discontinuity)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg lit litByte zeroSalt createChain kdfRk)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields PreKeyRep Step
   setupTrace setupRandoms setupSent setupSecret setupPublic secretBytes runTrace
   storedStates availableStates ownKeys principalTerms prefixTerms honestSaltsOf
   whisperTrials bobTrials MemoCollisionOn RecvCollisionOn
   BobSessionStartCollidesOrImplicitRejectsOn randTerm litOf gamma' gamma)
open Symbolic.BugInjection (fillFresh)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB bh1 t4 t5 o1 keys1 dhsA stA0 t5_runs)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (serialize_local_pqxdh_eq_bridge slowString_serialize_eq slowNat_serialize_succ
   slowNat_serialize_zero concatPrefixes_cons concatPrefixes_nil
   alice_utf8_sizes bob_utf8_sizes)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue (bool_serialize_singleton_head)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprI0 rcprHooks0 rcprRecordsI0 rcprCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs
  (DagOp dagOpBytesOk dagNodeOk SafeMemo TermAt)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagTermAt
  (termAt_lit termAt_litOf randTerm_eq_dagShape termAt_rand termAt_concat
   termAt_dhPk termAt_dh termAt_dh_symm termAt_kdf termAt_trunc8
   termAt_kemEncap termAt_of_opaque safeMemo_kemPk)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
  (dagSize dagOp dagBytes dag_nodes_ok wmkInfo1Id wmkInfo2Id wmkInfo3Id)

/-! ## 1. Concrete `r0` Normalization and `ImplicitReject` Refutation -/

/-- Reference concrete `ProtocolSetup` of `rcprSetup` under `rcprI0`. -/
abbrev r0 : ProtocolSetup := rcprRecordsI0 rcprSetup

theorem r_alice_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : r.alice = "alice" :=
  hfit.1.2.2.2.1.1

theorem r_bob_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : r.bob = "bob" :=
  hfit.1.2.2.2.1.2

theorem r_withOpk_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : r.withOpk = false :=
  hfit.1.1.2.1

theorem r_secret3_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : secretBytes r 3 = fillFresh 11 64 :=
  hfit.1.2.2.1.1

theorem r_secret4_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : secretBytes r 4 = fillFresh 16 64 :=
  hfit.1.2.2.1.2.1

theorem r_secret5_eq {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) : secretBytes r 5 = fillFresh 17 64 :=
  hfit.1.2.2.1.2.2

theorem setupTrace_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    setupTrace r = setupTrace r0 := by
  unfold setupTrace
  rw [r_alice_eq hfit, r_bob_eq hfit, r_withOpk_eq hfit]
  rfl

theorem setupTrace_r0_eq_t4 : setupTrace r0 = t4 := by
  have h : setupTrace r0 = setupTrace Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.r0 := rfl
  rw [h]
  exact Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs.setupTrace_r0_eq

theorem runTrace_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (ss : List Step) :
    runTrace r ss = runTrace r0 ss := by
  unfold runTrace
  rw [setupTrace_eq_r0 hfit]

theorem storedStates_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (tr : ExecTrace) :
    storedStates r tr = storedStates r0 tr := by
  unfold storedStates
  rw [setupTrace_eq_r0 hfit]

theorem availableStates_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (tr : ExecTrace) :
    availableStates r tr = availableStates r0 tr := by
  unfold availableStates
  rw [storedStates_eq_r0 hfit]

theorem honestSaltsOf_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (ss : List Step) :
    honestSaltsOf r ss = honestSaltsOf r0 ss := by
  unfold honestSaltsOf
  rw [setupTrace_eq_r0 hfit]

theorem setupSecret_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (i : Nat) :
    setupSecret r i = setupSecret r0 i := by
  unfold setupSecret setupRandoms
  rw [setupTrace_eq_r0 hfit]

theorem setupPublic_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) (i : Nat) :
    setupPublic r i = setupPublic r0 i := by
  unfold setupPublic setupSent
  rw [setupTrace_eq_r0 hfit]

theorem principalTerms_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (tr : ExecTrace) (vis : List VisEntry) :
    principalTerms r tr vis = principalTerms r0 tr vis := by
  unfold principalTerms
  rw [storedStates_eq_r0 hfit]

theorem prefixTerms_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (tr : ExecTrace) (vis : List VisEntry) :
    prefixTerms r tr vis = prefixTerms r0 tr vis := by
  unfold prefixTerms
  rw [principalTerms_eq_r0 hfit]

theorem memoCollisionOn_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost) (known : Bytes → Prop)
    (tr : ExecTrace) (vis : List VisEntry) (newTerms newPts : List Bytes) :
    MemoCollisionOn i r S g known tr vis newTerms newPts ↔
      MemoCollisionOn i r0 S g known tr vis newTerms newPts := by
  unfold MemoCollisionOn
  rw [prefixTerms_eq_r0 hfit]

theorem ownKeys_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (tr : ExecTrace) (st : TRState) (msg : TRSignalMsg) :
    ownKeys r tr st msg = ownKeys r0 tr st msg := by
  unfold ownKeys
  rw [availableStates_eq_r0 hfit]

theorem whisperTrials_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (msg : TRSignalMsg) :
    whisperTrials i r S g tr msg = whisperTrials i r0 S g tr msg := by
  unfold whisperTrials
  simp only [availableStates_eq_r0 hfit, ownKeys_eq_r0 hfit]

theorem bobTrials_eq_r0 {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep) (msg : TRSignalMsg) :
    bobTrials r tr p x msg = bobTrials r0 tr p x msg := by
  have hopk : r.withOpk = false := r_withOpk_eq hfit
  have hopk0 : r0.withOpk = false := rfl
  unfold bobTrials ProtocolSetup.opkSecTerm ProtocolSetup.ikAPubTerm ProtocolSetup.spkSecTerm ProtocolSetup.pqskSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.ikBPubTerm
  rw [hopk, hopk0]
  cases p.preKeyId <;>
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.all_none,
      setupPublic_eq_r0 hfit, setupSecret_eq_r0 hfit]

theorem bobSessionStartCollides_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List Bytes)
    (p : PreKeyFields) (x : PreKeyRep) :
    BobSessionStartCollidesOrImplicitRejectsOn i r S g tr vis salts p x ↔
      BobSessionStartCollidesOrImplicitRejectsOn i r0 S g tr vis salts p x := by
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  cases DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg with
  | none => exact memoCollisionOn_eq_r0 hfit S g _ tr vis [x.ek, x.ct, x.msg] []
  | some msg =>
    dsimp only
    rw [bobTrials_eq_r0 hfit, memoCollisionOn_eq_r0 hfit]

theorem recvCollisionOn_eq_r0 {i : ExternInterpretation} {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (tr : ExecTrace) (vis : List VisEntry) (salts : List Bytes) (t : Bytes) :
    RecvCollisionOn i r S g tr vis salts t ↔
      RecvCollisionOn i r0 S g tr vis salts t := by
  unfold RecvCollisionOn
  cases DY.Libsignal.TripleRatchet.parseTrSignalMsg t with
  | none => exact memoCollisionOn_eq_r0 hfit S g _ tr vis [t] []
  | some msg =>
    dsimp only
    rw [whisperTrials_eq_r0 hfit, memoCollisionOn_eq_r0 hfit]

theorem setupSecret_r0_4 : setupSecret r0 4 = pqskB :=
  Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy.setupSecret_4 (r := r0) (by decide)

theorem step0_next_t4 :
    (Step.aliceStart "alice" "bob" 4 6 bh1).next t4 = t5 := by
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.Composed.aliceStart.reachability ("alice", "bob", 4, 6, bh1) t4]
  exact t5_runs.2

theorem length_append {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem at?_append_of_lt {E1 E2 : Type} [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

theorem at?_append_self {E1 E2 : Type} [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

theorem getMessageSentAt_append_of_lt {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    (tr.append e).getMessageSentAt i = tr.getMessageSentAt i := by
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?,
    at?_append_of_lt tr e hi]

theorem getMessageSentAt_append_self (tr : ExecTrace) (b : Bytes) :
    (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE b)).getMessageSentAt tr.length =
      some b := by
  simp only [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?,
    at?_append_self]
  rfl

theorem t5_getMessageSentAt_25 : t5.getMessageSentAt 25 = some o1.ek := by
  unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]

theorem t5_getMessageSentAt_26 : t5.getMessageSentAt 26 = some o1.ct := by
  unfold t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [getMessageSentAt_append_of_lt _ _
    (by simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; omega)]
  convert getMessageSentAt_append_self _ _ using 2
  simp only [length_append, Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]

theorem getMessageSentAt_mono {t1 t2 : ExecTrace} {i : Nat} {m : Bytes}
    (hle : t1 ≤ t2) (h : t1.getMessageSentAt i = some m) :
    t2.getMessageSentAt i = some m := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?] at h ⊢
  have hle' := Trace.at?_le (EntryT := DY.Network.ExecEntryT) t1 t2 i hle
  cases hat : (t1.at? i : Option DY.Network.ExecEntryT) with
  | none => rw [hat] at h; cases h
  | some _ =>
    rw [hat] at h hle'
    rw [hle']
    exact h

/-! ## 2. Boolean `DagOp` Checkers, Handshake DAG Walk, and `pqSecretsList` -/

theorem dag_bytes_ok {id : Nat} (hid : id < dagSize) :
    dagOpBytesOk dagBytes id (dagOp id) = true := by
  have hn := dag_nodes_ok id hid
  unfold dagNodeOk at hn
  simp only [Bool.and_eq_true] at hn
  exact hn.1.2

def isKdfOp (op : DagOp) (a b : Nat) : Bool :=
  match op with | .kdf x y => decide (x = a) && decide (y = b) | _ => false

def isConcatOp (op : DagOp) (l r : Nat) : Bool :=
  match op with | .concat x y => decide (x = l) && decide (y = r) | _ => false

def isTrunc8Op (op : DagOp) (a : Nat) : Bool :=
  match op with | .trunc8 x => decide (x = a) | _ => false

def isLitOp (op : DagOp) (v : HwBytes) : Bool :=
  match op with | .lit x => decide (x = v) | _ => false

def isRandOp (op : DagOp) (ts len : Nat) : Bool :=
  match op with | .rand t l => decide (t = ts) && decide (l = len) | _ => false

def isDhPkOp (op : DagOp) (s : Nat) : Bool :=
  match op with | .dhPk x => decide (x = s) | _ => false

def isDhOp (op : DagOp) (a b : Nat) : Bool :=
  match op with | .dh x y => decide (x = a) && decide (y = b) | _ => false

def isKemEncapOp (op : DagOp) (pk ent : Nat) : Bool :=
  match op with | .kemEncap p e => decide (p = pk) && decide (e = ent) | _ => false

def isKemSSOp (op : DagOp) (pk ent : Nat) : Bool :=
  match op with | .kemSS p e => decide (p = pk) && decide (e = ent) | _ => false

def checkDhRand (s1 pk1 s2 pk2 id ts1 ts2 : Nat) : Bool :=
  decide (id < dagSize) && decide (s1 < dagSize) && decide (s2 < dagSize) &&
  isDhOp (dagOp id) pk1 s2 &&
  isDhPkOp (dagOp pk1) s1 &&
  isDhPkOp (dagOp pk2) s2 &&
  isRandOp (dagOp s1) ts1 32 &&
  isRandOp (dagOp s2) ts2 32

def isSymEncPtOp (op : DagOp) (ck iv ptTs : Nat) (pt : HwBytes) : Bool :=
  match op with
  | .symEncPt c i t p => decide (c = ck) && decide (i = iv) && decide (t = ptTs) && decide (p = pt)
  | _ => false

def isTrWireOp (op : DagOp) (ver : UInt8) (rk : Nat) (cnt prev : UInt32)
    (ct pq : Nat) (addr : HwBytes) : Bool :=
  match op with
  | .trWire v r c p ct' pq' ad =>
    decide (v = ver) && decide (r = rk) && decide (c = cnt) && decide (p = prev) &&
    decide (ct' = ct) && decide (pq' = pq) && decide (ad = addr)
  | _ => false

theorem kdf_of_isKdfOp {op : DagOp} {a b : Nat} (h : isKdfOp op a b = true) :
    op = .kdf a b := by
  cases op <;> simp [isKdfOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem concat_of_isConcatOp {op : DagOp} {l r : Nat} (h : isConcatOp op l r = true) :
    op = .concat l r := by
  cases op <;> simp [isConcatOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

theorem trunc8_of_isTrunc8Op {op : DagOp} {a : Nat} (h : isTrunc8Op op a = true) :
    op = .trunc8 a := by
  cases op <;> simp [isTrunc8Op] at h; subst h; rfl

theorem lit_of_isLitOp {op : DagOp} {v : HwBytes} (h : isLitOp op v = true) :
    op = .lit v := by
  cases op <;> simp [isLitOp] at h; subst h; rfl

theorem termAt_strLit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {s : String} {id : Nat} (hid : id < dagSize)
    (hop : isLitOp (dagOp id) (DY.Libsignal.Composed.Refinement.ofByteArray s.toList.utf8Encode) = true) :
    TermAt dagSize dagOp dagBytes S g pts (lit s) id := by
  have hs : s.toUTF8 = s.toList.utf8Encode := by
    conv_lhs => rw [← String.ofList_toList (s := s)]
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  exact termAt_lit dag_nodes_ok hid (by rw [hs]; exact lit_of_isLitOp hop)

theorem wmkInfo_termAt (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) :
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 1)) wmkInfo1Id ∧
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 2)) wmkInfo2Id ∧
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 3)) wmkInfo3Id := by
  have hl : TermAt dagSize dagOp dagBytes S g pts (lit "WhisperMessageKeys") 11 :=
    termAt_strLit (by decide) (by decide +kernel)
  have hb1 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  have hb2 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  have hb3 : TermAt dagSize dagOp dagBytes S g pts (litByte 3) 4 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  exact ⟨termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb1,
         termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb2,
         termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb3⟩

theorem termAt_lit_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ba : ByteArray} {id : Nat}
    (hok : (decide (id < dagSize) &&
      isLitOp (dagOp id) (DY.Libsignal.Composed.Refinement.ofByteArray ba)) = true) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Literal.literalToBytes ba) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isLitOp, h] at hop
  subst hop
  exact termAt_lit dag_nodes_ok hid h

theorem termAt_litOf_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {id : Nat} (hid : id < dagSize) (hop : isLitOp (dagOp id) (dagBytes id) = true) :
    TermAt dagSize dagOp dagBytes S g pts (litOf (dagBytes id)) id := by
  cases h : dagOp id <;> simp [isLitOp, h] at hop
  exact termAt_litOf dag_nodes_ok hid (h.trans (congrArg DagOp.lit hop))

theorem termAt_rand_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ts len id : Nat} (hsig : g.σ ts len = dagBytes id)
    (hok : (decide (id < dagSize) && isRandOp (dagOp id) ts len) = true) :
    TermAt dagSize dagOp dagBytes S g pts (rnd ts len) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isRandOp, h] at hop
  obtain ⟨rfl, rfl⟩ := hop
  exact termAt_rand dag_nodes_ok hid h hsig

theorem termAt_concat_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {a b : Bytes} {la rb id : Nat}
    (hok : (decide (id < dagSize) && isConcatOp (dagOp id) la rb) = true)
    (ha : TermAt dagSize dagOp dagBytes S g pts a la)
    (hb : TermAt dagSize dagOp dagBytes S g pts b rb) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat a b) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isConcatOp, h] at hop
  obtain ⟨rfl, rfl⟩ := hop
  exact termAt_concat dag_nodes_ok hid h ha hb

theorem termAt_dhPk_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {sk : Bytes} {s id : Nat}
    (hok : (decide (id < dagSize) && isDhPkOp (dagOp id) s) = true)
    (hs : TermAt dagSize dagOp dagBytes S g pts sk s) :
    TermAt dagSize dagOp dagBytes S g pts (dhPk sk) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isDhPkOp, h] at hop
  subst hop
  exact termAt_dhPk dag_nodes_ok hid h hs

private theorem unpack_checkDhRand {s1 pk1 s2 pk2 id ts1 ts2 : Nat}
    (hok : checkDhRand s1 pk1 s2 pk2 id ts1 ts2 = true) :
    id < dagSize ∧ s1 < dagSize ∧ s2 < dagSize ∧
    dagOp id = .dh pk1 s2 ∧ dagOp pk1 = .dhPk s1 ∧ dagOp pk2 = .dhPk s2 ∧
    dagOp s1 = .rand ts1 32 ∧ dagOp s2 = .rand ts2 32 := by
  unfold checkDhRand at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hid, hs1⟩, hs2⟩, hd⟩, hpk1⟩, hpk2⟩, hr1⟩, hr2⟩ := hok
  have hd' : dagOp id = .dh pk1 s2 := by
    cases h : dagOp id <;> simp [isDhOp, h] at hd; obtain ⟨rfl, rfl⟩ := hd; rfl
  have hpk1' : dagOp pk1 = .dhPk s1 := by
    cases h : dagOp pk1 <;> simp [isDhPkOp, h] at hpk1; subst hpk1; rfl
  have hpk2' : dagOp pk2 = .dhPk s2 := by
    cases h : dagOp pk2 <;> simp [isDhPkOp, h] at hpk2; subst hpk2; rfl
  have hr1' : dagOp s1 = .rand ts1 32 := by
    cases h : dagOp s1 <;> simp [isRandOp, h] at hr1; obtain ⟨rfl, rfl⟩ := hr1; rfl
  have hr2' : dagOp s2 = .rand ts2 32 := by
    cases h : dagOp s2 <;> simp [isRandOp, h] at hr2; obtain ⟨rfl, rfl⟩ := hr2; rfl
  exact ⟨hid, hs1, hs2, hd', hpk1', hpk2', hr1', hr2'⟩

theorem termAt_dh_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {s1 pk1 s2 pk2 id ts1 ts2 : Nat}
    (hok : checkDhRand s1 pk1 s2 pk2 id ts1 ts2 = true)
    (hs1 : TermAt dagSize dagOp dagBytes S g pts (rnd ts1 32) s1)
    (hp1 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts1 32)) pk1)
    (hs2 : TermAt dagSize dagOp dagBytes S g pts (rnd ts2 32) s2)
    (hp2 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts2 32)) pk2) :
    TermAt dagSize dagOp dagBytes S g pts (DY.DiffieHellman.dh (dhPk (rnd ts1 32)) (rnd ts2 32)) id := by
  obtain ⟨hid, hs1_lt, hs2_lt, hd, hpk1, hpk2, hr1, hr2⟩ := unpack_checkDhRand hok
  exact termAt_dh dag_nodes_ok hid hd hpk1 hpk2
    (randTerm_eq_dagShape dag_nodes_ok hs1_lt hr1)
    (randTerm_eq_dagShape dag_nodes_ok hs2_lt hr2)
    hs1 hp1 hs2 hp2

theorem termAt_dh_symm_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {s1 pk1 s2 pk2 id ts1 ts2 : Nat}
    (hok : checkDhRand s1 pk1 s2 pk2 id ts1 ts2 = true)
    (hs1 : TermAt dagSize dagOp dagBytes S g pts (rnd ts1 32) s1)
    (hp1 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts1 32)) pk1)
    (hs2 : TermAt dagSize dagOp dagBytes S g pts (rnd ts2 32) s2)
    (hp2 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts2 32)) pk2) :
    TermAt dagSize dagOp dagBytes S g pts (DY.DiffieHellman.dh (dhPk (rnd ts2 32)) (rnd ts1 32)) id := by
  obtain ⟨hid, hs1_lt, hs2_lt, hd, hpk1, hpk2, hr1, hr2⟩ := unpack_checkDhRand hok
  exact termAt_dh_symm dag_nodes_ok hid hd hpk1 hpk2
    (randTerm_eq_dagShape dag_nodes_ok hs1_lt hr1)
    (randTerm_eq_dagShape dag_nodes_ok hs2_lt hr2)
    hs1 hp1 hs2 hp2

theorem termAt_kdf_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salt ikm : Bytes} {s i id : Nat}
    (hok : (decide (id < dagSize) && isKdfOp (dagOp id) s i) = true)
    (hs : TermAt dagSize dagOp dagBytes S g pts salt s)
    (hi : TermAt dagSize dagOp dagBytes S g pts ikm i) :
    TermAt dagSize dagOp dagBytes S g pts (DY.KdfExtract.kdfExtract salt ikm) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isKdfOp, h] at hop
  obtain ⟨rfl, rfl⟩ := hop
  exact termAt_kdf dag_nodes_ok hid h hs hi

theorem termAt_trunc8_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {m : Bytes} {a id : Nat}
    (hok : (decide (id < dagSize) && isTrunc8Op (dagOp id) a) = true)
    (hm : TermAt dagSize dagOp dagBytes S g pts m a) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Trunc.trunc8 m) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hid, hop⟩ := hok
  cases h : dagOp id <;> simp [isTrunc8Op, h] at hop
  subst hop
  exact termAt_trunc8 dag_nodes_ok hid h hm

theorem termAt_kemEncap_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {pk e : Bytes} {p_id e_id id1 id2 : Nat}
    (hok : (decide (id1 < dagSize) && isKemEncapOp (dagOp id1) p_id e_id &&
            decide (id2 < dagSize) && isKemSSOp (dagOp id2) p_id e_id) = true)
    (hp : TermAt dagSize dagOp dagBytes S g pts pk p_id)
    (he : TermAt dagSize dagOp dagBytes S g pts e e_id) :
    TermAt dagSize dagOp dagBytes S g pts (kemEncap pk e).1 id1 ∧
      TermAt dagSize dagOp dagBytes S g pts (kemEncap pk e).2 id2 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hid1, hop1⟩, hid2⟩, hop2⟩ := hok
  have hop1' : dagOp id1 = .kemEncap p_id e_id := by
    cases h : dagOp id1 <;> simp [isKemEncapOp, h] at hop1; obtain ⟨rfl, rfl⟩ := hop1; rfl
  have hop2' : dagOp id2 = .kemSS p_id e_id := by
    cases h : dagOp id2 <;> simp [isKemSSOp, h] at hop2; obtain ⟨rfl, rfl⟩ := hop2; rfl
  exact termAt_kemEncap dag_nodes_ok hid1 hop1' hid2 hop2' hp he

theorem norm_dhPk (a : Bytes) :
    DY.X25519.normalizeX25519Key (dhPk a) = dhPk a := by
  dsimp only [DY.X25519.normalizeX25519Key, DY.DiffieHellman.dhPk,
    DY.DiffieHellman.instCanDHBytes]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

theorem agree_dhPk (pkSk sk : Bytes) :
    agree (dhPk pkSk) sk = DY.DiffieHellman.dh (dhPk pkSk) sk := by
  unfold agree; rw [norm_dhPk]

theorem createChain_dhPk (rk pkSk sk : Bytes) :
    createChain rk (dhPk pkSk) sk = kdfRk rk (DY.DiffieHellman.dh (dhPk pkSk) sk) := by
  unfold createChain; rw [agree_dhPk]

/-- Setup and Call 0 (`aliceStart`) ghost coins and public Kyber outputs pinned to `dagBytes`. -/
structure SetupAndCall0Pinned (S : OpaqueSymbolSemantics) (g : Ghost) : Prop where
  sig0  : g.σ 0 32 = dagBytes 21
  sig5  : g.σ 5 32 = dagBytes 22
  sig10 : g.σ 10 32 = dagBytes 23
  sig11 : g.σ 11 64 = dagBytes 24
  sig16 : g.σ 16 64 = dagBytes 25
  sig17 : g.σ 17 64 = dagBytes 26
  sig22 : g.σ 22 32 = dagBytes 65
  sig23 : g.σ 23 32 = dagBytes 66
  sig24 : g.σ 24 32 = dagBytes 67
  pqpk  : gamma rcprI0 S g (kemPk (randTerm 16 64)) = dagBytes 71
  ek0   : gamma rcprI0 S g o1.ek = dagBytes 68
  ct0   : gamma rcprI0 S g o1.ct = dagBytes 73

/-- Certified `TermAt` bundle for all setup and Call 0 handshake terms. -/
structure HandshakeAt (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) : Prop where
  t_ikA : TermAt dagSize dagOp dagBytes S g pts ikA 21
  t_ikB : TermAt dagSize dagOp dagBytes S g pts ikB 22
  t_spkB : TermAt dagSize dagOp dagBytes S g pts spkB 23
  t_pqskB : TermAt dagSize dagOp dagBytes S g pts pqskB 25
  t_r22 : TermAt dagSize dagOp dagBytes S g pts (rnd 22 32) 65
  t_dhsA : TermAt dagSize dagOp dagBytes S g pts dhsA 67
  pk0 : TermAt dagSize dagOp dagBytes S g pts (dhPk ikA) 27
  pk1 : TermAt dagSize dagOp dagBytes S g pts (dhPk ikB) 28
  pk2 : TermAt dagSize dagOp dagBytes S g pts (dhPk spkB) 29
  ek : TermAt dagSize dagOp dagBytes S g pts o1.ek 68
  pk4 : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsA) 69
  ik0s : TermAt dagSize dagOp dagBytes S g pts (serializedIk (dhPk ikA)) 30
  ik1s : TermAt dagSize dagOp dagBytes S g pts (serializedIk (dhPk ikB)) 31
  ct : TermAt dagSize dagOp dagBytes S g pts o1.ct 73
  rk_init : TermAt dagSize dagOp dagBytes S g pts keys1.rk 83
  ck_init : TermAt dagSize dagOp dagBytes S g pts keys1.ck 85
  pqr : TermAt dagSize dagOp dagBytes S g pts keys1.pqr 87
  stA0_rk : TermAt dagSize dagOp dagBytes S g pts stA0.rk 93
  stA0_cks : TermAt dagSize dagOp dagBytes S g pts stA0.cks 95
  stA0_sid : TermAt dagSize dagOp dagBytes S g pts stA0.sid 88

theorem termAt_kemPk_pqskB {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (hb : SetupAndCall0Pinned S g) :
    TermAt dagSize dagOp dagBytes S g pts (kemPk pqskB) 71 := by
  have hpqsk : TermAt dagSize dagOp dagBytes S g pts pqskB 25 :=
    termAt_rand_b hb.sig16 (by decide +kernel)
  have hsh : (gamma' rcprI0 S g (kemPk pqskB)).shape = litOf (dagBytes 71) := by
    have hg : gamma rcprI0 S g (kemPk pqskB) = dagBytes 71 := hb.pqpk
    unfold gamma at hg
    unfold gamma' at hg ⊢
    dsimp only [DY.PQKem.kemPk, DY.PQKem.instCanPQKemBytes] at hg ⊢
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemPk S)
      (DY.Libsignal.Composed.Refinement.concretizeAll rcprI0 S g)] at hg ⊢
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeKemPk,
      DY.Libsignal.Composed.Refinement.opaqueNode,
      DY.Libsignal.Composed.Refinement.node] at hg ⊢
    rw [hg]
  have hop71 : dagOp 71 = .lit (dagBytes 71) := by
    have h : isLitOp (dagOp 71) (dagBytes 71) = true := by decide +kernel
    cases hd : dagOp 71 <;> simp [isLitOp, hd] at h
    subst h; rfl
  exact termAt_of_opaque dag_nodes_ok (by decide) hop71 hb.pqpk hsh (safeMemo_kemPk hpqsk.safeMemo)

theorem handshake_termAt {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (hb : SetupAndCall0Pinned S g) : HandshakeAt S g pts := by
  have tikA : TermAt dagSize dagOp dagBytes S g pts ikA 21 :=
    termAt_rand_b hb.sig0 (by decide +kernel)
  have tikB : TermAt dagSize dagOp dagBytes S g pts ikB 22 :=
    termAt_rand_b hb.sig5 (by decide +kernel)
  have tspkB : TermAt dagSize dagOp dagBytes S g pts spkB 23 :=
    termAt_rand_b hb.sig10 (by decide +kernel)
  have tpqskB : TermAt dagSize dagOp dagBytes S g pts pqskB 25 :=
    termAt_rand_b hb.sig16 (by decide +kernel)
  have tr22 : TermAt dagSize dagOp dagBytes S g pts (rnd 22 32) 65 :=
    termAt_rand_b hb.sig22 (by decide +kernel)
  have tr23 : TermAt dagSize dagOp dagBytes S g pts (rnd 23 32) 66 :=
    termAt_rand_b hb.sig23 (by decide +kernel)
  have tdhsA : TermAt dagSize dagOp dagBytes S g pts dhsA 67 :=
    termAt_rand_b hb.sig24 (by decide +kernel)
  have tpk0 := termAt_dhPk_b (id := 27) (by decide +kernel) tikA
  have tpk1 := termAt_dhPk_b (id := 28) (by decide +kernel) tikB
  have tpk2 := termAt_dhPk_b (id := 29) (by decide +kernel) tspkB
  have hek_eq : o1.ek = dhPk (rnd 22 32) := by
    dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; rfl
  have tek : TermAt dagSize dagOp dagBytes S g pts o1.ek 68 := by
    rw [hek_eq]; exact termAt_dhPk_b (id := 68) (by decide +kernel) tr22
  have tpk4 := termAt_dhPk_b (id := 69) (by decide +kernel) tdhsA
  have tb05 : TermAt dagSize dagOp dagBytes S g pts (litByte 5) 5 := termAt_lit_b (by decide +kernel)
  have tik0s := termAt_concat_b (id := 30) (by decide +kernel) tb05 tpk0
  have tik1s := termAt_concat_b (id := 31) (by decide +kernel) tb05 tpk1
  have tpqpk := termAt_kemPk_pqskB (pts := pts) hb
  have hkem := termAt_kemEncap_b (id1 := 73) (id2 := 74) (by decide +kernel) tpqpk tr23
  have hct_eq : o1.ct = (kemEncap (kemPk pqskB) (rnd 23 32)).1 := by
    dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]; rfl
  have tct : TermAt dagSize dagOp dagBytes S g pts o1.ct 73 := hct_eq ▸ hkem.1
  have tss : TermAt dagSize dagOp dagBytes S g pts (kemEncap (kemPk pqskB) (rnd 23 32)).2 74 := hkem.2
  have hkeys_eq : keys1 = pqxdhKdf (pqxdhIkm
      (DY.DiffieHellman.dh (dhPk spkB) ikA)
      (DY.DiffieHellman.dh (dhPk ikB) (rnd 22 32))
      (DY.DiffieHellman.dh (dhPk spkB) (rnd 22 32))
      none (kemEncap (kemPk pqskB) (rnd 23 32)).2) := by
    dsimp only [keys1, o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [Symbolic.Proofs.Tests.Shared.Composed.HonestSession.t4_length]
    dsimp only [Option.map]
    rw [agree_dhPk, agree_dhPk, agree_dhPk]; rfl
  have tdh02 := termAt_dh_symm_b (id := 75) (by decide +kernel) tikA tpk0 tspkB tpk2
  have tdh13 := termAt_dh_b (id := 76) (by decide +kernel) tikB tpk1 tr22 (hek_eq ▸ tek)
  have tdh23 := termAt_dh_b (id := 77) (by decide +kernel) tspkB tpk2 tr22 (hek_eq ▸ tek)
  have tc3 := termAt_concat_b (id := 78) (by decide +kernel) tdh23 tss
  have tc2 := termAt_concat_b (id := 79) (by decide +kernel) tdh13 tc3
  have tc1 := termAt_concat_b (id := 80) (by decide +kernel) tdh02 tc2
  have tdisc : TermAt dagSize dagOp dagBytes S g pts discontinuity 7 := termAt_lit_b (by decide +kernel)
  have tikm := termAt_concat_b (id := 81) (by decide +kernel) tdisc tc1
  have tz32 : TermAt dagSize dagOp dagBytes S g pts zeroSalt 8 := termAt_lit_b (by decide +kernel)
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (by decide +kernel)
  have tb03 : TermAt dagSize dagOp dagBytes S g pts (litByte 3) 4 := termAt_lit_b (by decide +kernel)
  have tpqlbl : TermAt dagSize dagOp dagBytes S g pts pqxdhLabel 12 :=
    termAt_strLit (by decide) (by decide +kernel)
  have tpqi1 := termAt_concat_b (id := 18) (by decide +kernel) tpqlbl tb01
  have tpqi2 := termAt_concat_b (id := 19) (by decide +kernel) tpqlbl tb02
  have tpqi3 := termAt_concat_b (id := 20) (by decide +kernel) tpqlbl tb03
  have tprk := termAt_kdf_b (id := 82) (by decide +kernel) tz32 tikm
  have trk0 := termAt_kdf_b (id := 83) (by decide +kernel) tprk tpqi1
  have ti2_pq := termAt_concat_b (id := 84) (by decide +kernel) trk0 tpqi2
  have tck0 := termAt_kdf_b (id := 85) (by decide +kernel) tprk ti2_pq
  have ti3_pq := termAt_concat_b (id := 86) (by decide +kernel) tck0 tpqi3
  have tpqr0 := termAt_kdf_b (id := 87) (by decide +kernel) tprk ti3_pq
  have trk_k1 : TermAt dagSize dagOp dagBytes S g pts keys1.rk 83 := hkeys_eq ▸ trk0
  have tck_k1 : TermAt dagSize dagOp dagBytes S g pts keys1.ck 85 := hkeys_eq ▸ tck0
  have tpqr_k1 : TermAt dagSize dagOp dagBytes S g pts keys1.pqr 87 := hkeys_eq ▸ tpqr0
  have twrlbl : TermAt dagSize dagOp dagBytes S g pts (lit "WhisperRatchet") 10 :=
    termAt_strLit (by decide) (by decide +kernel)
  have twri1 := termAt_concat_b (id := 16) (by decide +kernel) twrlbl tb01
  have twri2 := termAt_concat_b (id := 17) (by decide +kernel) twrlbl tb02
  have tdh24 := termAt_dh_b (id := 91) (by decide +kernel) tspkB tpk2 tdhsA tpk4
  have tprkA := termAt_kdf_b (id := 92) (by decide +kernel) trk_k1 tdh24
  have trkA := termAt_kdf_b (id := 93) (by decide +kernel) tprkA twri1
  have ti2A := termAt_concat_b (id := 94) (by decide +kernel) trkA twri2
  have tcksA := termAt_kdf_b (id := 95) (by decide +kernel) tprkA ti2A
  have hstA0_cc : createChain keys1.rk o1.spk dhsA =
      kdfRk keys1.rk (DY.DiffieHellman.dh (dhPk spkB) dhsA) :=
    createChain_dhPk keys1.rk spkB dhsA
  have trk_stA0 : TermAt dagSize dagOp dagBytes S g pts stA0.rk 93 := by
    change TermAt dagSize dagOp dagBytes S g pts (createChain keys1.rk o1.spk dhsA).1 93
    rw [hstA0_cc]; exact trkA
  have tcks_stA0 : TermAt dagSize dagOp dagBytes S g pts stA0.cks 95 := by
    change TermAt dagSize dagOp dagBytes S g pts (createChain keys1.rk o1.spk dhsA).2 95
    rw [hstA0_cc]; exact tcksA
  have tsid_stA0 : TermAt dagSize dagOp dagBytes S g pts stA0.sid 88 :=
    termAt_concat_b (id := 88) (by decide +kernel) tpk4 trk_k1
  exact ⟨tikA, tikB, tspkB, tpqskB, tr22, tdhsA, tpk0, tpk1, tpk2, tek, tpk4,
    tik0s, tik1s, tct, trk_k1, tck_k1, tpqr_k1, trk_stA0, tcks_stA0, tsid_stA0⟩

theorem bool_ser_false :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize false =
      [litByte 0] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head false
  exact heq

theorem bool_ser_true :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true =
      [litByte 1] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head true
  exact heq

def pqSecretsList : List Bytes :=
  [DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := ikA }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := ikB }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkB }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskB }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState)]

theorem pqSecrets_safeMemo {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (hh : HandshakeAt S g pts) :
    ∀ t ∈ pqSecretsList, SafeMemo dagSize dagOp dagBytes S g pts t := by
  have tb00 : TermAt dagSize dagOp dagBytes S g pts (litByte 0) 1 := termAt_lit_b (by decide +kernel)
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (by decide +kernel)
  have talice : TermAt dagSize dagOp dagBytes S g pts (lit "alice") 33 :=
    termAt_strLit (by decide) (by decide +kernel)
  have tbob : TermAt dagSize dagOp dagBytes S g pts (lit "bob") 43 :=
    termAt_strLit (by decide) (by decide +kernel)
  have ta : TermAt dagSize dagOp dagBytes S g pts
      (DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := ikA }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) 42 := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, alice_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := 42) (by decide +kernel) tb01
      (termAt_concat_b (id := 41) (by decide +kernel) tb01
        (termAt_concat_b (id := 40) (by decide +kernel) tb01
          (termAt_concat_b (id := 39) (by decide +kernel) tb01
            (termAt_concat_b (id := 38) (by decide +kernel) tb01
              (termAt_concat_b (id := 37) (by decide +kernel) tb00
                (termAt_concat_b (id := 36) (by decide +kernel) talice
                  (termAt_concat_b (id := 35) (by decide +kernel) tb00
                    (termAt_concat_b (id := 34) (by decide +kernel) tb00 hh.t_ikA))))))))
  have tb1 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := ikB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) 50 := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := 50) (by decide +kernel) tb01
      (termAt_concat_b (id := 49) (by decide +kernel) tb01
        (termAt_concat_b (id := 48) (by decide +kernel) tb01
          (termAt_concat_b (id := 47) (by decide +kernel) tb00
            (termAt_concat_b (id := 46) (by decide +kernel) tbob
              (termAt_concat_b (id := 45) (by decide +kernel) tb00
                (termAt_concat_b (id := 44) (by decide +kernel) tb00 hh.t_ikB))))))
  have tb2 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) 57 := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := 57) (by decide +kernel) tb01
      (termAt_concat_b (id := 56) (by decide +kernel) tb01
        (termAt_concat_b (id := 55) (by decide +kernel) tb01
          (termAt_concat_b (id := 54) (by decide +kernel) tb00
            (termAt_concat_b (id := 53) (by decide +kernel) tbob
              (termAt_concat_b (id := 52) (by decide +kernel) tb00
                (termAt_concat_b (id := 51) (by decide +kernel) tb01 hh.t_spkB))))))
  have tb3 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) 64 := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := 64) (by decide +kernel) tb01
      (termAt_concat_b (id := 63) (by decide +kernel) tb01
        (termAt_concat_b (id := 62) (by decide +kernel) tb01
          (termAt_concat_b (id := 61) (by decide +kernel) tb00
            (termAt_concat_b (id := 60) (by decide +kernel) tbob
              (termAt_concat_b (id := 59) (by decide +kernel) tb01
                (termAt_concat_b (id := 58) (by decide +kernel) tb00 hh.t_pqskB))))))
  intro t ht
  simp only [pqSecretsList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ta.safeMemo
  · exact tb1.safeMemo
  · exact tb2.safeMemo
  · exact tb3.safeMemo

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
