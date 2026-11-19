/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
public import Symbolic.Proofs.Tests.CliNonvacuity.Defs
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean 5-Step Symbolic Schedule (`CleanTrace.lean`)

Defines the 5-step symbolic trace `cleanCallSteps cls` (`s0Clean..s4Clean`) matching Calls `0..4`
of `KeepOpkCli.trace` (`aliceStart`, `messageEncrypt`, `bobStart` consuming Bob's OPK, second
`aliceStart`, second `messageEncrypt`), parameterized by outer SPQR coin lengths `cls : Nat → Nat`.
Proves `Step.next` / `Step.ok`, `ModelRunWF`, `¬ ReadCollisionCli`, `honestSaltsOf`, `storedStates`,
`storedSecrets`, and `bobTrials` at both `k = 2` and `k = 5`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace

open DY (Bytes ExecTrace Participant Trace Traceful ExecTraceTypes TraceEntryHas)
open DY.Bytes (view?)
open DY.BytesView (pack)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Spqr (spqrInit spqrSend spqrRecv spqrChainKey encodeSpqrIndexTerm zeroKey)
open DY.X25519 (normalizeX25519Key)
open DY.Libsignal.PQXDH
  (AliceHandshakeOut HandshakeKeys PreKeyMsgHandles PQXDHEvent PQXDHState
   aliceAgreement bobAgreement agree pqxdhIkm pqxdhKdf serializedIk errToOption)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain SessionInfo kdfCk createChain setRecvChain consumeMessageKey skippedSeeds
   isCurrentSnapshot maxReceiverChains spqrA2B spqrB2A u32Max trMsgKeys computeMac)
open DY.Libsignal.Composed (reachability)
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
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step stepIn newIndices
   setupTrace setupRandoms setupSent setupPublic setupSecret runSteps runTrace
   StepsWF StepsStateFaithful ModelRunWF PreKeyRep TrialCtx
   honestKeysOf honestSaltsOf storedStates storedSecrets bobTrials trialTerms)
open DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs bobSt0 bobAgreement_honest_opk encSt encMsg encSig parse_encMsg
   ratchetState recvSt mac_ok dec_ok rnd createChain_comm agree_comm kemDecap_kemEncap
   registerIdentityTr genSignedPrekeyTr genPQPrekeyTr genOneTimePrekeyTr
   aliceOutOpk aliceOutOpt aliceSt aliceTrOpk aliceTrOpt skipTr
   StP StT RndE NetE EvP EvT EvC)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB spkNonce pqskB pqNonce opkB
   bhOpk khOpk mhOpk oOpk keysOpk dhsAOpk stA0Opk key0Opk
   dhsB1Opk stB00Opk stB0'Opk cBOpk cB'Opk seedB0Opk seedB0Opk_eq
   t1 t2 t3 t4 t4Opk t5Opk t7Opk
   t1_length t2_length t3_length t4_length t4Opk_length t5Opk_length t7Opk_length
   t4Opk_reach t5Opk_runs t5Opk_stA0Opk_at)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (mkRecords)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (setupTrace_true_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (modelRunWF_of_append)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (p2 p2_fields_base p5 p5_fields_base)

/-! ## 1. Trace Primitives and Generic `messageEncrypt` -/

/-- Valid SPQR coin lengths for the two `send` calls (`ev 1` and `ev 4`). -/
def ValidCoinLens (cls : Nat → Nat) : Prop :=
  (cls 0 = 0 ∨ cls 0 = 32 ∨ cls 0 = 64) ∧
  (cls 1 = 0 ∨ cls 1 = 32 ∨ cls 1 = 64)

theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le t2 e)

theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace} {i : Nat} {x : E}
    (hle : t1 ≤ t2) (h : t1.at? i = some x) : t2.at? i = some x := by
  have := Trace.at?_le (EntryT := E) t1 t2 i hle
  rwa [h] at this

theorem at?_append_at {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) {i : Nat}
    (hi : tr.length = i) : (tr.append e).at? i = some e := by
  subst hi; exact Trace.at?_append tr e

theorem at?_append_self_proj {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self]
  simp only [Trace.at?, hlt, ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2]

theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = tr.at? i := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hi' : i < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  have hne : i ≠ tr.length := by omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, hne]

theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

theorem stepIn_next (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

theorem stepIn_isSome (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (inst.pf_step x).symm

theorem stepIn_preCond_iff (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    reachability.PreCond (stepIn c x) tr ↔ c.PreCond x tr :=
  (inst.pf_pre x tr).symm.to_iff

/-- Trace after `TripleRatchet.messageEncrypt me stH cl pqH` reading `st` and salt `pq`. -/
def encTrGen (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState) (pq : Bytes) :
    ExecTrace :=
  let m := rnd tr.length 32
  let coins := rnd (tr.length + 1) cl
  ((((((tr.append (RndE 32)).append (RndE cl)).append
    (NetE (spqrSend st.spqr coins).2.1)).append
    (EvT (.Sent me st.peer (dhPk st.dhs) st.ns m))).append
    (EvT (.MessageKey (st.sessionInfo me) .sender (kdfCk st.cks).2 pq st.ns
      st.rIdx stH))).append
    (StT me (encSt st coins))).append
    (NetE (encMsg st coins pq m))

theorem encTrGen_length (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : (encTrGen tr me stH cl st pq).length = tr.length + 7 := by
  dsimp only [encTrGen]; simp only [append_len]

theorem encTrGen_le (tr : ExecTrace) (me : Participant) (stH cl : Nat) (st : TRState)
    (pq : Bytes) : tr ≤ encTrGen tr me stH cl st pq := by
  dsimp only [encTrGen]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _

theorem Runs.messageEncryptGen {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
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

theorem x25519LowOrder_dhPk (sk : Bytes) :
    DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _
  have hl0 : (dhPk sk).view? DY.Literal.Literal.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
  have hl : DY.Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold DY.Libsignal.TripleRatchet.x25519LowOrder normalizeX25519Key
  rw [hv, hl]

theorem isCanonicalKey_dhPk (sk : Bytes) :
    DY.Libsignal.PQXDH.isCanonicalKey (dhPk sk) = true := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none := by
    dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.instCanDHBytes]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _
  have hl : DY.Libsignal.PQXDH.x25519LowOrder (dhPk sk) = false := x25519LowOrder_dhPk sk
  unfold DY.Libsignal.PQXDH.isCanonicalKey
  rw [hv, hl]; rfl

theorem bytesToLiteral_spqrSendMsg (st coins : Bytes) :
    DY.Literal.bytesToLiteral (spqrSend st coins).2.2 = none := by
  have hl0 : ((spqrSend st coins).2.2).view? DY.Literal.Literal.SubF = none := by
    dsimp only [spqrSend]
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]

theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo)
    (pk : Bytes) (c : RecvChain) (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]

theorem isCurrentSnapshot_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  unfold isCurrentSnapshot DY.Libsignal.TripleRatchet.getStoredLocalStateAt?
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]; rfl

theorem isCurrentSnapshot_non {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {k : Nat}
    (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none)
    (hcur : isCurrentSnapshot tr k = true) :
    isCurrentSnapshot (tr.append e) k = true := by
  unfold isCurrentSnapshot DY.Libsignal.TripleRatchet.getStoredLocalStateAt? at hcur ⊢
  cases hst : (tr.at? k :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) with
  | none => rw [hst] at hcur; cases hcur
  | some es =>
    have hk : k < tr.length := by
      have := Trace.at?_eq_some_implies_length_le
        (EntryT := DY.PersistentGlobalState.State.ExecEntryT
          (DY.PersistentLocalState.LocalState TRState)) tr k
      rwa [hst] at this
    rw [hst] at hcur
    rw [at?_mono (Trace.append_le tr e) hst]
    dsimp only [Option.map] at hcur ⊢
    have hsub : (tr.append e).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
      rw [append_len]; omega
    rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [List.all_eq_true] at hcur ⊢
      intro j hj
      rw [at?_append_of_lt tr e (by rw [List.mem_range'_1] at hj; omega)]
      exact hcur j hj
    · simp [at?_append_self_proj, hnone]

/-! ## 2. Setup Equations on `t4Opk` -/

theorem setupTrace_eq_t4Opk {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    setupTrace r = t4Opk := by
  have heq : setupTrace r = setupTrace (mkRecords true) := by
    unfold setupTrace
    rw [ha, hb, ho]
    rfl
  exact heq.trans setupTrace_true_eq

theorem setupRandoms_len_eq {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    (setupRandoms r).length = (if r.withOpk then 7 else 6) := by
  unfold setupRandoms
  rw [setupTrace_eq_t4Opk ha hb ho, ← setupTrace_true_eq, ho]
  exact Symbolic.Swarm.CREF.TR.setupRandoms_length (mkRecords true) (by decide)

theorem aliceTrOpt_le (tr : ExecTrace) (a b : Participant)
    (ikA' ikBPk spkPk pqPk : Bytes) (opkPk : Option Bytes) :
    tr ≤ aliceTrOpt tr a b ikA' ikBPk spkPk pqPk opkPk := by
  dsimp only [aliceTrOpt]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _

theorem t4_le_t4Opk : t4 ≤ t4Opk := by
  dsimp only [t4Opk, genOneTimePrekeyTr]
  exact le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _

/-! ## 3. Clean Symbolic Steps `s0Clean .. s4Clean` and Traces `trClean2 .. trClean5` -/

def s0Clean : Step := .aliceStart "alice" "bob" 4 6 bhOpk
def s1Clean (cls : Nat → Nat) : Step := .messageEncrypt "alice" 34 (cls 0) 37
def s2Clean : Step := .bobStart "bob" "alice" khOpk 1 mhOpk 37 1
def s3Clean : Step := .aliceStart "alice" "bob" 4 6 bhOpk
def s4Clean (cls : Nat → Nat) : Step := .messageEncrypt "alice" 60 (cls 1) 63

def cleanCallSteps (cls : Nat → Nat) : List Step :=
  [s0Clean, s1Clean cls, s2Clean, s3Clean, s4Clean cls]

theorem cleanCallSteps_length (cls : Nat → Nat) : (cleanCallSteps cls).length = 5 := rfl

def ssClean (cls : Nat → Nat) (k : Nat) : List Step :=
  (cleanCallSteps cls).take k

theorem ssClean_succ {cls : Nat → Nat} {k : Nat} {s : Step}
    (hs : (cleanCallSteps cls)[k]? = some s) :
    ssClean cls (k + 1) = ssClean cls k ++ [s] := by
  unfold ssClean
  rw [List.take_add_one, hs, Option.toList_some]

/-- Call 1 (`s1Clean`): Alice encrypts message 0 in session 1. -/
def pt0Clean : Bytes := rnd 35 32
def coins0Clean (cls : Nat → Nat) : Bytes := rnd 36 (cls 0)
def key0Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0Opk.spqr (coins0Clean cls)).2.1
def pqm0Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0Opk.spqr (coins0Clean cls)).2.2
def stA1Clean (cls : Nat → Nat) : TRState := encSt stA0Opk (coins0Clean cls)
def m0Clean (cls : Nat → Nat) : Bytes := encMsg stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean
def trClean2 (cls : Nat → Nat) : ExecTrace :=
  encTrGen t5Opk "alice" 34 (cls 0) stA0Opk (key0Clean cls)

theorem key0Clean_eq (cls : Nat → Nat) : key0Clean cls = key0Opk := by
  unfold key0Clean key0Opk spqrSend
  dsimp only [stA0Opk, aliceSt, spqrInit]
  rw [DY.BytesView.view_pack]

theorem spqrChainKey_keysOpk_eq :
    spqrChainKey keysOpk.pqr spqrA2B (encodeSpqrIndexTerm 1) = key0Opk := by
  unfold key0Opk spqrSend
  dsimp only [stA0Opk, aliceSt, spqrInit]
  rw [DY.BytesView.view_pack]

theorem trClean2_length (cls : Nat → Nat) : (trClean2 cls).length = 42 := by
  rw [trClean2, encTrGen_length, t5Opk_length]

/-- Call 2 (`s2Clean`): Bob accepts Alice's first pre-key message (`opk = some 24`). -/
def stB1Clean (cls : Nat → Nat) : TRState :=
  { stB0'Opk with
    recv := [cB'Opk]
    spqr := recvSt (spqrInit keysOpk.pqr spqrB2A) (pqm0Clean cls) }

def trClean3 (cls : Nat → Nat) : ExecTrace :=
  let tr1 := (((trClean2 cls).append (RndE 32)).append (NetE key0Opk)).append
    (EvP (.OPKUsed "bob" (dhPk opkB)))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) (some (dhPk opkB)) oOpk.ek oOpk.ct keysOpk))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsAOpk) (dhPk dhsB1Opk)))).append
      (EvT (.HonestDH (stB0'Opk.sessionInfo "bob") dhsB1Opk 0))).append
      (EvC (.HandshakeSession (stB0'Opk.sessionInfo "bob") 45))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsAOpk) 0 pt0Clean))).append
    (EvT (.MessageKey (stB0'Opk.sessionInfo "bob") .receiver seedB0Opk (key0Clean cls) 0 2 51))).append
    (StT "bob" (stB1Clean cls))

theorem trClean3_length (cls : Nat → Nat) : (trClean3 cls).length = 52 := by
  dsimp only [trClean3]; simp only [append_len, trClean2_length]

theorem trClean2_le_trClean3 (cls : Nat → Nat) : trClean2 cls ≤ trClean3 cls := by
  dsimp only [trClean3]
  exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
    (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _) _) _) _) _) _

/-- Call 3 (`s3Clean`): Alice initiates session 2 on `trClean3 cls` (length `52`). -/
def o2Clean : AliceHandshakeOut :=
  aliceOutOpk t7Opk ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB)

def keys2Clean : HandshakeKeys := o2Clean.keys
def dhsA2Clean : Bytes := rnd 54 32
def stA2_0Clean : TRState := aliceSt "bob" o2Clean dhsA2Clean

def trClean4 (cls : Nat → Nat) : ExecTrace :=
  aliceTrOpk (trClean3 cls) "alice" "bob" ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB)

theorem trClean4_length (cls : Nat → Nat) : (trClean4 cls).length = 61 := by
  dsimp only [trClean4, aliceTrOpk, aliceTrOpt]; simp only [append_len, trClean3_length]

theorem aliceOutOpk_trClean3_eq (cls : Nat → Nat) :
    aliceOutOpk (trClean3 cls) ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB) = o2Clean := by
  dsimp only [o2Clean, aliceOutOpk,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
  rw [trClean3_length, t7Opk_length]

/-- Call 4 (`s4Clean`): Alice encrypts message 0 in session 2. -/
def pt1Clean : Bytes := rnd 61 32
def coins1Clean (cls : Nat → Nat) : Bytes := rnd 62 (cls 1)
def key1Opk : Bytes := spqrChainKey keys2Clean.pqr spqrA2B (encodeSpqrIndexTerm 1)
def key1Clean (cls : Nat → Nat) : Bytes := (spqrSend stA2_0Clean.spqr (coins1Clean cls)).2.1
def pqm1Clean (cls : Nat → Nat) : Bytes := (spqrSend stA2_0Clean.spqr (coins1Clean cls)).2.2
def stA2_1Clean (cls : Nat → Nat) : TRState := encSt stA2_0Clean (coins1Clean cls)
def m1Clean (cls : Nat → Nat) : Bytes :=
  encMsg stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean

def trClean5 (cls : Nat → Nat) : ExecTrace :=
  encTrGen (trClean4 cls) "alice" 60 (cls 1) stA2_0Clean (key1Clean cls)

theorem key1Clean_eq (cls : Nat → Nat) : key1Clean cls = key1Opk := by
  unfold key1Clean key1Opk spqrSend
  dsimp only [stA2_0Clean, aliceSt, spqrInit]
  rw [DY.BytesView.view_pack]; rfl

theorem spqrRecv_init_b2a_1 (authKey msg : Bytes) (hmsg : DY.Literal.bytesToLiteral msg = none) :
    spqrRecv (spqrInit authKey spqrB2A) msg 1 =
      some (recvSt (spqrInit authKey spqrB2A) msg,
        spqrChainKey authKey spqrA2B (encodeSpqrIndexTerm 1)) := by
  unfold spqrRecv DY.Spqr.spqrEmptyMsg
  rw [hmsg]
  have hinit : (spqrInit authKey spqrB2A).view? DY.Spqr.InitState.SubF =
      some { authKey := authKey, params := spqrB2A } := by
    dsimp only [spqrInit]; exact DY.BytesView.view_pack _
  have hdir : DY.Spqr.spqrParamsDir? spqrB2A = some .b2a :=
    DY.Spqr.spqrParamsDir?_spqrParams .b2a
  rw [hinit]; dsimp only; rw [hdir]; rfl

theorem trClean5_length (cls : Nat → Nat) : (trClean5 cls).length = 68 := by
  rw [trClean5, encTrGen_length, trClean4_length]

/-- Candidate `PreKeyRep` at `k = 2` (`ev 2`) and `k = 5` (`ev 5`). -/
def cleanPreKeyRep (cls : Nat → Nat) (k : Nat) : PreKeyRep :=
  if k = 2 then { ek := oOpk.ek, ct := oOpk.ct, msg := m0Clean cls }
  else { ek := o2Clean.ek, ct := o2Clean.ct, msg := m1Clean cls }

/-! ## 4. `Step.next` and `Step.ok` for `s0Clean .. s4Clean` -/

theorem s0_next_ok :
    s0Clean.next t4Opk = t5Opk ∧ s0Clean.ok t4Opk = true :=
  ⟨(stepIn_next DY.Libsignal.Composed.aliceStart.reachability _ t4Opk).trans t5Opk_runs.2,
   (stepIn_isSome DY.Libsignal.Composed.aliceStart.reachability _ t4Opk).trans
     (congrArg Option.isSome t5Opk_runs.1)⟩

theorem s1_next_ok (cls : Nat → Nat) :
    (s1Clean cls).next t5Opk = trClean2 cls ∧ (s1Clean cls).ok t5Opk = true := by
  have hpq : (((t5Opk.append (RndE 32)).append (RndE (cls 0))).append
      (NetE (spqrSend stA0Opk.spqr (rnd (t5Opk.length + 1) (cls 0))).2.1)).at? 37 =
      some (NetE (key0Clean cls)) := by
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hc]
    exact at?_append_at _ (NetE (key0Clean cls)) (by simp only [append_len, t5Opk_length])
  have hr := runs_cast (Runs.messageEncryptGen (tr := t5Opk) (stH := 34) (cl := cls 0) (pqH := 37)
    (st := stA0Opk) (pq := key0Clean cls) t5Opk_stA0Opk_at (by decide) hpq)
    (by rw [t5Opk_length]) rfl
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5Opk).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5Opk).trans
      (congrArg Option.isSome hr.1)⟩

private theorem someEventB_non {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
    (p : PQXDHEvent → Bool)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none)
    (h : DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false) :
    DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent (tr.append x) p = false := by
  unfold DY.Libsignal.TripleRatchet.anyEventOnTrace at h ⊢
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h ⊢
  rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
    exact h i hi
  · simp [at?_append_self_proj, hnone]

private theorem someEventB_ev (tr : ExecTrace) (ev : PQXDHEvent)
    (p : PQXDHEvent → Bool) (hp : p ev = false)
    (h : DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false) :
    DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent (tr.append (EvP ev)) p = false := by
  unfold DY.Libsignal.TripleRatchet.anyEventOnTrace at h ⊢
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h ⊢
  rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · rw [List.any_eq_false] at h ⊢
    intro i hi
    rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
    exact h i hi
  · simp [Trace.at?_append, EvP, hp]

theorem t4_entry_facts :
    t1 = registerIdentityTr Trace.nil "alice" ∧
    t2 = registerIdentityTr t1 "bob" ∧
    t3 = genSignedPrekeyTr t2 "bob" ikB ∧
    t4 = genPQPrekeyTr t3 "bob" ikB ∧
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) ∧
    t4.at? 4 = some (StP "alice" { kind := .identity, sk := ikA }) ∧
    t4.at? 6 = some (EvP (.IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true)) ∧
    t4.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (StP "bob" { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 14 = some (NetE (dhPk spkB)) ∧
    t4.at? 15 = some (NetE (DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)))) ∧
    t4.at? 19 = some (StP "bob" { kind := .pqPrekey, sk := pqskB }) ∧
    t4.at? 20 = some (NetE (kemPk pqskB)) ∧
    t4.at? 21 = some (NetE (DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)))) := by
  have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have hnil : ∀ p : PQXDHEvent → Bool,
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent Trace.nil p = false := by
    intro p; unfold DY.Libsignal.TripleRatchet.anyEventOnTrace; rw [nil_len]; rfl
  have ht1 : t1 = registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [hnil]; rfl)).2
  have ht2 : t2 = registerIdentityTr t1 "bob" := by
    refine (Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]; dsimp only [registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (hnil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (StP "bob" { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have ht3 : t3 = genSignedPrekeyTr t2 "bob" ikB := (Runs.genSignedPrekey hb2).2
  have h23 : t2 ≤ t3 := by
    rw [ht3]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t2 _) _) _) _) _) _
  have ht4 : t4 = genPQPrekeyTr t3 "bob" ikB := (Runs.genPQPrekey (at?_mono h23 hb2)).2
  have h12 : t1 ≤ t2 := by
    rw [ht2]
    exact le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t1 _) _) _) _) _
  have h34 : t3 ≤ t4 := by
    rw [ht4]
    exact le_append_of_le (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le t3 _) _) _) _) _) _
  have h24 : t2 ≤ t4 := Trace.le_trans _ _ _ h23 h34
  have h14 : t1 ≤ t4 := Trace.le_trans _ _ _ h12 h24
  refine ⟨ht1, ht2, ht3, ht4, ?_, ?_, ?_, at?_mono h24 hb2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine at?_mono h14 ?_; rw [ht1]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h14 ?_; rw [ht1]; dsimp only [registerIdentityTr]; rw [nil_len]
    exact at?_append_at _ _ (by simp only [append_len, nil_len])
  · refine at?_mono h24 ?_; rw [ht2]; dsimp only [registerIdentityTr]; rw [t1_length]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t1_length]))
  · refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · refine at?_mono h34 ?_; rw [ht3]; dsimp only [genSignedPrekeyTr]; rw [t2_length]
    exact at?_append_at _ _ (by simp only [append_len, t2_length])
  · rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))
  · rw [ht4]; dsimp only [genPQPrekeyTr]; rw [t3_length]
    exact at?_append_at _ _ (by simp only [append_len, t3_length])

theorem s2_next_ok (cls : Nat → Nat) :
    s2Clean.next (trClean2 cls) = trClean3 cls ∧ s2Clean.ok (trClean2 cls) = true := by
  obtain ⟨ht1, ht2, ht3, ht4, ha1, _, _, hb9, hs13, _, _, hp19, _, _⟩ := t4_entry_facts
  have h5_2 : t5Opk ≤ trClean2 cls := encTrGen_le _ _ _ _ _ _
  have h4o_2 : t4Opk ≤ trClean2 cls := Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _) h5_2
  have h4_2 : t4 ≤ trClean2 cls := Trace.le_trans _ _ _ t4_le_t4Opk h4o_2
  have hopk24 : (trClean2 cls).at? 24 = some (StP "bob" { kind := .oneTimePrekey, sk := opkB }) := by
    refine at?_mono h4o_2 ?_; dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hek : (trClean2 cls).at? 29 = some (NetE oOpk.ek) := by
    refine at?_mono h5_2 ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hct : (trClean2 cls).at? 30 = some (NetE oOpk.ct) := by
    refine at?_mono h5_2 ?_; dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hmsg : (trClean2 cls).at? 41 = some (NetE (m0Clean cls)) := by
    dsimp only [trClean2, encTrGen, m0Clean]
    have hm : rnd t5Opk.length 32 = pt0Clean := by rw [t5Opk_length]; rfl
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5Opk_length])
  have hpq : (((trClean2 cls).append (RndE 32)).append (NetE key0Opk)).at? 37 =
      some (NetE (key0Clean cls)) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [trClean2, encTrGen]
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE (key0Clean cls)) (by simp only [append_len, t5Opk_length]))
  have hrecv : spqrRecv stB0'Opk.spqr (pqm0Clean cls) 1 =
      some (recvSt (spqrInit keysOpk.pqr spqrB2A) (pqm0Clean cls), key0Opk) := by
    have h0 := spqrRecv_init_b2a_1 keysOpk.pqr (pqm0Clean cls) (bytesToLiteral_spqrSendMsg _ _)
    exact h0.trans (congrArg (fun k => some (_, k)) spqrChainKey_keysOpk_eq)
  have hopkUnused :
      (!DY.Libsignal.PQXDH.opkUsedB (((trClean2 cls).append (RndE 32)).append (NetE key0Opk))
        "bob" (dhPk opkB)) = true := by
    have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
    have hnil : ∀ p : PQXDHEvent → Bool,
        DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent Trace.nil p = false := by
      intro p; unfold DY.Libsignal.TripleRatchet.anyEventOnTrace; rw [nil_len]; rfl
    unfold DY.Libsignal.PQXDH.opkUsedB
    rw [show DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent
        (((trClean2 cls).append (RndE 32)).append (NetE key0Opk)) _ = false by
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl ?_)
      dsimp only [trClean2, encTrGen]
      iterate 7 refine someEventB_non _ _ _ rfl ?_
      dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl ?_)))
      iterate 5 refine someEventB_non _ _ _ rfl ?_
      dsimp only [t4Opk, genOneTimePrekeyTr]
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_ev _ _ _ rfl (someEventB_non _ _ _ rfl ?_)))
      rw [ht4]; dsimp only [genPQPrekeyTr]
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_ev _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl ?_)))))
      rw [ht3]; dsimp only [genSignedPrekeyTr]
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_ev _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl ?_)))))
      rw [ht2]; dsimp only [registerIdentityTr]
      refine someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_ev _ _ _ rfl (someEventB_non _ _ _ rfl ?_))))
      rw [ht1]; dsimp only [registerIdentityTr]
      exact someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
        (someEventB_ev _ _ _ rfl (someEventB_non _ _ _ rfl (hnil _)))))]
    rfl
  have hset : setRecvChain stB0'Opk.recv cB'Opk = [cB'Opk] := by
    simp [setRecvChain, stB0'Opk, ratchetState, cB'Opk, cBOpk, stB00Opk, bobSt0, maxReceiverChains]
  have hrs : ratchetState
      (bobSt0 "alice" ikB spkB (dhPk ikA) keysOpk
        (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean))
      (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).ratchetKey
      (rnd (trClean2 cls).length 32) = (stB0'Opk, cBOpk) := by
    rw [trClean2_length]; rfl
  obtain ⟨hr1, hr2⟩ := Runs.bobStartOpk (kh := khOpk) (mh := mhOpk) (keys := keysOpk)
    (msg := encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean)
    (t := m0Clean cls) (st' := stB0'Opk) (c := cBOpk) (c' := cB'Opk)
    (seed := seedB0Opk) (pq := key0Clean cls) (m := pt0Clean)
    (at?_mono h4_2 hb9) (at?_mono h4_2 hs13) (at?_mono h4_2 hp19) rfl hopk24
    (at?_mono h4_2 ha1) hek hct (isCanonicalKey_dhPk _)
    (bobAgreement_honest_opk ikA (rnd t4Opk.length 32) ikB spkB pqskB opkB
      (rnd (t4Opk.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsAOpk) hrs rfl hrecv hpq
    (mac_ok seedB0Opk_eq rfl rfl) (dec_ok seedB0Opk_eq) hopkUnused (stOut := stB1Clean cls)
    (by rw [hset]; rfl)
  have hr2' : ((DY.Libsignal.Composed.bobStart "bob" "alice" khOpk 1 mhOpk 37 1).run
      (trClean2 cls)).2.val = trClean3 cls := by
    dsimp only [encSig, stA0Opk, aliceSt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.bobOutOpt] at hr2
    rw [skipTr_zero _ _ _ _ _ _ rfl] at hr2
    refine hr2.trans ?_
    dsimp only [trClean3, stB0'Opk, ratchetState, stB00Opk, bobSt0, cBOpk]
    simp only [append_len, trClean2_length]
    rfl
  exact ⟨(stepIn_next DY.Libsignal.Composed.bobStart.reachability _ _).trans hr2',
    (stepIn_isSome DY.Libsignal.Composed.bobStart.reachability _ _).trans
      (congrArg Option.isSome hr1)⟩

theorem s3_next_ok (cls : Nat → Nat) :
    s3Clean.next (trClean3 cls) = trClean4 cls ∧ s3Clean.ok (trClean3 cls) = true := by
  obtain ⟨_, _, _, _, _, ha4, hb6, _, _, hs14, hs15, _, hp20, hp21⟩ := t4_entry_facts
  have h4o_3 : t4Opk ≤ trClean3 cls :=
    Trace.le_trans _ _ _ (aliceTrOpt_le _ _ _ _ _ _ _ _)
      (Trace.le_trans _ _ _ (encTrGen_le _ _ _ _ _ _) (trClean2_le_trClean3 cls))
  have h4_3 : t4 ≤ trClean3 cls := Trace.le_trans _ _ _ t4_le_t4Opk h4o_3
  have hopk : (trClean3 cls).at? 25 = some (NetE (dhPk opkB)) := by
    refine at?_mono h4o_3 ?_; dsimp only [t4Opk, genOneTimePrekeyTr, opkB]; rw [t4_length]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hlowOpk : ((some (dhPk opkB)).all (!DY.Libsignal.TripleRatchet.x25519LowOrder ·)) = true := by
    simp [x25519LowOrder_dhPk]
  have hr := Runs.aliceStartOpk (tr := trClean3 cls) (a := "alice") (b := "bob")
    (idH := 4) (regB := 6) (h := bhOpk) (oi := 25)
    (at?_mono h4_3 ha4) (at?_mono h4_3 hb6)
    (at?_mono h4_3 hs14) (at?_mono h4_3 hs15) (at?_mono h4_3 hp20) (at?_mono h4_3 hp21)
    (DY.Signature.verify_sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)))
    (DY.Signature.verify_sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)))
    rfl hopk (x25519LowOrder_dhPk spkB) hlowOpk
  exact ⟨(stepIn_next DY.Libsignal.Composed.aliceStart.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.Composed.aliceStart.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem trClean4_stA2_0_at (cls : Nat → Nat) :
    (trClean4 cls).at? 60 = some (StT "alice" stA2_0Clean) := by
  dsimp only [trClean4, aliceTrOpk, aliceTrOpt]
  have hao : aliceOutOpt (trClean3 cls) ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB)) =
      o2Clean := aliceOutOpk_trClean3_eq cls
  have hdhs : rnd ((trClean3 cls).length + 2) 32 = dhsA2Clean := by rw [trClean3_length]; rfl
  rw [hao, hdhs]
  exact at?_append_at _ (StT "alice" stA2_0Clean) (by simp only [append_len, trClean3_length])

theorem s4_next_ok (cls : Nat → Nat) :
    (s4Clean cls).next (trClean4 cls) = trClean5 cls ∧ (s4Clean cls).ok (trClean4 cls) = true := by
  have hpq : ((((trClean4 cls).append (RndE 32)).append (RndE (cls 1))).append
      (NetE (spqrSend stA2_0Clean.spqr (rnd ((trClean4 cls).length + 1) (cls 1))).2.1)).at? 63 =
      some (NetE (key1Clean cls)) := by
    have hc : rnd ((trClean4 cls).length + 1) (cls 1) = coins1Clean cls := by
      rw [trClean4_length]; rfl
    rw [hc]
    exact at?_append_at _ (NetE (key1Clean cls)) (by simp only [append_len, trClean4_length])
  have hr := runs_cast (Runs.messageEncryptGen (tr := trClean4 cls) (stH := 60) (cl := cls 1)
    (pqH := 63) (st := stA2_0Clean) (pq := key1Clean cls) (trClean4_stA2_0_at cls) (by decide) hpq)
    (by rw [trClean4_length]) rfl
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem runTrace_ssClean_eqs {r : ProtocolSetup} (cls : Nat → Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    runTrace r (ssClean cls 0) = t4Opk ∧
    runTrace r (ssClean cls 1) = t5Opk ∧
    runTrace r (ssClean cls 2) = trClean2 cls ∧
    runTrace r (ssClean cls 3) = trClean3 cls ∧
    runTrace r (ssClean cls 4) = trClean4 cls ∧
    runTrace r (ssClean cls 5) = trClean5 cls := by
  have h0 := setupTrace_eq_t4Opk ha hb ho
  obtain ⟨hn0, _⟩ := s0_next_ok
  obtain ⟨hn1, _⟩ := s1_next_ok cls
  obtain ⟨hn2, _⟩ := s2_next_ok cls
  obtain ⟨hn3, _⟩ := s3_next_ok cls
  obtain ⟨hn4, _⟩ := s4_next_ok cls
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold runTrace ssClean cleanCallSteps; rw [h0]; simp only [List.take, runSteps, hn0, hn1, hn2, hn3, hn4])

/-! ## 5. `ModelRunWF` and Vacuous `¬ ReadCollisionCli` -/

private def stateFaithfulBool (ss : List Step) : Bool :=
  (List.range ss.length).all fun i =>
    (List.range ss.length).all fun j =>
      !(decide (i < j)) ||
        match ss[i]?, ss[j]? with
        | some si, some sj =>
          match si.stateLoad?, sj.stateLoad? with
          | some (p1, k1, true), some (p2, k2, _) => !(p1 == p2 && k1 == k2)
          | _, _ => true
        | _, _ => true

private theorem stateFaithful_cleanCallSteps (r : ProtocolSetup) (cls : Nat → Nat) :
    StepsStateFaithful r (cleanCallSteps cls) := by
  have hbool : stateFaithfulBool (cleanCallSteps (fun _ => 0)) = true := by decide +kernel
  have hmap : (cleanCallSteps cls).map Step.stateLoad? =
      (cleanCallSteps (fun _ => 0)).map Step.stateLoad? := rfl
  intro i j si sj p k b hij hsi hsj hli _ hlj
  have hjlt : j < 5 := by
    rw [← cleanCallSteps_length cls]
    exact (List.getElem?_eq_some_iff.mp hsj).1
  have hilt : i < 5 := Nat.lt_trans hij hjlt
  have hi0 : ((cleanCallSteps (fun _ => 0)).map Step.stateLoad?)[i]? =
      some (some (p, k, true)) := by
    rw [← hmap, List.getElem?_map, hsi, Option.map_some, hli]
  have hj0 : ((cleanCallSteps (fun _ => 0)).map Step.stateLoad?)[j]? =
      some (some (p, k, b)) := by
    rw [← hmap, List.getElem?_map, hsj, Option.map_some, hlj]
  rw [List.getElem?_map] at hi0 hj0
  obtain ⟨si0, hsi0, hli0⟩ := Option.map_eq_some_iff.mp hi0
  obtain ⟨sj0, hsj0, hlj0⟩ := Option.map_eq_some_iff.mp hj0
  have hi := List.all_eq_true.mp hbool i
    (List.mem_range.mpr (by rw [cleanCallSteps_length]; exact hilt))
  have hj := List.all_eq_true.mp hi j
    (List.mem_range.mpr (by rw [cleanCallSteps_length]; exact hjlt))
  rw [hsi0, hsj0] at hj; dsimp only at hj; rw [hli0, hlj0] at hj
  simp [hij] at hj

theorem modelRunWF_ssClean {r : ProtocolSetup} {cls : Nat → Nat} (k : Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true)
    (hv : ValidCoinLens cls) :
    ModelRunWF r (ssClean cls k) := by
  have hcur34 : isCurrentSnapshot t5Opk 34 = true := by
    dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, t4Opk_length])
  have hcur60 : isCurrentSnapshot (trClean4 cls) 60 = true := by
    dsimp only [trClean4, aliceTrOpk, aliceTrOpt]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, trClean3_length])
  have hp1 : (s1Clean cls).PreCond t5Opk :=
    (stepIn_preCond_iff DY.Libsignal.TripleRatchet.messageEncrypt.reachability
      ("alice", 34, cls 0, 37) t5Opk).mpr hcur34
  have hp4 : (s4Clean cls).PreCond (trClean4 cls) :=
    (stepIn_preCond_iff DY.Libsignal.TripleRatchet.messageEncrypt.reachability
      ("alice", 60, cls 1, 63) (trClean4 cls)).mpr hcur60
  have hwf : StepsWF (cleanCallSteps cls) t4Opk := by
    refine ⟨trivial, trivial, ?_⟩
    rw [s0_next_ok.1]
    refine ⟨hp1, ⟨hv.1, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t5Opk_length])⟩, ?_⟩
    rw [(s1_next_ok cls).1]
    refine ⟨trivial, trivial, ?_⟩
    rw [(s2_next_ok cls).1]
    refine ⟨trivial, trivial, ?_⟩
    rw [(s3_next_ok cls).1]
    exact ⟨hp4, ⟨hv.2, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [trClean4_length])⟩, trivial⟩
  have hfull : ModelRunWF r (cleanCallSteps cls) :=
    ⟨setupRandoms_len_eq ha hb ho,
     setupTrace_eq_t4Opk ha hb ho ▸ t4Opk_reach,
     setupTrace_eq_t4Opk ha hb ho ▸ hwf,
     stateFaithful_cleanCallSteps r cls⟩
  rw [← List.take_append_drop k (cleanCallSteps cls)] at hfull
  exact modelRunWF_of_append hfull

theorem not_readCollisionCli_ssClean (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (cls : Nat → Nat) (k : Nat)
    (evs : List CliEvent) :
    ¬ ReadCollisionCli interp r S g (ssClean cls k) evs := by
  rintro ⟨_, _, _, ss₁, ss₂, m, _, msgIdx, _, _, _, _, hss, _, _, _, _, hm, _, _⟩
  have hmem : m ∈ cleanCallSteps cls := by
    have hm_take : m ∈ (cleanCallSteps cls).take k := by
      rw [show (cleanCallSteps cls).take k = ss₁ ++ m :: ss₂ from hss]
      exact List.mem_append_right _ List.mem_cons_self
    exact List.mem_of_mem_take hm_take
  simp only [cleanCallSteps, s0Clean, s1Clean, s2Clean, s3Clean, s4Clean,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> cases hm

/-! ## 6. `honestSaltsOf`, `storedStates`, `storedSecrets`, and `bobTrials` at `k = 2` and `k = 5` -/

theorem honestSaltsOf_2 {r : ProtocolSetup} (cls : Nat → Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    honestSaltsOf r (ssClean cls 2) = [zeroKey, key0Opk] := by
  have hn0 : (Step.aliceStart "alice" "bob" 4 6 bhOpk).next t4Opk = t5Opk := s0_next_ok.1
  have hn1 : (Step.messageEncrypt "alice" 34 (cls 0) 37).next t5Opk = trClean2 cls :=
    (s1_next_ok cls).1
  unfold honestSaltsOf ssClean cleanCallSteps
  rw [setupTrace_eq_t4Opk ha hb ho]
  simp only [List.take, honestKeysOf, s0Clean, s1Clean, Step.publishedSpqrKey?,
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
    DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
    hn0, hn1, t5Opk_length,
    show (37 = 35 + 3) = False by decide, ↓reduceIte, Option.toList,
    List.nil_append, List.append_nil]
  have hpq : (trClean2 cls).at? 37 = some (NetE (key0Clean cls)) := by
    dsimp only [trClean2, encTrGen]
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE (key0Clean cls)) (by simp only [append_len, t5Opk_length]))
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hpq, key0Clean_eq]

theorem honestSaltsOf_5 {r : ProtocolSetup} (cls : Nat → Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    honestSaltsOf r (ssClean cls 5) = [zeroKey, key0Opk, key1Opk] := by
  have hn0 : (Step.aliceStart "alice" "bob" 4 6 bhOpk).next t4Opk = t5Opk := s0_next_ok.1
  have hn1 : (Step.messageEncrypt "alice" 34 (cls 0) 37).next t5Opk = trClean2 cls :=
    (s1_next_ok cls).1
  have hn2 : (Step.bobStart "bob" "alice" khOpk 1 mhOpk 37 1).next (trClean2 cls) = trClean3 cls :=
    (s2_next_ok cls).1
  have hn3 : (Step.aliceStart "alice" "bob" 4 6 bhOpk).next (trClean3 cls) = trClean4 cls :=
    (s3_next_ok cls).1
  have hn4 : (Step.messageEncrypt "alice" 60 (cls 1) 63).next (trClean4 cls) = trClean5 cls :=
    (s4_next_ok cls).1
  unfold honestSaltsOf ssClean cleanCallSteps
  rw [setupTrace_eq_t4Opk ha hb ho]
  simp only [List.take, honestKeysOf, s0Clean, s1Clean, s2Clean, s3Clean, s4Clean,
    Step.publishedSpqrKey?,
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx,
    DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
    hn0, hn1, hn2, hn3, hn4, t5Opk_length, trClean4_length,
    show (37 = 35 + 3) = False by decide, show (63 = 61 + 3) = False by decide,
    ↓reduceIte, Option.toList, List.nil_append, List.append_nil]
  have hpq0 : (trClean2 cls).at? 37 = some (NetE (key0Clean cls)) := by
    dsimp only [trClean2, encTrGen]
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE (key0Clean cls)) (by simp only [append_len, t5Opk_length]))
  have hpq1 : (trClean5 cls).at? 63 = some (NetE (key1Clean cls)) := by
    dsimp only [trClean5, encTrGen]
    have hc : rnd ((trClean4 cls).length + 1) (cls 1) = coins1Clean cls := by
      rw [trClean4_length]; rfl
    rw [hc]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ (NetE (key1Clean cls)) (by simp only [append_len, trClean4_length]))
  have hpq0_5 : (trClean2 cls).getMessageSentAt 37 = some (key0Clean cls) := by
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hpq0]
  have hpq1_5 : (trClean5 cls).getMessageSentAt 63 = some (key1Clean cls) := by
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hpq1]
  simp [hpq0_5, hpq1_5, key0Clean_eq, key1Clean_eq]

private theorem range_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [append_len, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self_proj]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

private theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr₀ tr : ExecTrace) (e : E1) (f : Nat → Option E2 → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((newIndices tr₀ (tr.append e)).filterMap fun i => f i ((tr.append e).at? i)) =
      ((newIndices tr₀ tr).filterMap fun i => f i (tr.at? i)) ++
      (f tr.length (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  unfold newIndices
  rw [append_len, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self_proj]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hilt : i < tr.length := by have := List.mem_range'.mp hi; omega
  rw [at?_append_of_lt tr e hilt]

private theorem range_filterMap_at?_append_self {E α : Type}
    [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) (f : Option E → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++ (f (some e)).toList := by
  rw [append_len, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, Trace.at?_append]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

private theorem newIndices_filterMap_at?_append_self {E α : Type}
    [ExecTraceTypes.Has E]
    (tr₀ tr : ExecTrace) (e : E) (f : Nat → Option E → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((newIndices tr₀ (tr.append e)).filterMap fun i => f i ((tr.append e).at? i)) =
      ((newIndices tr₀ tr).filterMap fun i => f i (tr.at? i)) ++
      (f tr.length (some e)).toList := by
  unfold newIndices
  rw [append_len, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Trace.at?_append]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hilt : i < tr.length := by have := List.mem_range'.mp hi; omega
  rw [at?_append_of_lt tr e hilt]

private theorem storedSecrets_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) = none) :
    storedSecrets (tr.append e) = storedSecrets tr := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  rw [range_filterMap_at?_append tr e
    (fun (o : Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) =>
      Option.map DY.Comparse.serialize (Option.map (·.st) o)), hnone]
  exact List.append_nil _

private theorem storedSecrets_append_st (tr : ExecTrace) (me : Participant) (st : PQXDHState) :
    storedSecrets (tr.append (StP me st)) =
      storedSecrets tr ++
      [DY.Comparse.serialize ({ participant := me, state := st } :
        DY.PersistentLocalState.LocalState PQXDHState)] := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  exact range_filterMap_at?_append_self tr (StP me st)
    (fun o => Option.map DY.Comparse.serialize (Option.map (·.st) o))

private theorem storedStates_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (r : ProtocolSetup) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) = storedStates r tr := by
  have h := newIndices_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState))
    (setupTrace r) tr e (fun _ o => o.map (·.st)) hle
  unfold storedStates DY.ExecTrace.getLocalStateAt
  change ((newIndices (setupTrace r) (tr.append e)).filterMap _) =
    ((newIndices (setupTrace r) tr).filterMap _)
  rw [h, hnone]
  exact List.append_nil _

private theorem storedStates_append_st (tr : ExecTrace) (r : ProtocolSetup)
    (me : Participant) (st : TRState)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append (StT me st)) =
      storedStates r tr ++ [{ participant := me, state := st }] := by
  unfold storedStates DY.ExecTrace.getLocalStateAt
  exact newIndices_filterMap_at?_append_self (setupTrace r) tr (StT me st)
    (fun _ o => o.map (·.st)) hle

private theorem storedStates_encTrGen (r : ProtocolSetup) (tr : ExecTrace) (me : Participant)
    (stH cl : Nat) (st : TRState) (pq : Bytes)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (encTrGen tr me stH cl st pq) =
      storedStates r tr ++ [⟨me, encSt st (rnd (tr.length + 1) cl)⟩] := by
  unfold encTrGen; dsimp only
  rw [storedStates_append_non _ r _ rfl (by simp only [append_len]; omega),
      storedStates_append_st _ r _ _ (by simp only [append_len]; omega)]
  repeat rw [storedStates_append_non _ r _ rfl (by simp -failIfUnchanged only [append_len]; omega)]

private theorem storedSecrets_encTrGen (tr : ExecTrace) (me : Participant)
    (stH cl : Nat) (st : TRState) (pq : Bytes) :
    storedSecrets (encTrGen tr me stH cl st pq) = storedSecrets tr := by
  unfold encTrGen; dsimp only
  repeat rw [storedSecrets_append_non _ _ rfl]

def storedStatesClean2 (cls : Nat → Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  [{ participant := "alice", state := stA0Opk },
   { participant := "alice", state := stA1Clean cls }]

def storedStatesClean5 (cls : Nat → Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  [{ participant := "alice", state := stA0Opk },
   { participant := "alice", state := stA1Clean cls },
   { participant := "bob", state := stB1Clean cls },
   { participant := "alice", state := stA2_0Clean },
   { participant := "alice", state := stA2_1Clean cls }]

private theorem storedStates_t5Opk {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    storedStates r t5Opk = [{ participant := "alice", state := stA0Opk }] := by
  have h0 : storedStates r t4Opk = [] := by
    unfold storedStates newIndices
    rw [setupTrace_eq_t4Opk ha hb ho, Nat.sub_self]; rfl
  dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
  rw [storedStates_append_st _ r _ _
    (by simp only [setupTrace_eq_t4Opk ha hb ho, append_len]; omega)]
  repeat rw [storedStates_append_non _ r _ rfl
    (by simp -failIfUnchanged only [setupTrace_eq_t4Opk ha hb ho, append_len]; omega)]
  rw [h0, List.nil_append]
  have hdhs : rnd (t4Opk.length + 2) 32 = dhsAOpk := by rw [t4Opk_length]
  rw [hdhs]; rfl

theorem storedStates_2 {r : ProtocolSetup} (cls : Nat → Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    storedStates r (trClean2 cls) = storedStatesClean2 cls := by
  have hle : (setupTrace r).length ≤ t5Opk.length := by
    rw [setupTrace_eq_t4Opk ha hb ho, t4Opk_length, t5Opk_length]; decide
  dsimp only [trClean2]
  rw [storedStates_encTrGen r t5Opk "alice" 34 (cls 0) stA0Opk (key0Clean cls) hle,
    storedStates_t5Opk ha hb ho]
  have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
  rw [hc]; rfl

theorem storedStates_5 {r : ProtocolSetup} (cls : Nat → Nat)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    storedStates r (trClean5 cls) = storedStatesClean5 cls := by
  have h3 : storedStates r (trClean3 cls) =
      storedStatesClean2 cls ++ [{ participant := "bob", state := stB1Clean cls }] := by
    dsimp only [trClean3]
    rw [storedStates_append_st _ r _ _
      (by simp only [setupTrace_eq_t4Opk ha hb ho, append_len, t4Opk_length, trClean2_length]; omega)]
    repeat rw [storedStates_append_non _ r _ rfl
      (by simp -failIfUnchanged only [setupTrace_eq_t4Opk ha hb ho, append_len,
            t4Opk_length, trClean2_length]; omega)]
    rw [storedStates_2 cls ha hb ho]
  have h4 : storedStates r (trClean4 cls) =
      (storedStatesClean2 cls ++ [{ participant := "bob", state := stB1Clean cls }]) ++
        [{ participant := "alice", state := stA2_0Clean }] := by
    dsimp only [trClean4, aliceTrOpk, aliceTrOpt]
    rw [storedStates_append_st _ r _ _
      (by simp only [setupTrace_eq_t4Opk ha hb ho, append_len, t4Opk_length, trClean3_length]; omega)]
    repeat rw [storedStates_append_non _ r _ rfl
      (by simp -failIfUnchanged only [setupTrace_eq_t4Opk ha hb ho, append_len,
            t4Opk_length, trClean3_length]; omega)]
    rw [h3]
    have hao : aliceOutOpt (trClean3 cls) ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB)) =
        o2Clean := aliceOutOpk_trClean3_eq cls
    rw [hao]
    have hdhs : rnd ((trClean3 cls).length + 2) 32 = dhsA2Clean := by
      rw [trClean3_length]; rfl
    rw [hdhs]; rfl
  have hle4 : (setupTrace r).length ≤ (trClean4 cls).length := by
    rw [setupTrace_eq_t4Opk ha hb ho, t4Opk_length, trClean4_length]; decide
  dsimp only [trClean5]
  rw [storedStates_encTrGen r (trClean4 cls) "alice" 60 (cls 1) stA2_0Clean (key1Clean cls) hle4,
    h4]
  have hc : rnd ((trClean4 cls).length + 1) (cls 1) = coins1Clean cls := by
    rw [trClean4_length]; rfl
  rw [hc]; rfl

def storedSecretsOpk : List Bytes :=
  [DY.Comparse.serialize ({ participant := "alice", state := { kind := .identity, sk := ikA } } :
     DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .identity, sk := ikB } } :
     DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .signedPrekey, sk := spkB } } :
     DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .pqPrekey, sk := pqskB } } :
     DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize ({ participant := "bob", state := { kind := .oneTimePrekey, sk := opkB } } :
     DY.PersistentLocalState.LocalState PQXDHState)]

private theorem storedSecrets_nil : storedSecrets Trace.nil = [] := by
  unfold storedSecrets
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem newRandoms_nil_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Random.ExecEntryT) = none) :
    DY.Libsignal.Composed.Refinement.newRandoms Trace.nil (tr.append e) =
      DY.Libsignal.Composed.Refinement.newRandoms Trace.nil tr := by
  unfold DY.Libsignal.Composed.Refinement.newRandoms
  rw [newIndices_filterMap_at?_append Trace.nil tr e
    (fun i (o : Option DY.Random.ExecEntryT) =>
      o.map fun r => (DY.Libsignal.Composed.Refinement.randTerm i r.length, r.length))
    (by rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega), hnone]
  exact List.append_nil _

private theorem newRandoms_nil_append_rnd (tr : ExecTrace) (n : Nat) :
    DY.Libsignal.Composed.Refinement.newRandoms Trace.nil (tr.append (RndE n)) =
      DY.Libsignal.Composed.Refinement.newRandoms Trace.nil tr ++ [(rnd tr.length n, n)] := by
  unfold DY.Libsignal.Composed.Refinement.newRandoms
  exact newIndices_filterMap_at?_append_self Trace.nil tr (RndE n)
    (fun i (o : Option DY.Random.ExecEntryT) =>
      o.map fun r => (DY.Libsignal.Composed.Refinement.randTerm i r.length, r.length))
    (by rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)

private theorem newRandoms_nil_self :
    DY.Libsignal.Composed.Refinement.newRandoms Trace.nil Trace.nil = [] := by
  unfold DY.Libsignal.Composed.Refinement.newRandoms newIndices
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem setupSent_at_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option DY.Network.ExecEntryT) = none) :
    ((newIndices (Trace.nil : ExecTrace) (tr.append e)).filterMap fun i =>
        (tr.append e).getMessageSentAt i) =
      ((newIndices (Trace.nil : ExecTrace) tr).filterMap fun i => tr.getMessageSentAt i) := by
  unfold newIndices
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1, append_len, Nat.sub_zero, Nat.sub_zero,
    List.range'_concat, show 0 + 1 * tr.length = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, at?_append_self_proj, hnone,
    List.append_nil]
  refine List.filterMap_congr fun i hi => ?_
  have hilt : i < tr.length := by have := List.mem_range'.mp hi; omega
  rw [at?_append_of_lt tr e hilt]

private theorem setupSent_at_append_net (tr : ExecTrace) (m : Bytes) :
    ((newIndices (Trace.nil : ExecTrace) (tr.append (NetE m))).filterMap fun i =>
        (tr.append (NetE m)).getMessageSentAt i) =
      ((newIndices (Trace.nil : ExecTrace) tr).filterMap fun i => tr.getMessageSentAt i) ++ [m] := by
  unfold newIndices
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1, append_len, Nat.sub_zero, Nat.sub_zero,
    List.range'_concat, show 0 + 1 * tr.length = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, Trace.at?_append]
  refine congrArg (· ++ [m]) (List.filterMap_congr fun i hi => ?_)
  have hilt : i < tr.length := by have := List.mem_range'.mp hi; omega
  rw [at?_append_of_lt tr (NetE m) hilt]

private theorem setupSent_at_nil :
    ((newIndices Trace.nil Trace.nil).filterMap fun i => (Trace.nil : ExecTrace).getMessageSentAt i) = [] := by
  unfold newIndices
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

local macro "reduce_setupSent" : tactic =>
  `(tactic| repeat (first
    | rw [setupSent_at_append_net]
    | rw [setupSent_at_append_non _ _ rfl]))

local macro "reduce_newRandoms" : tactic =>
  `(tactic| repeat (first
    | rw [newRandoms_nil_append_rnd]
    | rw [newRandoms_nil_append_non _ _ rfl]))

local macro "reduce_storedSecrets" : tactic =>
  `(tactic| repeat (first
    | rw [storedSecrets_append_st]
    | rw [storedSecrets_append_non _ _ rfl]))

theorem setupPublic_eqs {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    setupPublic r 0 = dhPk ikA ∧
    setupPublic r 2 = dhPk ikB ∧
    setupPublic r 4 = dhPk spkB ∧
    setupPublic r 6 = kemPk pqskB ∧
    setupPublic r 8 = dhPk opkB := by
  obtain ⟨ht1, ht2, ht3, ht4, _, _, _, _, _, _, _, _, _, _⟩ := t4_entry_facts
  have hsent : setupSent r =
      [dhPk ikA, DY.Signature.vk ikA, dhPk ikB, DY.Signature.vk ikB,
       dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
       kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)),
       dhPk opkB] := by
    unfold setupSent
    rw [setupTrace_eq_t4Opk ha hb ho]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    reduce_setupSent
    rw [t4_length, ht4]; dsimp only [genPQPrekeyTr]
    reduce_setupSent
    rw [t3_length, ht3]; dsimp only [genSignedPrekeyTr]
    reduce_setupSent
    rw [t2_length, ht2]; dsimp only [registerIdentityTr]
    reduce_setupSent
    rw [t1_length, ht1]; dsimp only [registerIdentityTr]
    reduce_setupSent
    rw [setupSent_at_nil, Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold setupPublic; rw [hsent]; rfl)

theorem setupSecret_eqs {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true) :
    setupSecret r 0 = ikA ∧
    setupSecret r 1 = ikB ∧
    setupSecret r 2 = spkB ∧
    setupSecret r 4 = pqskB ∧
    setupSecret r 6 = opkB := by
  obtain ⟨ht1, ht2, ht3, ht4, _, _, _, _, _, _, _, _, _, _⟩ := t4_entry_facts
  have hrnds : setupRandoms r = [ikA, ikB, spkB, spkNonce, pqskB, pqNonce, opkB] := by
    unfold setupRandoms
    rw [setupTrace_eq_t4Opk ha hb ho]
    dsimp only [t4Opk, genOneTimePrekeyTr]
    reduce_newRandoms
    rw [t4_length, ht4]; dsimp only [genPQPrekeyTr]
    reduce_newRandoms
    simp only [append_len, t3_length]
    rw [ht3]; dsimp only [genSignedPrekeyTr]
    reduce_newRandoms
    simp only [append_len, t2_length]
    rw [ht2]; dsimp only [registerIdentityTr]
    reduce_newRandoms
    rw [t1_length, ht1]; dsimp only [registerIdentityTr]
    reduce_newRandoms
    rw [newRandoms_nil_self, Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold setupSecret; rw [hrnds]; rfl)

private theorem storedSecrets_t5Opk : storedSecrets t5Opk = storedSecretsOpk := by
  obtain ⟨ht1, ht2, ht3, ht4, _, _, _, _, _, _, _, _, _, _⟩ := t4_entry_facts
  dsimp only [t5Opk, aliceTrOpk, aliceTrOpt]
  reduce_storedSecrets
  dsimp only [t4Opk, genOneTimePrekeyTr]
  reduce_storedSecrets
  rw [t4_length, ht4]; dsimp only [genPQPrekeyTr]
  reduce_storedSecrets
  rw [t3_length, ht3]; dsimp only [genSignedPrekeyTr]
  reduce_storedSecrets
  rw [t2_length, ht2]; dsimp only [registerIdentityTr]
  reduce_storedSecrets
  rw [t1_length, ht1]; dsimp only [registerIdentityTr]
  reduce_storedSecrets
  rw [storedSecrets_nil, Symbolic.DYBridge.DY.Trace.length_eq_1]
  rfl

theorem storedSecrets_2 (cls : Nat → Nat) : storedSecrets (trClean2 cls) = storedSecretsOpk := by
  dsimp only [trClean2]
  rw [storedSecrets_encTrGen, storedSecrets_t5Opk]

theorem storedSecrets_5 (cls : Nat → Nat) : storedSecrets (trClean5 cls) = storedSecretsOpk := by
  dsimp only [trClean5]
  rw [storedSecrets_encTrGen]
  dsimp only [trClean4, aliceTrOpk, aliceTrOpt]
  reduce_storedSecrets
  dsimp only [trClean3]
  reduce_storedSecrets
  exact storedSecrets_2 cls

def bobCtx2 : TrialCtx :=
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keysOpk.rk, keysOpk.ck, keysOpk.pqr, stA0Opk.cks, (kdfCk stA0Opk.cks).1]
    ownSalts := [key0Opk]
    seed? := some (kdfCk stA0Opk.cks).2 }

def bobCtx5 : TrialCtx :=
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keys2Clean.rk, keys2Clean.ck, keys2Clean.pqr, stA2_0Clean.cks, (kdfCk stA2_0Clean.cks).1]
    ownSalts := [key1Opk]
    seed? := some (kdfCk stA2_0Clean.cks).2 }

private theorem ite_eq_nil_or {α : Type} (c : Bool) {xs ys : List α} (h : xs = ys) :
    (if c = true then [] else xs) = [] ∨ (if c = true then [] else xs) = ys := by
  subst h; cases c <;> simp

theorem bobTrials_2 {r : ProtocolSetup} (cls : Nat → Nat) (tr : DY.ExecTrace)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true)
    (hopkId : r.opkId = 3#32) :
    bobTrials r tr p2 (cleanPreKeyRep cls 2)
        (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean) = [] ∨
      bobTrials r tr p2 (cleanPreKeyRep cls 2)
        (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean) = [bobCtx2] := by
  obtain ⟨hp0, hp2, _, _, _⟩ := setupPublic_eqs ha hb ho
  obtain ⟨_, hs1, hs2, hs4, hs6⟩ := setupSecret_eqs ha hb ho
  obtain ⟨_, hpkId, _, _, _, _, _, hspqrIdx, _⟩ := p2_fields_base
  unfold bobTrials
  rw [hpkId, hspqrIdx, ho, hopkId]
  simp only [BEq.rfl, Bool.true_and, ↓reduceIte]
  refine ite_eq_nil_or _ ?_
  dsimp only [ProtocolSetup.ikAPubTerm, ProtocolSetup.ikBPubTerm,
    ProtocolSetup.ikBSecTerm, ProtocolSetup.spkSecTerm,
    ProtocolSetup.pqskSecTerm, ProtocolSetup.opkSecTerm]
  rw [hp0, hp2, hs1, hs2, hs4, hs6]
  have hct_eq : (cleanPreKeyRep cls 2).ct = (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).1 := by
    dsimp only [cleanPreKeyRep, oOpk, aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt, aliceAgreement]
    rw [t4Opk_length]; rfl
  have hek_eq : (cleanPreKeyRep cls 2).ek = dhPk (rnd 26 32) := by
    dsimp only [cleanPreKeyRep, oOpk, aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t4Opk_length]; rfl
  have hss : (errToOption (DY.PQKem.kemDecap pqskB (cleanPreKeyRep cls 2).ct)).getD
      (DY.PQKem.kemRejKey pqskB (cleanPreKeyRep cls 2).ct) =
      (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).2 := by
    rw [hct_eq, kemDecap_kemEncap]; rfl
  rw [hss, hek_eq]
  have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (dhPk (rnd 26 32)) ikB)
      (agree (dhPk (rnd 26 32)) spkB)
      (Option.map (agree (dhPk (rnd 26 32))) (some opkB))
      (DY.PQKem.kemEncap (kemPk pqskB) (rnd 27 32)).2) = keysOpk := by
    have h2 : keysOpk =
        (aliceAgreement ikA (rnd 26 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB))
          (rnd 27 32)).2 := by
      dsimp only [keysOpk, oOpk, aliceOutOpk,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
      rw [t4Opk_length]; rfl
    rw [h2]; dsimp only [aliceAgreement, Option.map]
    rw [agree_comm ikA spkB, agree_comm (rnd 26 32) ikB, agree_comm (rnd 26 32) spkB,
      agree_comm (rnd 26 32) opkB]
  rw [hkeys]
  have hc : (createChain keysOpk.rk
      (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).ratchetKey spkB).2 =
      stA0Opk.cks := by
    show (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2 =
      (createChain keysOpk.rk (dhPk spkB) dhsAOpk).2
    rw [createChain_comm keysOpk.rk dhsAOpk spkB]
  rw [hc]
  have hcnt : (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).counter = 0 := rfl
  have hpqm : (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).pqRatchet =
      pqm0Clean cls := rfl
  rw [hcnt, hpqm]
  dsimp only [consumeMessageKey, skippedSeeds, List.append_nil]
  have hrecv : spqrRecv (spqrInit keysOpk.pqr spqrB2A) (pqm0Clean cls) 1 =
      some (recvSt (spqrInit keysOpk.pqr spqrB2A) (pqm0Clean cls), key0Opk) := by
    have h0 := spqrRecv_init_b2a_1 keysOpk.pqr (pqm0Clean cls) (bytesToLiteral_spqrSendMsg _ _)
    exact h0.trans (congrArg (fun k => some (_, k)) spqrChainKey_keysOpk_eq)
  rw [hrecv]; rfl

theorem bobTrials_5 {r : ProtocolSetup} (cls : Nat → Nat) (tr : DY.ExecTrace)
    (ha : r.alice = "alice") (hb : r.bob = "bob") (ho : r.withOpk = true)
    (hopkId : r.opkId = 3#32) :
    bobTrials r tr p5 (cleanPreKeyRep cls 5)
        (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean) = [] ∨
      bobTrials r tr p5 (cleanPreKeyRep cls 5)
        (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean) = [bobCtx5] := by
  obtain ⟨hp0, hp2, _, _, _⟩ := setupPublic_eqs ha hb ho
  obtain ⟨_, hs1, hs2, hs4, hs6⟩ := setupSecret_eqs ha hb ho
  obtain ⟨_, hpkId, _, _, _, _, _, hspqrIdx, _⟩ := p5_fields_base
  unfold bobTrials
  rw [hpkId, hspqrIdx, ho, hopkId]
  simp only [BEq.rfl, Bool.true_and, ↓reduceIte]
  refine ite_eq_nil_or _ ?_
  dsimp only [ProtocolSetup.ikAPubTerm, ProtocolSetup.ikBPubTerm,
    ProtocolSetup.ikBSecTerm, ProtocolSetup.spkSecTerm,
    ProtocolSetup.pqskSecTerm, ProtocolSetup.opkSecTerm]
  rw [hp0, hp2, hs1, hs2, hs4, hs6]
  have hct_eq : (cleanPreKeyRep cls 5).ct = (DY.PQKem.kemEncap (kemPk pqskB) (rnd 53 32)).1 := by
    dsimp only [cleanPreKeyRep, o2Clean, aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt, aliceAgreement]
    rw [t7Opk_length]; rfl
  have hek_eq : (cleanPreKeyRep cls 5).ek = dhPk (rnd 52 32) := by
    dsimp only [cleanPreKeyRep, o2Clean, aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t7Opk_length]; rfl
  have hss : (errToOption (DY.PQKem.kemDecap pqskB (cleanPreKeyRep cls 5).ct)).getD
      (DY.PQKem.kemRejKey pqskB (cleanPreKeyRep cls 5).ct) =
      (DY.PQKem.kemEncap (kemPk pqskB) (rnd 53 32)).2 := by
    rw [hct_eq, kemDecap_kemEncap]; rfl
  rw [hss, hek_eq]
  have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree (dhPk (rnd 52 32)) ikB)
      (agree (dhPk (rnd 52 32)) spkB)
      (Option.map (agree (dhPk (rnd 52 32))) (some opkB))
      (DY.PQKem.kemEncap (kemPk pqskB) (rnd 53 32)).2) = keys2Clean := by
    have h2 : keys2Clean =
        (aliceAgreement ikA (rnd 52 32) (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB))
          (rnd 53 32)).2 := by
      dsimp only [keys2Clean, o2Clean, aliceOutOpk,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
      rw [t7Opk_length]; rfl
    rw [h2]; dsimp only [aliceAgreement, Option.map]
    rw [agree_comm ikA spkB, agree_comm (rnd 52 32) ikB, agree_comm (rnd 52 32) spkB,
      agree_comm (rnd 52 32) opkB]
  rw [hkeys]
  have hc : (createChain keys2Clean.rk
      (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).ratchetKey spkB).2 =
      stA2_0Clean.cks := by
    show (createChain keys2Clean.rk (dhPk dhsA2Clean) spkB).2 =
      (createChain keys2Clean.rk (dhPk spkB) dhsA2Clean).2
    rw [createChain_comm keys2Clean.rk dhsA2Clean spkB]
  rw [hc]
  have hcnt : (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).counter = 0 := rfl
  have hpqm : (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).pqRatchet =
      pqm1Clean cls := rfl
  rw [hcnt, hpqm]
  dsimp only [consumeMessageKey, skippedSeeds, List.append_nil]
  have hrecv : spqrRecv (spqrInit keys2Clean.pqr spqrB2A) (pqm1Clean cls) 1 =
      some (recvSt (spqrInit keys2Clean.pqr spqrB2A) (pqm1Clean cls), key1Opk) :=
    spqrRecv_init_b2a_1 keys2Clean.pqr (pqm1Clean cls) (bytesToLiteral_spqrSendMsg _ _)
  rw [hrecv]; rfl

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
