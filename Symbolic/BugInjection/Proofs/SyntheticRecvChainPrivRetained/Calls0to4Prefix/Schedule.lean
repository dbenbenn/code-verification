/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Parse
public import Symbolic.Proofs.Tests.Shared.Composed.HonestSession
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Tests.Nonvacuity
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean 5-Step Symbolic Schedule & Front-to-Back Peeling (`Calls0to4Prefix/Schedule.lean`)

Provides:
1. The 5-step clean symbolic schedule (`cleanCallSteps cls`, `ssClean cls k`, `trClean1..trClean5`,
   `s0_next_ok..s4_next_ok`, `modelRunWF_ssClean`).
2. Front-to-back `MatchesEventsAt` peeling (`PeeledValid`, `peel_evsRange`, `clsOfCalls`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace Participant Trace Traceful ExecTraceTypes TraceEntryHas)
open DY.Bytes (view?)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Spqr (spqrInit spqrSend spqrRecv)
open DY.X25519 (normalizeX25519Key)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain SessionInfo findRecvChain kdfCk createChain setRecvChain
   isCurrentSnapshot maxReceiverChains spqrB2A u32Max)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   setupTrace setupRandoms runSteps StepsWF StepsStateFaithful ModelRunWF
   RunMatches MatchesEventsAt nextBundleIds stepIn)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs bobSt0 bobAgreement_honest encSt encMsg encSig parse_encMsg
   ratchetState recvSt recvKey mac_ok dec_ok rnd createChain_comm
   aliceTr aliceTrOpt skipTr dhPk_rnd_ne StT RndE NetE EvP EvT EvC)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA o1 keys1 stA0 bh1 kh1 mh1
   t1 t2 t3 t4 t5 t1_length t2_length t3_length t4_length t5_length t4_reach t5_runs)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprHooks0 rcprCompFitsPinned rcprTrace)

attribute [local irreducible] ev

/-! ## 1. Clean 5-Step Symbolic Schedule (`Calls 0..4`) & `ModelRunWF` -/

/-- Valid SPQR coin draw lengths for the 2 `.send` steps (`s = 0, 1`). -/
def ValidCoinLens (cls : Nat → Nat) : Prop :=
  ∀ s < 2, cls s = 0 ∨ cls s = 32 ∨ cls s = 64

/-- All timestamps `ts` whose `dhPk (rnd ts 32)` can appear as a `RecvChain.ratchetKey` in `ssClean`. -/
def ratchetKeyTimestamps : List Nat := [10, 24, 38, 54]

theorem r_names_of_fit {r : ProtocolSetup}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    r.alice = "alice" ∧ r.bob = "bob" := hfit.1.2.2.2.1

theorem append_len {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem le_append_of_le {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace}
    (h : t1 ≤ t2) (e : E) : t1 ≤ t2.append e :=
  Trace.le_trans _ _ _ h (Trace.append_le t2 e)

theorem at?_mono {E : Type} [ExecTraceTypes.Has E] {t1 t2 : ExecTrace} {i : Nat} {x : E}
    (hle : t1 ≤ t2) (h : t1.at? i = some x) : t2.at? i = some x := by
  have := Trace.at?_le (EntryT := E) t1 t2 i hle; rwa [h] at this

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
  simp only [Trace.at?, hi, hi', ↓reduceDIte, Symbolic.DYBridge.DY.Trace.at_eq_2, show i ≠ tr.length by omega]

private theorem runs_cast {α : Type} {x : Traceful α} {tr t1 t2 : ExecTrace} {a1 a2 : α}
    (h : Runs x tr a1 t1) (ha : a1 = a2) (ht : t1 = t2) : Runs x tr a2 t2 := by
  subst ha; subst ht; exact h

theorem stepIn_next (c : DY.ReachabilityConfig) [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (inst.pf_step x).symm

theorem stepIn_isSome (c : DY.ReachabilityConfig) [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => ((s.2.run tr).1).isSome) (inst.pf_step x).symm

theorem setupTrace_eq_t4 {r : ProtocolSetup} (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    setupTrace r = t4 := by
  have ⟨ha, hb⟩ := r_names_of_fit hfit
  unfold setupTrace; rw [ha, hb, hfit.1.1.2.1]; exact Symbolic.Proofs.Tests.Nonvacuity.keySetupTrace_eq

theorem setupRandoms_len_eq {r : ProtocolSetup} (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    (setupRandoms r).length = (if r.withOpk then 7 else 6) := by
  have ⟨ha, hb⟩ := r_names_of_fit hfit
  exact Symbolic.Swarm.CREF.TR.setupRandoms_length r (by rw [ha, hb]; decide)

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
    (hst : tr.at? stH = some (StT me st)) (hns : st.ns ≠ u32Max)
    (hpq : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)).at? pqH = some (NetE pq)) :
    Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pqH) tr (tr.length + 6)
      (encTrGen tr me stH cl st pq) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine Runs.bind (Runs.getLocalState hst) (Runs.bind (Runs.guard _ hns)
    (Runs.bind (Runs.genRand _ _) (Runs.bind (Runs.genRand _ _)
    (Runs.bind (Runs.sendMessage _ _) ?_))))
  have hpq' : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (spqrSend st.spqr (rnd (tr.append (RndE 32)).length cl)).2.1)).at? pqH = some (NetE pq) := by
    rw [append_len]; exact hpq
  refine Runs.bind (Runs.receiveMessage hpq') (Runs.bind (Runs.logEvent _ _)
    (Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _)
    (runs_cast (Runs.sendMessage _ _) ?_ ?_)))
  · simp only [NetE, EvT, StT, append_len, Nat.add_assoc]
  · simp only [encTrGen, encSt, encMsg, RndE, NetE, EvT, StT, append_len]; dsimp only [kdfCk, spqrSend]

theorem x25519LowOrder_dhPk (sk : Bytes) :
    DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk sk) = false := by
  have hv : (dhPk sk).view? DY.X25519.Variant.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _
  have hl0 : (dhPk sk).view? DY.Literal.Literal.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF _
  have hl : DY.Literal.bytesToLiteral (dhPk sk) = none := by
    dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]; rw [hl0]
  unfold DY.Libsignal.TripleRatchet.x25519LowOrder normalizeX25519Key; rw [hv, hl]

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
  dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
  rw [hl0]

theorem spqrSend_st_not_init (st coins : Bytes) :
    (spqrSend st coins).1.view? DY.Spqr.InitState.SubF = none := by
  dsimp only [spqrSend]
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF _

private theorem skipTr_zero (tr : ExecTrace) (s : SessionInfo) (pk : Bytes) (c : RecvChain)
    (src : Nat) (n : UInt32) (hz : n.toNat - c.index.toNat = 0) :
    skipTr tr s pk c src n = tr := by
  dsimp only [skipTr]; rw [hz]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, Traceful.run_pure]

theorem isCurrentSnapshot_self (tr : ExecTrace) (me : Participant) (st : TRState)
    {k : Nat} (hk : tr.length = k) :
    isCurrentSnapshot (tr.append (StT me st)) k = true := by
  subst hk
  unfold isCurrentSnapshot DY.Libsignal.TripleRatchet.getStoredLocalStateAt?
  rw [Trace.at?_append tr (StT me st), append_len, Nat.sub_self]; rfl

theorem isCurrentSnapshot_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {k : Nat} (e : E)
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
    · rw [at?_append_self_proj, hnone]

theorem isCurrentSnapshot_st_ne {tr : ExecTrace} {me me' : Participant}
    {st st' : TRState} {k : Nat}
    (hst : tr.at? k = some (StT me st)) (hne : (me' != me) = true)
    (hcur : isCurrentSnapshot tr k = true) :
    isCurrentSnapshot (tr.append (StT me' st')) k = true := by
  have hk : k < tr.length := by
    have := Trace.at?_eq_some_implies_length_le
      (EntryT := DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState)) tr k
    rwa [hst] at this
  unfold isCurrentSnapshot DY.Libsignal.TripleRatchet.getStoredLocalStateAt? at hcur ⊢
  rw [hst] at hcur
  rw [at?_mono (Trace.append_le tr (StT me' st')) hst]
  dsimp only [Option.map] at hcur ⊢
  have hsub : (tr.append (StT me' st')).length - (k + 1) = (tr.length - (k + 1)) + 1 := by
    rw [append_len]; omega
  rw [hsub, List.range'_concat, show (k + 1) + 1 * (tr.length - (k + 1)) = tr.length by omega,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true] at hcur ⊢
    intro j hj
    rw [at?_append_of_lt tr (StT me' st') (by rw [List.mem_range'_1] at hj; omega)]
    exact hcur j hj
  · rw [Trace.at?_append]; simp [hne]

/-! ### Clean States, Messages, & Traces `trClean1 .. trClean5` -/

abbrev trClean1 : ExecTrace := t5

theorem trClean1_length : trClean1.length = 31 := t5_length

abbrev pt0Clean : Bytes := rnd 31 32
abbrev coins0Clean (cls : Nat → Nat) : Bytes := rnd 32 (cls 0)
def key0Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0.spqr (coins0Clean cls)).2.1
def pqm0Clean (cls : Nat → Nat) : Bytes := (spqrSend stA0.spqr (coins0Clean cls)).2.2
def stA1Clean (cls : Nat → Nat) : TRState := encSt stA0 (coins0Clean cls)
def m0Clean (cls : Nat → Nat) : Bytes := encMsg stA0 (coins0Clean cls) (key0Clean cls) pt0Clean
def trClean2 (cls : Nat → Nat) : ExecTrace := encTrGen t5 "alice" 30 (cls 0) stA0 (key0Clean cls)

theorem trClean2_length (cls : Nat → Nat) : (trClean2 cls).length = 38 := by
  rw [trClean2, encTrGen_length, t5_length]

abbrev dhsB1Clean : Bytes := rnd 38 32
abbrev dhsBClean : Bytes := dhsB1Clean

def stB20Clean (cls : Nat → Nat) : TRState :=
  bobSt0 "alice" ikB spkB (dhPk ikA) keys1 (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean)
def stB20'Clean (cls : Nat → Nat) : TRState :=
  (ratchetState (stB20Clean cls) (dhPk dhsA) dhsB1Clean).1
def cBClean : RecvChain :=
  { ratchetKey := dhPk dhsA, chainKey := (createChain keys1.rk (dhPk dhsA) spkB).2,
    index := 0, rIdx := 2 }
def cB'Clean : RecvChain := { cBClean with chainKey := (kdfCk cBClean.chainKey).1, index := 1 }
def seedB0Clean : Bytes := (kdfCk cBClean.chainKey).2
def stB2Clean (cls : Nat → Nat) : TRState :=
  { stB20'Clean cls with
      recv := [cB'Clean]
      spqr := recvSt (spqrInit keys1.pqr spqrB2A) (pqm0Clean cls) }

def trClean3 (cls : Nat → Nat) : ExecTrace :=
  let tr1 := ((trClean2 cls).append (RndE 32)).append (NetE (key0Clean cls))
  let tr5 := (((tr1.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
      (kemPk pqskB) none o1.ek o1.ct keys1))).append
      (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1Clean)))).append
      (EvT (.HonestDH ((stB20'Clean cls).sessionInfo "bob") dhsB1Clean 0))).append
      (EvC (.HandshakeSession ((stB20'Clean cls).sessionInfo "bob") 40))
  ((tr5.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 pt0Clean))).append
    (EvT (.MessageKey ((stB20'Clean cls).sessionInfo "bob") .receiver seedB0Clean (key0Clean cls)
      0 2 46))).append
    (StT "bob" (stB2Clean cls))

theorem trClean3_length (cls : Nat → Nat) : (trClean3 cls).length = 47 := by
  dsimp only [trClean3]; simp only [append_len, trClean2_length]

abbrev pt1Clean : Bytes := rnd 47 32
abbrev coins1Clean (cls : Nat → Nat) : Bytes := rnd 48 (cls 1)
def key1Clean (cls : Nat → Nat) : Bytes := (spqrSend (stB2Clean cls).spqr (coins1Clean cls)).2.1
def pqm1Clean (cls : Nat → Nat) : Bytes := (spqrSend (stB2Clean cls).spqr (coins1Clean cls)).2.2
def stB3Clean (cls : Nat → Nat) : TRState := encSt (stB2Clean cls) (coins1Clean cls)
def m1Clean (cls : Nat → Nat) : Bytes :=
  encMsg (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean
def trClean4 (cls : Nat → Nat) : ExecTrace :=
  encTrGen (trClean3 cls) "bob" 46 (cls 1) (stB2Clean cls) (key1Clean cls)

theorem trClean4_length (cls : Nat → Nat) : (trClean4 cls).length = 54 := by
  rw [trClean4, encTrGen_length, trClean3_length]

abbrev dhsA1Clean : Bytes := rnd 54 32
def stA3'Clean (cls : Nat → Nat) : TRState :=
  (ratchetState (stA1Clean cls) (dhPk dhsB1Clean) dhsA1Clean).1
def cA0Clean : RecvChain :=
  { ratchetKey := dhPk spkB, chainKey := keys1.ck, index := 0, rIdx := 1 }
def cA1RawClean : RecvChain :=
  { ratchetKey := dhPk dhsB1Clean, chainKey := (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2,
    index := 0, rIdx := 3 }
def cA1Clean : RecvChain :=
  { cA1RawClean with chainKey := (kdfCk cA1RawClean.chainKey).1, index := 1 }
def seedA1Clean : Bytes := (kdfCk cA1RawClean.chainKey).2
def stA4Clean (cls : Nat → Nat) : TRState :=
  { stA3'Clean cls with
      recv := [cA0Clean, cA1Clean]
      spqr := recvSt (stA1Clean cls).spqr (pqm1Clean cls) }

def trClean5 (cls : Nat → Nat) : ExecTrace :=
  let tr1 := ((((trClean4 cls).append (RndE 32)).append
      (NetE (recvKey (stA1Clean cls).spqr (pqm1Clean cls)))).append
      (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1Clean) (dhPk dhsA1Clean)))).append
      (EvT (.HonestDH ((stA3'Clean cls).sessionInfo "alice") dhsA1Clean 1))
  ((tr1.append (EvT (.Received "alice" "bob" (dhPk dhsB1Clean) 0 pt1Clean))).append
    (EvT (.MessageKey ((stA3'Clean cls).sessionInfo "alice") .receiver seedA1Clean (key1Clean cls)
      0 3 36))).append
    (StT "alice" (stA4Clean cls))

theorem trClean5_length (cls : Nat → Nat) : (trClean5 cls).length = 61 := by
  dsimp only [trClean5]; simp only [append_len, trClean4_length]

def s0Clean : Step := .aliceStart "alice" "bob" 4 6 bh1
def s1Clean (cls : Nat → Nat) : Step := .messageEncrypt "alice" 30 (cls 0) 33
def s2Clean : Step := .bobStart "bob" "alice" kh1 1 mh1 33 1
def s3Clean (cls : Nat → Nat) : Step := .messageEncrypt "bob" 46 (cls 1) 49
def s4Clean : Step := .messageDecrypt "alice" 36 53 49 1

def cleanCallSteps (cls : Nat → Nat) : List Step :=
  [s0Clean, s1Clean cls, s2Clean, s3Clean cls, s4Clean]

theorem cleanCallSteps_length (cls : Nat → Nat) : (cleanCallSteps cls).length = 5 := rfl

def ssClean (cls : Nat → Nat) (k : Nat) : List Step :=
  (cleanCallSteps cls).take k

theorem ssClean_succ (cls : Nat → Nat) {k : Nat} (hk : k < 5) :
    ∃ s, (cleanCallSteps cls)[k]? = some s ∧ ssClean cls (k + 1) = ssClean cls k ++ [s] := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => exact ⟨_, rfl, rfl⟩
  | n + 5 => omega

/-! ### Clean Symbolic Step Execution (`s0_next_ok .. s4_next_ok`) -/

private theorem t4_le_t5 : t4 ≤ t5 := by
  dsimp only [t5, aliceTr, aliceTrOpt]
  iterate 8 refine le_append_of_le ?_ _
  exact Trace.append_le _ _

private theorem trClean2_le_trClean3 (cls : Nat → Nat) : trClean2 cls ≤ trClean3 cls := by
  dsimp only [trClean3]
  iterate 8 refine le_append_of_le ?_ _
  exact Trace.append_le _ _

private theorem t4_pki_at :
    t4.at? 1 = some (EvP (.IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true)) ∧
    t4.at? 9 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .identity, sk := ikB }) ∧
    t4.at? 13 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .signedPrekey, sk := spkB }) ∧
    t4.at? 19 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .pqPrekey, sk := pqskB }) := by
  have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have someEventB_nil : ∀ p : DY.Libsignal.PQXDH.PQXDHEvent → Bool,
      DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent Trace.nil p = false := fun p => by
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?, nil_len]; rfl
  have someEventB_non : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
      (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool),
      (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = none →
      DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent (tr.append x) p = false := by
    intro E _ tr x p hnone h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
      exact h i hi
    · rw [at?_append_self_proj, hnone]
  have someEventB_ev : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent)
      (p : DY.Libsignal.PQXDH.PQXDHEvent → Bool), p ev = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace DY.Libsignal.PQXDH.PQXDHEvent (tr.append (EvP ev)) p = false := by
    intro tr ev p hp h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
      exact h i hi
    · rw [Trace.at?_append]; exact hp
  have ht1 : t1 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2
  have ht2 : t2 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr t1 "bob" := by
    refine (Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_nil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have ht3 : t3 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey hb2).2
  have h23 : t2 ≤ t3 := by
    rw [ht3]; iterate 5 refine le_append_of_le ?_ _
    exact Trace.append_le _ _
  have ht4 : t4 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey (at?_mono h23 hb2)).2
  have h12 : t1 ≤ t2 := by
    rw [ht2]; iterate 4 refine le_append_of_le ?_ _
    exact Trace.append_le _ _
  have h34 : t3 ≤ t4 := by
    rw [ht4]; iterate 5 refine le_append_of_le ?_ _
    exact Trace.append_le _ _
  have h24 : t2 ≤ t4 := Trace.le_trans _ _ _ h23 h34
  have h14 : t1 ≤ t4 := Trace.le_trans _ _ _ h12 h24
  refine ⟨?_, at?_mono h24 hb2, ?_, ?_⟩
  · refine at?_mono h14 ?_; rw [ht1]
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]; rw [nil_len]
    exact at?_mono (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _)
      (at?_append_at _ _ (by simp only [append_len, nil_len]))
  · refine at?_mono h34 ?_; rw [ht3]
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr]; rw [t2_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t2_length]))
  · rw [ht4]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr]; rw [t3_length]
    exact at?_mono (le_append_of_le (Trace.append_le _ _) _)
      (at?_append_at _ _ (by simp only [append_len, t3_length]))

theorem s0_next_ok : s0Clean.next t4 = t5 ∧ s0Clean.ok t4 = true :=
  ⟨(stepIn_next DY.Libsignal.Composed.aliceStart.reachability _ t4).trans t5_runs.2,
   (stepIn_isSome DY.Libsignal.Composed.aliceStart.reachability _ t4).trans
     (congrArg Option.isSome t5_runs.1)⟩

theorem s1_next_ok (cls : Nat → Nat) :
    (s1Clean cls).next t5 = trClean2 cls ∧ (s1Clean cls).ok t5 = true := by
  have hst : t5.at? 30 = some (StT "alice" stA0) := by
    dsimp only [t5, aliceTr, aliceTrOpt, stA0, dhsA]
    rw [show rnd (t4.length + 2) 32 = rnd 24 32 by rw [t4_length]]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hpq : (((t5.append (RndE 32)).append (RndE (cls 0))).append
      (NetE (spqrSend stA0.spqr (rnd (t5.length + 1) (cls 0))).2.1)).at? 33 =
      some (NetE (key0Clean cls)) := by
    rw [show rnd (t5.length + 1) (cls 0) = coins0Clean cls by rw [t5_length]]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  have hns : stA0.ns ≠ u32Max := by
    dsimp only [stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]; decide
  have hr := Runs.messageEncryptGen hst hns hpq
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ t5).trans
      (congrArg Option.isSome hr.1)⟩

theorem s2_next_ok (cls : Nat → Nat) :
    s2Clean.next (trClean2 cls) = trClean3 cls ∧ s2Clean.ok (trClean2 cls) = true := by
  obtain ⟨ha1, hb9, hs13, hp19⟩ := t4_pki_at
  have h52 : t5 ≤ trClean2 cls := encTrGen_le _ _ _ _ _ _
  have h42 : t4 ≤ trClean2 cls := Trace.le_trans _ _ _ t4_le_t5 h52
  have hek : (trClean2 cls).at? 25 = some (NetE o1.ek) := by
    refine at?_mono h52 ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hct : (trClean2 cls).at? 26 = some (NetE o1.ct) := by
    refine at?_mono h52 ?_; dsimp only [t5, aliceTr, aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hmsg : (trClean2 cls).at? 37 = some (NetE (m0Clean cls)) := by
    dsimp only [trClean2, encTrGen, m0Clean, pt0Clean, coins0Clean]
    rw [t5_length]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  have hpq : (((trClean2 cls).append (RndE 32)).append (NetE (key0Clean cls))).at? 33 =
      some (NetE (key0Clean cls)) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [trClean2, encTrGen]
    rw [show rnd (t5.length + 1) (cls 0) = coins0Clean cls by rw [t5_length]]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hrs : ratchetState (stB20Clean cls)
      (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).ratchetKey
      (rnd (trClean2 cls).length 32) = (stB20'Clean cls, cBClean) := by
    rw [trClean2_length]; rfl
  have hset : setRecvChain (stB20'Clean cls).recv cB'Clean = [cB'Clean] := by
    simp [setRecvChain, stB20'Clean, ratchetState, cB'Clean, cBClean, stB20Clean, bobSt0,
      maxReceiverChains]
  have hspqr : spqrRecv (stB20'Clean cls).spqr (pqm0Clean cls) 1 =
      some (recvSt (spqrInit keys1.pqr spqrB2A) (pqm0Clean cls), key0Clean cls) := by
    unfold spqrRecv DY.Spqr.spqrEmptyMsg pqm0Clean
    rw [bytesToLiteral_spqrSendMsg]
    have hinit : (stB20'Clean cls).spqr.view? DY.Spqr.InitState.SubF =
        some { authKey := keys1.pqr, params := spqrB2A } := by
      dsimp only [stB20'Clean, ratchetState, stB20Clean, bobSt0, spqrInit]
      exact DY.BytesView.view_pack _
    rw [hinit]; dsimp only; rw [DY.Spqr.spqrParamsDir?_spqrParams .b2a]
    dsimp only [key0Clean, spqrSend, stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
      spqrInit, DY.Libsignal.TripleRatchet.spqrA2B]
    rw [DY.BytesView.view_pack]
    simp [stB20'Clean, ratchetState, stB20Clean, bobSt0, recvSt, keys1, spqrInit,
      DY.Spqr.Direction.flip]
  have hseed : (kdfCk stA0.cks).2 = seedB0Clean := by
    show (kdfCk (createChain keys1.rk (dhPk spkB) dhsA).2).2 =
      (kdfCk (createChain keys1.rk (dhPk dhsA) spkB).2).2
    rw [createChain_comm keys1.rk dhsA spkB]
  have hr := runs_cast (a2 := 46) (t2 := trClean3 cls)
    (Runs.bobStart (kh := kh1) (mh := mh1) (keys := keys1)
    (msg := encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean)
    (t := m0Clean cls) (st' := stB20'Clean cls) (c := cBClean) (c' := cB'Clean)
    (seed := seedB0Clean) (pq := key0Clean cls) (m := pt0Clean)
    (at?_mono h42 hb9) (at?_mono h42 hs13) (at?_mono h42 hp19) rfl (at?_mono h42 ha1) hek hct
    (isCanonicalKey_dhPk _)
    (bobAgreement_honest ikA (rnd t4.length 32) ikB spkB pqskB (rnd (t4.length + 1) 32))
    hmsg (parse_encMsg _ _ _ _) rfl (x25519LowOrder_dhPk dhsA) hrs rfl hspqr hpq
    (mac_ok hseed rfl rfl) (dec_ok hseed) (stOut := stB2Clean cls) (by rw [hset]; rfl))
    (by
      dsimp only [encSig, stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
      rw [skipTr_zero _ _ _ _ _ _ rfl]
      simp only [append_len, trClean2_length])
    (by
      dsimp only [encSig, stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.bobOutOpt]
      rw [skipTr_zero _ _ _ _ _ _ rfl]
      dsimp only [trClean3, stB20'Clean, ratchetState, stB20Clean, bobSt0]
      simp only [append_len, trClean2_length]
      rfl)
  exact ⟨(stepIn_next DY.Libsignal.Composed.bobStart.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.Composed.bobStart.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem s3_next_ok (cls : Nat → Nat) :
    (s3Clean cls).next (trClean3 cls) = trClean4 cls ∧ (s3Clean cls).ok (trClean3 cls) = true := by
  have hst : (trClean3 cls).at? 46 = some (StT "bob" (stB2Clean cls)) := by
    dsimp only [trClean3]
    exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
  have hpq : ((((trClean3 cls).append (RndE 32)).append (RndE (cls 1))).append
      (NetE (spqrSend (stB2Clean cls).spqr (rnd ((trClean3 cls).length + 1) (cls 1))).2.1)).at? 49 =
      some (NetE (key1Clean cls)) := by
    rw [show rnd ((trClean3 cls).length + 1) (cls 1) = coins1Clean cls by rw [trClean3_length]]
    exact at?_append_at _ _ (by simp only [append_len, trClean3_length])
  have hns : (stB2Clean cls).ns ≠ u32Max := by
    dsimp only [stB2Clean, stB20'Clean, ratchetState, stB20Clean, bobSt0]; decide
  have hr := Runs.messageEncryptGen hst hns hpq
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem s4_next_ok (cls : Nat → Nat) :
    s4Clean.next (trClean4 cls) = trClean5 cls ∧ s4Clean.ok (trClean4 cls) = true := by
  have h24 : trClean2 cls ≤ trClean4 cls :=
    Trace.le_trans _ _ _ (trClean2_le_trClean3 cls) (encTrGen_le _ _ _ _ _ _)
  have hst : (trClean4 cls).at? 36 = some (StT "alice" (stA1Clean cls)) := by
    refine at?_mono h24 ?_; dsimp only [trClean2, encTrGen, stA1Clean]
    rw [show rnd (t5.length + 1) (cls 0) = coins0Clean cls by rw [t5_length]]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hmsg : (trClean4 cls).at? 53 = some (NetE (m1Clean cls)) := by
    dsimp only [trClean4, encTrGen, m1Clean, pt1Clean, coins1Clean]
    rw [trClean3_length]
    exact at?_append_at _ _ (by simp only [append_len, trClean3_length])
  have hpq : (((trClean4 cls).append (RndE 32)).append
      (NetE (recvKey (stA1Clean cls).spqr (pqm1Clean cls)))).at? 49 =
      some (NetE (key1Clean cls)) := by
    refine at?_mono (le_append_of_le (Trace.append_le _ _) _) ?_
    dsimp only [trClean4, encTrGen]
    rw [show rnd ((trClean3 cls).length + 1) (cls 1) = coins1Clean cls by rw [trClean3_length]]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, trClean3_length]))
  have hne : dhPk spkB ≠ dhPk dhsB1Clean := dhPk_rnd_ne (by decide)
  have ho1 : o1.spk = dhPk spkB := rfl
  have hrs : ratchetState (stA1Clean cls)
      (encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean).ratchetKey
      (rnd (trClean4 cls).length 32) = (stA3'Clean cls, cA1RawClean) := by
    rw [trClean4_length]; rfl
  have hset : setRecvChain (stA3'Clean cls).recv cA1Clean = [cA0Clean, cA1Clean] := by
    simp [setRecvChain, stA3'Clean, ratchetState, cA1Clean, cA1RawClean, stA1Clean, encSt,
      stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt, cA0Clean, ho1, hne,
      maxReceiverChains]
  have hfind : findRecvChain (stA1Clean cls).recv (dhPk dhsB1Clean) = none := by
    simp [findRecvChain, stA1Clean, encSt, stA0,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt, ho1, hne]
  have hspqr : spqrRecv (stA3'Clean cls).spqr (pqm1Clean cls) 1 =
      some ((stA4Clean cls).spqr, recvKey (stA1Clean cls).spqr (pqm1Clean cls)) := by
    dsimp only [stA3'Clean, ratchetState, pqm1Clean, stA4Clean, stA1Clean, encSt]
    unfold spqrRecv DY.Spqr.spqrEmptyMsg
    rw [bytesToLiteral_spqrSendMsg, spqrSend_st_not_init]; rfl
  have hseed : (kdfCk (stB2Clean cls).cks).2 = seedA1Clean := by
    show (kdfCk (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1Clean).2).2 =
      (kdfCk (createChain (createChain keys1.rk (dhPk spkB) dhsA).1 (dhPk dhsB1Clean) dhsA).2).2
    rw [createChain_comm keys1.rk dhsA spkB, createChain_comm _ dhsA dhsB1Clean]
  have hr := runs_cast (a2 := 60) (t2 := trClean5 cls)
    (Runs.messageDecrypt_ratchet (st := stA1Clean cls)
    (st' := stA3'Clean cls) (c := cA1RawClean) (c' := cA1Clean)
    (msg := encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean)
    (t := m1Clean cls) (pq := key1Clean cls) (seed := seedA1Clean) (m := pt1Clean)
    hst hmsg (parse_encMsg _ _ _ _) rfl hfind (x25519LowOrder_dhPk dhsB1Clean) hrs rfl hspqr hpq
    (mac_ok hseed rfl rfl) (dec_ok hseed) (stOut := stA4Clean cls) (by rw [hset]; rfl))
    (by
      dsimp only [encSig, stB2Clean, stB20'Clean, ratchetState, stB20Clean, bobSt0]
      rw [skipTr_zero _ _ _ _ _ _ rfl]
      simp only [append_len, trClean4_length])
    (by
      dsimp only [encSig, stB2Clean, stB20'Clean, ratchetState, stB20Clean, bobSt0]
      rw [skipTr_zero _ _ _ _ _ _ rfl]
      dsimp only [trClean5, stA3'Clean, ratchetState, stA1Clean, encSt, stA0,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
      rfl)
  exact ⟨(stepIn_next DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ _).trans hr.2,
    (stepIn_isSome DY.Libsignal.TripleRatchet.messageDecrypt.reachability _ _).trans
      (congrArg Option.isSome hr.1)⟩

theorem runSteps_ssClean (cls : Nat → Nat) :
    runSteps (ssClean cls 0) t4 = t4 ∧
    runSteps (ssClean cls 1) t4 = trClean1 ∧
    runSteps (ssClean cls 2) t4 = trClean2 cls ∧
    runSteps (ssClean cls 3) t4 = trClean3 cls ∧
    runSteps (ssClean cls 4) t4 = trClean4 cls ∧
    runSteps (ssClean cls 5) t4 = trClean5 cls := by
  simp only [ssClean, cleanCallSteps, List.take, runSteps,
    (s0_next_ok).1, (s1_next_ok cls).1, (s2_next_ok cls).1, (s3_next_ok cls).1, (s4_next_ok cls).1,
    and_self]

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
  have hi := List.all_eq_true.mp hbool i (List.mem_range.mpr hilt)
  have hj := List.all_eq_true.mp hi j (List.mem_range.mpr hjlt)
  rw [hsi0, hsj0] at hj; dsimp only at hj; rw [hli0, hlj0] at hj
  simp [hij] at hj

theorem stepsWF_cleanCallSteps {cls : Nat → Nat} (hv : ValidCoinLens cls) :
    StepsWF (cleanCallSteps cls) t4 := by
  have hcur_t5_30 : isCurrentSnapshot t5 30 = true := by
    dsimp only [t5, aliceTr, aliceTrOpt]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, t4_length])
  have hst_tr2_36 : (trClean2 cls).at? 36 = some (StT "alice" (stA1Clean cls)) := by
    dsimp only [trClean2, encTrGen, stA1Clean]
    rw [show rnd (t5.length + 1) (cls 0) = coins0Clean cls by rw [t5_length]]
    exact at?_mono (Trace.append_le _ _) (at?_append_at _ _ (by simp only [append_len, t5_length]))
  have hcur_tr2_36 : isCurrentSnapshot (trClean2 cls) 36 = true := by
    dsimp only [trClean2, encTrGen]
    exact isCurrentSnapshot_non _ rfl
      (isCurrentSnapshot_self _ _ _ (by simp only [append_len, t5_length]))
  have hcur_tr3_36 : isCurrentSnapshot (trClean3 cls) 36 = true := by
    dsimp only [trClean3]
    have hpre : trClean2 cls ≤
        ((((((((trClean2 cls).append (RndE 32)).append (NetE (key0Clean cls))).append
        (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
          (kemPk pqskB) none o1.ek o1.ct keys1))).append
        (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1Clean)))).append
        (EvT (.HonestDH ((stB20'Clean cls).sessionInfo "bob") dhsB1Clean 0))).append
        (EvC (.HandshakeSession ((stB20'Clean cls).sessionInfo "bob") 40))).append
        (EvT (.Received "bob" "alice" (dhPk dhsA) 0 pt0Clean))).append
        (EvT (.MessageKey ((stB20'Clean cls).sessionInfo "bob") .receiver seedB0Clean
          (key0Clean cls) 0 2 46)) := by
      iterate 7 refine le_append_of_le ?_ _
      exact Trace.append_le _ _
    refine isCurrentSnapshot_st_ne (at?_mono hpre hst_tr2_36) (by decide) ?_
    iterate 8 refine isCurrentSnapshot_non _ rfl ?_
    exact hcur_tr2_36
  have hcur_tr3_46 : isCurrentSnapshot (trClean3 cls) 46 = true := by
    dsimp only [trClean3]
    exact isCurrentSnapshot_self _ _ _ (by simp only [append_len, trClean2_length])
  have hcur_tr4_36 : isCurrentSnapshot (trClean4 cls) 36 = true := by
    dsimp only [trClean4, encTrGen]
    have hpre : trClean2 cls ≤
        ((((((trClean3 cls).append (RndE 32)).append (RndE (cls 1))).append
        (NetE (spqrSend (stB2Clean cls).spqr
          (rnd ((trClean3 cls).length + 1) (cls 1))).2.1)).append
        (EvT (.Sent "bob" (stB2Clean cls).peer (dhPk (stB2Clean cls).dhs) (stB2Clean cls).ns
          (rnd (trClean3 cls).length 32)))).append
        (EvT (.MessageKey ((stB2Clean cls).sessionInfo "bob") .sender (kdfCk (stB2Clean cls).cks).2
          (key1Clean cls) (stB2Clean cls).ns (stB2Clean cls).rIdx 46))) := by
      refine Trace.le_trans _ _ _ (trClean2_le_trClean3 cls) ?_
      iterate 4 refine le_append_of_le ?_ _
      exact Trace.append_le _ _
    refine isCurrentSnapshot_non _ rfl
      (isCurrentSnapshot_st_ne (at?_mono hpre hst_tr2_36) (by decide) ?_)
    iterate 5 refine isCurrentSnapshot_non _ rfl ?_
    exact hcur_tr3_36
  dsimp only [cleanCallSteps, StepsWF]
  refine ⟨trivial, trivial, ?_⟩
  rw [(s0_next_ok).1]
  refine ⟨hcur_t5_30, ⟨hv 0 (by decide),
    Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t5_length])⟩, ?_⟩
  rw [(s1_next_ok cls).1]
  refine ⟨trivial, trivial, ?_⟩
  rw [(s2_next_ok cls).1]
  refine ⟨hcur_tr3_46, ⟨hv 1 (by decide),
    Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [trClean3_length])⟩, ?_⟩
  rw [(s3_next_ok cls).1]
  exact ⟨hcur_tr4_36, trivial, trivial⟩

theorem step_ok_ssClean {cls : Nat → Nat} {k : Nat} (hk : k < 5) {s : Step}
    (hs : (cleanCallSteps cls)[k]? = some s) :
    s.ok (runSteps (ssClean cls k) t4) = true := by
  have hrs := runSteps_ssClean cls
  match k with
  | 0 => injection hs with h; subst h; rw [hrs.1]; exact s0_next_ok.2
  | 1 => injection hs with h; subst h; rw [hrs.2.1]; exact (s1_next_ok cls).2
  | 2 => injection hs with h; subst h; rw [hrs.2.2.1]; exact (s2_next_ok cls).2
  | 3 => injection hs with h; subst h; rw [hrs.2.2.2.1]; exact (s3_next_ok cls).2
  | 4 => injection hs with h; subst h; rw [hrs.2.2.2.2.1]; exact (s4_next_ok cls).2
  | n + 5 => omega

private theorem stepsWF_of_append : ∀ {a b : List Step} {tr : ExecTrace},
    StepsWF (a ++ b) tr → StepsWF a tr
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, h.2.1, stepsWF_of_append h.2.2⟩

private theorem stepsStateFaithful_of_append {r : ProtocolSetup} {a b : List Step}
    (h : StepsStateFaithful r (a ++ b)) : StepsStateFaithful r a := by
  intro i j si sj p k bb hij hi hj hload hok hload'
  have hilt : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjlt : j < a.length := (List.getElem?_eq_some_iff.mp hj).1
  refine h i j si sj p k bb hij (by rw [List.getElem?_append_left hilt]; exact hi)
    (by rw [List.getElem?_append_left hjlt]; exact hj) hload ?_ hload'
  rw [List.take_append_of_le_length (Nat.le_of_lt hilt)]
  exact hok

theorem modelRunWF_ssClean {r : ProtocolSetup} {cls : Nat → Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hv : ValidCoinLens cls) (k : Nat) :
    ModelRunWF r (ssClean cls k) := by
  have hfull : ModelRunWF r (cleanCallSteps cls) :=
    ⟨setupRandoms_len_eq hfit,
     setupTrace_eq_t4 hfit ▸ t4_reach,
     setupTrace_eq_t4 hfit ▸ stepsWF_cleanCallSteps hv,
     stateFaithful_cleanCallSteps r cls⟩
  have hsplit : cleanCallSteps cls = ssClean cls k ++ (cleanCallSteps cls).drop k :=
    (List.take_append_drop k (cleanCallSteps cls)).symm
  rw [hsplit] at hfull
  exact ⟨hfull.1, hfull.2.1, stepsWF_of_append hfull.2.2.1, stepsStateFaithful_of_append hfull.2.2.2⟩

/-! ## 2. Front-to-Back Peeling of `rcprTrace.take k` (`k ≤ 5`) & `clsOfCalls` -/

theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

theorem stepsWF_append_right :
    ∀ (xs : List Step) {ys : List Step} {tr : ExecTrace},
      StepsWF (xs ++ ys) tr → StepsWF ys (runSteps xs tr)
  | [], _, _, h => h
  | _ :: xs, _, _, ⟨_, _, h⟩ => stepsWF_append_right xs h

structure PeeledCall where
  pre : List Step
  s : Step
  v : List VisEntry

def evsRange (j k : Nat) : List CliEvent :=
  if _ : j < k then .run (ev j) :: evsRange (j + 1) k else []
termination_by k - j

theorem evsRange_self (k : Nat) : evsRange k k = [] := by unfold evsRange; simp

theorem evsRange_lt {j k : Nat} (h : j < k) : evsRange j k = .run (ev j) :: evsRange (j + 1) k := by
  conv => lhs; unfold evsRange
  simp [h]

theorem evsRange_snoc {j k : Nat} (h : j ≤ k) :
    evsRange j (k + 1) = evsRange j k ++ [.run (ev k)] := by
  by_cases hlt : j < k
  · rw [evsRange_lt (by omega), evsRange_lt hlt, List.cons_append, evsRange_snoc hlt]
  · obtain rfl : j = k := by omega
    rw [evsRange_self, List.nil_append, evsRange_lt (by omega), evsRange_self]
termination_by k - j

theorem rcprTrace_take_eq_evsRange : ∀ {k : Nat}, k ≤ 5 → rcprTrace.take k = evsRange 0 k
  | 0, _ => by simp [evsRange_self]
  | k + 1, hk => by
    rw [rcprTrace_take_succ (by omega), rcprTrace_take_eq_evsRange (by omega), evsRange_snoc (Nat.zero_le k)]

inductive PeeledValid (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (visAll : List VisEntry) :
    Nat → Option BundlePreKeyIds → ExecTrace → List PeeledCall → List Step → Prop where
  | nil {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {tail : List Step} :
      (∀ x ∈ tail, ∃ msg, x = .network msg) →
      PeeledValid r S g visAll j initIds tr [] tail
  | cons {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {c : PeeledCall} {cs : List PeeledCall} {rest : List Step} :
      (∀ x ∈ c.pre, ∃ msg, x = .network msg) →
      c.s.PreCond (runSteps c.pre tr) →
      c.s.LocalOk (runSteps c.pre tr) →
      RunMatches rcprI0 r S g (runSteps c.pre tr) c.s (ev j) c.v initIds →
      (∀ w ∈ c.v, w ∈ visAll) →
      PeeledValid r S g visAll (j + 1) (nextBundleIds initIds (ev j))
        (c.s.next (runSteps c.pre tr)) cs rest →
      PeeledValid r S g visAll j initIds tr (c :: cs) (c.pre ++ c.s :: rest)

theorem peel_evsRange {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ (n j : Nat) {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {ss : List Step} {vis : List VisEntry},
      j + n ≤ 5 →
      StepsWF ss tr →
      MatchesEventsAt rcprI0 r S g initIds tr ss (evsRange j (j + n)) vis →
      (∀ w ∈ vis, w ∈ visAll) →
      ∃ cs : List PeeledCall, cs.length = n ∧ PeeledValid r S g visAll j initIds tr cs ss
  | 0, j, initIds, tr, ss, vis, _, _, hm, _ => by
    rw [Nat.add_zero, evsRange_self] at hm
    cases hm with
    | nil hinv => exact ⟨[], rfl, .nil (fun x hx => step_invisible_eq_network (hinv x hx))⟩
  | n + 1, j, initIds, tr, ss, vis, hjn, hwf, hm, hsub => by
    rw [evsRange_lt (by omega)] at hm
    cases hm with
    | run0 _ hrej _ => exact False.elim (ev_not_rejected j (by omega) hrej)
    | @run1 _ _ pre s ss' _ _ v vs hinv hrm hrest =>
      obtain ⟨hpre, hlok, hwf_tail⟩ := stepsWF_append_right pre hwf
      have hnet : ∀ x ∈ pre, ∃ msg, x = .network msg :=
        fun x hx => step_invisible_eq_network (hinv x hx)
      have hv_sub : ∀ w ∈ v, w ∈ visAll := fun w hw => hsub w (List.mem_append_left _ hw)
      have hvs_sub : ∀ w ∈ vs, w ∈ visAll := fun w hw => hsub w (List.mem_append_right _ hw)
      rw [show j + (n + 1) = (j + 1) + n by omega] at hrest
      obtain ⟨cs, hlen, hpv⟩ := peel_evsRange n (j + 1) (by omega) hwf_tail hrest hvs_sub
      exact ⟨⟨pre, s, v⟩ :: cs, by simp [hlen], .cons hnet hpre hlok hrm hv_sub hpv⟩

def stepCoinLen : Step → Nat
  | .messageEncrypt _ _ cl _ => cl
  | _ => 0

def clsOfCalls (cs : List PeeledCall) (s : Nat) : Nat :=
  match cs[sendCallOf s]? with
  | some c => stepCoinLen c.s
  | none => 0

theorem peeledValid_localOk_at {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {cs : List PeeledCall} {ss : List Step},
      PeeledValid r S g visAll j initIds tr cs ss →
      ∀ (i : Nat) (c : PeeledCall), cs[i]? = some c → ∃ tr_i, c.s.LocalOk tr_i
  | _, _, _, _, _, .nil _, i, _, hget => by simp at hget
  | _, _, _, _, _, .cons _ _ hlok _ _ _, 0, c, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
    subst hget; exact ⟨_, hlok⟩
  | _, _, _, _, _, .cons _ _ _ _ _ hpv, i + 1, c, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact peeledValid_localOk_at hpv i c hget

theorem validCoinLens_clsOfCalls {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {j : Nat} {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {cs : List PeeledCall} {ss : List Step}
    (hpv : PeeledValid r S g visAll j initIds tr cs ss) :
    ValidCoinLens (clsOfCalls cs) := by
  intro s _
  unfold clsOfCalls
  rcases hget : cs[sendCallOf s]? with _ | c
  · exact Or.inl rfl
  · dsimp only
    obtain ⟨tr_i, hlok⟩ := peeledValid_localOk_at hpv (sendCallOf s) c hget
    cases hs : c.s with
    | messageEncrypt me idx cl pq =>
      rw [hs] at hlok; dsimp only [stepCoinLen]; exact hlok.1
    | _ => dsimp only [stepCoinLen]; exact Or.inl rfl

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
