/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Actions.Network
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.DagData

/-!
# Certified DAG Walk, Representation Membership, and Collision-Freedom (`MemoCheck.lean`)

Proves for `m = 2` (`ev 2`) and `m = 5` (`ev 5`) under a clean prefix explanation:
1. `cleanPreKeyRep_2_mem` and `cleanPreKeyRep_5_mem` (`cleanPreKeyRep cls m ∈ preKeyRepresentationsOn ...`).
2. `not_bobStartCollides_2` and `not_bobStartCollides_5`
   (`¬ BobSessionStartCollidesOrImplicitRejectsOn ...`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck

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

open DY (Bytes Trace ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap)
open DY.Spqr (spqrInit spqrSend zeroKey)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.PQXDH
  (PQXDHState serializedIk agree pqxdhIkm pqxdhKdf pqxdhLabel discontinuity)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg RecvChain lit litByte zeroSalt createChain kdfRk kdfCk
   trMsgKeys computeMac parseTrSignalMsg trHonestWireMsg messageVersion spqrA2B spqrB2A)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   PreKeyFields PreKeyRep TrialCtx randTerm litOf gamma gamma' ecKey kyberKey pubBytes
   secretBytes setupTrace setupPublic runSteps runTrace stepView runWrapped trWireBytes
   gRandom node concretizeRandom assumedInjective
   nextBundleIds RunRejected RunMatches MatchesEventsAt Explains
   spqrHeaded FaithfulInner PreKeyRecvMatches OpkNamed preKeyRepresentationsOn
   honestSaltsOf storedStates storedSecrets principalTerms plaintextTerms prefixTerms
   bobTrials trialTerms UnknownSeedMacGuess TruncatedMacSeedCollision MacTagForgeryOrCollision
   BobSessionStartCollidesOrImplicitRejectsOn)
open Symbolic.BugInjection (fillFresh)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound (ms_pack_random)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encMsg encSig encSt parse_encMsg ratchetState recvSt bobSt0 createChain_comm NetE)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB opkB oOpk keysOpk dhsAOpk stA0Opk key0Opk
   dhsB1Opk stB00Opk stB0'Opk cBOpk cB'Opk
   t4Opk t5Opk t4Opk_length t5Opk_length t7Opk_length)
open ByteSpecs (hmacWith)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (serialize_local_pqxdh_eq_bridge slowString_serialize_eq slowNat_serialize_succ
   slowNat_serialize_zero concatPrefixes_cons concatPrefixes_nil
   alice_utf8_sizes bob_utf8_sizes spqrHeaded_computeMac_bridge)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned keepOpkAesPerm)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
  (FK gamma_hmacK gamma_concatK gamma_trunc8K)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (w0 trace0 trace_eq_evs ev ev_not_rejected ev0_cmd_and_exit ev3_cmd_and_exit
   ev1_to_ev2 ev4_to_ev5 ev0Coins_eq ev1In_eq ev1Coins_eq ev2In_eq ev2Coins_eq
   ev3Coins_eq ev4In_eq ev4Coins_eq ev5In_eq ev0KyberEnt_eq ev3KyberEnt_eq
   ev1_facts ev4_facts p2 p5 parse_ev2 parse_ev5
   aliceBobAddrBytes serializeAddresses_alice_bob_eq)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (ValidCoinLens append_len le_append_of_le at?_mono at?_append_at
   setupTrace_eq_t4Opk setupPublic_eqs
   s0Clean s1Clean s2Clean s3Clean s4Clean ssClean
   pt0Clean coins0Clean key0Clean pqm0Clean stA1Clean m0Clean trClean2 key0Clean_eq
   stB1Clean trClean3 o2Clean keys2Clean dhsA2Clean stA2_0Clean trClean4
   pt1Clean coins1Clean key1Opk key1Clean pqm1Clean stA2_1Clean m1Clean trClean5 key1Clean_eq
   trClean2_length trClean3_length trClean4_length
   s0_next_ok s1_next_ok s2_next_ok s3_next_ok
   runTrace_ssClean_eqs honestSaltsOf_2 honestSaltsOf_5
   storedStatesClean2 storedStatesClean5 storedStates_2 storedStates_5
   storedSecretsOpk storedSecrets_2 storedSecrets_5
   cleanPreKeyRep bobCtx2 bobCtx5 bobTrials_2 bobTrials_5)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis
  (visClean stepView_s1 stepView_s4 sendTerms_visClean_2 sendTerms_visClean_5
   plaintextTerms_visClean_2 plaintextTerms_visClean_5)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
  (r_facts_of_fit setupRandomsAt_of_fit gClean
   gClean_sigma_lt26 gClean_sigma_26 gClean_sigma_27 gClean_sigma_28
   gClean_sigma_35 gClean_sigma_36 gClean_sigma_42
   gClean_sigma_52 gClean_sigma_53 gClean_sigma_54
   gClean_sigma_61 gClean_sigma_62 gClean_addr)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.DagDefs
  (DagOp SafeMemo TermAt SafeMemo2
   gamma_litOf spqrSend_shapes
   safeMemo_lit_short safeMemo_plaintext safeMemo_toSafeMemo2
   termAt_lit termAt_litOf randTerm_eq_dagShape termAt_rand termAt_concat
   termAt_dhPk termAt_dh termAt_dh_symm termAt_kdf termAt_trunc8
   termAt_symEncPt termAt_trWire termAt_kemEncap termAt_of_opaque
   safeMemo_kemPk safeMemo_spqrInit safeMemo_recvSt safeMemo_spqrSend
   termAt_computeMac termAt_trMsgKeys safeMemo_trialTerms
   safeMemo2_trState_of_dr not_memoCollisionOn_of_safeMemo2 encMsg_pins_pqKey_and_pqMsg)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.DagData

attribute [local irreducible] WitnessParse.ev

/-! ## 1. Extracting `gamma` of `m0Clean` and `m1Clean` from `Explains` -/

private theorem matchesEventsAt_cons_party
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {u : Step} {us : List Step}
    {e : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hcls : u.cls = .party) (hnrej : ¬ RunRejected e)
    (hm : MatchesEventsAt keepOpkI0 r S g initIds tr (u :: us) (.run e :: evs) vis) :
    ∃ v vs, vis = v ++ vs ∧
      RunMatches keepOpkI0 r S g tr u e v initIds ∧
      MatchesEventsAt keepOpkI0 r S g (nextBundleIds initIds e) (u.next tr) us evs vs := by
  generalize hss : (u :: us) = ss_all at hm
  generalize hevs : (CliEvent.run e :: evs) = evs_all at hm
  cases hm with
  | nil _ => cases hevs
  | env _ _ _ => cases hevs
  | run0 _ hrej _ =>
    injection hevs with he1 _
    injection he1 with he_eq
    subst he_eq
    exact absurd hrej hnrej
  | @run1 _ _ pre s ss ev' evs' v vs hinv hrm hrest =>
    injection hevs with he1 he2
    injection he1 with he_eq
    subst he_eq he2
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hss
      obtain ⟨hs1, hs2⟩ := hss
      subst hs1 hs2
      dsimp only [runSteps] at hrm hrest
      exact ⟨v, vs, rfl, hrm, hrest⟩
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at hss
      have hp := hinv p List.mem_cons_self
      rw [← hss.1, hcls] at hp
      cases hp

private theorem getLast?_append_singleton {α : Type} : ∀ (l : List α) (x : α),
    (l ++ [x]).getLast? = some x
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: b :: rest, x => getLast?_append_singleton (b :: rest) x

private theorem gamma_m0Clean_of_runMatches
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    {v : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hrm : RunMatches keepOpkI0 r S (gClean r cls) t5Opk (s1Clean cls) (ev 1) v initIds) :
    gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message := by
  obtain ⟨_, _, _, _, _, _, hv_eq, inp, drs, outs, hv_split, _, _, houts, _, _⟩ := hrm
  rw [ev1_facts.2.2.2.2, stepView_s1] at hv_eq
  unfold DY.Libsignal.Composed.Refinement.OutputsMatch at houts
  rw [ev1_to_ev2, ev1_facts.2.1] at houts
  obtain ⟨v_out, rfl, hbme⟩ := houts
  have hlast1 : v.getLast? = some v_out := by
    rw [hv_split, ← List.cons_append]
    exact getLast?_append_singleton (inp :: drs) v_out
  have hlast2 : v.getLast? = some ⟨.send, [oOpk.ek, oOpk.ct, m0Clean cls], .preKeySend, none⟩ := by
    rw [hv_eq, ← List.cons_append]
    exact getLast?_append_singleton _ _
  rw [hlast1] at hlast2
  injection hlast2 with hv_out_eq
  subst hv_out_eq
  obtain ⟨_, preKeyId, spkId, kpkId, _, hw⟩ := hbme
  have hlen : (ev 2).input.length < 2 ^ 63 := by rw [ev2In_eq]; decide +kernel
  exact (parsePreKeyWire_preKeyWire_inv hw hlen parse_ev2).2.2.2.symm

private theorem gamma_m1Clean_of_runMatches
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    {v : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hrm : RunMatches keepOpkI0 r S (gClean r cls) (trClean4 cls) (s4Clean cls) (ev 4) v initIds) :
    gamma keepOpkI0 S (gClean r cls) (m1Clean cls) = p5.message := by
  obtain ⟨_, _, _, _, _, _, hv_eq, inp, drs, outs, hv_split, _, _, houts, _, _⟩ := hrm
  rw [ev4_facts.2.2.2.2, stepView_s4] at hv_eq
  unfold DY.Libsignal.Composed.Refinement.OutputsMatch at houts
  rw [ev4_to_ev5, ev4_facts.2.1] at houts
  obtain ⟨v_out, rfl, hbme⟩ := houts
  have hlast1 : v.getLast? = some v_out := by
    rw [hv_split, ← List.cons_append]
    exact getLast?_append_singleton (inp :: drs) v_out
  have hlast2 : v.getLast? = some ⟨.send, [o2Clean.ek, o2Clean.ct, m1Clean cls], .preKeySend, none⟩ := by
    rw [hv_eq, ← List.cons_append]
    exact getLast?_append_singleton _ _
  rw [hlast1] at hlast2
  injection hlast2 with hv_out_eq
  subst hv_out_eq
  obtain ⟨_, preKeyId, spkId, kpkId, _, hw⟩ := hbme
  have hlen : (ev 5).input.length < 2 ^ 63 := by rw [ev5In_eq]; decide +kernel
  exact (parsePreKeyWire_preKeyWire_inv hw hlen parse_ev5).2.2.2.symm

private theorem m0Clean_eq_of_explains_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2)
      (visClean r cls 2) (trace0.take 2)) :
    gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message := by
  have hf := r_facts_of_fit hfit
  have hm := hex.2.2.2
  rw [trace_eq_evs] at hm
  dsimp only [List.take, DY.Libsignal.Composed.Refinement.MatchesEvents,
    ssClean, CleanTrace.cleanCallSteps] at hm
  rw [setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq] at hm
  obtain ⟨_, _, _, _, hm1⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 0 (by decide)) hm
  rw [s0_next_ok.1] at hm1
  obtain ⟨_, _, _, hrm1, _⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 1 (by decide)) hm1
  exact gamma_m0Clean_of_runMatches hrm1

private theorem m0_and_m1_eq_of_explains_5
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 5)
      (visClean r cls 5) (trace0.take 5)) :
    gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message ∧
    gamma keepOpkI0 S (gClean r cls) (m1Clean cls) = p5.message := by
  have hf := r_facts_of_fit hfit
  have hm := hex.2.2.2
  rw [trace_eq_evs] at hm
  dsimp only [List.take, DY.Libsignal.Composed.Refinement.MatchesEvents,
    ssClean, CleanTrace.cleanCallSteps] at hm
  rw [setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq] at hm
  obtain ⟨_, _, _, _, hm1⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 0 (by decide)) hm
  rw [s0_next_ok.1] at hm1
  obtain ⟨_, _, _, hrm1, hm2⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 1 (by decide)) hm1
  rw [(s1_next_ok cls).1] at hm2
  obtain ⟨_, _, _, _, hm3⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 2 (by decide)) hm2
  rw [(s2_next_ok cls).1] at hm3
  obtain ⟨_, _, _, _, hm4⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 3 (by decide)) hm3
  rw [(s3_next_ok cls).1] at hm4
  obtain ⟨_, _, _, hrm4, _⟩ := matchesEventsAt_cons_party rfl (ev_not_rejected 4 (by decide)) hm4
  exact ⟨gamma_m0Clean_of_runMatches hrm1, gamma_m1Clean_of_runMatches hrm4⟩

/-! ## 2. Boolean `decide +kernel`-Driven `TermAt` Builders -/

private def isLitOp (op : DagOp) (v : HwBytes) : Bool :=
  match op with | .lit x => decide (x = v) | _ => false

private def isRandOp (op : DagOp) (ts len : Nat) : Bool :=
  match op with | .rand t l => decide (t = ts) && decide (l = len) | _ => false

private def isConcatOp (op : DagOp) (l r : Nat) : Bool :=
  match op with | .concat x y => decide (x = l) && decide (y = r) | _ => false

private def isDhPkOp (op : DagOp) (s : Nat) : Bool :=
  match op with | .dhPk x => decide (x = s) | _ => false

private def isDhOp (op : DagOp) (a b : Nat) : Bool :=
  match op with | .dh x y => decide (x = a) && decide (y = b) | _ => false

private def isKdfOp (op : DagOp) (a b : Nat) : Bool :=
  match op with | .kdf x y => decide (x = a) && decide (y = b) | _ => false

private def isTrunc8Op (op : DagOp) (a : Nat) : Bool :=
  match op with | .trunc8 x => decide (x = a) | _ => false

private def isKemEncapOp (op : DagOp) (pk ent : Nat) : Bool :=
  match op with | .kemEncap p e => decide (p = pk) && decide (e = ent) | _ => false

private def isKemSSOp (op : DagOp) (pk ent : Nat) : Bool :=
  match op with | .kemSS p e => decide (p = pk) && decide (e = ent) | _ => false

private def isSymEncPtOp (op : DagOp) (ck iv ptTs : Nat) (pt : HwBytes) : Bool :=
  match op with
  | .symEncPt c i t p => decide (c = ck) && decide (i = iv) && decide (t = ptTs) && decide (p = pt)
  | _ => false

private def isTrWireOp (op : DagOp) (ver : UInt8) (rk : Nat) (cnt prev : UInt32)
    (ct pq : Nat) (addr : HwBytes) : Bool :=
  match op with
  | .trWire v r c p ct' pq' ad =>
    decide (v = ver) && decide (r = rk) && decide (c = cnt) && decide (p = prev) &&
    decide (ct' = ct) && decide (pq' = pq) && decide (ad = addr)
  | _ => false

private def checkDhRand (s1 pk1 s2 pk2 id ts1 ts2 : Nat) : Bool :=
  decide (id < dagSize) && decide (s1 < dagSize) && decide (s2 < dagSize) &&
  isDhOp (dagOp id) pk1 s2 &&
  isDhPkOp (dagOp pk1) s1 &&
  isDhPkOp (dagOp pk2) s2 &&
  isRandOp (dagOp s1) ts1 32 &&
  isRandOp (dagOp s2) ts2 32

private theorem TermAt.gamma_eq {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {b : Bytes} {id : Nat} (h : TermAt dagSize dagOp dagBytes S g pts b id) :
    gamma keepOpkI0 S g b = dagBytes id := h.2.1

private theorem isLitOp_eq {op : DagOp} {v : HwBytes} (h : isLitOp op v = true) :
    op = .lit v := by
  cases op <;> simp [isLitOp] at h; exact congrArg DagOp.lit h

private theorem isRandOp_eq {op : DagOp} {ts len : Nat} (h : isRandOp op ts len = true) :
    op = .rand ts len := by
  cases op <;> simp [isRandOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isConcatOp_eq {op : DagOp} {l r : Nat} (h : isConcatOp op l r = true) :
    op = .concat l r := by
  cases op <;> simp [isConcatOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isDhPkOp_eq {op : DagOp} {s : Nat} (h : isDhPkOp op s = true) :
    op = .dhPk s := by
  cases op <;> simp [isDhPkOp] at h; exact congrArg DagOp.dhPk h

private theorem isDhOp_eq {op : DagOp} {a b : Nat} (h : isDhOp op a b = true) :
    op = .dh a b := by
  cases op <;> simp [isDhOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isKdfOp_eq {op : DagOp} {a b : Nat} (h : isKdfOp op a b = true) :
    op = .kdf a b := by
  cases op <;> simp [isKdfOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isTrunc8Op_eq {op : DagOp} {a : Nat} (h : isTrunc8Op op a = true) :
    op = .trunc8 a := by
  cases op <;> simp [isTrunc8Op] at h; exact congrArg DagOp.trunc8 h

private theorem isKemEncapOp_eq {op : DagOp} {pk ent : Nat} (h : isKemEncapOp op pk ent = true) :
    op = .kemEncap pk ent := by
  cases op <;> simp [isKemEncapOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isKemSSOp_eq {op : DagOp} {pk ent : Nat} (h : isKemSSOp op pk ent = true) :
    op = .kemSS pk ent := by
  cases op <;> simp [isKemSSOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem isSymEncPtOp_eq {op : DagOp} {ck iv ptTs : Nat} {pt : HwBytes}
    (h : isSymEncPtOp op ck iv ptTs pt = true) :
    op = .symEncPt ck iv ptTs pt := by
  cases op <;> simp [isSymEncPtOp] at h; obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl

private theorem isTrWireOp_eq {op : DagOp} {ver : UInt8} {rk : Nat} {cnt prev : UInt32}
    {ct pq : Nat} {addr : HwBytes}
    (h : isTrWireOp op ver rk cnt prev ct pq addr = true) :
    op = .trWire ver rk cnt prev ct pq addr := by
  cases op <;> simp [isTrWireOp] at h
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h; rfl

private theorem termAt_lit_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ba : ByteArray} {id : Nat}
    (hok : (decide (id < dagSize) &&
      isLitOp (dagOp id) (DY.Libsignal.Composed.Refinement.ofByteArray ba)) = true) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Literal.literalToBytes ba) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_lit dag_nodes_ok hok.1 (isLitOp_eq hok.2)

private theorem termAt_strLit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {s : String} {id : Nat} (hid : id < dagSize)
    (hop : isLitOp (dagOp id) (DY.Libsignal.Composed.Refinement.ofByteArray s.toList.utf8Encode) = true) :
    TermAt dagSize dagOp dagBytes S g pts (lit s) id := by
  have hs : s.toUTF8 = s.toList.utf8Encode := by
    conv_lhs => rw [← String.ofList_toList (s := s)]
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  exact termAt_lit dag_nodes_ok hid (by rw [hs]; exact isLitOp_eq hop)

private theorem termAt_rand_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ts len id : Nat} (hsig : g.σ ts len = dagBytes id)
    (hok : (decide (id < dagSize) && isRandOp (dagOp id) ts len) = true) :
    TermAt dagSize dagOp dagBytes S g pts (rnd ts len) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_rand dag_nodes_ok hok.1 (isRandOp_eq hok.2) hsig

private theorem termAt_concat_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {a b : Bytes} {la rb id : Nat}
    (hok : (decide (id < dagSize) && isConcatOp (dagOp id) la rb) = true)
    (ha : TermAt dagSize dagOp dagBytes S g pts a la)
    (hb : TermAt dagSize dagOp dagBytes S g pts b rb) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat a b) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_concat dag_nodes_ok hok.1 (isConcatOp_eq hok.2) ha hb

private theorem termAt_dhPk_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {sk : Bytes} {s id : Nat}
    (hok : (decide (id < dagSize) && isDhPkOp (dagOp id) s) = true)
    (hs : TermAt dagSize dagOp dagBytes S g pts sk s) :
    TermAt dagSize dagOp dagBytes S g pts (dhPk sk) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_dhPk dag_nodes_ok hok.1 (isDhPkOp_eq hok.2) hs

private theorem unpack_checkDhRand {s1 pk1 s2 pk2 id ts1 ts2 : Nat}
    (hok : checkDhRand s1 pk1 s2 pk2 id ts1 ts2 = true) :
    id < dagSize ∧ s1 < dagSize ∧ s2 < dagSize ∧
    dagOp id = .dh pk1 s2 ∧ dagOp pk1 = .dhPk s1 ∧ dagOp pk2 = .dhPk s2 ∧
    dagOp s1 = .rand ts1 32 ∧ dagOp s2 = .rand ts2 32 := by
  unfold checkDhRand at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hid, hs1⟩, hs2⟩, hd⟩, hpk1⟩, hpk2⟩, hr1⟩, hr2⟩ := hok
  exact ⟨hid, hs1, hs2, isDhOp_eq hd, isDhPkOp_eq hpk1, isDhPkOp_eq hpk2,
    isRandOp_eq hr1, isRandOp_eq hr2⟩

private theorem termAt_dh_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
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

private theorem termAt_dh_symm_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
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

private theorem termAt_kdf_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salt ikm : Bytes} {s i id : Nat}
    (hok : (decide (id < dagSize) && isKdfOp (dagOp id) s i) = true)
    (hs : TermAt dagSize dagOp dagBytes S g pts salt s)
    (hi : TermAt dagSize dagOp dagBytes S g pts ikm i) :
    TermAt dagSize dagOp dagBytes S g pts (DY.KdfExtract.kdfExtract salt ikm) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_kdf dag_nodes_ok hok.1 (isKdfOp_eq hok.2) hs hi

private theorem termAt_trunc8_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {m : Bytes} {a id : Nat}
    (hok : (decide (id < dagSize) && isTrunc8Op (dagOp id) a) = true)
    (hm : TermAt dagSize dagOp dagBytes S g pts m a) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Trunc.trunc8 m) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_trunc8 dag_nodes_ok hok.1 (isTrunc8Op_eq hok.2) hm

private theorem termAt_kemEncap_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {pk e : Bytes} {p_id e_id id1 id2 : Nat}
    (hok : (decide (id1 < dagSize) && isKemEncapOp (dagOp id1) p_id e_id &&
            decide (id2 < dagSize) && isKemSSOp (dagOp id2) p_id e_id) = true)
    (hp : TermAt dagSize dagOp dagBytes S g pts pk p_id)
    (he : TermAt dagSize dagOp dagBytes S g pts e e_id) :
    TermAt dagSize dagOp dagBytes S g pts (kemEncap pk e).1 id1 ∧
      TermAt dagSize dagOp dagBytes S g pts (kemEncap pk e).2 id2 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hid1, hop1⟩, hid2⟩, hop2⟩ := hok
  exact termAt_kemEncap dag_nodes_ok hid1 (isKemEncapOp_eq hop1) hid2 (isKemSSOp_eq hop2) hp he

private theorem termAt_symEncPt_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {k iv : Bytes} {k_id iv_id ptTs id : Nat} {ptBs : HwBytes}
    (hok : (decide (id < dagSize) && isSymEncPtOp (dagOp id) k_id iv_id ptTs ptBs &&
            decide (ptBs.length < 8)) = true)
    (hk : TermAt dagSize dagOp dagBytes S g pts k k_id)
    (hiv : TermAt dagSize dagOp dagBytes S g pts iv iv_id)
    (hpt_mem : randTerm ptTs 32 ∈ pts)
    (hσ : g.σ ptTs 32 = ptBs) :
    TermAt dagSize dagOp dagBytes S g pts (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hid, hop⟩, hlen⟩ := hok
  exact termAt_symEncPt dag_nodes_ok hid (isSymEncPtOp_eq hop) hk hiv hpt_mem hσ hlen

private theorem termAt_trWire_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {rk ct pq : Bytes} {cnt prev : UInt32} {rk_id ct_id pq_id id : Nat} {addr : HwBytes}
    (hok : (decide (id < dagSize) &&
            isTrWireOp (dagOp id) messageVersion rk_id cnt prev ct_id pq_id addr) = true)
    (hrk : TermAt dagSize dagOp dagBytes S g pts rk rk_id)
    (hct : TermAt dagSize dagOp dagBytes S g pts ct ct_id)
    (hpq : TermAt dagSize dagOp dagBytes S g pts pq pq_id)
    (haddr : g.addr (trHonestWireMsg rk cnt prev ct pq) = addr) :
    TermAt dagSize dagOp dagBytes S g pts (trHonestWireMsg rk cnt prev ct pq) id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_trWire dag_nodes_ok hok.1 (isTrWireOp_eq hok.2) hrk hct hpq haddr

private theorem termAt_opaque_b {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {b : Bytes} {id : Nat}
    (hok : (decide (id < dagSize) && isLitOp (dagOp id) (dagBytes id)) = true)
    (hbs : gamma keepOpkI0 S g b = dagBytes id)
    (hsh : (gamma' keepOpkI0 S g b).shape = litOf (dagBytes id))
    (hsm : SafeMemo dagSize dagOp dagBytes S g pts b) :
    TermAt dagSize dagOp dagBytes S g pts b id := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact termAt_of_opaque dag_nodes_ok hok.1 (isLitOp_eq hok.2) hbs hsh hsm

private theorem safeMemo_rand_zero {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (ts : Nat) : SafeMemo dagSize dagOp dagBytes S g pts (rnd ts 0) := by
  have hg := ms_pack_random keepOpkI0 S g ⟨ts, 0⟩
  change gamma' keepOpkI0 S g (rnd ts 0) = _ at hg
  intro x hx
  rw [hg] at hx
  dsimp only [gRandom, concretizeRandom, node] at hx
  simp only [↓reduceIte] at hx
  cases hx

private theorem safeMemo_spqrA2B {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    SafeMemo dagSize dagOp dagBytes S g pts spqrA2B :=
  safeMemo_lit_short (ba := ⟨#[DY.Spqr.Direction.a2b.toByte]⟩) (by decide)

private theorem safeMemo_spqrB2A {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    SafeMemo dagSize dagOp dagBytes S g pts spqrB2A :=
  safeMemo_lit_short (ba := ⟨#[DY.Spqr.Direction.b2a.toByte]⟩) (by decide)

private theorem norm_dhPk (a : Bytes) :
    DY.X25519.normalizeX25519Key (dhPk a) = dhPk a := by
  dsimp only [DY.X25519.normalizeX25519Key, DY.DiffieHellman.dhPk,
    DY.DiffieHellman.instCanDHBytes]
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF]

private theorem agree_dhPk (pkSk sk : Bytes) :
    agree (dhPk pkSk) sk = DY.DiffieHellman.dh (dhPk pkSk) sk := by
  unfold agree; rw [norm_dhPk]

private theorem createChain_dhPk (rk pkSk sk : Bytes) :
    createChain rk (dhPk pkSk) sk = kdfRk rk (DY.DiffieHellman.dh (dhPk pkSk) sk) := by
  unfold createChain; rw [agree_dhPk]

private theorem bool_ser_false :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize false =
      [litByte 0] := by
  obtain ⟨ba, _, rfl, heq⟩ :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.bool_serialize_singleton_head false
  exact heq

private theorem bool_ser_true :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true =
      [litByte 1] := by
  obtain ⟨ba, _, rfl, heq⟩ :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.bool_serialize_singleton_head true
  exact heq

/-! ## 3. Common Labels, Setup Nodes, and `storedSecretsOpk` -/

private structure SetupDag (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) : Prop where
  b0 : TermAt dagSize dagOp dagBytes S g pts (litByte 0) id_b0
  b1 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) id_b1
  b2 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) id_b2
  b3 : TermAt dagSize dagOp dagBytes S g pts (litByte 3) id_b3
  b5 : TermAt dagSize dagOp dagBytes S g pts (litByte 5) id_b5
  discont : TermAt dagSize dagOp dagBytes S g pts discontinuity id_discont
  zeroK : TermAt dagSize dagOp dagBytes S g pts zeroKey id_zeroKey
  pqInfo1 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat pqxdhLabel (litByte 1)) id_pqInfo1
  pqInfo2 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat pqxdhLabel (litByte 2)) id_pqInfo2
  pqInfo3 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat pqxdhLabel (litByte 3)) id_pqInfo3
  wrInfo1 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat (lit "WhisperRatchet") (litByte 1)) id_wrInfo1
  wrInfo2 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat (lit "WhisperRatchet") (litByte 2)) id_wrInfo2
  wmkInfo1 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 1)) id_wmkInfo1
  wmkInfo2 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 2)) id_wmkInfo2
  wmkInfo3 : TermAt dagSize dagOp dagBytes S g pts (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 3)) id_wmkInfo3
  ikA : TermAt dagSize dagOp dagBytes S g pts _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikA id_ikA
  ikB : TermAt dagSize dagOp dagBytes S g pts _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikB id_ikB
  spkB : TermAt dagSize dagOp dagBytes S g pts _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.spkB id_spkB
  pqskB : TermAt dagSize dagOp dagBytes S g pts _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.pqskB id_pqskB
  opkB : TermAt dagSize dagOp dagBytes S g pts _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.opkB id_opkB
  ikAPk : TermAt dagSize dagOp dagBytes S g pts (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikA) id_ikAPk
  ikBPk : TermAt dagSize dagOp dagBytes S g pts (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikB) id_ikBPk
  spkBPk : TermAt dagSize dagOp dagBytes S g pts (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.spkB) id_spkBPk
  opkBPk : TermAt dagSize dagOp dagBytes S g pts (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.opkB) id_opkBPk
  ikASer : TermAt dagSize dagOp dagBytes S g pts (serializedIk (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikA)) id_ikASer
  ikBSer : TermAt dagSize dagOp dagBytes S g pts (serializedIk (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikB)) id_ikBSer
  pqpkB : TermAt dagSize dagOp dagBytes S g pts (kemPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.pqskB) id_pqpkB
  dh_spk_ikA : TermAt dagSize dagOp dagBytes S g pts (DY.DiffieHellman.dh (dhPk _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.spkB) _root_.Symbolic.Proofs.Tests.Shared.Composed.HonestSession.ikA) id_dh_spkB_ikA
  secrets_sm : ∀ t ∈ storedSecretsOpk, SafeMemo dagSize dagOp dagBytes S g pts t

private theorem setupDag_of_fit
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat} {pts : List Bytes}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hgsm : DY.Libsignal.Composed.Refinement.GhostAndSemMatchSetup keepOpkI0 r S (gClean r cls)) :
    SetupDag S (gClean r cls) pts := by
  have hf := r_facts_of_fit hfit
  have hrandAt := setupRandomsAt_of_fit hfit
  have hs0 : (gClean r cls).σ 0 32 = dagBytes id_ikA := by
    rw [gClean_sigma_lt26 r cls (by decide)]
    have h : secretBytes r 0 = r.fresh 0 32 := by unfold secretBytes; rw [hrandAt]; rfl
    rw [← h, hf.sec0_eq]; decide +kernel
  have hs5 : (gClean r cls).σ 5 32 = dagBytes id_ikB := by
    rw [gClean_sigma_lt26 r cls (by decide)]
    have h : secretBytes r 1 = r.fresh 5 32 := by unfold secretBytes; rw [hrandAt]; rfl
    rw [← h, hf.sec1_eq]; decide +kernel
  have hs10 : (gClean r cls).σ 10 32 = dagBytes id_spkB := by
    rw [gClean_sigma_lt26 r cls (by decide)]
    have h : secretBytes r 2 = r.fresh 10 32 := by unfold secretBytes; rw [hrandAt]; rfl
    rw [← h, hf.sec2_eq]; decide +kernel
  have hs16 : (gClean r cls).σ 16 64 = dagBytes id_pqskB := by
    rw [gClean_sigma_lt26 r cls (by decide)]
    have h : secretBytes r 4 = r.fresh 16 64 := by unfold secretBytes; rw [hrandAt]; rfl
    rw [← h, hf.sec4_eq]; decide +kernel
  have hs22 : (gClean r cls).σ 22 32 = dagBytes id_opkB := by
    rw [gClean_sigma_lt26 r cls (by decide)]
    have h : secretBytes r 6 = r.fresh 22 32 := by unfold secretBytes; rw [hrandAt]; rfl
    rw [← h, hf.sec6_eq]; decide +kernel
  have tb0 := termAt_lit_b (S := S) (g := gClean r cls) (pts := pts) (ba := ⟨#[0]⟩) (id := id_b0) (by decide +kernel)
  have tb1 := termAt_lit_b (S := S) (g := gClean r cls) (pts := pts) (ba := ⟨#[1]⟩) (id := id_b1) (by decide +kernel)
  have tb2 := termAt_lit_b (S := S) (g := gClean r cls) (pts := pts) (ba := ⟨#[2]⟩) (id := id_b2) (by decide +kernel)
  have tb3 := termAt_lit_b (S := S) (g := gClean r cls) (pts := pts) (ba := ⟨#[3]⟩) (id := id_b3) (by decide +kernel)
  have tb5 := termAt_lit_b (S := S) (g := gClean r cls) (pts := pts) (ba := ⟨#[5]⟩) (id := id_b5) (by decide +kernel)
  have tdisc : TermAt dagSize dagOp dagBytes S (gClean r cls) pts discontinuity id_discont :=
    termAt_lit_b (by decide +kernel)
  have tzK : TermAt dagSize dagOp dagBytes S (gClean r cls) pts zeroKey id_zeroKey :=
    termAt_lit_b (by decide +kernel)
  have tpql := termAt_strLit (S := S) (g := gClean r cls) (pts := pts)
    (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") (id := id_pqLabel) (by decide) (by decide +kernel)
  have twrl := termAt_strLit (S := S) (g := gClean r cls) (pts := pts)
    (s := "WhisperRatchet") (id := id_wrLabel) (by decide) (by decide +kernel)
  have twmkl := termAt_strLit (S := S) (g := gClean r cls) (pts := pts)
    (s := "WhisperMessageKeys") (id := id_wmkLabel) (by decide) (by decide +kernel)
  have talice := termAt_strLit (S := S) (g := gClean r cls) (pts := pts)
    (s := "alice") (id := id_alice) (by decide) (by decide +kernel)
  have tbob := termAt_strLit (S := S) (g := gClean r cls) (pts := pts)
    (s := "bob") (id := id_bob) (by decide) (by decide +kernel)
  have tpqi1 := termAt_concat_b (id := id_pqInfo1) (by decide +kernel) tpql tb1
  have tpqi2 := termAt_concat_b (id := id_pqInfo2) (by decide +kernel) tpql tb2
  have tpqi3 := termAt_concat_b (id := id_pqInfo3) (by decide +kernel) tpql tb3
  have twri1 := termAt_concat_b (id := id_wrInfo1) (by decide +kernel) twrl tb1
  have twri2 := termAt_concat_b (id := id_wrInfo2) (by decide +kernel) twrl tb2
  have twmki1 := termAt_concat_b (id := id_wmkInfo1) (by decide +kernel) twmkl tb1
  have twmki2 := termAt_concat_b (id := id_wmkInfo2) (by decide +kernel) twmkl tb2
  have twmki3 := termAt_concat_b (id := id_wmkInfo3) (by decide +kernel) twmkl tb3
  have tikA := termAt_rand_b (S := S) (pts := pts) (id := id_ikA) hs0 (by decide +kernel)
  have tikB := termAt_rand_b (S := S) (pts := pts) (id := id_ikB) hs5 (by decide +kernel)
  have tspkB := termAt_rand_b (S := S) (pts := pts) (id := id_spkB) hs10 (by decide +kernel)
  have tpqskB := termAt_rand_b (S := S) (pts := pts) (id := id_pqskB) hs16 (by decide +kernel)
  have topkB := termAt_rand_b (S := S) (pts := pts) (id := id_opkB) hs22 (by decide +kernel)
  have tikAPk := termAt_dhPk_b (id := id_ikAPk) (by decide +kernel) tikA
  have tikBPk := termAt_dhPk_b (id := id_ikBPk) (by decide +kernel) tikB
  have tspkBPk := termAt_dhPk_b (id := id_spkBPk) (by decide +kernel) tspkB
  have topkBPk := termAt_dhPk_b (id := id_opkBPk) (by decide +kernel) topkB
  have tikASer := termAt_concat_b (id := id_ikASer) (by decide +kernel) tb5 tikAPk
  have tikBSer := termAt_concat_b (id := id_ikBSer) (by decide +kernel) tb5 tikBPk
  have hpqpk_bs : gamma keepOpkI0 S (gClean r cls) (kemPk pqskB) = dagBytes id_pqpkB := by
    have h6 : gamma keepOpkI0 S (gClean r cls) (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) :=
      hgsm.2.1 r.pqpkPubTerm (by simp)
    have hsp6 := (setupPublic_eqs hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.2.1
    have hw : w0.kyberPk = dagBytes id_pqpkB := by decide +kernel
    exact (congrArg (gamma keepOpkI0 S (gClean r cls)) hsp6.symm).trans (h6.trans (hf.pub6_eq.trans hw))
  have hpqpk_sh : (gamma' keepOpkI0 S (gClean r cls) (kemPk pqskB)).shape =
      litOf (dagBytes id_pqpkB) := by
    have hg := hpqpk_bs
    unfold gamma at hg; unfold gamma' at hg ⊢
    dsimp only [DY.PQKem.kemPk, DY.PQKem.instCanPQKemBytes] at hg ⊢
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeKemPk S)
      (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S (gClean r cls))] at hg ⊢
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeKemPk,
      DY.Libsignal.Composed.Refinement.opaqueNode,
      DY.Libsignal.Composed.Refinement.node] at hg ⊢
    rw [hg]
  have tpqpkB := termAt_opaque_b (id := id_pqpkB) (by decide +kernel)
    hpqpk_bs hpqpk_sh (safeMemo_kemPk tpqskB.2.2.2)
  have tdh_spk_ikA := termAt_dh_b (id := id_dh_spkB_ikA) (by decide +kernel)
    tspkB tspkBPk tikA tikAPk
  have tsec0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := ikA }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) id_sec_ikA := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, alice_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := id_sec_ikA) (by decide +kernel) tb1
      (termAt_concat_b (id := id_sec_ikA_7) (by decide +kernel) tb1
        (termAt_concat_b (id := id_sec_ikA_6) (by decide +kernel) tb1
          (termAt_concat_b (id := id_sec_ikA_5) (by decide +kernel) tb1
            (termAt_concat_b (id := id_sec_ikA_4) (by decide +kernel) tb1
              (termAt_concat_b (id := id_sec_ikA_3) (by decide +kernel) tb0
                (termAt_concat_b (id := id_sec_ikA_2) (by decide +kernel) talice
                  (termAt_concat_b (id := id_sec_ikA_1) (by decide +kernel) tb0
                    (termAt_concat_b (id := id_sec_ikA_0) (by decide +kernel) tb0 tikA))))))))
  have tsec1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := ikB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) id_sec_ikB := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := id_sec_ikB) (by decide +kernel) tb1
      (termAt_concat_b (id := id_sec_ikB_5) (by decide +kernel) tb1
        (termAt_concat_b (id := id_sec_ikB_4) (by decide +kernel) tb1
          (termAt_concat_b (id := id_sec_ikB_3) (by decide +kernel) tb0
            (termAt_concat_b (id := id_sec_ikB_2) (by decide +kernel) tbob
              (termAt_concat_b (id := id_sec_ikB_1) (by decide +kernel) tb0
                (termAt_concat_b (id := id_sec_ikB_0) (by decide +kernel) tb0 tikB))))))
  have tsec2 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) id_sec_spkB := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := id_sec_spkB) (by decide +kernel) tb1
      (termAt_concat_b (id := id_sec_spkB_5) (by decide +kernel) tb1
        (termAt_concat_b (id := id_sec_spkB_4) (by decide +kernel) tb1
          (termAt_concat_b (id := id_sec_spkB_3) (by decide +kernel) tb0
            (termAt_concat_b (id := id_sec_spkB_2) (by decide +kernel) tbob
              (termAt_concat_b (id := id_sec_spkB_1) (by decide +kernel) tb0
                (termAt_concat_b (id := id_sec_spkB_0) (by decide +kernel) tb1 tspkB))))))
  have tsec3 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) id_sec_pqskB := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := id_sec_pqskB) (by decide +kernel) tb1
      (termAt_concat_b (id := id_sec_pqskB_5) (by decide +kernel) tb1
        (termAt_concat_b (id := id_sec_pqskB_4) (by decide +kernel) tb1
          (termAt_concat_b (id := id_sec_pqskB_3) (by decide +kernel) tb0
            (termAt_concat_b (id := id_sec_pqskB_2) (by decide +kernel) tbob
              (termAt_concat_b (id := id_sec_pqskB_1) (by decide +kernel) tb1
                (termAt_concat_b (id := id_sec_pqskB_0) (by decide +kernel) tb0 tpqskB))))))
  have tsec4 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize (⟨"bob", { kind := .oneTimePrekey, sk := opkB }⟩ :
        DY.PersistentLocalState.LocalState PQXDHState)) id_sec_opkB := by
    rw [serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, bob_utf8_sizes.1]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_false, bool_ser_true,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    exact termAt_concat_b (id := id_sec_opkB) (by decide +kernel) tb1
      (termAt_concat_b (id := id_sec_opkB_5) (by decide +kernel) tb1
        (termAt_concat_b (id := id_sec_opkB_4) (by decide +kernel) tb1
          (termAt_concat_b (id := id_sec_opkB_3) (by decide +kernel) tb0
            (termAt_concat_b (id := id_sec_opkB_2) (by decide +kernel) tbob
              (termAt_concat_b (id := id_sec_opkB_1) (by decide +kernel) tb1
                (termAt_concat_b (id := id_sec_opkB_0) (by decide +kernel) tb1 topkB))))))
  have hsecs : ∀ t ∈ storedSecretsOpk, SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts t := by
    intro t ht
    simp only [storedSecretsOpk, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact tsec0.2.2.2
    · exact tsec1.2.2.2
    · exact tsec2.2.2.2
    · exact tsec3.2.2.2
    · exact tsec4.2.2.2
  exact ⟨tb0, tb1, tb2, tb3, tb5, tdisc, tzK,
    tpqi1, tpqi2, tpqi3, twri1, twri2, twmki1, twmki2, twmki3,
    tikA, tikB, tspkB, tpqskB, topkB,
    tikAPk, tikBPk, tspkBPk, topkBPk, tikASer, tikBSer, tpqpkB,
    tdh_spk_ikA, hsecs⟩

/-! ## 4. Session 1 (`s0Clean`, `s1Clean`) and Session 2 (`s3Clean`, `s4Clean`) DAG Walks -/

private theorem dag_kdf_eq {a b id : Nat} (h : id < dagSize ∧ dagOp id = .kdf a b) :
    hmacWith FK (dagBytes a) (dagBytes b) = dagBytes id := by
  have hok := dag_nodes_ok id h.1
  unfold DagDefs.dagNodeOk at hok
  rw [h.2] at hok
  simp only [DagDefs.dagOpBytesOk, Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.2.symm

private theorem dag_concat_eq {a b id : Nat} (h : id < dagSize ∧ dagOp id = .concat a b) :
    dagBytes a ++ dagBytes b = dagBytes id := by
  have hok := dag_nodes_ok id h.1
  unfold DagDefs.dagNodeOk at hok
  rw [h.2] at hok
  simp only [DagDefs.dagOpBytesOk, Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.2.symm

private theorem dag_trunc8_eq {a id : Nat} (h : id < dagSize ∧ dagOp id = .trunc8 a) :
    (dagBytes a).take 8 = dagBytes id := by
  have hok := dag_nodes_ok id h.1
  unfold DagDefs.dagNodeOk at hok
  rw [h.2] at hok
  simp only [DagDefs.dagOpBytesOk, Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.2.symm

private theorem gamma_lit_of_trialRowOk
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {pIk_id mIk_id wire_id : Nat} {row : TrialRow}
    (sd : SetupDag S g pts)
    (hok : TrialRowOk pIk_id mIk_id wire_id row) :
    gamma keepOpkI0 S g (trMsgKeys (litOf (dagBytes row.salt)) (litOf (dagBytes row.seed))).cipherKey =
      dagBytes row.ck ∧
    gamma keepOpkI0 S g (trMsgKeys (litOf (dagBytes row.salt)) (litOf (dagBytes row.seed))).iv =
      dagBytes row.iv ∧
    gamma keepOpkI0 S g
        (computeMac (trMsgKeys (litOf (dagBytes row.salt)) (litOf (dagBytes row.seed))).macKey
          (litOf (dagBytes pIk_id)) (litOf (dagBytes mIk_id)) (litOf (dagBytes wire_id))) =
      dagBytes row.mac := by
  obtain ⟨hprk, hck, hc2, hmk, hc3, hiv, hcm1, hcm2, hhm, hmac⟩ := hok
  unfold trMsgKeys DY.Libsignal.TripleRatchet.hkdfBlock3
    DY.Libsignal.TripleRatchet.hkdfBlock2 DY.Libsignal.TripleRatchet.hkdfBlock1 computeMac
  dsimp only
  simp only [gamma_trunc8K, gamma_hmacK, gamma_concatK, gamma_litOf,
    sd.wmkInfo1.gamma_eq, sd.wmkInfo2.gamma_eq, sd.wmkInfo3.gamma_eq,
    dag_kdf_eq hprk, dag_kdf_eq hck, dag_concat_eq hc2, dag_kdf_eq hmk,
    dag_concat_eq hc3, dag_kdf_eq hiv, dag_concat_eq hcm1, dag_concat_eq hcm2,
    dag_kdf_eq hhm, dag_trunc8_eq hmac]
  exact ⟨trivial, trivial, trivial⟩

private structure Session1Dag (S : OpaqueSymbolSemantics) (g : Ghost)
    (cls : Nat → Nat) (pts : List Bytes) : Prop where
  dhsA : TermAt dagSize dagOp dagBytes S g pts dhsAOpk id_s1_dhsA
  ekPk : TermAt dagSize dagOp dagBytes S g pts oOpk.ek id_s1_ekPk
  dhsAPk : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsAOpk) id_s1_dhsAPk
  ct : TermAt dagSize dagOp dagBytes S g pts oOpk.ct id_s1_ct
  rk0 : TermAt dagSize dagOp dagBytes S g pts keysOpk.rk id_s1_rk0
  ck0 : TermAt dagSize dagOp dagBytes S g pts keysOpk.ck id_s1_ck0
  pqr : TermAt dagSize dagOp dagBytes S g pts keysOpk.pqr id_s1_pqr
  st_rk : TermAt dagSize dagOp dagBytes S g pts stA0Opk.rk id_s1_st_rk
  st_cks : TermAt dagSize dagOp dagBytes S g pts stA0Opk.cks id_s1_st_cks
  st_sid : TermAt dagSize dagOp dagBytes S g pts stA0Opk.sid id_s1_st_sid
  nck0 : TermAt dagSize dagOp dagBytes S g pts (kdfCk stA0Opk.cks).1 id_nck0
  seed0 : TermAt dagSize dagOp dagBytes S g pts (kdfCk stA0Opk.cks).2 id_seed0
  salt0 : TermAt dagSize dagOp dagBytes S g pts (key0Clean cls) id_salt0
  salt0_opk : TermAt dagSize dagOp dagBytes S g pts key0Opk id_salt0
  pqm0 : TermAt dagSize dagOp dagBytes S g pts (pqm0Clean cls) id_pqm0
  ct0 : TermAt dagSize dagOp dagBytes S g pts (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).ciphertext id_ct0
  wire0 : TermAt dagSize dagOp dagBytes S g pts (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).wire id_wire0
  mac0 : TermAt dagSize dagOp dagBytes S g pts (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).mac id_m0m_mac
  wmac0 : TermAt dagSize dagOp dagBytes S g pts (m0Clean cls) id_wmac0
  stA0_sm2 : SafeMemo2 dagSize dagOp dagBytes S g pts
    (DY.Comparse.serialize ({ participant := "alice", state := stA0Opk } :
      DY.PersistentLocalState.LocalState TRState))
  stA1_sm2 : SafeMemo2 dagSize dagOp dagBytes S g pts
    (DY.Comparse.serialize ({ participant := "alice", state := stA1Clean cls } :
      DY.PersistentLocalState.LocalState TRState))

private theorem session1Dag_of_m0
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat} {pts : List Bytes}
    (sd : SetupDag S (gClean r cls) pts)
    (hcl0 : cls 0 = 0 ∨ cls 0 = 32 ∨ cls 0 = 64)
    (hpt0_mem : pt0Clean ∈ pts)
    (hm0 : gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message) :
    Session1Dag S (gClean r cls) cls pts := by
  have hs26 : (gClean r cls).σ 26 32 = dagBytes id_s1_ek := by
    rw [gClean_sigma_26, ev0Coins_eq]; decide +kernel
  have hs27 : (gClean r cls).σ 27 32 = dagBytes id_s1_e := by
    rw [gClean_sigma_27, ev0KyberEnt_eq]; decide +kernel
  have hs28 : (gClean r cls).σ 28 32 = dagBytes id_s1_dhsA := by
    rw [gClean_sigma_28, ev0Coins_eq]; decide +kernel
  have tek := termAt_rand_b (S := S) (pts := pts) (id := id_s1_ek) hs26 (by decide +kernel)
  have te := termAt_rand_b (S := S) (pts := pts) (id := id_s1_e) hs27 (by decide +kernel)
  have tdhsA : TermAt dagSize dagOp dagBytes S (gClean r cls) pts dhsAOpk id_s1_dhsA :=
    termAt_rand_b (pts := pts) (id := id_s1_dhsA) hs28 (by decide +kernel)
  have tekPk0 := termAt_dhPk_b (id := id_s1_ekPk) (by decide +kernel) tek
  have hek_eq : oOpk.ek = dhPk (rnd 26 32) := by
    dsimp only [oOpk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t4Opk_length]; rfl
  have tekPk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts oOpk.ek id_s1_ekPk :=
    hek_eq ▸ tekPk0
  have tdhsAPk := termAt_dhPk_b (id := id_s1_dhsAPk) (by decide +kernel) tdhsA
  have hkem := termAt_kemEncap_b (id1 := id_s1_ct) (id2 := id_s1_ss) (by decide +kernel) sd.pqpkB te
  have hct_eq : oOpk.ct = (kemEncap (kemPk pqskB) (rnd 27 32)).1 := by
    dsimp only [oOpk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t4Opk_length]; rfl
  have tct : TermAt dagSize dagOp dagBytes S (gClean r cls) pts oOpk.ct id_s1_ct := hct_eq ▸ hkem.1
  have tss := hkem.2
  have hkeys_eq : keysOpk = pqxdhKdf (pqxdhIkm
      (DY.DiffieHellman.dh (dhPk spkB) ikA)
      (DY.DiffieHellman.dh (dhPk ikB) (rnd 26 32))
      (DY.DiffieHellman.dh (dhPk spkB) (rnd 26 32))
      (some (DY.DiffieHellman.dh (dhPk opkB) (rnd 26 32)))
      (kemEncap (kemPk pqskB) (rnd 27 32)).2) := by
    dsimp only [keysOpk, oOpk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t4Opk_length]; dsimp only [Option.map]
    rw [agree_dhPk, agree_dhPk, agree_dhPk, agree_dhPk]; rfl
  have tdh2 := termAt_dh_b (id := id_s1_dh2) (by decide +kernel) sd.ikB sd.ikBPk tek tekPk0
  have tdh3 := termAt_dh_b (id := id_s1_dh3) (by decide +kernel) sd.spkB sd.spkBPk tek tekPk0
  have tdh4 := termAt_dh_b (id := id_s1_dh4) (by decide +kernel) sd.opkB sd.opkBPk tek tekPk0
  have tikm4 := termAt_concat_b (id := id_s1_ikm4) (by decide +kernel) tdh4 tss
  have tikm3 := termAt_concat_b (id := id_s1_ikm3) (by decide +kernel) tdh3 tikm4
  have tikm2 := termAt_concat_b (id := id_s1_ikm2) (by decide +kernel) tdh2 tikm3
  have tikm1 := termAt_concat_b (id := id_s1_ikm1) (by decide +kernel) sd.dh_spk_ikA tikm2
  have tikm := termAt_concat_b (id := id_s1_ikm) (by decide +kernel) sd.discont tikm1
  have tprk := termAt_kdf_b (id := id_s1_prk) (by decide +kernel) sd.zeroK tikm
  have trk0_raw := termAt_kdf_b (id := id_s1_rk0) (by decide +kernel) tprk sd.pqInfo1
  have tcrk0 := termAt_concat_b (id := id_s1_c_rk0) (by decide +kernel) trk0_raw sd.pqInfo2
  have tck0_raw := termAt_kdf_b (id := id_s1_ck0) (by decide +kernel) tprk tcrk0
  have tcck0 := termAt_concat_b (id := id_s1_c_ck0) (by decide +kernel) tck0_raw sd.pqInfo3
  have tpqr_raw := termAt_kdf_b (id := id_s1_pqr) (by decide +kernel) tprk tcck0
  have trk0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keysOpk.rk id_s1_rk0 := hkeys_eq ▸ trk0_raw
  have tck0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keysOpk.ck id_s1_ck0 := hkeys_eq ▸ tck0_raw
  have tpqr : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keysOpk.pqr id_s1_pqr := hkeys_eq ▸ tpqr_raw
  have tdh_rat := termAt_dh_b (id := id_s1_dh_rat) (by decide +kernel) sd.spkB sd.spkBPk tdhsA tdhsAPk
  have trat_prk := termAt_kdf_b (id := id_s1_rat_prk) (by decide +kernel) trk0 tdh_rat
  have tst_rk_raw := termAt_kdf_b (id := id_s1_st_rk) (by decide +kernel) trat_prk sd.wrInfo1
  have tc_st_rk := termAt_concat_b (id := id_s1_c_st_rk) (by decide +kernel) tst_rk_raw sd.wrInfo2
  have tst_cks_raw := termAt_kdf_b (id := id_s1_st_cks) (by decide +kernel) trat_prk tc_st_rk
  have hcc : createChain keysOpk.rk oOpk.spk dhsAOpk =
      kdfRk keysOpk.rk (DY.DiffieHellman.dh (dhPk spkB) dhsAOpk) :=
    createChain_dhPk keysOpk.rk spkB dhsAOpk
  have tst_rk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA0Opk.rk id_s1_st_rk := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts (createChain keysOpk.rk oOpk.spk dhsAOpk).1 id_s1_st_rk
    rw [hcc]; exact tst_rk_raw
  have tst_cks : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA0Opk.cks id_s1_st_cks := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts (createChain keysOpk.rk oOpk.spk dhsAOpk).2 id_s1_st_cks
    rw [hcc]; exact tst_cks_raw
  have tst_sid : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA0Opk.sid id_s1_st_sid :=
    termAt_concat_b (id := id_s1_st_sid) (by decide +kernel) tdhsAPk trk0
  have tnck0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (kdfCk stA0Opk.cks).1 id_nck0 :=
    termAt_kdf_b (id := id_nck0) (by decide +kernel) tst_cks sd.b2
  have tseed0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (kdfCk stA0Opk.cks).2 id_seed0 :=
    termAt_kdf_b (id := id_seed0) (by decide +kernel) tst_cks sd.b1
  have hcoins0_sm : SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts (coins0Clean cls) := by
    unfold coins0Clean
    rcases hcl0 with hc | hc | hc <;> rw [hc]
    · exact safeMemo_rand_zero 36
    · exact (termAt_rand_b (S := S) (pts := pts) (id := id_coins0_32)
        (by rw [gClean_sigma_36, ev1Coins_eq]; decide +kernel) (by decide +kernel)).2.2.2
    · exact (termAt_rand_b (S := S) (pts := pts) (id := id_coins0_64)
        (by rw [gClean_sigma_36, ev1Coins_eq]; decide +kernel) (by decide +kernel)).2.2.2
  have hspqrA0_sm : SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts stA0Opk.spqr :=
    safeMemo_spqrInit tpqr.2.2.2 safeMemo_spqrA2B
  obtain ⟨hspqrA1_sm, hkey0_sm, hpqm0_sm⟩ := safeMemo_spqrSend hspqrA0_sm hcoins0_sm
  obtain ⟨hlit_ck, hlit_iv, hlit_mac⟩ := gamma_lit_of_trialRowOk sd trow2_s0_ok
  have hpins := encMsg_pins_pqKey_and_pqMsg (st := stA0Opk) (coins := coins0Clean cls) (ptTs := 35)
    (salt₀ := dagBytes id_salt0) (seed₀ := dagBytes id_seed0) (rk₀ := dagBytes id_s1_dhsAPk)
    (myIk₀ := dagBytes id_ikASer) (peerIk₀ := dagBytes id_ikBSer)
    (pt₀ := (ev 1).input) (addr₀ := aliceBobAddrBytes) (pqm₀ := dagBytes id_pqm0)
    (ckey₀ := dagBytes id_m0k_ck) (iv₀ := dagBytes id_m0k_iv)
    (ct₀ := dagBytes id_ct0) (wire₀ := dagBytes id_wire0) (mac₀ := dagBytes id_m0m_mac)
    (hm0.trans wire0_append_mac0_eq_p2.symm)
    (by decide +kernel) (by decide +kernel) mac0_untagged
    tseed0.2.1 tdhsAPk.2.1 (gClean_sigma_35 r cls 32)
    ((gClean_addr r cls _).trans serializeAddresses_alice_bob_eq)
    hlit_mac.symm hlit_ck hlit_iv
    (by rw [ev1In_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨hsh_k0, hsh_pqm0⟩ := spqrSend_shapes S (gClean r cls) stA0Opk.spqr (coins0Clean cls)
  have tsalt0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (key0Clean cls) id_salt0 :=
    termAt_opaque_b (id := id_salt0) (by decide +kernel)
      hpins.1 (hsh_k0.trans (congrArg litOf hpins.1)) hkey0_sm
  have tsalt0_opk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts key0Opk id_salt0 :=
    key0Clean_eq cls ▸ tsalt0
  have tpqm0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (pqm0Clean cls) id_pqm0 :=
    termAt_opaque_b (id := id_pqm0) (by decide +kernel)
      hpins.2 (hsh_pqm0.trans (congrArg litOf hpins.2)) hpqm0_sm
  obtain ⟨hprk0, hck0, hc2_0, hmk0, hc3_0, hiv0, hcm1_0, hcm2_0, hhm0, hmac0⟩ := trow2_s0_ok
  obtain ⟨tm0_ck, tm0_mk, tm0_iv⟩ := termAt_trMsgKeys dag_nodes_ok
    sd.wmkInfo1 sd.wmkInfo2 sd.wmkInfo3
    hprk0 hck0 hc2_0 hmk0 hc3_0 hiv0 tsalt0 tseed0
  have tct0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).ciphertext id_ct0 :=
    termAt_symEncPt_b (id := id_ct0) (ptBs := WitnessParse.ev1InF) (by decide +kernel)
      tm0_ck tm0_iv hpt0_mem ((gClean_sigma_35 r cls 32).trans ev1In_eq)
  have twire0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).wire id_wire0 :=
    termAt_trWire_b (id := id_wire0) (by decide +kernel) tdhsAPk tct0 tpqm0
      ((gClean_addr r cls _).trans serializeAddresses_alice_bob_eq)
  have tmac0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).mac id_m0m_mac :=
    termAt_computeMac dag_nodes_ok hcm1_0 hcm2_0 hhm0 hmac0 tm0_mk sd.ikASer sd.ikBSer twire0
  have twmac0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (m0Clean cls) id_wmac0 :=
    termAt_concat_b (id := id_wmac0) (by decide +kernel) twire0 tmac0
  have hstA0_sm2 : SafeMemo2 dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize ({ participant := "alice", state := stA0Opk } :
        DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := { participant := "alice", state := stA0Opk })
      (cLast := { ratchetKey := dhPk spkB, chainKey := keysOpk.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqrA0_sm ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact sd.ikASer.2.2.2
      · exact sd.ikBSer.2.2.2
      · exact tst_rk.2.2.2
      · exact tdhsA.2.2.2
      · exact tst_cks.2.2.2
      · exact tst_sid.2.2.2
    · intro c hc
      change c ∈ [{ ratchetKey := dhPk spkB, chainKey := keysOpk.ck, index := 0, rIdx := 1 }] at hc
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨sd.spkBPk.2.2.2, tck0.2.2.2⟩
  have hstA1_sm2 : SafeMemo2 dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize ({ participant := "alice", state := stA1Clean cls } :
        DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := { participant := "alice", state := stA1Clean cls })
      (cLast := { ratchetKey := dhPk spkB, chainKey := keysOpk.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqrA1_sm ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact sd.ikASer.2.2.2
      · exact sd.ikBSer.2.2.2
      · exact tst_rk.2.2.2
      · exact tdhsA.2.2.2
      · exact tnck0.2.2.2
      · exact tst_sid.2.2.2
    · intro c hc
      change c ∈ [{ ratchetKey := dhPk spkB, chainKey := keysOpk.ck, index := 0, rIdx := 1 }] at hc
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨sd.spkBPk.2.2.2, tck0.2.2.2⟩
  exact ⟨tdhsA, tekPk, tdhsAPk, tct, trk0, tck0, tpqr, tst_rk, tst_cks, tst_sid,
    tnck0, tseed0, tsalt0, tsalt0_opk, tpqm0, tct0, twire0, tmac0, twmac0,
    hstA0_sm2, hstA1_sm2⟩

private theorem stB1Clean_sm2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat} {pts : List Bytes}
    (sd : SetupDag S (gClean r cls) pts)
    (s1 : Session1Dag S (gClean r cls) cls pts) :
    SafeMemo2 dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize ({ participant := "bob", state := stB1Clean cls } :
        DY.PersistentLocalState.LocalState TRState)) := by
  have hs42 : (gClean r cls).σ 42 32 = dagBytes id_dhsB1 := by
    rw [gClean_sigma_42, ev2Coins_eq]; decide +kernel
  have tdhsB1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts dhsB1Opk id_dhsB1 :=
    termAt_rand_b (pts := pts) (id := id_dhsB1) hs42 (by decide +kernel)
  have tdhsB1Pk := termAt_dhPk_b (id := id_dhsB1Pk) (by decide +kernel) tdhsB1
  have tdh_b1 := termAt_dh_b (id := id_dh_b1) (by decide +kernel) s1.dhsA s1.dhsAPk tdhsB1 tdhsB1Pk
  have tb1_prk := termAt_kdf_b (id := id_b1_prk) (by decide +kernel) s1.st_rk tdh_b1
  have tb1_rk_raw := termAt_kdf_b (id := id_b1_rk) (by decide +kernel) tb1_prk sd.wrInfo1
  have tc_b1_rk := termAt_concat_b (id := id_c_b1_rk) (by decide +kernel) tb1_rk_raw sd.wrInfo2
  have tb1_cks_raw := termAt_kdf_b (id := id_b1_cks) (by decide +kernel) tb1_prk tc_b1_rk
  have hrk1 : (createChain keysOpk.rk (dhPk dhsAOpk) spkB).1 = stA0Opk.rk := by
    show (createChain keysOpk.rk (dhPk dhsAOpk) spkB).1 =
      (createChain keysOpk.rk (dhPk spkB) dhsAOpk).1
    rw [createChain_comm keysOpk.rk dhsAOpk spkB]
  have hckr : (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2 = stA0Opk.cks := by
    show (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2 =
      (createChain keysOpk.rk (dhPk spkB) dhsAOpk).2
    rw [createChain_comm keysOpk.rk dhsAOpk spkB]
  have hcc_b1 : createChain stA0Opk.rk (dhPk dhsAOpk) dhsB1Opk =
      kdfRk stA0Opk.rk (DY.DiffieHellman.dh (dhPk dhsAOpk) dhsB1Opk) :=
    createChain_dhPk stA0Opk.rk dhsAOpk dhsB1Opk
  have tb1_rk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (stB1Clean cls).rk id_b1_rk := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (createChain (createChain keysOpk.rk (dhPk dhsAOpk) spkB).1 (dhPk dhsAOpk) dhsB1Opk).1 id_b1_rk
    rw [hrk1, hcc_b1]; exact tb1_rk_raw
  have tb1_cks : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (stB1Clean cls).cks id_b1_cks := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (createChain (createChain keysOpk.rk (dhPk dhsAOpk) spkB).1 (dhPk dhsAOpk) dhsB1Opk).2 id_b1_cks
    rw [hrk1, hcc_b1]; exact tb1_cks_raw
  have hb1_sid : (stB1Clean cls).sid = stA0Opk.sid := by
    change DY.Concat.concat (DY.X25519.normalizeX25519Key (dhPk dhsAOpk)) keysOpk.rk = _
    rw [norm_dhPk]; rfl
  have hcB'_ck : cB'Opk.chainKey = (kdfCk stA0Opk.cks).1 := by
    change (kdfCk (createChain keysOpk.rk (dhPk dhsAOpk) spkB).2).1 = _
    rw [hckr]
  have hspqr_b1 : SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts (stB1Clean cls).spqr :=
    safeMemo_recvSt (safeMemo_spqrInit s1.pqr.2.2.2 safeMemo_spqrB2A) s1.pqm0.2.2.2
  refine safeMemo2_trState_of_dr (ls₀ := { participant := "bob", state := stB1Clean cls })
    (cLast := cB'Opk)
    rfl rfl (Or.inr rfl) (Or.inl rfl) hspqr_b1 ?_ ?_ rfl (by decide)
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sd.ikBSer.2.2.2
    · exact sd.ikASer.2.2.2
    · exact tb1_rk.2.2.2
    · exact tdhsB1.2.2.2
    · exact tb1_cks.2.2.2
    · rw [hb1_sid]; exact s1.st_sid.2.2.2
  · intro c hc
    change c ∈ [cB'Opk] at hc
    rw [List.mem_singleton] at hc; subst hc
    exact ⟨s1.dhsAPk.2.2.2, by rw [hcB'_ck]; exact s1.nck0.2.2.2⟩

private structure Session2Dag (S : OpaqueSymbolSemantics) (g : Ghost)
    (cls : Nat → Nat) (pts : List Bytes) : Prop where
  ekPk : TermAt dagSize dagOp dagBytes S g pts o2Clean.ek id_s2_ekPk
  dhsAPk : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsA2Clean) id_s2_dhsAPk
  ct : TermAt dagSize dagOp dagBytes S g pts o2Clean.ct id_s2_ct
  rk0 : TermAt dagSize dagOp dagBytes S g pts keys2Clean.rk id_s2_rk0
  ck0 : TermAt dagSize dagOp dagBytes S g pts keys2Clean.ck id_s2_ck0
  pqr : TermAt dagSize dagOp dagBytes S g pts keys2Clean.pqr id_s2_pqr
  st_cks : TermAt dagSize dagOp dagBytes S g pts stA2_0Clean.cks id_s2_st_cks
  nck1 : TermAt dagSize dagOp dagBytes S g pts (kdfCk stA2_0Clean.cks).1 id_nck1
  seed1 : TermAt dagSize dagOp dagBytes S g pts (kdfCk stA2_0Clean.cks).2 id_seed1
  salt1 : TermAt dagSize dagOp dagBytes S g pts (key1Clean cls) id_salt1
  salt1_opk : TermAt dagSize dagOp dagBytes S g pts key1Opk id_salt1
  pqm1 : TermAt dagSize dagOp dagBytes S g pts (pqm1Clean cls) id_pqm1
  ct1 : TermAt dagSize dagOp dagBytes S g pts (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).ciphertext id_ct1
  wire1 : TermAt dagSize dagOp dagBytes S g pts (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).wire id_wire1
  mac1 : TermAt dagSize dagOp dagBytes S g pts (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).mac id_m1m_mac
  wmac1 : TermAt dagSize dagOp dagBytes S g pts (m1Clean cls) id_wmac1
  stA2_0_sm2 : SafeMemo2 dagSize dagOp dagBytes S g pts
    (DY.Comparse.serialize ({ participant := "alice", state := stA2_0Clean } :
      DY.PersistentLocalState.LocalState TRState))
  stA2_1_sm2 : SafeMemo2 dagSize dagOp dagBytes S g pts
    (DY.Comparse.serialize ({ participant := "alice", state := stA2_1Clean cls } :
      DY.PersistentLocalState.LocalState TRState))

private theorem session2Dag_of_m1
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat} {pts : List Bytes}
    (sd : SetupDag S (gClean r cls) pts)
    (hcl1 : cls 1 = 0 ∨ cls 1 = 32 ∨ cls 1 = 64)
    (hpt1_mem : pt1Clean ∈ pts)
    (hm1 : gamma keepOpkI0 S (gClean r cls) (m1Clean cls) = p5.message) :
    Session2Dag S (gClean r cls) cls pts := by
  have hs52 : (gClean r cls).σ 52 32 = dagBytes id_s2_ek := by
    rw [gClean_sigma_52, ev3Coins_eq]; decide +kernel
  have hs53 : (gClean r cls).σ 53 32 = dagBytes id_s2_e := by
    rw [gClean_sigma_53, ev3KyberEnt_eq]; decide +kernel
  have hs54 : (gClean r cls).σ 54 32 = dagBytes id_s2_dhsA := by
    rw [gClean_sigma_54, ev3Coins_eq]; decide +kernel
  have tek := termAt_rand_b (S := S) (pts := pts) (id := id_s2_ek) hs52 (by decide +kernel)
  have te := termAt_rand_b (S := S) (pts := pts) (id := id_s2_e) hs53 (by decide +kernel)
  have tdhsA : TermAt dagSize dagOp dagBytes S (gClean r cls) pts dhsA2Clean id_s2_dhsA :=
    termAt_rand_b (pts := pts) (id := id_s2_dhsA) hs54 (by decide +kernel)
  have tekPk0 := termAt_dhPk_b (id := id_s2_ekPk) (by decide +kernel) tek
  have hek_eq : o2Clean.ek = dhPk (rnd 52 32) := by
    dsimp only [o2Clean, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
    rw [t7Opk_length]; rfl
  have tekPk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts o2Clean.ek id_s2_ekPk :=
    hek_eq ▸ tekPk0
  have tdhsAPk := termAt_dhPk_b (id := id_s2_dhsAPk) (by decide +kernel) tdhsA
  have hkem := termAt_kemEncap_b (id1 := id_s2_ct) (id2 := id_s2_ss) (by decide +kernel) sd.pqpkB te
  have hct_eq : o2Clean.ct = (kemEncap (kemPk pqskB) (rnd 53 32)).1 := by
    dsimp only [o2Clean, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t7Opk_length]; rfl
  have tct : TermAt dagSize dagOp dagBytes S (gClean r cls) pts o2Clean.ct id_s2_ct := hct_eq ▸ hkem.1
  have tss := hkem.2
  have hkeys_eq : keys2Clean = pqxdhKdf (pqxdhIkm
      (DY.DiffieHellman.dh (dhPk spkB) ikA)
      (DY.DiffieHellman.dh (dhPk ikB) (rnd 52 32))
      (DY.DiffieHellman.dh (dhPk spkB) (rnd 52 32))
      (some (DY.DiffieHellman.dh (dhPk opkB) (rnd 52 32)))
      (kemEncap (kemPk pqskB) (rnd 53 32)).2) := by
    dsimp only [keys2Clean, o2Clean, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [t7Opk_length]; dsimp only [Option.map]
    rw [agree_dhPk, agree_dhPk, agree_dhPk, agree_dhPk]; rfl
  have tdh2 := termAt_dh_b (id := id_s2_dh2) (by decide +kernel) sd.ikB sd.ikBPk tek tekPk0
  have tdh3 := termAt_dh_b (id := id_s2_dh3) (by decide +kernel) sd.spkB sd.spkBPk tek tekPk0
  have tdh4 := termAt_dh_b (id := id_s2_dh4) (by decide +kernel) sd.opkB sd.opkBPk tek tekPk0
  have tikm4 := termAt_concat_b (id := id_s2_ikm4) (by decide +kernel) tdh4 tss
  have tikm3 := termAt_concat_b (id := id_s2_ikm3) (by decide +kernel) tdh3 tikm4
  have tikm2 := termAt_concat_b (id := id_s2_ikm2) (by decide +kernel) tdh2 tikm3
  have tikm1 := termAt_concat_b (id := id_s2_ikm1) (by decide +kernel) sd.dh_spk_ikA tikm2
  have tikm := termAt_concat_b (id := id_s2_ikm) (by decide +kernel) sd.discont tikm1
  have tprk := termAt_kdf_b (id := id_s2_prk) (by decide +kernel) sd.zeroK tikm
  have trk0_raw := termAt_kdf_b (id := id_s2_rk0) (by decide +kernel) tprk sd.pqInfo1
  have tcrk0 := termAt_concat_b (id := id_s2_c_rk0) (by decide +kernel) trk0_raw sd.pqInfo2
  have tck0_raw := termAt_kdf_b (id := id_s2_ck0) (by decide +kernel) tprk tcrk0
  have tcck0 := termAt_concat_b (id := id_s2_c_ck0) (by decide +kernel) tck0_raw sd.pqInfo3
  have tpqr_raw := termAt_kdf_b (id := id_s2_pqr) (by decide +kernel) tprk tcck0
  have trk0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keys2Clean.rk id_s2_rk0 := hkeys_eq ▸ trk0_raw
  have tck0 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keys2Clean.ck id_s2_ck0 := hkeys_eq ▸ tck0_raw
  have tpqr : TermAt dagSize dagOp dagBytes S (gClean r cls) pts keys2Clean.pqr id_s2_pqr := hkeys_eq ▸ tpqr_raw
  have tdh_rat := termAt_dh_b (id := id_s2_dh_rat) (by decide +kernel) sd.spkB sd.spkBPk tdhsA tdhsAPk
  have trat_prk := termAt_kdf_b (id := id_s2_rat_prk) (by decide +kernel) trk0 tdh_rat
  have tst_rk_raw := termAt_kdf_b (id := id_s2_st_rk) (by decide +kernel) trat_prk sd.wrInfo1
  have tc_st_rk := termAt_concat_b (id := id_s2_c_st_rk) (by decide +kernel) tst_rk_raw sd.wrInfo2
  have tst_cks_raw := termAt_kdf_b (id := id_s2_st_cks) (by decide +kernel) trat_prk tc_st_rk
  have hcc : createChain keys2Clean.rk o2Clean.spk dhsA2Clean =
      kdfRk keys2Clean.rk (DY.DiffieHellman.dh (dhPk spkB) dhsA2Clean) :=
    createChain_dhPk keys2Clean.rk spkB dhsA2Clean
  have tst_rk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA2_0Clean.rk id_s2_st_rk := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts (createChain keys2Clean.rk o2Clean.spk dhsA2Clean).1 id_s2_st_rk
    rw [hcc]; exact tst_rk_raw
  have tst_cks : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA2_0Clean.cks id_s2_st_cks := by
    change TermAt dagSize dagOp dagBytes S (gClean r cls) pts (createChain keys2Clean.rk o2Clean.spk dhsA2Clean).2 id_s2_st_cks
    rw [hcc]; exact tst_cks_raw
  have tst_sid : TermAt dagSize dagOp dagBytes S (gClean r cls) pts stA2_0Clean.sid id_s2_st_sid :=
    termAt_concat_b (id := id_s2_st_sid) (by decide +kernel) tdhsAPk trk0
  have tnck1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (kdfCk stA2_0Clean.cks).1 id_nck1 :=
    termAt_kdf_b (id := id_nck1) (by decide +kernel) tst_cks sd.b2
  have tseed1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (kdfCk stA2_0Clean.cks).2 id_seed1 :=
    termAt_kdf_b (id := id_seed1) (by decide +kernel) tst_cks sd.b1
  have hcoins1_sm : SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts (coins1Clean cls) := by
    unfold coins1Clean
    rcases hcl1 with hc | hc | hc <;> rw [hc]
    · exact safeMemo_rand_zero 62
    · exact (termAt_rand_b (S := S) (pts := pts) (id := id_coins1_32)
        (by rw [gClean_sigma_62, ev4Coins_eq]; decide +kernel) (by decide +kernel)).2.2.2
    · exact (termAt_rand_b (S := S) (pts := pts) (id := id_coins1_64)
        (by rw [gClean_sigma_62, ev4Coins_eq]; decide +kernel) (by decide +kernel)).2.2.2
  have hspqrA0_sm : SafeMemo dagSize dagOp dagBytes S (gClean r cls) pts stA2_0Clean.spqr :=
    safeMemo_spqrInit tpqr.2.2.2 safeMemo_spqrA2B
  obtain ⟨hspqrA1_sm, hkey1_sm, hpqm1_sm⟩ := safeMemo_spqrSend hspqrA0_sm hcoins1_sm
  obtain ⟨hlit_ck, hlit_iv, hlit_mac⟩ := gamma_lit_of_trialRowOk sd trow5_s1_ok
  have hpins := encMsg_pins_pqKey_and_pqMsg (st := stA2_0Clean) (coins := coins1Clean cls) (ptTs := 61)
    (salt₀ := dagBytes id_salt1) (seed₀ := dagBytes id_seed1) (rk₀ := dagBytes id_s2_dhsAPk)
    (myIk₀ := dagBytes id_ikASer) (peerIk₀ := dagBytes id_ikBSer)
    (pt₀ := (ev 4).input) (addr₀ := aliceBobAddrBytes) (pqm₀ := dagBytes id_pqm1)
    (ckey₀ := dagBytes id_m1k_ck) (iv₀ := dagBytes id_m1k_iv)
    (ct₀ := dagBytes id_ct1) (wire₀ := dagBytes id_wire1) (mac₀ := dagBytes id_m1m_mac)
    (hm1.trans wire1_append_mac1_eq_p5.symm)
    (by decide +kernel) (by decide +kernel) mac1_untagged
    tseed1.2.1 tdhsAPk.2.1 (gClean_sigma_61 r cls 32)
    ((gClean_addr r cls _).trans serializeAddresses_alice_bob_eq)
    hlit_mac.symm hlit_ck hlit_iv
    (by rw [ev4In_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  obtain ⟨hsh_k1, hsh_pqm1⟩ := spqrSend_shapes S (gClean r cls) stA2_0Clean.spqr (coins1Clean cls)
  have tsalt1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (key1Clean cls) id_salt1 :=
    termAt_opaque_b (id := id_salt1) (by decide +kernel)
      hpins.1 (hsh_k1.trans (congrArg litOf hpins.1)) hkey1_sm
  have tsalt1_opk : TermAt dagSize dagOp dagBytes S (gClean r cls) pts key1Opk id_salt1 :=
    key1Clean_eq cls ▸ tsalt1
  have tpqm1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (pqm1Clean cls) id_pqm1 :=
    termAt_opaque_b (id := id_pqm1) (by decide +kernel)
      hpins.2 (hsh_pqm1.trans (congrArg litOf hpins.2)) hpqm1_sm
  obtain ⟨hprk1, hck1, hc2_1, hmk1, hc3_1, hiv1, hcm1_1, hcm2_1, hhm1, hmac1⟩ := trow5_s1_ok
  obtain ⟨tm1_ck, tm1_mk, tm1_iv⟩ := termAt_trMsgKeys dag_nodes_ok
    sd.wmkInfo1 sd.wmkInfo2 sd.wmkInfo3
    hprk1 hck1 hc2_1 hmk1 hc3_1 hiv1 tsalt1 tseed1
  have tct1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).ciphertext id_ct1 :=
    termAt_symEncPt_b (id := id_ct1) (ptBs := WitnessParse.ev4InF) (by decide +kernel)
      tm1_ck tm1_iv hpt1_mem ((gClean_sigma_61 r cls 32).trans ev4In_eq)
  have twire1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).wire id_wire1 :=
    termAt_trWire_b (id := id_wire1) (by decide +kernel) tdhsAPk tct1 tpqm1
      ((gClean_addr r cls _).trans serializeAddresses_alice_bob_eq)
  have tmac1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts
      (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).mac id_m1m_mac :=
    termAt_computeMac dag_nodes_ok hcm1_1 hcm2_1 hhm1 hmac1 tm1_mk sd.ikASer sd.ikBSer twire1
  have twmac1 : TermAt dagSize dagOp dagBytes S (gClean r cls) pts (m1Clean cls) id_wmac1 :=
    termAt_concat_b (id := id_wmac1) (by decide +kernel) twire1 tmac1
  have hstA2_0_sm2 : SafeMemo2 dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize ({ participant := "alice", state := stA2_0Clean } :
        DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := { participant := "alice", state := stA2_0Clean })
      (cLast := { ratchetKey := dhPk spkB, chainKey := keys2Clean.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqrA0_sm ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact sd.ikASer.2.2.2
      · exact sd.ikBSer.2.2.2
      · exact tst_rk.2.2.2
      · exact tdhsA.2.2.2
      · exact tst_cks.2.2.2
      · exact tst_sid.2.2.2
    · intro c hc
      change c ∈ [{ ratchetKey := dhPk spkB, chainKey := keys2Clean.ck, index := 0, rIdx := 1 }] at hc
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨sd.spkBPk.2.2.2, tck0.2.2.2⟩
  have hstA2_1_sm2 : SafeMemo2 dagSize dagOp dagBytes S (gClean r cls) pts
      (DY.Comparse.serialize ({ participant := "alice", state := stA2_1Clean cls } :
        DY.PersistentLocalState.LocalState TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := { participant := "alice", state := stA2_1Clean cls })
      (cLast := { ratchetKey := dhPk spkB, chainKey := keys2Clean.ck, index := 0, rIdx := 1 })
      rfl rfl (Or.inl rfl) (Or.inr rfl) hspqrA1_sm ?_ ?_ rfl (by decide)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact sd.ikASer.2.2.2
      · exact sd.ikBSer.2.2.2
      · exact tst_rk.2.2.2
      · exact tdhsA.2.2.2
      · exact tnck1.2.2.2
      · exact tst_sid.2.2.2
    · intro c hc
      change c ∈ [{ ratchetKey := dhPk spkB, chainKey := keys2Clean.ck, index := 0, rIdx := 1 }] at hc
      rw [List.mem_singleton] at hc; subst hc
      exact ⟨sd.spkBPk.2.2.2, tck0.2.2.2⟩
  exact ⟨tekPk, tdhsAPk, tct, trk0, tck0, tpqr, tst_cks,
    tnck1, tseed1, tsalt1, tsalt1_opk, tpqm1, tct1, twire1, tmac1, twmac1,
    hstA2_0_sm2, hstA2_1_sm2⟩

/-! ## 5. Trial Row Expansion & `¬ MacTagForgeryOrCollision` -/

private theorem safeMemo_of_trialRowOk
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salt seed pIk mIk wire : Bytes} {pIk_id mIk_id wire_id : Nat} {row : TrialRow}
    (sd : SetupDag S g pts)
    (hok : TrialRowOk pIk_id mIk_id wire_id row)
    (hsalt : TermAt dagSize dagOp dagBytes S g pts salt row.salt)
    (hseed : TermAt dagSize dagOp dagBytes S g pts seed row.seed)
    (hpIk : TermAt dagSize dagOp dagBytes S g pts pIk pIk_id)
    (hmIk : TermAt dagSize dagOp dagBytes S g pts mIk mIk_id)
    (hwire : TermAt dagSize dagOp dagBytes S g pts wire wire_id) :
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).cipherKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).macKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).iv ∧
    SafeMemo dagSize dagOp dagBytes S g pts
      (computeMac (trMsgKeys salt seed).macKey pIk mIk wire) := by
  obtain ⟨hprk, hck, hc2, hmk, hc3, hiv, hcm1, hcm2, hhm, hmac⟩ := hok
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys dag_nodes_ok
    sd.wmkInfo1 sd.wmkInfo2 sd.wmkInfo3
    hprk hck hc2 hmk hc3 hiv hsalt hseed
  have tmac := termAt_computeMac dag_nodes_ok hcm1 hcm2 hhm hmac tmk hpIk hmIk hwire
  exact ⟨tck.2.2.2, tmk.2.2.2, tiv.2.2.2, tmac.2.2.2⟩

private theorem not_macTagForgeryOrCollision_singleton
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : Bytes → Prop}
    {honest : List Bytes} {msg : TRSignalMsg} {ctx : TrialCtx} {ownSalt : Bytes}
    (hown : ctx.ownSalts = [ownSalt]) (hmem : ownSalt ∈ honest) :
    ¬ MacTagForgeryOrCollision keepOpkI0 S g known honest msg [ctx] := by
  rintro (⟨c, hc, seed, _, k, hk, _, _, hneq⟩ |
          ⟨c, hc, seed, hseed, _, _, _, c₀, hc₀, seed₀, hseed₀, hne_seed, _⟩)
  · rw [List.mem_singleton] at hc; subst hc
    rw [hown, List.mem_singleton] at hk; subst hk
    exact hneq k hmem rfl
  · rw [List.mem_singleton] at hc hc₀; subst hc hc₀
    rw [hseed] at hseed₀; injection hseed₀ with h_eq; subst h_eq
    exact hne_seed rfl

/-! ## 6. Attacker Knowledge & Public Exports at `m = 2` and `m = 5` -/

private theorem attackerKnows_of_at_net {tr : ExecTrace} {idx : Nat} {t : Bytes}
    (hat : tr.at? idx = some (NetE t)) : t.AttackerKnows tr :=
  Trace.MessageSentAt_implies_AttackerKnows tr t idx
    ((Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1 tr t idx).mpr hat)

private theorem cleanPreKeyRep_2_ak (cls : Nat → Nat) :
    oOpk.ek.AttackerKnows (trClean2 cls) ∧
    oOpk.ct.AttackerKnows (trClean2 cls) ∧
    (m0Clean cls).AttackerKnows (trClean2 cls) := by
  have h5_2 : t5Opk ≤ trClean2 cls := CleanTrace.encTrGen_le _ _ _ _ _ _
  have hek : (trClean2 cls).at? 29 = some (NetE oOpk.ek) := by
    refine at?_mono h5_2 ?_
    dsimp only [t5Opk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hct : (trClean2 cls).at? 30 = some (NetE oOpk.ct) := by
    refine at?_mono h5_2 ?_
    dsimp only [t5Opk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4Opk_length]))
  have hmsg : (trClean2 cls).at? 41 = some (NetE (m0Clean cls)) := by
    dsimp only [trClean2, CleanTrace.encTrGen, m0Clean]
    have hm : rnd t5Opk.length 32 = pt0Clean := by rw [t5Opk_length]; rfl
    have hc : rnd (t5Opk.length + 1) (cls 0) = coins0Clean cls := by rw [t5Opk_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, t5Opk_length])
  exact ⟨attackerKnows_of_at_net hek, attackerKnows_of_at_net hct, attackerKnows_of_at_net hmsg⟩

private theorem cleanPreKeyRep_5_ak (cls : Nat → Nat) :
    o2Clean.ek.AttackerKnows (trClean5 cls) ∧
    o2Clean.ct.AttackerKnows (trClean5 cls) ∧
    (m1Clean cls).AttackerKnows (trClean5 cls) := by
  have h4_5 : trClean4 cls ≤ trClean5 cls := CleanTrace.encTrGen_le _ _ _ _ _ _
  have hao : Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt
      (trClean3 cls) ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (some (dhPk opkB)) = o2Clean :=
    CleanTrace.aliceOutOpk_trClean3_eq cls
  have hek : (trClean5 cls).at? 55 = some (NetE o2Clean.ek) := by
    refine at?_mono h4_5 ?_
    dsimp only [trClean4, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
    rw [hao]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, trClean3_length]))
  have hct : (trClean5 cls).at? 56 = some (NetE o2Clean.ct) := by
    refine at?_mono h4_5 ?_
    dsimp only [trClean4, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpk,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
    rw [hao]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, trClean3_length]))
  have hmsg : (trClean5 cls).at? 67 = some (NetE (m1Clean cls)) := by
    dsimp only [trClean5, CleanTrace.encTrGen, m1Clean]
    have hm : rnd (trClean4 cls).length 32 = pt1Clean := by rw [trClean4_length]; rfl
    have hc : rnd ((trClean4 cls).length + 1) (cls 1) = coins1Clean cls := by rw [trClean4_length]; rfl
    rw [hm, hc]
    exact at?_append_at _ _ (by simp only [append_len, trClean4_length])
  exact ⟨attackerKnows_of_at_net hek, attackerKnows_of_at_net hct, attackerKnows_of_at_net hmsg⟩

private theorem cleanPreKeyRep_2_eq (cls : Nat → Nat) :
    cleanPreKeyRep cls 2 = { ek := oOpk.ek, ct := oOpk.ct, msg := m0Clean cls } := rfl

private theorem cleanPreKeyRep_5_eq (cls : Nat → Nat) :
    cleanPreKeyRep cls 5 = { ek := o2Clean.ek, ct := o2Clean.ct, msg := m1Clean cls } := rfl

theorem cleanPreKeyRep_2_mem
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2)
      (visClean r cls 2) (trace0.take 2)) :
    cleanPreKeyRep cls 2 ∈
      preKeyRepresentationsOn keepOpkI0 r S (gClean r cls)
        (runTrace r (ssClean cls 2)) (ev 2).input := by
  have hf := r_facts_of_fit hfit
  have hm0 := m0Clean_eq_of_explains_2 hfit hex
  have sd := setupDag_of_fit (pts := [pt0Clean]) hfit hex.1
  have s1 := session1Dag_of_m0 sd hv.1 List.mem_cons_self hm0
  rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.1, cleanPreKeyRep_2_eq]
  obtain ⟨hak_ek, hak_ct, hak_msg⟩ := cleanPreKeyRep_2_ak cls
  refine ⟨hak_ek, hak_ct, hak_msg, ?_, p2, parse_ev2, ?_⟩
  · refine ⟨p2, parse_ev2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [s1.ekPk.gamma_eq]; decide +kernel
    · dsimp only; rw [s1.ct.gamma_eq]; decide +kernel
    · dsimp only; rw [s1.wmac0.gamma_eq]; decide +kernel
    · decide +kernel
    · rw [hf.spkId_eq]; decide +kernel
    · rw [hf.kpkId_eq]; decide +kernel
    · unfold pubBytes ProtocolSetup.ikASecBytes; rw [hf.sec0_eq]; decide +kernel
    · exact ⟨true, p2, parse_ev2, by rw [hf.opkId_eq, hf.withOpk_eq]; exact ⟨by decide +kernel, rfl⟩⟩
  · refine ⟨encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean,
      parse_encMsg _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s1.wire0.gamma_eq]; decide +kernel
    · rw [s1.mac0.gamma_eq]; decide +kernel
    · exact spqrHeaded_computeMac_bridge _ _ _ _
    · rw [s1.ct0.gamma_eq]; decide +kernel
    · have hdrk : (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).ratchetKey =
          dhPk dhsAOpk := rfl
      rw [hdrk, s1.dhsAPk.gamma_eq]; decide +kernel
    · have hpqr : (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean).pqRatchet =
          pqm0Clean cls := rfl
      rw [hpqr, s1.pqm0.gamma_eq]; decide +kernel
    · dsimp only [encSig, stA0Opk, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]; decide +kernel
    · dsimp only [encSig]; decide +kernel

theorem not_bobStartCollides_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2)
      (visClean r cls 2) (trace0.take 2)) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn keepOpkI0 r S (gClean r cls)
        (runTrace r (ssClean cls 2)) (visClean r cls 2)
        (honestSaltsOf r (ssClean cls 2)) p2 (cleanPreKeyRep cls 2) := by
  have hf := r_facts_of_fit hfit
  have hm0 := m0Clean_eq_of_explains_2 hfit hex
  set pts := plaintextTerms (visClean r cls 2) ++ ([] : List Bytes)
  have hpts_eq : pts = [pt0Clean] := by
    dsimp only [pts]; rw [List.append_nil,
      plaintextTerms_visClean_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq]
  have hpt0_mem : pt0Clean ∈ pts := by rw [hpts_eq]; exact List.mem_cons_self
  have sd := setupDag_of_fit (pts := pts) hfit hex.1
  have s1 := session1Dag_of_m0 sd hv.1 hpt0_mem hm0
  have hbt2 := bobTrials_2 cls (runTrace r (ssClean cls 2)) hf.alice_eq hf.bob_eq hf.withOpk_eq hf.opkId_eq
  rw [cleanPreKeyRep_2_eq] at hbt2 ⊢
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only [m0Clean] at hbt2 ⊢
  rw [parse_encMsg]
  dsimp only
  rintro (hmemo | hmac_coll)
  · refine not_memoCollisionOn_of_safeMemo2 dag_nodes_ok dag_no_collision dag_no_ai_0100 ?_ ?_ hmemo
    · intro t ht
      unfold prefixTerms principalTerms at ht
      rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.1,
          sendTerms_visClean_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq,
          storedStates_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq,
          storedSecrets_2 cls,
          plaintextTerms_visClean_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at ht
      rcases List.mem_append.mp ht with hp | hpt
      · rcases List.mem_append.mp hp with hs_st | hsec
        · rcases List.mem_append.mp hs_st with hsend | hst
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsend
            rcases hsend with rfl | rfl | rfl
            · exact safeMemo_toSafeMemo2 s1.ekPk.2.2.2
            · exact safeMemo_toSafeMemo2 s1.ct.2.2.2
            · exact safeMemo_toSafeMemo2 s1.wmac0.2.2.2
          · simp only [storedStatesClean2, List.map_cons, List.map_nil,
              List.mem_cons, List.not_mem_nil, or_false] at hst
            rcases hst with rfl | rfl
            · exact s1.stA0_sm2
            · exact s1.stA1_sm2
        · exact safeMemo_toSafeMemo2 (sd.secrets_sm t hsec)
      · rw [List.mem_singleton] at hpt; subst hpt
        exact safeMemo_toSafeMemo2
          (safeMemo_plaintext hpt0_mem (by rw [gClean_sigma_35, ev1In_eq]; decide +kernel))
    · intro t ht
      have ht_full : t ∈ [oOpk.ek, oOpk.ct, encMsg stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean] ++
          ([bobCtx2]).flatMap (trialTerms (honestSaltsOf r (ssClean cls 2))
            (encSig stA0Opk (coins0Clean cls) (key0Clean cls) pt0Clean)) := by
        rcases hbt2 with hbt | hbt <;> rw [hbt] at ht
        · simp only [List.flatMap_nil, List.append_nil] at ht
          exact List.mem_append_left _ ht
        · exact ht
      replace ht := ht_full
      simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons] at ht
      rcases ht with rfl | rfl | rfl | ht_trial
      · exact safeMemo_toSafeMemo2 s1.ekPk.2.2.2
      · exact safeMemo_toSafeMemo2 s1.ct.2.2.2
      · exact safeMemo_toSafeMemo2 s1.wmac0.2.2.2
      · refine safeMemo_toSafeMemo2 (safeMemo_trialTerms ?_ s1.ct0.2.2.2 ?_ t ht_trial)
        · intro u hu
          simp only [bobCtx2, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl
          · exact s1.rk0.2.2.2
          · exact s1.ck0.2.2.2
          · exact s1.pqr.2.2.2
          · exact s1.st_cks.2.2.2
          · exact s1.nck0.2.2.2
        · intro seed hseed salt hsalt
          change some (kdfCk stA0Opk.cks).2 = some seed at hseed
          injection hseed with h_eq; subst h_eq
          rw [honestSaltsOf_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at hsalt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
          rcases hsalt with rfl | rfl
          · exact safeMemo_of_trialRowOk sd trow2_zero_ok sd.zeroK s1.seed0 sd.ikASer sd.ikBSer s1.wire0
          · exact safeMemo_of_trialRowOk sd trow2_s0_ok s1.salt0_opk s1.seed0 sd.ikASer sd.ikBSer s1.wire0
  · rcases hbt2 with hbt | hbt <;> rw [hbt] at hmac_coll
    · rcases hmac_coll with ⟨_, ⟨⟩, _⟩ | ⟨_, ⟨⟩, _⟩
    · rw [honestSaltsOf_2 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at hmac_coll
      exact not_macTagForgeryOrCollision_singleton rfl (by simp) hmac_coll

theorem cleanPreKeyRep_5_mem
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 5)
      (visClean r cls 5) (trace0.take 5)) :
    cleanPreKeyRep cls 5 ∈
      preKeyRepresentationsOn keepOpkI0 r S (gClean r cls)
        (runTrace r (ssClean cls 5)) (ev 5).input := by
  have hf := r_facts_of_fit hfit
  obtain ⟨_, hm1⟩ := m0_and_m1_eq_of_explains_5 hfit hex
  have sd := setupDag_of_fit (pts := [pt1Clean]) hfit hex.1
  have s2 := session2Dag_of_m1 sd hv.2 List.mem_cons_self hm1
  rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.2.2.2, cleanPreKeyRep_5_eq]
  obtain ⟨hak_ek, hak_ct, hak_msg⟩ := cleanPreKeyRep_5_ak cls
  refine ⟨hak_ek, hak_ct, hak_msg, ?_, p5, parse_ev5, ?_⟩
  · refine ⟨p5, parse_ev5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [s2.ekPk.gamma_eq]; decide +kernel
    · dsimp only; rw [s2.ct.gamma_eq]; decide +kernel
    · dsimp only; rw [s2.wmac1.gamma_eq]; decide +kernel
    · decide +kernel
    · rw [hf.spkId_eq]; decide +kernel
    · rw [hf.kpkId_eq]; decide +kernel
    · unfold pubBytes ProtocolSetup.ikASecBytes; rw [hf.sec0_eq]; decide +kernel
    · exact ⟨true, p5, parse_ev5, by rw [hf.opkId_eq, hf.withOpk_eq]; exact ⟨by decide +kernel, rfl⟩⟩
  · refine ⟨encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean,
      parse_encMsg _ _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s2.wire1.gamma_eq]; decide +kernel
    · rw [s2.mac1.gamma_eq]; decide +kernel
    · exact spqrHeaded_computeMac_bridge _ _ _ _
    · rw [s2.ct1.gamma_eq]; decide +kernel
    · have hdrk : (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).ratchetKey =
          dhPk dhsA2Clean := rfl
      rw [hdrk, s2.dhsAPk.gamma_eq]; decide +kernel
    · have hpqr : (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean).pqRatchet =
          pqm1Clean cls := rfl
      rw [hpqr, s2.pqm1.gamma_eq]; decide +kernel
    · dsimp only [encSig, stA2_0Clean, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]; decide +kernel
    · dsimp only [encSig]; decide +kernel

theorem not_bobStartCollides_5
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hex : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 5)
      (visClean r cls 5) (trace0.take 5)) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn keepOpkI0 r S (gClean r cls)
        (runTrace r (ssClean cls 5)) (visClean r cls 5)
        (honestSaltsOf r (ssClean cls 5)) p5 (cleanPreKeyRep cls 5) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hm0, hm1⟩ := m0_and_m1_eq_of_explains_5 hfit hex
  set pts := plaintextTerms (visClean r cls 5) ++ ([] : List Bytes)
  have hpts_eq : pts = [pt0Clean, pt1Clean] := by
    dsimp only [pts]; rw [List.append_nil,
      plaintextTerms_visClean_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq]
  have hpt0_mem : pt0Clean ∈ pts := by rw [hpts_eq]; exact List.mem_cons_self
  have hpt1_mem : pt1Clean ∈ pts := by rw [hpts_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have sd := setupDag_of_fit (pts := pts) hfit hex.1
  have s1 := session1Dag_of_m0 sd hv.1 hpt0_mem hm0
  have sb1 := stB1Clean_sm2 sd s1
  have s2 := session2Dag_of_m1 sd hv.2 hpt1_mem hm1
  have hbt5 := bobTrials_5 cls (runTrace r (ssClean cls 5)) hf.alice_eq hf.bob_eq hf.withOpk_eq hf.opkId_eq
  rw [cleanPreKeyRep_5_eq] at hbt5 ⊢
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only [m1Clean] at hbt5 ⊢
  rw [parse_encMsg]
  dsimp only
  rintro (hmemo | hmac_coll)
  · refine not_memoCollisionOn_of_safeMemo2 dag_nodes_ok dag_no_collision dag_no_ai_0100 ?_ ?_ hmemo
    · intro t ht
      unfold prefixTerms principalTerms at ht
      rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.2.2.2,
          sendTerms_visClean_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq,
          storedStates_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq,
          storedSecrets_5 cls,
          plaintextTerms_visClean_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at ht
      rcases List.mem_append.mp ht with hp | hpt
      · rcases List.mem_append.mp hp with hs_st | hsec
        · rcases List.mem_append.mp hs_st with hsend | hst
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsend
            rcases hsend with rfl | rfl | rfl | rfl | rfl | rfl
            · exact safeMemo_toSafeMemo2 s1.ekPk.2.2.2
            · exact safeMemo_toSafeMemo2 s1.ct.2.2.2
            · exact safeMemo_toSafeMemo2 s1.wmac0.2.2.2
            · exact safeMemo_toSafeMemo2 s2.ekPk.2.2.2
            · exact safeMemo_toSafeMemo2 s2.ct.2.2.2
            · exact safeMemo_toSafeMemo2 s2.wmac1.2.2.2
          · simp only [storedStatesClean5, List.map_cons, List.map_nil,
              List.mem_cons, List.not_mem_nil, or_false] at hst
            rcases hst with rfl | rfl | rfl | rfl | rfl
            · exact s1.stA0_sm2
            · exact s1.stA1_sm2
            · exact sb1
            · exact s2.stA2_0_sm2
            · exact s2.stA2_1_sm2
        · exact safeMemo_toSafeMemo2 (sd.secrets_sm t hsec)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
        rcases hpt with rfl | rfl
        · exact safeMemo_toSafeMemo2
            (safeMemo_plaintext hpt0_mem (by rw [gClean_sigma_35, ev1In_eq]; decide +kernel))
        · exact safeMemo_toSafeMemo2
            (safeMemo_plaintext hpt1_mem (by rw [gClean_sigma_61, ev4In_eq]; decide +kernel))
    · intro t ht
      have ht_full : t ∈ [o2Clean.ek, o2Clean.ct, encMsg stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean] ++
          ([bobCtx5]).flatMap (trialTerms (honestSaltsOf r (ssClean cls 5))
            (encSig stA2_0Clean (coins1Clean cls) (key1Clean cls) pt1Clean)) := by
        rcases hbt5 with hbt | hbt <;> rw [hbt] at ht
        · simp only [List.flatMap_nil, List.append_nil] at ht
          exact List.mem_append_left _ ht
        · exact ht
      replace ht := ht_full
      simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons] at ht
      rcases ht with rfl | rfl | rfl | ht_trial
      · exact safeMemo_toSafeMemo2 s2.ekPk.2.2.2
      · exact safeMemo_toSafeMemo2 s2.ct.2.2.2
      · exact safeMemo_toSafeMemo2 s2.wmac1.2.2.2
      · refine safeMemo_toSafeMemo2 (safeMemo_trialTerms ?_ s2.ct1.2.2.2 ?_ t ht_trial)
        · intro u hu
          simp only [bobCtx5, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl
          · exact s2.rk0.2.2.2
          · exact s2.ck0.2.2.2
          · exact s2.pqr.2.2.2
          · exact s2.st_cks.2.2.2
          · exact s2.nck1.2.2.2
        · intro seed hseed salt hsalt
          change some (kdfCk stA2_0Clean.cks).2 = some seed at hseed
          injection hseed with h_eq; subst h_eq
          rw [honestSaltsOf_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at hsalt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
          rcases hsalt with rfl | rfl | rfl
          · exact safeMemo_of_trialRowOk sd trow5_zero_ok sd.zeroK s2.seed1 sd.ikASer sd.ikBSer s2.wire1
          · exact safeMemo_of_trialRowOk sd trow5_s0_ok s1.salt0_opk s2.seed1 sd.ikASer sd.ikBSer s2.wire1
          · exact safeMemo_of_trialRowOk sd trow5_s1_ok s2.salt1_opk s2.seed1 sd.ikASer sd.ikBSer s2.wire1
  · rcases hbt5 with hbt | hbt <;> rw [hbt] at hmac_coll
    · rcases hmac_coll with ⟨_, ⟨⟩, _⟩ | ⟨_, ⟨⟩, _⟩
    · rw [honestSaltsOf_5 cls hf.alice_eq hf.bob_eq hf.withOpk_eq] at hmac_coll
      exact not_macTagForgeryOrCollision_singleton rfl (by simp) hmac_coll

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
