/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2Part2DSetup

/-!
# Bob Session-Start & Whisper Trial `SafeMemo` and Reselect-Collision Refutation
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

noncomputable section Step2Part2D

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.Composed
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
open ByteSpecs (hmacWith sha256With)
open _root_.Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

/-! ### 5. `SafeMemo` for `bobTrials` on `c2`, `whisperTrials` on `c1`, and `not_reselectCollisionOn_c1` -/

theorem safeMemo_bobTrials_c2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {pts : List DY.Bytes} {cl1 cl2 : Nat} {tr : ExecTrace}
    (hp : FitsPins r)
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    let x : PreKeyRep := ⟨oClean.ek, oClean.ct, m2Clean cl1 cl2⟩
    let msg := msg2Clean cl1 cl2
    let salts := [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2]
    ∀ t ∈ (bobTrials r tr p_c2 x msg).flatMap (trialTerms salts msg),
      DagSafeMemo S g pts t := by
  dsimp only
  rw [bobTrials_eq_of_parties hp.ha hp.hb hp.hopk tr _ _ _ (by decide)]
  have hp_pre : p_c2.preKeyId = none := by decide
  have hikA : r0.ikAPubTerm = ikAPkClean := by
    unfold ProtocolSetup.ikAPubTerm
    simp [setupPublic, setupSent_r0_eq]
  have hikBPub : r0.ikBPubTerm = ikBPkClean := by
    unfold ProtocolSetup.ikBPubTerm
    simp [setupPublic, setupSent_r0_eq]
  have hikBSec : r0.ikBSecTerm = ikBSkClean := by
    unfold ProtocolSetup.ikBSecTerm setupSecret
    rw [setupRandoms_r0_eq]; rfl
  have hspkSec : r0.spkSecTerm = spkBSkClean := by
    unfold ProtocolSetup.spkSecTerm setupSecret
    rw [setupRandoms_r0_eq]; rfl
  have hpqskSec : r0.pqskSecTerm = pqskBClean := by
    unfold ProtocolSetup.pqskSecTerm setupSecret
    rw [setupRandoms_r0_eq]; rfl
  have hkeys :
      (let ss := (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqskBClean oClean.ct)).getD
        (DY.PQKem.kemRejKey pqskBClean oClean.ct)
       DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
         (DY.Libsignal.PQXDH.agree ikAPkClean spkBSkClean)
         (DY.Libsignal.PQXDH.agree oClean.ek ikBSkClean)
         (DY.Libsignal.PQXDH.agree oClean.ek spkBSkClean)
         none ss)) = oClean.keys := by
    have hba := Runs.bobAgreement_honest ikASkClean (randTerm 22 32) ikBSkClean spkBSkClean pqskBClean (randTerm 23 32)
    have hlen := setupTrace_r0_len
    unfold oClean CompTrace.aliceOut
    dsimp only
    rw [hlen]
    unfold DY.Libsignal.PQXDH.bobAgreement at hba
    exact Option.some.inj hba
  have hcc :
      (DY.Libsignal.TripleRatchet.createChain oClean.keys.rk (msg2Clean cl1 cl2).ratchetKey spkBSkClean).2 =
        stA0Clean.cks := by
    change (DY.Libsignal.TripleRatchet.createChain oClean.keys.rk
      (DY.DiffieHellman.dhPk stA0Clean.dhs) spkBSkClean).2 = stA0Clean.cks
    rw [Runs.createChain_comm]
    rfl
  obtain ⟨_, _, hrk0, hck0, hpqr0⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, hcks0, _, hcks1, _, hcks2, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hdhsPk : DagTermAt S g pts (msg2Clean cl1 cl2).ratchetKey 73 := by
    change DagTermAt S g pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
  have hseed2 : DagTermAt S g pts (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 112 :=
    termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1 (dagN_2 hw)
  obtain ⟨tck2, tmk2, tiv2⟩ := termAt_trMsgKeys
    (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
    dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_23 hw) hseed2
  have hct2 := termAt_symEncPt (id := 120) dag_nodes_ok (by decide)
    (congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel) : dagOp 120 = .symEncPt 115 119 38 ev2.input)
    tck2 tiv2 hw.hpt2_mem hw.hσ_pt2 (by decide +kernel)
  have hwire2 : DagTermAt S g pts (msg2Clean cl1 cl2).wire 121 :=
    termAt_trWire (id := 121) dag_nodes_ok (by decide)
      (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24) (by decide +kernel) :
        dagOp 121 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24 cleanAddrBs)
      hdhsPk hct2 (dagN_24 hw) (hw.haddr _)
  unfold bobTrials
  rw [hp_pre, hikA, hikBPub, hikBSec, hspkSec, hpqskSec]
  dsimp only [Option.map]
  split
  case isTrue =>
    intro t ht; simp at ht
  case isFalse =>
  rw [hkeys, hcc]
  have hcnt : (msg2Clean cl1 cl2).counter = 1 := rfl
  rw [hcnt]
  change ∀ t ∈ [({ peerIk := stA0Clean.myIk,
                    myIk := stA0Clean.peerIk,
                    extra := [oClean.keys.rk, oClean.keys.ck, oClean.keys.pqr,
                              stA0Clean.cks, (stA2Clean cl1 cl2).cks,
                              (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2],
                    ownSalts := _,
                    seed? := some (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 } : TrialCtx)].flatMap
      (trialTerms [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2] (msg2Clean cl1 cl2)),
    DagSafeMemo S g pts t
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  intro t ht
  refine safeMemo_trialTerms ?_ hct2.safeMemo ?_ t ht
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrk0.safeMemo
    · exact hck0.safeMemo
    · exact hpqr0.safeMemo
    · exact hcks0.safeMemo
    · exact hcks2.safeMemo
    · exact (termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0 (dagN_2 hw)).safeMemo
  · intro seed hseed salt hsalt
    injection hseed with hseed_eq; subst hseed_eq
    have hmyIk : DagTermAt S g pts stA0Clean.myIk 28 := dagN_28 hw
    have hpeerIk : DagTermAt S g pts stA0Clean.peerIk 31 := dagN_31 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
    rcases hsalt with rfl | rfl | rfl
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 141) (ck_id := 142) (c2_id := 143) (mk_id := 144) (c3_id := 145) (iv_id := 146)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_zeroKey hw) hseed2
      have tmac := termAt_computeMac
        (c1_id := 122) (c2_id := 123) (h_id := 147) (t_id := 148)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hmyIk hpeerIk hwire2
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 149) (ck_id := 150) (c2_id := 151) (mk_id := 152) (c3_id := 153) (iv_id := 154)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_21 hw) hseed2
      have tmac := termAt_computeMac
        (c1_id := 122) (c2_id := 123) (h_id := 155) (t_id := 156)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hmyIk hpeerIk hwire2
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
    · have tmac := termAt_computeMac
        (c1_id := 122) (c2_id := 123) (h_id := 124) (t_id := 125)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk2 hmyIk hpeerIk hwire2
      exact ⟨tck2.safeMemo, tmk2.safeMemo, tiv2.safeMemo, tmac.safeMemo⟩

theorem not_reselectCollisionOn_c1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {pts : List DY.Bytes} {tr : ExecTrace} {vis : List VisEntry}
    {salts : List DY.Bytes} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2))
    (havail : ∀ st ∈ availableStates r0 tr,
      st = stA0Clean ∨ st = stA1Clean cl1 ∨ st = stA2Clean cl1 cl2 ∨
      st = stB3Clean cl1 cl2 ∨ st = stB4Clean cl1 cl2)
    (hsk : ∀ i, i < tr.length → ∀ s pk n seed rIdx srcIdx,
      tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2) :
    ¬ ReselectCollisionOn compI0 r S g tr vis salts (m1Clean cl1) := by
  rintro ⟨msg, hparse, rk, hrk_mem, hγ_eq, hrk_ne, _⟩
  rw [parse_m1Clean] at hparse
  injection hparse with hmsg; subst hmsg
  rw [storedRatchetKeys_eq_of_parties hp.ha hp.hb hp.hopk] at hrk_mem
  unfold storedRatchetKeys at hrk_mem
  rw [List.mem_append] at hrk_mem
  have hmsg_rk : (msg1Clean cl1).ratchetKey = DY.DiffieHellman.dhPk stA0Clean.dhs := rfl
  have hγ_spk : gamma compI0 S g oClean.spk = dagBytes 33 := (dagN_33 hw).2.1
  have hγ_dhs : gamma compI0 S g (DY.DiffieHellman.dhPk stA0Clean.dhs) = dagBytes 73 := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]
    exact (dagN_73 hw).2.1
  rcases hrk_mem with hrk_av | hrk_sk
  · rw [List.mem_flatMap] at hrk_av
    obtain ⟨st, hst_mem, hrk_recv⟩ := hrk_av
    rcases havail st hst_mem with rfl | rfl | rfl | rfl | rfl
    · simp only [stA0Clean, localAliceStartState, List.map_cons, List.map_nil, List.mem_singleton] at hrk_recv
      subst hrk_recv
      rw [hmsg_rk, hγ_spk, hγ_dhs] at hγ_eq
      exact absurd hγ_eq (by decide +kernel)
    · simp only [stA1Clean, localEncState, stA0Clean, localAliceStartState, List.map_cons, List.map_nil, List.mem_singleton] at hrk_recv
      subst hrk_recv
      rw [hmsg_rk, hγ_spk, hγ_dhs] at hγ_eq
      exact absurd hγ_eq (by decide +kernel)
    · simp only [stA2Clean, stA1Clean, localEncState, stA0Clean, localAliceStartState, List.map_cons, List.map_nil, List.mem_singleton] at hrk_recv
      subst hrk_recv
      rw [hmsg_rk, hγ_spk, hγ_dhs] at hγ_eq
      exact absurd hγ_eq (by decide +kernel)
    · simp only [stB3Clean, recvChainB3Clean, List.map_cons, List.map_nil, List.mem_singleton] at hrk_recv
      exact hrk_ne (hrk_recv.trans hmsg_rk.symm)
    · simp only [stB4Clean, stB3Clean, recvChainB3Clean, List.map_cons, List.map_nil, List.mem_singleton] at hrk_recv
      exact hrk_ne (hrk_recv.trans hmsg_rk.symm)
  · rw [List.mem_filterMap] at hrk_sk
    obtain ⟨i, hi_mem, hi_eq⟩ := hrk_sk
    have hi_lt : i < tr.length := List.mem_range.mp hi_mem
    cases hev : tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i with
    | none => rw [hev] at hi_eq; cases hi_eq
    | some ev =>
      rw [hev] at hi_eq
      cases ev with
      | SkippedKeyStored s pk n seed rIdx srcIdx =>
        dsimp only at hi_eq
        split at hi_eq
        · injection hi_eq with hrk_pk
          have ⟨hpk, _, _⟩ := hsk i hi_lt s pk n seed rIdx srcIdx hev
          exact hrk_ne (hrk_pk.symm.trans (hpk.trans hmsg_rk.symm))
        · cases hi_eq
      | _ => cases hi_eq

theorem safeMemo_whisperTrials_c1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {pts : List DY.Bytes} {tr : ExecTrace} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2))
    (havail : ∀ st ∈ availableStates r0 tr,
      st = stA0Clean ∨ st = stA1Clean cl1 ∨ st = stA2Clean cl1 cl2 ∨
      st = stB3Clean cl1 cl2 ∨ st = stB4Clean cl1 cl2)
    (hsk : ∀ i, i < tr.length → ∀ s pk n seed rIdx srcIdx,
      tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2) :
    let msg := msg1Clean cl1
    let salts := [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2]
    ∀ t ∈ (whisperTrials compI0 r S g tr msg).flatMap (trialTerms salts msg),
      DagSafeMemo S g pts t := by
  dsimp only
  rw [whisperTrials_eq_of_parties hp.ha hp.hb hp.hopk]
  obtain ⟨hrkA0, hdhsA, hcks0, _, _, _, hcks2, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hdhsPk : DagTermAt S g pts (msg1Clean cl1).ratchetKey 73 := by
    change DagTermAt S g pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
  have hseed1 : DagTermAt S g pts (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 97 :=
    termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0 (dagN_2 hw)
  obtain ⟨tck1, tmk1, tiv1⟩ := termAt_trMsgKeys
    (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
    dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) hseed1
  have hct1 := termAt_symEncPt (id := 105) dag_nodes_ok (by decide)
    (congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel) : dagOp 105 = .symEncPt 100 104 31 ev1.input)
    tck1 tiv1 hw.hpt1_mem hw.hσ_pt1 (by decide +kernel)
  have hwire1 : DagTermAt S g pts (msg1Clean cl1).wire 106 :=
    termAt_trWire (id := 106) dag_nodes_ok (by decide)
      (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22) (by decide +kernel) :
        dagOp 106 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22 cleanAddrBs)
      hdhsPk hct1 (dagN_22 hw) (hw.haddr _)
  have hmyIk : DagTermAt S g pts stA0Clean.myIk 28 := dagN_28 hw
  have hpeerIk : DagTermAt S g pts stA0Clean.peerIk 31 := dagN_31 hw
  have hγ_spk : gamma compI0 S g oClean.spk = dagBytes 33 := (dagN_33 hw).2.1
  have hγ_dhs : gamma compI0 S g (msg1Clean cl1).ratchetKey = dagBytes 73 := hdhsPk.2.1
  have hspk_ne_dhs_γ : gamma compI0 S g oClean.spk ≠ gamma compI0 S g (msg1Clean cl1).ratchetKey := by
    rw [hγ_spk, hγ_dhs]; decide +kernel
  have hspk_ne_dhs : oClean.spk ≠ (msg1Clean cl1).ratchetKey := fun h => hspk_ne_dhs_γ (congrArg _ h)
  -- Alice self-ratchet DagTermAt (134..140)
  have hdh_self : DagTermAt S g pts (DY.Libsignal.PQXDH.agree (msg1Clean cl1).ratchetKey stA0Clean.dhs) 134 := by
    change DagTermAt S g pts (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk stA0Clean.dhs) stA0Clean.dhs) 134
    rw [agree_dhPk]
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]
    exact dagN_134_symm hw
  have hself_prk := termAt_kdf (id := 135) dag_nodes_ok (by decide) rfl hrkA0 hdh_self
  have hself_b1 := termAt_kdf (id := 136) dag_nodes_ok (by decide) rfl hself_prk (dagN_13 hw)
  have hself_c2 := termAt_concat (id := 137) dag_nodes_ok (by decide) rfl hself_b1 (dagN_14 hw)
  have hself_ckr : DagTermAt S g pts
      (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2 138 :=
    termAt_kdf (id := 138) dag_nodes_ok (by decide) rfl hself_prk hself_c2
  have hself_seed : DagTermAt S g pts
      (DY.Libsignal.TripleRatchet.kdfCk
        (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2).2 139 :=
    termAt_kdf (id := 139) dag_nodes_ok (by decide) rfl hself_ckr (dagN_2 hw)
  have hself_ck1 : DagTermAt S g pts
      (DY.Libsignal.TripleRatchet.kdfCk
        (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2).1 140 :=
    termAt_kdf (id := 140) dag_nodes_ok (by decide) rfl hself_ckr (dagN_3 hw)
  have hlow : DY.X25519.x25519LowOrder (msg1Clean cl1).ratchetKey = false := by
    let sk := stA0Clean.dhs
    change DY.X25519.x25519LowOrder (DY.DiffieHellman.dhPk sk) = false
    have hv_var : (DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
        ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    have hv_lit : (DY.DiffieHellman.dhPk sk).view? DY.Literal.Literal.SubF = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
        ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    have hnorm : DY.X25519.normalizeX25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := by
      unfold DY.X25519.normalizeX25519Key; rw [hv_var]
    have hlit : DY.Literal.bytesToLiteral (DY.DiffieHellman.dhPk sk) = none := by
      dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
      rw [hv_lit]
    unfold DY.X25519.x25519LowOrder
    rw [hnorm, hlit]
  have hver : (msg1Clean cl1).version = DY.Libsignal.TripleRatchet.messageVersion := rfl
  have hcnt0 : (msg1Clean cl1).counter = 0 := rfl
  unfold whisperTrials
  simp only [hver, ↓reduceIte]
  intro t ht
  rw [List.mem_flatMap] at ht
  obtain ⟨ctx, hctx, ht⟩ := ht
  rw [List.mem_flatMap] at hctx
  obtain ⟨st, hst_mem, hctx_st⟩ := hctx
  rw [List.mem_append] at hctx_st
  -- Helper for Alice's half-step trial
  have halice_body : ∀ seed, some (DY.Libsignal.TripleRatchet.kdfCk
        (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2).2 = some seed →
      ∀ salt ∈ [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2],
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.computeMac
          (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey stA0Clean.peerIk stA0Clean.myIk (msg1Clean cl1).wire) := by
    intro seed hs salt hsalt
    injection hs with hs_eq; subst hs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
    rcases hsalt with rfl | rfl | rfl
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 159) (ck_id := 160) (c2_id := 161) (mk_id := 162) (c3_id := 163) (iv_id := 164)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_zeroKey hw) hself_seed
      have tmac := termAt_computeMac
        (c1_id := 157) (c2_id := 158) (h_id := 165) (t_id := 166)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hpeerIk hmyIk hwire1
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 167) (ck_id := 168) (c2_id := 169) (mk_id := 170) (c3_id := 171) (iv_id := 172)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_21 hw) hself_seed
      have tmac := termAt_computeMac
        (c1_id := 157) (c2_id := 158) (h_id := 173) (t_id := 174)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hpeerIk hmyIk hwire1
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 175) (ck_id := 176) (c2_id := 177) (mk_id := 178) (c3_id := 179) (iv_id := 180)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_23 hw) hself_seed
      have tmac := termAt_computeMac
        (c1_id := 157) (c2_id := 158) (h_id := 181) (t_id := 182)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hpeerIk hmyIk hwire1
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
  -- Helper for Bob's SkippedKeyStored trial
  have hbob_body : ∀ seed, some (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 = some seed →
      ∀ salt ∈ [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2],
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv ∧
        DagSafeMemo S g pts (DY.Libsignal.TripleRatchet.computeMac
          (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey stA0Clean.myIk stA0Clean.peerIk (msg1Clean cl1).wire) := by
    intro seed hs salt hsalt
    injection hs with hs_eq; subst hs_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
    rcases hsalt with rfl | rfl | rfl
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 183) (ck_id := 184) (c2_id := 185) (mk_id := 186) (c3_id := 187) (iv_id := 188)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_zeroKey hw) hseed1
      have tmac := termAt_computeMac
        (c1_id := 107) (c2_id := 108) (h_id := 189) (t_id := 190)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hmyIk hpeerIk hwire1
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
    · have tmac := termAt_computeMac
        (c1_id := 107) (c2_id := 108) (h_id := 109) (t_id := 110)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk1 hmyIk hpeerIk hwire1
      exact ⟨tck1.safeMemo, tmk1.safeMemo, tiv1.safeMemo, tmac.safeMemo⟩
    · obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
        (prk_id := 191) (ck_id := 192) (c2_id := 193) (mk_id := 194) (c3_id := 195) (iv_id := 196)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_23 hw) hseed1
      have tmac := termAt_computeMac
        (c1_id := 107) (c2_id := 108) (h_id := 197) (t_id := 198)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk hmyIk hpeerIk hwire1
      exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩
  -- Alice DRState coincides on stA0Clean, stA1Clean, stA2Clean for recv/rk/dhs/peerIk/myIk
  have hfindA0 : DY.Libsignal.TripleRatchet.findRecvChain stA0Clean.recv (msg1Clean cl1).ratchetKey = none := by
    simp [stA0Clean, localAliceStartState, DY.Libsignal.TripleRatchet.findRecvChain, hspk_ne_dhs]
  have hfiltA0 : (stA0Clean.toDRState.recv.filter
      fun c => decide (gamma compI0 S g c.ratchetKey = gamma compI0 S g (msg1Clean cl1).ratchetKey)) = [] := by
    simp [stA0Clean, localAliceStartState, hspk_ne_dhs_γ]
  have hhalfA0 : DY.Libsignal.TripleRatchet.recvHalfStep stA0Clean.toDRState (msg1Clean cl1).ratchetKey =
      some ((DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).1,
            { ratchetKey := (msg1Clean cl1).ratchetKey,
              chainKey := (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2,
              index := 0, rIdx := stA0Clean.rIdx + 2 }) := by
    unfold DY.Libsignal.TripleRatchet.recvHalfStep
    rw [hlow]; rfl
  rcases hctx_st with hchain | hsk_mem
  · have halice_extra : ∀ u,
        (u ∈ [(DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).1,
              (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2,
              (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2).1] ∨
         u ∈ [(DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2,
              (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2).1]) →
        DagSafeMemo S g pts u := by
      rintro u (hu | hu)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl
        · exact hself_b1.safeMemo
        · exact hself_ckr.safeMemo
        · exact hself_ck1.safeMemo
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hself_ckr.safeMemo
        · exact hself_ck1.safeMemo
    rcases havail st hst_mem with hst_eq | hst_eq | hst_eq | hst_eq | hst_eq
    · subst hst_eq
      rw [hfiltA0, hfindA0, hhalfA0] at hchain
      simp only [List.nil_append, List.map_cons, List.map_nil, List.mem_singleton, hcnt0,
        DY.Libsignal.TripleRatchet.consumeMessageKey, show ¬ ((0 : UInt32) < 0) by decide,
        show ¬ ((0 : UInt32) = DY.Libsignal.TripleRatchet.u32Max) by decide, ↓reduceIte,
        DY.Libsignal.TripleRatchet.skippedSeeds] at hchain
      subst hchain
      refine safeMemo_trialTerms ?_ hct1.safeMemo halice_body t ht
      intro u hu
      exact halice_extra u (by first | exact Or.inl hu | exact Or.inr hu)
    · subst hst_eq
      have hfilt1 : ((stA1Clean cl1).toDRState.recv.filter
          fun c => decide (gamma compI0 S g c.ratchetKey = gamma compI0 S g (msg1Clean cl1).ratchetKey)) = [] := hfiltA0
      have hfind1 : DY.Libsignal.TripleRatchet.findRecvChain (stA1Clean cl1).recv (msg1Clean cl1).ratchetKey = none := hfindA0
      have hhalf1 : DY.Libsignal.TripleRatchet.recvHalfStep (stA1Clean cl1).toDRState (msg1Clean cl1).ratchetKey =
          some ((DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).1,
                { ratchetKey := (msg1Clean cl1).ratchetKey,
                  chainKey := (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2,
                  index := 0, rIdx := stA0Clean.rIdx + 2 }) := hhalfA0
      rw [hfilt1, hfind1, hhalf1] at hchain
      simp only [List.nil_append, List.map_cons, List.map_nil, List.mem_singleton, hcnt0,
        DY.Libsignal.TripleRatchet.consumeMessageKey, show ¬ ((0 : UInt32) < 0) by decide,
        show ¬ ((0 : UInt32) = DY.Libsignal.TripleRatchet.u32Max) by decide, ↓reduceIte,
        DY.Libsignal.TripleRatchet.skippedSeeds] at hchain
      subst hchain
      refine safeMemo_trialTerms ?_ hct1.safeMemo halice_body t ht
      intro u hu
      exact halice_extra u (by first | exact Or.inl hu | exact Or.inr hu)
    · subst hst_eq
      have hfilt2 : ((stA2Clean cl1 cl2).toDRState.recv.filter
          fun c => decide (gamma compI0 S g c.ratchetKey = gamma compI0 S g (msg1Clean cl1).ratchetKey)) = [] := hfiltA0
      have hfind2 : DY.Libsignal.TripleRatchet.findRecvChain (stA2Clean cl1 cl2).recv (msg1Clean cl1).ratchetKey = none := hfindA0
      have hhalf2 : DY.Libsignal.TripleRatchet.recvHalfStep (stA2Clean cl1 cl2).toDRState (msg1Clean cl1).ratchetKey =
          some ((DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).1,
                { ratchetKey := (msg1Clean cl1).ratchetKey,
                  chainKey := (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (msg1Clean cl1).ratchetKey stA0Clean.dhs).2,
                  index := 0, rIdx := stA0Clean.rIdx + 2 }) := hhalfA0
      rw [hfilt2, hfind2, hhalf2] at hchain
      simp only [List.nil_append, List.map_cons, List.map_nil, List.mem_singleton, hcnt0,
        DY.Libsignal.TripleRatchet.consumeMessageKey, show ¬ ((0 : UInt32) < 0) by decide,
        show ¬ ((0 : UInt32) = DY.Libsignal.TripleRatchet.u32Max) by decide, ↓reduceIte,
        DY.Libsignal.TripleRatchet.skippedSeeds] at hchain
      subst hchain
      refine safeMemo_trialTerms ?_ hct1.safeMemo halice_body t ht
      intro u hu
      exact halice_extra u (by first | exact Or.inl hu | exact Or.inr hu)
    · subst hst_eq
      have hfindB : DY.Libsignal.TripleRatchet.findRecvChain (stB3Clean cl1 cl2).recv (msg1Clean cl1).ratchetKey =
          some (recvChainB3Clean cl1 cl2) := by
        simp [stB3Clean, recvChainB3Clean, DY.Libsignal.TripleRatchet.findRecvChain]
        rfl
      rw [hfindB] at hchain
      simp only [stB3Clean, recvChainB3Clean, List.filter_cons, List.filter_nil, List.append_nil] at hchain
      split at hchain
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, hcnt0,
          DY.Libsignal.TripleRatchet.consumeMessageKey, show (0 : UInt32) < 2 by decide, ↓reduceIte] at hchain
        subst hchain
        refine safeMemo_trialTerms ?_ hct1.safeMemo (fun _ (h : none = some _) _ _ => nomatch h) t ht
        intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hcks2.safeMemo
      · simp at hchain
    · subst hst_eq
      have hfindB : DY.Libsignal.TripleRatchet.findRecvChain (stB4Clean cl1 cl2).recv (msg1Clean cl1).ratchetKey =
          some (recvChainB3Clean cl1 cl2) := by
        simp [stB4Clean, stB3Clean, recvChainB3Clean, DY.Libsignal.TripleRatchet.findRecvChain]
        rfl
      rw [hfindB] at hchain
      simp only [stB4Clean, stB3Clean, recvChainB3Clean, List.filter_cons, List.filter_nil, List.append_nil] at hchain
      split at hchain
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, hcnt0,
          DY.Libsignal.TripleRatchet.consumeMessageKey, show (0 : UInt32) < 2 by decide, ↓reduceIte] at hchain
        subst hchain
        refine safeMemo_trialTerms ?_ hct1.safeMemo (fun _ (h : none = some _) _ _ => nomatch h) t ht
        intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hcks2.safeMemo
      · simp at hchain
  · rw [List.mem_filterMap] at hsk_mem
    obtain ⟨i, hi_mem, hi_eq⟩ := hsk_mem
    have hi_lt : i < tr.length := List.mem_range.mp hi_mem
    cases hev : tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i with
    | none => rw [hev] at hi_eq; cases hi_eq
    | some ev =>
      rw [hev] at hi_eq
      cases ev with
      | SkippedKeyStored s pk n seed rIdx srcIdx =>
        have ⟨hpk, hn, hseed_eq⟩ := hsk i hi_lt s pk n seed rIdx srcIdx hev
        subst hpk; subst hn; subst hseed_eq
        dsimp only at hi_eq
        split at hi_eq
        · rename_i hcond
          injection hi_eq with hctx_eq; subst hctx_eq
          rcases havail st hst_mem with rfl | rfl | rfl | rfl | rfl
          · exfalso
            have hc1 : (DY.Libsignal.TripleRatchet.findRecvChain stA0Clean.recv (msg1Clean cl1).ratchetKey).isSome = true := hcond.1
            rw [hfindA0] at hc1; cases hc1
          · exfalso
            have hc1 : (DY.Libsignal.TripleRatchet.findRecvChain stA0Clean.recv (msg1Clean cl1).ratchetKey).isSome = true := hcond.1
            rw [hfindA0] at hc1; cases hc1
          · exfalso
            have hc1 : (DY.Libsignal.TripleRatchet.findRecvChain stA0Clean.recv (msg1Clean cl1).ratchetKey).isSome = true := hcond.1
            rw [hfindA0] at hc1; cases hc1
          · exact safeMemo_trialTerms (fun _ h => False.elim (List.not_mem_nil h)) hct1.safeMemo hbob_body t ht
          · exact safeMemo_trialTerms (fun _ h => False.elim (List.not_mem_nil h)) hct1.safeMemo hbob_body t ht
        · cases hi_eq
      | _ => cases hi_eq

theorem wireMacChainOk_ev3_fast :
    wireMacChainOk' (dagBytes 117) (dagBytes 114) c2Fast = true := by
  decide +kernel

theorem wireMacChainOk_ev3 :
    wireMacChainOk' (dagBytes 117) (dagBytes 114) ev3.input = true := by
  rw [ev3_input_eq_fast]; exact wireMacChainOk_ev3_fast

theorem c2_kdf_pins :
    (dagBytes 114).take 4 ≠ compTag4 ∧
    msg32OfTake8 ((dagBytes 114).take 8) = some (dagBytes 112) ∧
    keyOfTake8 ((dagBytes 114).take 8) = some (dagBytes 23) ∧
    wsPrk = dagBytes 99 ∧
    wsSeed1Bytes = dagBytes 97 ∧
    keyOfTake8 (wsPrk.take 8) = some (dagBytes 21) := by
  decide +kernel

theorem c2_mac_forces_prk {S : OpaqueSymbolSemantics} {g : Ghost}
    {pqSalt seed peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
        peerIk myIk wire) = msgMac8' p_c2) :
    gamma compI0 S g (msgPrk pqSalt seed) = dagBytes 114 := by
  set mKeys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
  obtain ⟨hMacTag, hMacKey, hKeyTag, hKeyPrk⟩ :=
    macChainOk'_spec (macChainOk'_of_wire wireMacChainOk_ev3 parsePreKeyWire_ev3)
  have htag1 : (gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac mKeys.macKey peerIk myIk wire)).take 4 ≠ compTag4 := by
    rw [hmac]; exact hMacTag
  have hk1 := keyOfTake8_computeMac S g mKeys.macKey peerIk myIk wire
    (gamma_macKey_length S g pqSalt seed) htag1
  rw [hmac, hMacKey] at hk1
  have hmKeyEq : gamma compI0 S g mKeys.macKey = dagBytes 117 := (Option.some.inj hk1).symm
  have htag2 : (gamma compI0 S g mKeys.macKey).take 4 ≠ compTag4 := by
    rw [hmKeyEq]; exact hKeyTag
  have hk2 := keyOfTake8_macKey S g pqSalt seed htag2
  rw [hmKeyEq, hKeyPrk] at hk2
  exact (Option.some.inj hk2).symm

theorem c2_mac_forces_salt {S : OpaqueSymbolSemantics} {g : Ghost}
    {pqSalt seed peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
        peerIk myIk wire) = msgMac8' p_c2)
    (hSaltLen : (gamma compI0 S g pqSalt).length = 32) :
    gamma compI0 S g pqSalt = dagBytes 23 := by
  have hPrkEq := c2_mac_forces_prk hmac
  have hPrkTag : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac pqSalt seed)).take 4 ≠ compTag4 := by
    change (gamma compI0 S g (msgPrk pqSalt seed)).take 4 ≠ compTag4
    rw [hPrkEq]; exact c2_kdf_pins.1
  have hk := gamma_hmac_key_of_take8 S g pqSalt seed hSaltLen hPrkTag
  change keyOfTake8 ((gamma compI0 S g (msgPrk pqSalt seed)).take 8) = _ at hk
  rw [hPrkEq, c2_kdf_pins.2.2.1] at hk
  exact (Option.some.inj hk).symm

theorem c1_mac_forces_prk {S : OpaqueSymbolSemantics} {g : Ghost}
    {pqSalt seed peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
        peerIk myIk wire) = msgMac8' p_c1) :
    gamma compI0 S g (msgPrk pqSalt seed) = wsPrk := by
  set mKeys := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed
  obtain ⟨hMacTag, hMacKey, hKeyTag, hKeyPrk⟩ :=
    macChainOk'_spec (macChainOk'_of_wire wireMacChainOk_ev4 parsePreKeyWire_ev4)
  have htag1 : (gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac mKeys.macKey peerIk myIk wire)).take 4 ≠ compTag4 := by
    rw [hmac]; exact hMacTag
  have hk1 := keyOfTake8_computeMac S g mKeys.macKey peerIk myIk wire
    (gamma_macKey_length S g pqSalt seed) htag1
  rw [hmac, hMacKey] at hk1
  have hmKeyEq : gamma compI0 S g mKeys.macKey = wsMacKey := (Option.some.inj hk1).symm
  have htag2 : (gamma compI0 S g mKeys.macKey).take 4 ≠ compTag4 := by
    rw [hmKeyEq]; exact hKeyTag
  have hk2 := keyOfTake8_macKey S g pqSalt seed htag2
  rw [hmKeyEq, hKeyPrk] at hk2
  exact (Option.some.inj hk2).symm

theorem c1_mac_forces_seed {S : OpaqueSymbolSemantics} {g : Ghost}
    {pqSalt seed peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
        peerIk myIk wire) = msgMac8' p_c1)
    (hSeedLen : (gamma compI0 S g seed).length = 32) :
    gamma compI0 S g seed = wsSeed1Bytes := by
  have hPrkEq := c1_mac_forces_prk hmac
  have hPrkTag : (hmacWith F0 (gamma compI0 S g pqSalt) (gamma compI0 S g seed)).take 4 ≠ compTag4 := by
    rw [← gamma_hmac_compI0]; change (gamma compI0 S g (msgPrk pqSalt seed)).take 4 ≠ compTag4
    rw [hPrkEq]; exact c1_kdf_pins.1
  have hmSeed := msg32OfTake8_hmacWith_any (gamma compI0 S g pqSalt) (gamma compI0 S g seed) hSeedLen hPrkTag
  rw [← gamma_hmac_compI0] at hmSeed
  change msg32OfTake8 ((gamma compI0 S g (msgPrk pqSalt seed)).take 8) = _ at hmSeed
  rw [hPrkEq, c1_kdf_pins.2.1] at hmSeed
  exact (Option.some.inj hmSeed).symm

theorem c1_mac_forces_salt {S : OpaqueSymbolSemantics} {g : Ghost}
    {pqSalt seed peerIk myIk wire : DY.Bytes}
    (hmac : gamma compI0 S g
      (DY.Libsignal.TripleRatchet.computeMac
        (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey
        peerIk myIk wire) = msgMac8' p_c1)
    (hSaltLen : (gamma compI0 S g pqSalt).length = 32) :
    gamma compI0 S g pqSalt = dagBytes 21 := by
  have hPrkEq := c1_mac_forces_prk hmac
  have hPrkTag : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac pqSalt seed)).take 4 ≠ compTag4 := by
    change (gamma compI0 S g (msgPrk pqSalt seed)).take 4 ≠ compTag4
    rw [hPrkEq]; exact c1_kdf_pins.1
  have hk := gamma_hmac_key_of_take8 S g pqSalt seed hSaltLen hPrkTag
  change keyOfTake8 ((gamma compI0 S g (msgPrk pqSalt seed)).take 8) = _ at hk
  rw [hPrkEq, c2_kdf_pins.2.2.2.2.2] at hk
  exact (Option.some.inj hk).symm

theorem gamma_spqrChainKey_length {S : OpaqueSymbolSemantics} {g : Ghost}
    (k p idx : DY.Bytes) :
    (gamma compI0 S g (DY.Spqr.spqrChainKey k p idx)).length = 32 := by
  unfold gamma gamma' DY.Spqr.spqrChainKey
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
    (concretizeAll compI0 S g)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey,
    DY.Libsignal.Composed.Refinement.spqrKeyNode,
    DY.Libsignal.Composed.Refinement.opaqueNode,
    DY.Libsignal.Composed.Refinement.spqrKeyBytes]
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

theorem gamma_spqrSend_key_length {S : OpaqueSymbolSemantics} {g : Ghost}
    (st coins : DY.Bytes) :
    (gamma compI0 S g (DY.Spqr.spqrSend st coins).2.1).length = 32 := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · exact gamma_spqrChainKey_length _ _ _
  · unfold gamma gamma'
    rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S)
      (concretizeAll compI0 S g)]
    dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey,
      DY.Libsignal.Composed.Refinement.spqrKeyNode,
      DY.Libsignal.Composed.Refinement.opaqueNode,
      DY.Libsignal.Composed.Refinement.spqrKeyBytes]
    rw [List.length_take, List.length_append, List.length_replicate]
    omega

theorem gamma_spqrInit_congr {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {k₁ p₁ k₂ p₂ : DY.Bytes}
    (hk : gamma compI0 S g₁ k₁ = gamma compI0 S g₂ k₂)
    (hp : gamma compI0 S g₁ p₁ = gamma compI0 S g₂ p₂) :
    gamma compI0 S g₁ (DY.Spqr.spqrInit k₁ p₁) =
      gamma compI0 S g₂ (DY.Spqr.spqrInit k₂ p₂) := by
  unfold gamma gamma' at hk hp
  unfold gamma gamma' DY.Spqr.spqrInit
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrInit S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrInit S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrInit,
    DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hk, hp]

theorem gamma_spqrSend_fst_congr {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {st₁ c₁ st₂ c₂ : DY.Bytes}
    (hst : gamma compI0 S g₁ st₁ = gamma compI0 S g₂ st₂)
    (hc : gamma compI0 S g₁ c₁ = gamma compI0 S g₂ c₂) :
    gamma compI0 S g₁ (DY.Spqr.spqrSend st₁ c₁).1 =
      gamma compI0 S g₂ (DY.Spqr.spqrSend st₂ c₂).1 := by
  unfold gamma gamma' at hst hc
  unfold gamma gamma' DY.Spqr.spqrSend
  dsimp only
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendState S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendState S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendState,
    DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hst, hc]

theorem gamma_spqrSend_msg_congr {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {st₁ c₁ st₂ c₂ : DY.Bytes}
    (hst : gamma compI0 S g₁ st₁ = gamma compI0 S g₂ st₂)
    (hc : gamma compI0 S g₁ c₁ = gamma compI0 S g₂ c₂) :
    gamma compI0 S g₁ (DY.Spqr.spqrSend st₁ c₁).2.2 =
      gamma compI0 S g₂ (DY.Spqr.spqrSend st₂ c₂).2.2 := by
  unfold gamma gamma' at hst hc
  unfold gamma gamma' DY.Spqr.spqrSend
  dsimp only
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg,
    DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hst, hc]

theorem gamma_spqrSend_key_init_congr {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {k₁ k₂ p c₁ c₂ : DY.Bytes}
    (hk : gamma compI0 S g₁ k₁ = gamma compI0 S g₂ k₂)
    (hp : gamma compI0 S g₁ p = gamma compI0 S g₂ p)
    (hi : gamma compI0 S g₁ (DY.Spqr.encodeSpqrIndexTerm 1) =
      gamma compI0 S g₂ (DY.Spqr.encodeSpqrIndexTerm 1)) :
    gamma compI0 S g₁ (DY.Spqr.spqrSend (DY.Spqr.spqrInit k₁ p) c₁).2.1 =
      gamma compI0 S g₂ (DY.Spqr.spqrSend (DY.Spqr.spqrInit k₂ p) c₂).2.1 := by
  unfold DY.Spqr.spqrSend DY.Spqr.spqrInit
  dsimp only
  simp only [_root_.DY.BytesView.view_pack]
  unfold gamma gamma' at hk hp hi
  unfold gamma gamma' DY.Spqr.spqrChainKey
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey,
    DY.Libsignal.Composed.Refinement.spqrKeyNode,
    DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hk, hp, hi]

theorem gamma_spqrSend_key_step_congr {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {st₀₁ c₀₁ c₁ st₀₂ c₀₂ c₂ : DY.Bytes}
    (hst : gamma compI0 S g₁ (DY.Spqr.spqrSend st₀₁ c₀₁).1 =
      gamma compI0 S g₂ (DY.Spqr.spqrSend st₀₂ c₀₂).1)
    (hc : gamma compI0 S g₁ c₁ = gamma compI0 S g₂ c₂) :
    gamma compI0 S g₁ (DY.Spqr.spqrSend (DY.Spqr.spqrSend st₀₁ c₀₁).1 c₁).2.1 =
      gamma compI0 S g₂ (DY.Spqr.spqrSend (DY.Spqr.spqrSend st₀₂ c₀₂).1 c₂).2.1 := by
  have hv1 : ((DY.Spqr.spqrSend st₀₁ c₀₁).1).view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := st₀₁, coins := c₀₁ } : DY.Spqr.SendState.SubF DY.Bytes)
  have hv2 : ((DY.Spqr.spqrSend st₀₂ c₀₂).1).view? DY.Spqr.InitState.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF
      ({ st := st₀₂, coins := c₀₂ } : DY.Spqr.SendState.SubF DY.Bytes)
  dsimp only [DY.Spqr.spqrSend] at hv1 hv2 hst
  conv_lhs => unfold DY.Spqr.spqrSend; dsimp only; rw [hv1]
  conv_rhs => unfold DY.Spqr.spqrSend; dsimp only; rw [hv2]
  unfold gamma gamma' at hst hc ⊢
  rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S) (concretizeAll compI0 S g₁),
      DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S) (concretizeAll compI0 S g₂)]
  dsimp only [DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey,
    DY.Libsignal.Composed.Refinement.spqrKeyNode,
    DY.Libsignal.Composed.Refinement.opaqueNode]
  simp only [hst, hc]

/-! ### 6. Clean Alice Execution (`s0Clean`, `s1Clean`, `s2Clean`), `extract_spqrPins`, and `ev3` Disproof -/

theorem ecKey_inj {a b : HwBytes}
    (h : DY.Libsignal.Composed.Refinement.ecKey a = DY.Libsignal.Composed.Refinement.ecKey b) :
    a = b := by
  unfold DY.Libsignal.Composed.Refinement.ecKey at h
  exact (List.cons.inj h).2

local macro "at?_localEncTr_tac" : tactic =>
  `(tactic| (dsimp only [localEncTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))

theorem s0Clean_runs :
    s0Clean.ok (setupTrace r0) = true ∧ s0Clean.next (setupTrace r0) = tr1Clean := by
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr
    simp [hl1]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr
    simp [hl2]
  have hat4 : (setupTrace r0).at? 4 =
      some (Runs.StP "alice" { kind := .identity, sk := ikASkClean }) := by
    rw [setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 registerIdentityTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl1, length_append_entry]; omega)])
    unfold setupTr1 registerIdentityTr; dsimp only
    rw [Symbolic.DYBridge.DY.Trace.length_eq_1]
    refine at?_append_eq_of_eq _ _ ?_
    simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, length_append_entry]
  have hat6 : (setupTrace r0).at? 6 =
      some (Runs.EvP (.IdentityRegistered "bob" ikBPkClean (DY.Signature.vk ikBSkClean) true)) := by
    rw [setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl2, length_append_entry]; omega)])
    unfold setupTr2 registerIdentityTr; dsimp only; rw [hl1]
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl1, length_append_entry]; omega)])
    refine at?_append_eq_of_eq _ _ ?_
    simp only [hl1, length_append_entry]
  have hat14 : (setupTrace r0).at? 14 = some (Runs.NetE spkBPkClean) := by
    rw [setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)])
    unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl2, length_append_entry]; omega)]
    refine at?_append_eq_of_eq _ _ ?_
    simp only [hl2, length_append_entry]
  have hat15 : (setupTrace r0).at? 15 = some (Runs.NetE (setupPublic r0 5)) := by
    rw [setupPublic_r0_5, setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr
    dsimp only
    repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)])
    unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
    refine at?_append_eq_of_eq _ _ ?_
    simp only [hl2, length_append_entry]
  have hat20 : (setupTrace r0).at? 20 = some (Runs.NetE pqpkBClean) := by
    rw [setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)]
    refine at?_append_eq_of_eq _ _ ?_
    simp only [hl3, length_append_entry]
  have hat21 : (setupTrace r0).at? 21 = some (Runs.NetE (setupPublic r0 7)) := by
    rw [setupPublic_r0_7, setupTrace_r0_eq]
    unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
    refine at?_append_eq_of_eq _ _ ?_
    simp only [hl3, length_append_entry]
  have hv_spk : DY.Signature.verify (DY.Signature.vk ikBSkClean)
      (DY.Libsignal.PQXDH.encodeEC spkBPkClean) (setupPublic r0 5) = true := by
    rw [setupPublic_r0_5]; exact DY.Signature.verify_sign _ _ _
  have hv_pq : DY.Signature.verify (DY.Signature.vk ikBSkClean)
      (DY.Libsignal.PQXDH.encodeKEM pqpkBClean) (setupPublic r0 7) = true := by
    rw [setupPublic_r0_7]; exact DY.Signature.verify_sign _ _ _
  have hlow : DY.X25519.x25519LowOrder spkBPkClean = false := by
    change DY.X25519.x25519LowOrder (DY.DiffieHellman.dhPk spkBSkClean) = false
    have hv_var : (DY.DiffieHellman.dhPk spkBSkClean).view? DY.X25519.Variant.SubF = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
        ({ sk := spkBSkClean } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    have hv_lit : (DY.DiffieHellman.dhPk spkBSkClean).view? DY.Literal.Literal.SubF = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
        ({ sk := spkBSkClean } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    unfold DY.X25519.x25519LowOrder DY.X25519.normalizeX25519Key
    dsimp only [DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral]
    rw [hv_var, hv_lit]
  have hrun := Runs.Runs.aliceStart (h := (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles))
    hat4 hat6 hat14 hat15 hat20 hat21 hv_spk hv_pq rfl hlow
  have hok_eq := stepIn_ok DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles)) (setupTrace r0)
  have hnext_eq := stepIn_next DY.Libsignal.Composed.aliceStart.reachability
    ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles)) (setupTrace r0)
  have h1 : ((DY.Libsignal.Composed.aliceStart "alice" "bob" 4 6 ⟨14, 15, 20, 21, none⟩).run (setupTrace r0)).1.isSome = true := by
    rw [hrun.1]; rfl
  exact ⟨hok_eq.trans h1, hnext_eq.trans hrun.2⟩

theorem messageEncrypt_clean_runs {tr : ExecTrace} {me : DY.Participant}
    {stIdx cl pqIdx : Nat} {st : DY.Libsignal.TripleRatchet.TRState}
    (hst : (tr.at? stIdx : Option CompTrace.TRStEntry) = some (CompTrace.TRStE me st))
    (hns : st.ns ≠ DY.Libsignal.TripleRatchet.u32Max)
    (hpq : pqIdx = tr.length + 2) :
    (Step.messageEncrypt me stIdx cl pqIdx).ok tr = true ∧
    (Step.messageEncrypt me stIdx cl pqIdx).next tr =
      localEncTr tr me stIdx cl st (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1 := by
  have hok_eq := stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stIdx, cl, pqIdx) tr
  have hnext_eq := stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stIdx, cl, pqIdx) tr
  set pqSalt := (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1
  have hpq_at : (((tr.append (Runs.RndE 32)).append (Runs.RndE cl)).append
      (Runs.NetE pqSalt)).at? pqIdx = some (Runs.NetE pqSalt) := by
    subst hpq
    exact at?_append_eq_of_eq _ _ (by simp only [Runs.RndE, length_append_entry])
  have hrun : Runs.Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stIdx cl pqIdx) tr
      (tr.length + 6) (localEncTr tr me stIdx cl st pqSalt) := by
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    refine Runs.Runs.bind (Runs.Runs.getLocalState hst) ?_
    refine Runs.Runs.bind (Runs.Runs.guard _ hns) ?_
    refine Runs.Runs.bind (Runs.Runs.genRand _ _) ?_
    refine Runs.Runs.bind (Runs.Runs.genRand _ _) ?_
    dsimp only
    have hr1 : Runs.rnd (tr.length + 1) cl = randTerm (tr.length + 1) cl := rfl
    have hl1 : (tr.append (Runs.RndE 32)).length = tr.length + 1 := length_append_entry tr _
    rw [hl1, hr1]
    refine Runs.Runs.bind (Runs.Runs.sendMessage _ _) ?_
    refine Runs.Runs.bind (Runs.Runs.receiveMessage hpq_at) ?_
    refine Runs.Runs.bind (Runs.Runs.logEvent _ _) ?_
    refine Runs.Runs.bind (Runs.Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
    have hdone := Runs.Runs.sendMessage
      ((((((tr.append (CompTrace.RndE 32)).append (CompTrace.RndE cl)).append
        (CompTrace.NetE pqSalt)).append
        (CompTrace.TREvE (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns (randTerm tr.length 32)))).append
        (CompTrace.TREvE (.MessageKey (st.sessionInfo me) .sender
          (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx stIdx))).append
        (CompTrace.TRStE me (localEncState st (randTerm (tr.length + 1) cl))))
      (localEncMsg st (randTerm (tr.length + 1) cl) pqSalt (randTerm tr.length 32))
    have hlen6 : ((((((tr.append (CompTrace.RndE 32)).append (CompTrace.RndE cl)).append
        (CompTrace.NetE pqSalt)).append
        (CompTrace.TREvE (.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns (randTerm tr.length 32)))).append
        (CompTrace.TREvE (.MessageKey (st.sessionInfo me) .sender
          (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx stIdx))).append
        (CompTrace.TRStE me (localEncState st (randTerm (tr.length + 1) cl)))).length = tr.length + 6 := by
      simp only [length_append_entry]
    rw [hlen6] at hdone
    exact hdone
  have h1 : ((DY.Libsignal.TripleRatchet.messageEncrypt me stIdx cl pqIdx).run tr).1.isSome = true := by
    rw [hrun.1]; rfl
  exact ⟨hok_eq.trans h1, hnext_eq.trans hrun.2⟩

theorem s1Clean_runs (cl1 : Nat) :
    (s1Clean cl1).ok tr1Clean = true ∧ (s1Clean cl1).next tr1Clean = tr2Clean cl1 := by
  have hst : (tr1Clean.at? 30 : Option CompTrace.TRStEntry) = some (CompTrace.TRStE "alice" stA0Clean) := by
    unfold tr1Clean localAliceStartTr stA0Clean
    exact at?_append_eq_of_eq _ _ (by simp [setupTrace_r0_len])
  have h := messageEncrypt_clean_runs (cl := cl1) (pqIdx := 33) hst (by decide)
    (by rw [tr1Clean_len])
  simpa [s1Clean, tr2Clean, salt1Clean, coins1Clean, tr1Clean_len] using h

theorem s2Clean_runs (cl1 cl2 : Nat) :
    (s2Clean cl2).ok (tr2Clean cl1) = true ∧ (s2Clean cl2).next (tr2Clean cl1) = tr3Clean cl1 cl2 := by
  have hst : ((tr2Clean cl1).at? 36 : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE "alice" (stA1Clean cl1)) := by
    have h36 : 36 = tr1Clean.length + 5 := by rw [tr1Clean_len]
    rw [h36]
    unfold tr2Clean stA1Clean coins1Clean
    have h32 : 32 = tr1Clean.length + 1 := by rw [tr1Clean_len]
    rw [h32]
    at?_localEncTr_tac
  have hns : (stA1Clean cl1).ns ≠ DY.Libsignal.TripleRatchet.u32Max := by
    change (1 : UInt32) ≠ DY.Libsignal.TripleRatchet.u32Max; decide
  have h := messageEncrypt_clean_runs (cl := cl2) (pqIdx := 40) hst hns
    (by rw [tr2Clean_len])
  have h39 : (tr2Clean cl1).length + 1 = 39 := by rw [tr2Clean_len]
  have hs : (DY.Spqr.spqrSend (stA1Clean cl1).spqr (randTerm ((tr2Clean cl1).length + 1) cl2)).2.1 =
      salt2Clean cl1 cl2 := by
    rw [h39]; rfl
  rw [hs] at h
  exact h

theorem runTrace_ss3Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    runTrace r (ss3Clean cl1 cl2) = tr3Clean cl1 cl2 := by
  unfold runTrace ss3Clean
  rw [setupTrace_eq_of_fits hp]
  dsimp only [runSteps]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2, (s2Clean_runs cl1 cl2).2]

theorem honestSaltsOf_ss3Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    honestSaltsOf r (ss3Clean cl1 cl2) = [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2] := by
  unfold honestSaltsOf ss3Clean
  rw [setupTrace_eq_of_fits hp]
  rw [honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_2, honestKeysOf.eq_1]
  rw [s0Clean_runs.2, (s1Clean_runs cl1).2]
  have hp0 : s0Clean.publishedSpqrKey? (setupTrace r0) = none := rfl
  have hp1 : (s1Clean cl1).publishedSpqrKey? tr1Clean = some (salt1Clean cl1) := by
    have hnext1 := (s1Clean_runs cl1).2
    dsimp only [s1Clean] at hnext1 ⊢
    unfold Step.publishedSpqrKey? encryptAbortAfterSpqrIdx encryptOwnSpqrKeyIdx
    dsimp only
    rw [hnext1, tr1Clean_len]
    simp only [show ¬ (33 = 31 + 3) by decide, ↓reduceIte, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
    have hat : ((tr2Clean cl1).at? 33 : Option DY.Network.ExecEntryT) =
        some (CompTrace.NetE (salt1Clean cl1)) := by
      have h33 : 33 = tr1Clean.length + 2 := by rw [tr1Clean_len]
      rw [h33]; unfold tr2Clean salt1Clean coins1Clean
      have h32 : 32 = tr1Clean.length + 1 := by rw [tr1Clean_len]
      rw [h32]; at?_localEncTr_tac
    simp [hat, CompTrace.NetE]
  have hp2 : (s2Clean cl2).publishedSpqrKey? (tr2Clean cl1) = some (salt2Clean cl1 cl2) := by
    have hnext2 := (s2Clean_runs cl1 cl2).2
    dsimp only [s2Clean] at hnext2 ⊢
    unfold Step.publishedSpqrKey? encryptAbortAfterSpqrIdx encryptOwnSpqrKeyIdx
    dsimp only
    rw [hnext2, tr2Clean_len]
    simp only [show ¬ (40 = 38 + 3) by decide, ↓reduceIte, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
    have hat : ((tr3Clean cl1 cl2).at? 40 : Option DY.Network.ExecEntryT) =
        some (CompTrace.NetE (salt2Clean cl1 cl2)) := by
      have h40 : 40 = (tr2Clean cl1).length + 2 := by rw [tr2Clean_len]
      rw [h40]; unfold tr3Clean salt2Clean coins2Clean
      have h39 : 39 = (tr2Clean cl1).length + 1 := by rw [tr2Clean_len]
      rw [h39]; at?_localEncTr_tac
    simp [hat, CompTrace.NetE]
  simp [hp0, hp1, hp2]

noncomputable def vis3Clean (cl1 cl2 : Nat) : List VisEntry :=
  stepView s0Clean (setupTrace r0) (runWrapped ev0) ++
  stepView (s1Clean cl1) tr1Clean (runWrapped ev1) ++
  stepView (s2Clean cl2) (tr2Clean cl1) (runWrapped ev2)

theorem filterMap_congr_loc {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x (.head _), filterMap_congr_loc (fun y hy => h y (.tail _ hy))]

theorem pendingPreKey_tr1Clean :
    pendingPreKey tr1Clean 30 = some (oClean.ek, oClean.ct) := by
  have hat30 : tr1Clean.getLocalStateAt DY.Libsignal.TripleRatchet.TRState 30 =
      some ⟨"alice", stA0Clean⟩ := by
    unfold DY.ExecTrace.getLocalStateAt tr1Clean stA0Clean
    have h : ((localAliceStartTr (setupTrace r0) "alice" "bob" oClean).at? 30 : Option CompTrace.TRStEntry) =
        some (CompTrace.TRStE "alice" (localAliceStartState (setupTrace r0) "bob" oClean)) := by
      unfold localAliceStartTr
      exact at?_append_eq_of_eq _ _ (by simp only [setupTrace_r0_len, length_append_entry])
    rw [h]; rfl
  have htr_ev : ∀ j < 30, (tr1Clean.at? j : Option CompTrace.TREntry) =
      if j = 28 then some (CompTrace.TREvE (.InitSession "alice" "bob"
        (DY.DiffieHellman.dhPk (randTerm 24 32)) oClean.spk))
      else none := by
    intro j hj
    unfold tr1Clean localAliceStartTr
    rw [at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl]
    by_cases hj28 : j = 28
    · subst hj28
      simp only [↓reduceIte]
      have heq : ((((((((setupTrace r0).append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append
          (CompTrace.RndE 32)).append (CompTrace.NetE oClean.ek)).append
          (CompTrace.NetE oClean.ct)).append
          (CompTrace.PQEvE (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys))).append
          (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk))).at? 28 =
          some (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk)) := by
        refine at?_append_eq_of_eq _ _ ?_
        have hlen0 := setupTrace_r0_len
        simp only [length_append_entry]; omega
      rw [heq, setupTrace_r0_len]
    · simp only [hj28, ↓reduceIte]
      by_cases hj29 : j = 29
      · subst hj29
        exact Symbolic.Swarm.CREF.at?_ge_length _
          (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)
      · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
        repeat rw [at?_append_other_eq _ _ rfl]
        rw [setupTrace_r0_eq]
        unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
        repeat rw [at?_append_other_eq _ _ rfl]
        exact Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
          (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])
  have hdecF : sessionHasDecrypted tr1Clean (stA0Clean.sessionInfo "alice") 30 = false := by
    unfold sessionHasDecrypted
    rw [List.any_eq_false]
    intro j hj
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, htr_ev j (List.mem_range.mp hj)]
    split_ifs <;> simp
  have hpq27 : tr1Clean.getEventAt DY.Libsignal.PQXDH.PQXDHEvent 27 =
      some (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys) := by
    have hp := (getEventAt_pq_localAliceStartTr (setupTrace r0) "alice" "bob" oClean).2.2.2.2.2.1
    rw [setupTrace_r0_len] at hp; exact hp
  have hce_only : ∀ i < 31, tr1Clean.getEventAt DY.Libsignal.Composed.ComposedEvent i =
      if i = 29 then some (.HandshakeSession (stA0Clean.sessionInfo "alice") 27) else none := by
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    have hat : (tr1Clean.at? i : Option CompTrace.CEntry) =
        if i = 29 then some (CompTrace.CEvE (.HandshakeSession (stA0Clean.sessionInfo "alice") 27))
        else none := by
      unfold tr1Clean localAliceStartTr stA0Clean
      rw [at?_append_other_eq _ _ rfl]
      by_cases h29 : i = 29
      · subst h29
        simp only [↓reduceIte]
        have heq : (((((((((setupTrace r0).append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append
            (CompTrace.RndE 32)).append (CompTrace.NetE oClean.ek)).append
            (CompTrace.NetE oClean.ct)).append
            (CompTrace.PQEvE (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys))).append
            (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk))).append
            (CompTrace.CEvE (.HandshakeSession ((localAliceStartState (setupTrace r0) "bob" oClean).sessionInfo "alice") ((setupTrace r0).length + 5)))).at? 29 =
            some (CompTrace.CEvE (.HandshakeSession ((localAliceStartState (setupTrace r0) "bob" oClean).sessionInfo "alice") ((setupTrace r0).length + 5))) := by
          refine at?_append_eq_of_eq _ _ ?_
          have hlen0 := setupTrace_r0_len
          simp only [length_append_entry]; omega
        rw [heq, setupTrace_r0_len]
      · simp only [h29, ↓reduceIte]
        by_cases h30 : i = 30
        · subst h30
          exact Symbolic.Swarm.CREF.at?_ge_length _
            (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)
        · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
            (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
          rw [setupTrace_r0_eq]
          unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
          repeat rw [at?_append_other_eq _ _ rfl]
          exact Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
            (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])
    rw [hat]
    split_ifs <;> rfl
  unfold pendingPreKey
  rw [hat30]
  dsimp only
  rw [hdecF]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sessionHandshakeEvents
  rw [tr1Clean_len]
  refine (congrArg (List.findSome? _) (filterMap_congr_loc (g := fun i =>
    if i = 29 then some (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys)
    else none) fun i hi => ?_)).trans rfl
  rw [hce_only i (List.mem_range.mp hi)]
  by_cases hx : i = 29 <;> simp [hx, hpq27]

theorem pendingPreKey_tr2Clean (cl1 : Nat) :
    pendingPreKey (tr2Clean cl1) 36 = some (oClean.ek, oClean.ct) := by
  have hat36 : (tr2Clean cl1).getLocalStateAt DY.Libsignal.TripleRatchet.TRState 36 =
      some ⟨"alice", stA1Clean cl1⟩ := by
    unfold DY.ExecTrace.getLocalStateAt
    have h36 : 36 = tr1Clean.length + 5 := by rw [tr1Clean_len]
    have h : ((tr2Clean cl1).at? 36 : Option CompTrace.TRStEntry) =
        some (CompTrace.TRStE "alice" (stA1Clean cl1)) := by
      rw [h36]; unfold tr2Clean stA1Clean coins1Clean
      have h32 : 32 = tr1Clean.length + 1 := by rw [tr1Clean_len]
      rw [h32]; at?_localEncTr_tac
    rw [h]; rfl
  have hsinfo : (stA1Clean cl1).sessionInfo "alice" = stA0Clean.sessionInfo "alice" := rfl
  have hdec2F : sessionHasDecrypted (tr2Clean cl1) (stA0Clean.sessionInfo "alice") 36 = false := by
    unfold sessionHasDecrypted
    rw [List.any_eq_false]
    intro j hj
    have hj36 : j < 36 := List.mem_range.mp hj
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    by_cases hj30 : j < 30
    · have hlt : j < tr1Clean.length := by rw [tr1Clean_len]; omega
      have hat : ((tr2Clean cl1).at? j : Option CompTrace.TREntry) = (tr1Clean.at? j : Option CompTrace.TREntry) := by
        unfold tr2Clean localEncTr
        repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
        exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hlt
      rw [hat]
      unfold tr1Clean localAliceStartTr
      rw [at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl]
      by_cases hj28 : j = 28
      · subst hj28
        have heq : ((((((((setupTrace r0).append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append
            (CompTrace.RndE 32)).append (CompTrace.NetE oClean.ek)).append
            (CompTrace.NetE oClean.ct)).append
            (CompTrace.PQEvE (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys))).append
            (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk))).at? 28 =
            some (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk)) := by
          refine at?_append_eq_of_eq _ _ ?_
          have hlen0 := setupTrace_r0_len
          simp only [length_append_entry]; omega
        rw [heq]; simp
      · by_cases hj29 : j = 29
        · subst hj29
          rw [Symbolic.Swarm.CREF.at?_ge_length _
            (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
          simp
        · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
            (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
          repeat rw [at?_append_other_eq _ _ rfl]
          rw [setupTrace_r0_eq]
          unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
          repeat rw [at?_append_other_eq _ _ rfl]
          rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])]
          simp
    · have hcases : j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      · have hlt : 30 < tr1Clean.length := by rw [tr1Clean_len]; decide
        have hat : ((tr2Clean cl1).at? 30 : Option CompTrace.TREntry) = (tr1Clean.at? 30 : Option CompTrace.TREntry) := by
          unfold tr2Clean localEncTr
          repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
          exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ hlt
        rw [hat]; unfold tr1Clean localAliceStartTr
        rw [at?_append_other_eq _ _ rfl]
        rw [Symbolic.Swarm.CREF.at?_ge_length _ (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
        simp
      · have t : ((tr2Clean cl1).at? 31 : Option CompTrace.TREntry) = none := by
          rw [show 31 = tr1Clean.length from tr1Clean_len.symm]; unfold tr2Clean; at?_localEncTr_tac
        rw [t]; simp
      · have t : ((tr2Clean cl1).at? 32 : Option CompTrace.TREntry) = none := by
          rw [show 32 = tr1Clean.length + 1 by rw [tr1Clean_len]]; unfold tr2Clean; at?_localEncTr_tac
        rw [t]; simp
      · have t : ((tr2Clean cl1).at? 33 : Option CompTrace.TREntry) = none := by
          rw [show 33 = tr1Clean.length + 2 by rw [tr1Clean_len]]; unfold tr2Clean; at?_localEncTr_tac
        rw [t]; simp
      · have t : ((tr2Clean cl1).at? 34 : Option CompTrace.TREntry) =
            some (CompTrace.TREvE (.Sent "alice" "bob" (DY.DiffieHellman.dhPk stA0Clean.dhs) 0 (randTerm tr1Clean.length 32))) := by
          rw [show 34 = tr1Clean.length + 3 by rw [tr1Clean_len]]; unfold tr2Clean; at?_localEncTr_tac
        rw [t]; simp
      · have t : ((tr2Clean cl1).at? 35 : Option CompTrace.TREntry) =
            some (CompTrace.TREvE (.MessageKey (stA0Clean.sessionInfo "alice") .sender (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 (salt1Clean cl1) 0 stA0Clean.rIdx 30)) := by
          rw [show 35 = tr1Clean.length + 4 by rw [tr1Clean_len]]; unfold tr2Clean; at?_localEncTr_tac
        rw [t]; simp
  have hpq27 : (tr2Clean cl1).getEventAt DY.Libsignal.PQXDH.PQXDHEvent 27 =
      some (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys) := by
    have hp := (getEventAt_pq_localAliceStartTr (setupTrace r0) "alice" "bob" oClean).2.2.2.2.2.1
    rw [setupTrace_r0_len] at hp
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hp ⊢
    have hat : ((tr2Clean cl1).at? 27 : Option CompTrace.PQXDHEntry) =
        (tr1Clean.at? 27 : Option CompTrace.PQXDHEntry) := by
      unfold tr2Clean localEncTr
      repeat rw [at?_append_other_eq _ _ rfl]
    rw [hat]; exact hp
  have hce2_only : ∀ i < 38, (tr2Clean cl1).getEventAt DY.Libsignal.Composed.ComposedEvent i =
      if i = 29 then some (.HandshakeSession (stA0Clean.sessionInfo "alice") 27) else none := by
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    have hat0 : ((tr2Clean cl1).at? i : Option CompTrace.CEntry) =
        (tr1Clean.at? i : Option CompTrace.CEntry) := by
      unfold tr2Clean localEncTr
      repeat rw [at?_append_other_eq _ _ rfl]
    rw [hat0]
    unfold tr1Clean localAliceStartTr stA0Clean
    rw [at?_append_other_eq _ _ rfl]
    by_cases h29 : i = 29
    · subst h29
      simp only [↓reduceIte]
      have heq : (((((((((setupTrace r0).append (CompTrace.RndE 32)).append (CompTrace.RndE 32)).append
          (CompTrace.RndE 32)).append (CompTrace.NetE oClean.ek)).append
          (CompTrace.NetE oClean.ct)).append
          (CompTrace.PQEvE (.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys))).append
          (CompTrace.TREvE (.InitSession "alice" "bob" (DY.DiffieHellman.dhPk (randTerm ((setupTrace r0).length + 2) 32)) oClean.spk))).append
          (CompTrace.CEvE (.HandshakeSession ((localAliceStartState (setupTrace r0) "bob" oClean).sessionInfo "alice") ((setupTrace r0).length + 5)))).at? 29 =
          some (CompTrace.CEvE (.HandshakeSession ((localAliceStartState (setupTrace r0) "bob" oClean).sessionInfo "alice") ((setupTrace r0).length + 5))) := by
        refine at?_append_eq_of_eq _ _ ?_
        have hlen0 := setupTrace_r0_len
        simp only [length_append_entry]; omega
      rw [heq, setupTrace_r0_len]
    · simp only [h29, ↓reduceIte]
      by_cases hge30 : 30 ≤ i
      · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
      · rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _
          (by have hlen0 := setupTrace_r0_len; simp only [length_append_entry]; omega)]
        rw [setupTrace_r0_eq]
        unfold setupTr0 genPQPrekeyTr setupTr3 genSignedPrekeyTr setupTr2 setupTr1 registerIdentityTr
        repeat rw [at?_append_other_eq _ _ rfl]
        rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
          (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])]
  unfold pendingPreKey
  rw [hat36]
  dsimp only
  rw [hsinfo, hdec2F]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sessionHandshakeEvents
  rw [tr2Clean_len]
  refine (congrArg (List.findSome? _) (filterMap_congr_loc (g := fun i =>
    if i = 29 then some (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone "alice" "bob" oClean.ikA oClean.ikB oClean.spk oClean.pqpk oClean.opk oClean.ek oClean.ct oClean.keys)
    else none) fun i hi => ?_)).trans rfl
  rw [hce2_only i (List.mem_range.mp hi)]
  by_cases hx : i = 29 <;> simp [hx, hpq27]

theorem plaintextTerms_vis3Clean (cl1 cl2 : Nat) :
    plaintextTerms (vis3Clean cl1 cl2) = [randTerm 31 32, randTerm 38 32] := by
  unfold plaintextTerms vis3Clean
  have hv0 : (stepView s0Clean (setupTrace r0) (runWrapped ev0)).filter (·.kind == .pt) = [] := by
    unfold stepView
    simp only [s0Clean_runs.1, ↓reduceIte, s0Clean_runs.2]
    dsimp only [s0Clean]
    unfold tr1Clean
    rw [exposures_localAliceStartTr, List.append_nil, aliceVis_localAliceStartTr]
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw1
    · simp
    · rcases List.mem_cons.mp hw1 with rfl | hw2
      · simp [rngEntry]
      · rcases List.mem_append.mp hw2 with hkc | hdhs
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc; simp
        · rcases List.mem_singleton.mp hdhs with rfl; simp [rngEntry]
  have hv1 : (stepView (s1Clean cl1) tr1Clean (runWrapped ev1)).filter (·.kind == .pt) =
      [(⟨.pt, [randTerm 31 32], .single, none⟩ : VisEntry)] := by
    unfold stepView
    simp only [(s1Clean_runs cl1).1, ↓reduceIte, (s1Clean_runs cl1).2]
    dsimp only [s1Clean]
    unfold tr2Clean
    rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr1Clean_len, runWrapped_ev1_fast]
    unfold encDraws encSendEntry
    rw [lastSent_localEncTr, tr1Clean_len, pendingPreKey_tr1Clean]
    simp only [List.cons_append, List.filter_cons, show (VisEventKind.pt == VisEventKind.pt) = true from rfl, ↓reduceIte]
    congr 1
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_append.mp hw with hrng | hse
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; simp [rngEntry]
    · rcases List.mem_singleton.mp hse with rfl; simp
  have hv2 : (stepView (s2Clean cl2) (tr2Clean cl1) (runWrapped ev2)).filter (·.kind == .pt) =
      [(⟨.pt, [randTerm 38 32], .single, none⟩ : VisEntry)] := by
    unfold stepView
    simp only [(s2Clean_runs cl1 cl2).1, ↓reduceIte, (s2Clean_runs cl1 cl2).2]
    dsimp only [s2Clean]
    unfold tr3Clean
    rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr2Clean_len, runWrapped_ev2_fast]
    unfold encDraws encSendEntry
    rw [lastSent_localEncTr, tr2Clean_len, pendingPreKey_tr2Clean]
    simp only [List.cons_append, List.filter_cons, show (VisEventKind.pt == VisEventKind.pt) = true from rfl, ↓reduceIte]
    congr 1
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_append.mp hw with hrng | hse
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng; simp [rngEntry]
    · rcases List.mem_singleton.mp hse with rfl; simp
  rw [List.filter_append, List.filter_append, hv0, hv1, hv2]
  rfl

theorem sendTerms_vis3Clean (cl1 cl2 : Nat) :
    ((vis3Clean cl1 cl2).filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m1Clean cl1, oClean.ek, oClean.ct, m2Clean cl1 cl2] := by
  unfold vis3Clean
  have hv0 : (stepView s0Clean (setupTrace r0) (runWrapped ev0)).filter (·.kind == .send) = [] := by
    unfold stepView
    simp only [s0Clean_runs.1, ↓reduceIte, s0Clean_runs.2]
    dsimp only [s0Clean]
    unfold tr1Clean
    rw [exposures_localAliceStartTr, List.append_nil, aliceVis_localAliceStartTr]
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw1
    · simp
    · rcases List.mem_cons.mp hw1 with rfl | hw2
      · simp [rngEntry]
      · rcases List.mem_append.mp hw2 with hkc | hdhs
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc; simp
        · rcases List.mem_singleton.mp hdhs with rfl; simp [rngEntry]
  have hv1 : ((stepView (s1Clean cl1) tr1Clean (runWrapped ev1)).filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m1Clean cl1] := by
    unfold stepView
    simp only [(s1Clean_runs cl1).1, ↓reduceIte, (s1Clean_runs cl1).2]
    dsimp only [s1Clean]
    unfold tr2Clean
    rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr1Clean_len, runWrapped_ev1_fast]
    unfold encDraws encSendEntry
    rw [lastSent_localEncTr, tr1Clean_len, pendingPreKey_tr1Clean]
    rw [List.filter_append]
    have hf1 : ((⟨.pt, [randTerm 31 32], .single, none⟩ : VisEntry) :: (([(randTerm 32 cl1, cl1)].filter fun r => r.2 != 0).map fun r => rngEntry r.1)).filter (·.kind == .send) = [] := by
      rw [List.filter_eq_nil_iff]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hmr
      · simp
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmr; simp [rngEntry]
    rw [hf1, List.nil_append]
    rfl
  have hv2 : ((stepView (s2Clean cl2) (tr2Clean cl1) (runWrapped ev2)).filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m2Clean cl1 cl2] := by
    unfold stepView
    simp only [(s2Clean_runs cl1 cl2).1, ↓reduceIte, (s2Clean_runs cl1 cl2).2]
    dsimp only [s2Clean]
    unfold tr3Clean
    rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr2Clean_len, runWrapped_ev2_fast]
    unfold encDraws encSendEntry
    rw [lastSent_localEncTr, tr2Clean_len, pendingPreKey_tr2Clean]
    rw [List.filter_append]
    have hf1 : ((⟨.pt, [randTerm 38 32], .single, none⟩ : VisEntry) :: (([(randTerm 39 cl2, cl2)].filter fun r => r.2 != 0).map fun r => rngEntry r.1)).filter (·.kind == .send) = [] := by
      rw [List.filter_eq_nil_iff]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hmr
      · simp
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmr; simp [rngEntry]
    rw [hf1, List.nil_append]
    rfl
  rw [List.filter_append, List.filter_append, hv0, List.nil_append, List.flatMap_append, hv1, hv2]
  rfl

theorem not_bobSessionStartCollides_c2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hc : GhostAndSemMatchSetup compI0 r S g)
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn compI0 r S (gClean g)
        (runTrace r (ss3Clean cl1 cl2)) (vis3Clean cl1 cl2)
        (honestSaltsOf r (ss3Clean cl1 cl2)) p_c2 ⟨oClean.ek, oClean.ct, m2Clean cl1 cl2⟩ := by
  rw [runTrace_ss3Clean hp, honestSaltsOf_ss3Clean hp]
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only
  rw [parse_m2Clean]
  set pts := plaintextTerms (vis3Clean cl1 cl2) ++ ([] : List DY.Bytes)
  have hpts_eq : pts = [randTerm 31 32, randTerm 38 32] := by
    simp [pts, plaintextTerms_vis3Clean]
  have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hc hcl1 hcl2
    (by rw [hpts_eq]; simp) (by rw [hpts_eq]; simp) hsalt1 hpqm1 hsalt2 hpqm2
  obtain ⟨hek0, hct0, _, _, _⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, _, _, hcks1, hm1, _, hm2⟩ := dagTermAt_aliceRatchetAndMsgs hw
  obtain ⟨hsa0, hsa1, hsa2⟩ := safeMemo2_aliceStates hcl1 hcl2 hw
  have hsec := safeMemo2_storedSecrets_tr3Clean hw
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      unfold prefixTerms principalTerms at ht
      rcases List.mem_append.mp ht with hprin | hpt
      · rcases List.mem_append.mp hprin with h12 | hs_mem
        · rcases List.mem_append.mp h12 with hsend | hst
          · rw [sendTerms_vis3Clean] at hsend
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hsend
            rcases hsend with rfl | rfl | rfl | rfl | rfl | rfl
            · exact safeMemo_toSafeMemo2 hek0.safeMemo
            · exact safeMemo_toSafeMemo2 hct0.safeMemo
            · exact safeMemo_toSafeMemo2 hm1.safeMemo
            · exact safeMemo_toSafeMemo2 hek0.safeMemo
            · exact safeMemo_toSafeMemo2 hct0.safeMemo
            · exact safeMemo_toSafeMemo2 hm2.safeMemo
          · rw [storedStates_eq_of_parties hp.ha hp.hb hp.hopk, storedStates_tr3Clean_eq] at hst
            simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hst
            rcases hst with rfl | rfl | rfl
            · exact hsa0
            · exact hsa1
            · exact hsa2
        · exact hsec t hs_mem
      · rw [plaintextTerms_vis3Clean] at hpt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt
        rcases hpt with rfl | rfl
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext (by change randTerm 31 32 ∈ pts; rw [hpts_eq]; simp)
            (by rw [hw.hσ_pt1]; decide +kernel))
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext (by change randTerm 38 32 ∈ pts; rw [hpts_eq]; simp)
            (by rw [hw.hσ_pt2]; decide +kernel))
    · intro t ht
      rcases List.mem_append.mp ht with hhead | htr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
        rcases hhead with rfl | rfl | rfl
        · exact safeMemo_toSafeMemo2 hek0.safeMemo
        · exact safeMemo_toSafeMemo2 hct0.safeMemo
        · exact safeMemo_toSafeMemo2 hm2.safeMemo
      · exact safeMemo_toSafeMemo2 (safeMemo_bobTrials_c2 hp hw t htr)
  · have hseed2 : DagTermAt S (gClean g) pts (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 112 :=
      termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1 (dagN_2 hw)
    obtain ⟨tck2, tmk2, tiv2⟩ := termAt_trMsgKeys
      (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
      dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
      ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
      ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
      (dagN_23 hw) hseed2
    have hprk2 := termAt_kdf (id := 114) dag_nodes_ok (by decide) rfl (dagN_23 hw) hseed2
    have hdhsPk : DagTermAt S (gClean g) pts (msg2Clean cl1 cl2).ratchetKey 73 := by
      change DagTermAt S (gClean g) pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73
      unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
    have hct2 := termAt_symEncPt (id := 120) dag_nodes_ok (by decide)
      (congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel) : dagOp 120 = .symEncPt 115 119 38 ev2.input)
      tck2 tiv2 hw.hpt2_mem hw.hσ_pt2 (by decide +kernel)
    have hwire2 : DagTermAt S (gClean g) pts (msg2Clean cl1 cl2).wire 121 :=
      termAt_trWire (id := 121) dag_nodes_ok (by decide)
        (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24) (by decide +kernel) :
          dagOp 121 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24 cleanAddrBs)
        hdhsPk hct2 (dagN_24 hw) (hw.haddr _)
    have hmac2 : DagTermAt S (gClean g) pts (msg2Clean cl1 cl2).mac 125 :=
      termAt_computeMac (c1_id := 122) (c2_id := 123) (h_id := 124) (t_id := 125)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk2 (dagN_28 hw) (dagN_31 hw) hwire2
    refine not_macTagForgeryOrCollision_of_honest_mac
      (salt_h := salt2Clean cl1 cl2)
      (seed_h := (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2)
      (a_h := stA0Clean.myIk) (b_h := stA0Clean.peerIk) (w_h := (msg2Clean cl1 cl2).wire)
      (by simp) rfl ?_ ?_ ?_ hmac
    · unfold gamma; rw [hmac2.2.1]; decide +kernel
    · unfold gamma; rw [tmk2.2.1]; decide +kernel
    · unfold gamma msgPrk DY.Libsignal.TripleRatchet.hmac; rw [hprk2.2.1]; decide +kernel


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
