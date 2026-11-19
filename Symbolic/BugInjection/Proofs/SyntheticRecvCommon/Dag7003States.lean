/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
import DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.BugInjection.Proofs.Common443.CliEventBridge

/-!
# `SafeMemo` for Stored States/Secrets, `symDec` Helper, and `gClean7003` Setup Match (`Dag7003States.lean`)

Connects `gClean7003` to `GhostAndSemMatchSetup`, discharges `SafeMemo` on `storedSecrets` and on all
honest `TRState` snapshots (`stA0Pure`, `stA1Pure`, `stB1Pure`, `stB2Pure`), and provides trace
projection helpers for `storedStates` and `storedSecrets`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States

open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (PQXDHState encodeEC encodeKEM)
open DY.Libsignal.TripleRatchet (TRState RecvChain)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost GhostAndSemMatchSetup
   setupRandomsAt setupPublic secretBytes storedStates storedSecrets
   randTerm ofByteArray gamma' gamma concretizeSign concretizeAll)
open Symbolic.BugInjection (fillFresh)
open Symbolic.Swarm.CREF (b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (aliceSt encSt bobSt0 ratchetState recvSt StT StP)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag (recvTailTerm stateAnchorPair trStateProxyRoots)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003 (setup7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
  (rec_eq_concretizeAll gamma_randTerm_pos gamma_dhPk gamma_kemPk gamma_concat gamma_literalToBytes
   setup_ids_7003 setup_secrets_7003 gamma_setup_keys_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
  (notAnyAiNodeBytes noAiSuffix noStrictAiSuffix SafeMemo TermAt
   safeMemo_of_termAt gamma_of_termAt)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt
  (safeMemo_bytesLike_empty safeMemo_mem_bool safeMemo_mem_slowNat safeMemo_mem_slowString
   safeMemo_mem_uint32_small safeMemo_recvTailTerm_0_1 safeMemo_recvTailTerm_1_2
   safeMemo_serialize_local_pqxdh safeMemo_trState_of_noAiSuffix)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
  (gClean7003 o1Pure stA0Pure stA1Pure cBPure cB'Pure stB00Pure stB0'Pure stB1Pure stB2Pure
   dhsBPure cBPure_chainKey_eq cB'Pure_chainKey_eq CommonNodes)

/-! ## 1. Symbolic `symDec` on `symEnc` Membership Helper -/

theorem symDec_symEnc_mem_eq {k iv k0 iv0 m u : DY.Bytes}
    (hu : u ∈ (DY.SymEnc.symDec k iv (DY.SymEnc.symEnc k0 iv0 m)).toList) :
    u = m := by
  simp only [DY.SymEnc.symDec, DY.SymEnc.symEnc] at hu
  split at hu <;> grind

/-! ## 2. `GhostAndSemMatchSetup` for `gClean7003` -/

theorem ghostAndSemMatchSetup_gClean7003 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hgs₀ : GhostAndSemMatchSetup compI7003 r S g₀) :
    GhostAndSemMatchSetup compI7003 r S (gClean7003 mode cl₁ cl₃) ∧
    S.kemPk (bytesOf pqskBId) = bytesOf pqpkId := by
  let g := gClean7003 mode cl₁ cl₃
  obtain ⟨hσ₀, hopq₀, hdec₀⟩ := hgs₀
  obtain ⟨_, _, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, _, _, _, _⟩ := setup_secrets_7003 hf
  obtain ⟨_, _, _, hg16₀, _, _, _, hkpk₀, _⟩ := gamma_setup_keys_7003 hf ⟨hσ₀, hopq₀, hdec₀⟩
  have hrat : setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hf.1.1.1, hopk]; rfl
  have hf0 : r.fresh 0 32 = bytesOf ikAId := by
    have h : r.fresh 0 32 = setup7003.aliceId := by simpa [secretBytes, hrat] using hs0
    exact h.trans (by decide)
  have hf5 : r.fresh 5 32 = bytesOf ikBId := by
    have h : r.fresh 5 32 = setup7003.bobId := by simpa [secretBytes, hrat] using hs1
    exact h.trans (by decide)
  have hf10 : r.fresh 10 32 = bytesOf spkBId := by
    have h : r.fresh 10 32 = setup7003.spk := by simpa [secretBytes, hrat] using hs2
    exact h.trans (by decide)
  have hf11 : r.fresh 11 64 = fillFresh 11 64 := by simpa [secretBytes, hrat] using hs3
  have hf16 : r.fresh 16 64 = bytesOf pqskBId := by
    have h : r.fresh 16 64 = fillFresh 16 64 := by simpa [secretBytes, hrat] using hs4
    exact h.trans (by decide)
  have hf17 : r.fresh 17 64 = fillFresh 17 64 := by simpa [secretBytes, hrat] using hs5
  have hσ_clean : ∀ p ∈ setupRandomsAt r, g.σ p.1 p.2 = r.fresh p.1 p.2 := by
    rw [hrat]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hf0]; rfl
    · rw [hf5]; rfl
    · rw [hf10]; rfl
    · rw [hf11]; rfl
    · rw [hf16]; rfl
    · rw [hf17]; rfl
  have hkpk_id : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId := by
    rw [gamma_kemPk, hg16₀] at hkpk₀
    have hpqsk_eq : bytesOf pqskBId = fillFresh 16 64 := by decide
    have hpqpk_eq : setup7003.kyberPk = bytesOf pqpkId := by decide
    rw [hpqsk_eq, hkpk₀, hpqpk_eq]
  have hpub := Symbolic.BugInjection.Proofs.Common443.CliEventBridge.gamma_setupPublic_eq_of_sigma_eq
    compI7003 r S g g₀ hf.1.1 hσ_clean hσ₀
  exact ⟨⟨hσ_clean, fun k hk => (hpub k hk).trans (hopq₀ k hk), hdec₀⟩, hkpk_id⟩

/-! ## 3. `SafeMemo` for `PQXDHState` Secrets and `TRState` Snapshots -/

def pqSecrets7003 : List DY.Bytes :=
  [DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := tRnd 0 32 }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := tRnd 5 32 }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := tRnd 10 32 }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState),
   DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := tRnd 16 64 }⟩ :
      DY.PersistentLocalState.LocalState PQXDHState)]

private theorem participant_str_ok :
    notAnyAiNodeBytes (ofByteArray "alice".toUTF8) = true ∧
    0 < (ofByteArray "alice".toUTF8).length ∧
    notAnyAiNodeBytes (ofByteArray "bob".toUTF8) = true ∧
    0 < (ofByteArray "bob".toUTF8).length := by
  simp only [String.toUTF8_eq_toByteArray]
  refine ⟨by decide +kernel, by decide, by decide +kernel, by decide⟩

theorem safeMemo_pqSecrets7003 {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes mode S pts cl₁ cl₃) :
    ∀ t ∈ pqSecrets7003, SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts t := by
  obtain ⟨ha_no, ha_pos, hb_no, hb_pos⟩ := participant_str_ok
  intro t ht
  simp only [pqSecrets7003, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact safeMemo_serialize_local_pqxdh _ ha_no ha_pos (safeMemo_of_termAt cn.ikA)
      (by dsimp only; rw [gamma_of_termAt cn.ikA]; decide +kernel)
  · exact safeMemo_serialize_local_pqxdh _ hb_no hb_pos (safeMemo_of_termAt cn.ikB)
      (by dsimp only; rw [gamma_of_termAt cn.ikB]; decide +kernel)
  · exact safeMemo_serialize_local_pqxdh _ hb_no hb_pos (safeMemo_of_termAt cn.spkB)
      (by dsimp only; rw [gamma_of_termAt cn.spkB]; decide +kernel)
  · exact safeMemo_serialize_local_pqxdh _ hb_no hb_pos (safeMemo_of_termAt cn.pqskB)
      (by dsimp only; rw [gamma_of_termAt cn.pqskB]; decide +kernel)

private theorem safeMemo_trState_oneRecv {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (me : DY.Participant) (st : TRState) (c : RecvChain)
    (hme : me = "alice" ∨ me = "bob")
    (hpeer : st.peer = "alice" ∨ st.peer = "bob")
    (hns : st.ns = 0 ∨ st.ns = 1 ∨ st.ns = 2)
    (hpn : st.pn = 0 ∨ st.pn = 1 ∨ st.pn = 2)
    (hc_idx : c.index = 0 ∨ c.index = 1 ∨ c.index = 2)
    (hrecv : st.recv = [c])
    (hmyIk : SafeMemo mode S g pts st.myIk)
    (hpeerIk : SafeMemo mode S g pts st.peerIk)
    (hrk : SafeMemo mode S g pts st.rk)
    (hdhs : SafeMemo mode S g pts st.dhs)
    (hcks : SafeMemo mode S g pts st.cks)
    (hsid : SafeMemo mode S g pts st.sid)
    (hspqr : SafeMemo mode S g pts st.spqr)
    (hcrk : SafeMemo mode S g pts c.ratchetKey)
    (hcck : SafeMemo mode S g pts c.chainKey)
    (htail : SafeMemo mode S g pts (recvTailTerm c))
    (hanc : noAiSuffix (gamma compI7003 S g c.chainKey ++ gamma compI7003 S g (recvTailTerm c)) = true) :
    SafeMemo mode S g pts (DY.Comparse.serialize (⟨me, st⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  obtain ⟨ha_no, ha_pos, hb_no, hb_pos⟩ := participant_str_ok
  refine safeMemo_trState_of_noAiSuffix ?_ (fun p hp => ?_)
  · dsimp only [stateAnchorPair]; rw [hrecv]; exact hanc
  · dsimp only [trStateProxyRoots, stateAnchorPair] at hp
    rw [hrecv] at hp
    simp only [List.getLast?_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (((((((((hb1 | hb2) | hs_me) | hs_peer) | h5) | hu_ns) | hu_pn) | rfl) | hsn_r) | h4) | hrc
    · exact (safeMemo_mem_bool true hb1).1
    · exact (safeMemo_mem_bool false hb2).1
    · rcases hme with rfl | rfl
      · exact (safeMemo_mem_slowString ha_no ha_pos hs_me).1
      · exact (safeMemo_mem_slowString hb_no hb_pos hs_me).1
    · rcases hpeer with hp_eq | hp_eq
      · rw [hp_eq] at hs_peer; exact (safeMemo_mem_slowString ha_no ha_pos hs_peer).1
      · rw [hp_eq] at hs_peer; exact (safeMemo_mem_slowString hb_no hb_pos hs_peer).1
    · rcases h5 with rfl | rfl | rfl | rfl | rfl <;> assumption
    · exact (safeMemo_mem_uint32_small hns hu_ns).1
    · exact (safeMemo_mem_uint32_small hpn hu_pn).1
    · exact hsid
    · exact (safeMemo_mem_slowNat st.rIdx hsn_r).1
    · rcases h4 with rfl | rfl | rfl | rfl
      · exact hspqr
      · exact safeMemo_bytesLike_empty.1
      · exact hcck
      · exact htail
    · rcases hrc with ((rfl | rfl) | hu_ci) | hsn_cr
      · exact hcrk
      · exact hcck
      · exact (safeMemo_mem_uint32_small hc_idx hu_ci).1
      · exact (safeMemo_mem_slowNat c.rIdx hsn_cr).1

theorem safeMemo_stA0 {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes mode S pts cl₁ cl₃) :
    SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts
      (DY.Comparse.serialize (⟨"alice", stA0Pure⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  obtain ⟨htail, u, hu, hgt⟩ := safeMemo_recvTailTerm_0_1 (mode := mode) (S := S)
    (g := gClean7003 mode cl₁ cl₃) (pts := pts) o1Pure.spk o1Pure.keys.ck
  exact safeMemo_trState_oneRecv "alice" stA0Pure _
    (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) rfl
    (safeMemo_of_termAt cn.ik0s) (safeMemo_of_termAt cn.ik1s)
    (safeMemo_of_termAt cn.stA0Rk) (safeMemo_of_termAt cn.dhsA)
    (safeMemo_of_termAt cn.stA0Cks) (safeMemo_of_termAt cn.sid) cn.spqrA0_safe
    (safeMemo_of_termAt cn.pk2) (safeMemo_of_termAt cn.ckInit) htail
    (by dsimp only; rw [gamma_of_termAt cn.ckInit, hgt]; rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

theorem safeMemo_stA1 {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes mode S pts cl₁ cl₃) :
    SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts
      (DY.Comparse.serialize (⟨"alice", stA1Pure cl₁⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  obtain ⟨htail, u, hu, hgt⟩ := safeMemo_recvTailTerm_0_1 (mode := mode) (S := S)
    (g := gClean7003 mode cl₁ cl₃) (pts := pts) o1Pure.spk o1Pure.keys.ck
  exact safeMemo_trState_oneRecv "alice" (stA1Pure cl₁) _
    (Or.inl rfl) (Or.inr rfl) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inl rfl) rfl
    (safeMemo_of_termAt cn.ik0s) (safeMemo_of_termAt cn.ik1s)
    (safeMemo_of_termAt cn.stA0Rk) (safeMemo_of_termAt cn.dhsA)
    (safeMemo_of_termAt cn.stA1Cks) (safeMemo_of_termAt cn.sid) cn.spqrA1_safe
    (safeMemo_of_termAt cn.pk2) (safeMemo_of_termAt cn.ckInit) htail
    (by dsimp only; rw [gamma_of_termAt cn.ckInit, hgt]; rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

theorem safeMemo_stB1 {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes mode S pts cl₁ cl₃) :
    SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts
      (DY.Comparse.serialize (⟨"bob", stB1Pure cl₁⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  have hcB'_eq : cB'Pure cl₁ =
      { ratchetKey := dhPk (tRnd 24 32),
        chainKey := (cB'Pure cl₁).chainKey, index := 1, rIdx := 2 } := rfl
  obtain ⟨htail, u, hu, hgt⟩ := safeMemo_recvTailTerm_1_2 (mode := mode) (S := S)
    (g := gClean7003 mode cl₁ cl₃) (pts := pts)
    (dhPk (tRnd 24 32)) (cB'Pure cl₁).chainKey
  have hcck : TermAt mode S (gClean7003 mode cl₁ cl₃) pts (cB'Pure cl₁).chainKey stA1CksId :=
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators.termAt_congr
      (cB'Pure_chainKey_eq cl₁) cn.stA1Cks
  have hsid : SafeMemo mode S (gClean7003 mode cl₁ cl₃) pts (stB1Pure cl₁).sid := by
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.stB1Pure_sid_eq]
    exact safeMemo_of_termAt cn.sid
  exact safeMemo_trState_oneRecv "bob" (stB1Pure cl₁) (cB'Pure cl₁)
    (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr (Or.inl rfl)) rfl
    (safeMemo_of_termAt cn.ik1s) (safeMemo_of_termAt cn.ik0s)
    (safeMemo_of_termAt cn.stB1Rk) (safeMemo_of_termAt cn.dhsB)
    (safeMemo_of_termAt cn.stB1Cks) hsid cn.spqrB1_safe
    (safeMemo_of_termAt cn.pk4) (safeMemo_of_termAt hcck) (hcB'_eq ▸ htail)
    (by rw [gamma_of_termAt hcck, hcB'_eq, hgt]; rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

theorem safeMemo_stB2 {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes true S pts cl₁ cl₃)
    (mn : Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.M2Nodes S pts cl₁ cl₃) :
    SafeMemo true S (gClean7003 true cl₁ cl₃) pts
      (DY.Comparse.serialize (⟨"bob", stB2Pure cl₁ cl₃⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  have hcB'_eq : cB'Pure cl₁ =
      { ratchetKey := dhPk (tRnd 24 32),
        chainKey := (cB'Pure cl₁).chainKey, index := 1, rIdx := 2 } := rfl
  obtain ⟨htail, u, hu, hgt⟩ := safeMemo_recvTailTerm_1_2 (mode := true) (S := S)
    (g := gClean7003 true cl₁ cl₃) (pts := pts)
    (dhPk (tRnd 24 32)) (cB'Pure cl₁).chainKey
  have hcck : TermAt true S (gClean7003 true cl₁ cl₃) pts (cB'Pure cl₁).chainKey stA1CksId :=
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators.termAt_congr
      (cB'Pure_chainKey_eq cl₁) cn.stA1Cks
  have hsid : SafeMemo true S (gClean7003 true cl₁ cl₃) pts (stB2Pure cl₁ cl₃).sid := by
    change SafeMemo true S _ pts (stB1Pure cl₁).sid
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.stB1Pure_sid_eq]
    exact safeMemo_of_termAt cn.sid
  exact safeMemo_trState_oneRecv "bob" (stB2Pure cl₁ cl₃) (cB'Pure cl₁)
    (Or.inr rfl) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)) rfl
    (safeMemo_of_termAt cn.ik1s) (safeMemo_of_termAt cn.ik0s)
    (safeMemo_of_termAt cn.stB1Rk) (safeMemo_of_termAt cn.dhsB)
    (safeMemo_of_termAt mn.stB2Cks) hsid mn.spqrB2_safe
    (safeMemo_of_termAt cn.pk4) (safeMemo_of_termAt hcck) (hcB'_eq ▸ htail)
    (by rw [gamma_of_termAt hcck, hcB'_eq, hgt]; rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
