/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.DagCert

/-!
# DAG Parameterized Term & `DagSafeMemo` Combinators
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

section Step1DagSafeMemo

open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain TRSignalMsg trHonestWireMsg messageVersion spqrA2B spqrB2A lit litByte
   hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys kdfCk computeMac)
open DY.Libsignal.Composed.Refinement
  (TrialCtx trialTerms trWireBytes litOf clamp ofByteArray node opaqueNode spqrKeyNode
   concretizeLit concretizeConcat concretizeDhPk concretizeDh concretizeKdf
   concretizeSym concretizeTrunc concretizeTrWire concretizeKemEncap concretizeKemSS
   concretizeKemPk concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrChainKey concretizeSpqrSendState
   concretizeSpqrSendKey concretizeSpqrSendMsg concretizeSpqrRecvState concretizeSpqrRecvKey
   sigFuns spqrFuns allFuns)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compLookupPub compLookupDh compAesPerm compKyberEncaps bytesToNat)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compI0_publicKey compI0_agreement compI0_aesEncrypt compI0_kyberEncaps compLookupDh_comm)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)


section ParamCombinators

variable {dagSize_p : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
variable {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}

theorem topo_of_nodes (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true) :
    ∀ i < dagSize_p, (opOf i).childrenLt i = true := by
  intro i hi
  have h := hNodes i hi
  unfold compDagNodeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem bytesOk_of_nodes (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {id : Nat} (hid : id < dagSize_p) :
    compDagOpBytesOk bytesOf id (opOf id) = true := by
  have h := hNodes id hid
  unfold compDagNodeOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem safeMemo_mono_pts {pts₁ pts₂ : List DY.Bytes} {b : DY.Bytes}
    (hsub : ∀ p ∈ pts₁, p ∈ pts₂)
    (h : SafeMemo dagSize_p opOf bytesOf S g pts₁ b) :
    SafeMemo dagSize_p opOf bytesOf S g pts₂ b := by
  intro x hx
  rcases h x hx with ⟨hm, hl⟩ | hsp | hdag
  · exact Or.inl ⟨hsub _ hm, hl⟩
  · exact Or.inr (Or.inl hsp)
  · exact Or.inr (Or.inr hdag)

theorem safeMemo_plaintext {ts : Nat}
    (hmem : randTerm ts 32 ∈ pts) (hlen : (g.σ ts 32).length < 8) :
    SafeMemo dagSize_p opOf bytesOf S g pts (randTerm ts 32) := by
  intro x hx
  rw [gamma'_randTerm compI0 S g ts 32 (by decide), List.mem_singleton] at hx
  subst hx
  exact Or.inl ⟨hmem, hlen⟩

theorem safeMemo_lit_short {ba : ByteArray} (hlen : ba.size < 8) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Literal.literalToBytes ba) := by
  intro x hx
  have hg : gamma' compI0 S g (DY.Literal.literalToBytes ba) =
      concretizeLit { lit := ba } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g) { lit := ba }
  rw [hg] at hx
  simp only [concretizeLit, node, List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  have hai : assumedInjective (DY.Literal.literalToBytes ba) = false := by
    unfold DY.Literal.literalToBytes; exact assumedInjective_lit { lit := ba }
  refine Or.inr (Or.inl ⟨hai, Or.inl ?_⟩)
  dsimp only [ofByteArray]
  rw [List.length_map, Array.length_toList]
  exact hlen

theorem safeMemo_randTerm_zero (ts : Nat) :
    SafeMemo dagSize_p opOf bytesOf S g pts (randTerm ts 0) := by
  intro x hx
  unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI0 S g)] at hx
  simp only [concretizeRandom, ↓reduceIte] at hx
  cases hx

theorem concat_gamma' (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (a b : DY.Bytes) :
    gamma' i S g (DY.Concat.concat a b) =
      concretizeConcat ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes)
        (fun y _ => gamma' i S g y) :=
  DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)
    ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes)

theorem termAt_of_node {b : DY.Bytes} {id : Nat}
    {cs : List DY.Libsignal.Composed.Refinement.ConcretizedTerm}
    (hid : id < dagSize_p)
    (hg : gamma' compI0 S g b = node (bytesOf id) b (dagShape opOf dagSize_p id) cs)
    (hai : assumedInjective b = true → (opOf id).isAI = true)
    (hcs : ∀ c ∈ cs, ∀ x ∈ c.memo, SafeEntry dagSize_p opOf bytesOf pts x) :
    TermAt dagSize_p opOf bytesOf S g pts b id := by
  refine ⟨hid, by rw [hg]; rfl, by rw [hg]; rfl, ?_⟩
  intro x hx
  rw [hg] at hx
  simp only [node, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨c, hc, hxc⟩
  · exact Or.inr (Or.inr ⟨id, hid, rfl, rfl, hai⟩)
  · exact hcs c hc x hxc

theorem termAt_lit (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {ba : ByteArray} {id : Nat} (hid : id < dagSize_p)
    (hop : opOf id = .lit (ofByteArray ba)) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.Literal.literalToBytes ba) id := by
  set v := ofByteArray ba
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  have hba : DY.Literal.literalToBytes ba = litOf v := by
    unfold litOf DY.Literal.literalToBytes
    congr 1; apply ByteArray.ext
    change ba.data = (v.map UInt8.ofBitVec).toArray
    rw [← Array.toList_inj, List.toList_toArray]
    change ba.data.toList = (ba.data.toList.map UInt8.toBitVec).map UInt8.ofBitVec
    induction ba.data.toList with
    | nil => rfl
    | cons u us ih => exact congrArg (u :: ·) ih
  have hg : gamma' compI0 S g (DY.Literal.literalToBytes ba) =
      concretizeLit { lit := ba } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq concretizeLit (concretizeAll compI0 S g) { lit := ba }
  apply termAt_of_node hid (cs := [])
  · rw [hg]; unfold concretizeLit
    change node v (DY.Literal.literalToBytes ba) (DY.Literal.literalToBytes ba) [] = _
    rw [← hbok, hsh, ← hba]
  · intro h
    rw [show DY.Literal.literalToBytes ba = ({ lit := ba } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
      assumedInjective_lit] at h
    cases h
  · intro _ hc; cases hc

theorem termAt_litOf (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {v : HwBytes} {id : Nat} (hid : id < dagSize_p) (hop : opOf id = .lit v) :
    TermAt dagSize_p opOf bytesOf S g pts (litOf v) id := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons b bs ih => exact congrArg (b :: ·) ih
  let ba := ByteArray.mk (v.map UInt8.ofBitVec).toArray
  have hv : ofByteArray ba = v := hv_aux v
  exact termAt_lit hNodes hid (hop.trans (congrArg DagOp.lit hv.symm))

theorem randTerm_eq_dagShape (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize_p) (hop : opOf id = .rand ts sz) :
    randTerm ts sz = dagShape opOf dagSize_p id := by
  rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]

theorem termAt_rand (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize_p) (hop : opOf id = .rand ts sz)
    (hσ : g.σ ts sz = bytesOf id) :
    TermAt dagSize_p opOf bytesOf S g pts (randTerm ts sz) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, decide_eq_true_eq] at hbok
  have hsh : dagShape opOf dagSize_p id = randTerm ts sz := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  apply termAt_of_node hid (cs := [])
  · rw [gamma'_randTerm compI0 S g ts sz hbok, hσ, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro _ hc; cases hc

theorem termAt_concat (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {a b : DY.Bytes} {l r id : Nat} (hid : id < dagSize_p) (hop : opOf id = .concat l r)
    (ha : TermAt dagSize_p opOf bytesOf S g pts a l)
    (hb : TermAt dagSize_p opOf bytesOf S g pts b r) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.Concat.concat a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id =
      DY.Concat.concat (dagShape opOf dagSize_p l) (dagShape opOf dagSize_p r) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  apply termAt_of_node hid (cs := [gamma' compI0 S g a, gamma' compI0 S g b])
  · rw [concat_gamma' compI0 S g a b]; unfold concretizeConcat; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro h
    rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      assumedInjective_concat] at h
    cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_dhPk (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {sk : DY.Bytes} {s id : Nat} (hid : id < dagSize_p) (hop : opOf id = .dhPk s)
    (hs : TermAt dagSize_p opOf bytesOf S g pts sk s) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id = DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg : gamma' compI0 S g (DY.DiffieHellman.dhPk sk) =
      concretizeDhPk compI0 { sk := sk } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq (concretizeDhPk compI0) (concretizeAll compI0 S g) { sk := sk }
  apply termAt_of_node hid (cs := [gamma' compI0 S g sk])
  · rw [hg]; unfold concretizeDhPk; dsimp only
    rw [hs.2.1, hs.2.2.1, hsh, compI0_publicKey, Option.getD_some, ← hbok]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact hs.2.2.2 x hxc

theorem termAt_dh (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : DY.Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize_p) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize_p s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize_p s2_id)
    (hs1 : TermAt dagSize_p opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize_p opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk1) sk2) id := by
  subst hsh1 hsh2
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hbpk1 := bytesOk_of_nodes hNodes hp1.1
  rw [hop_pk1] at hbpk1; simp only [compDagOpBytesOk, beq_iff_eq] at hbpk1
  have hbpk2 := bytesOk_of_nodes hNodes hp2.1
  rw [hop_pk2] at hbpk2; simp only [compDagOpBytesOk, beq_iff_eq] at hbpk2
  have hsh_pk1 : dagShape opOf dagSize_p pk1_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp1.1]; simp only [evalDagShapeAux, hop_pk1]; rfl
  have hsh_pk2 : dagShape opOf dagSize_p pk2_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp2.1]; simp only [evalDagShapeAux, hop_pk2]; rfl
  have hsh_id : dagShape opOf dagSize_p id =
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id))
        (dagShape opOf dagSize_p s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
    change DY.DiffieHellman.dh (dagShape opOf dagSize_p pk1_id) (dagShape opOf dagSize_p s2_id) = _
    rw [hsh_pk1]
  by_cases hge : dagShape opOf dagSize_p s2_id ≤ dagShape opOf dagSize_p s1_id
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id))
        (dagShape opOf dagSize_p s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id),
           sk := dagShape opOf dagSize_p s2_id } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk,
        _root_.DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg : gamma' compI0 S g
        (({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id),
             sk := dagShape opOf dagSize_p s2_id } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
        concretizeDh compI0
          { pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id),
             sk := dagShape opOf dagSize_p s2_id }
          (fun y _ => gamma' compI0 S g y) :=
      DY.Bytes.rec_eq (concretizeDh compI0) (concretizeAll compI0 S g) _
    apply termAt_of_node hid
      (cs := [gamma' compI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id)),
              gamma' compI0 S g (dagShape opOf dagSize_p s2_id)])
    · rw [hg]; unfold concretizeDh; dsimp only
      rw [hp1.2.1, hs2.2.1, hp1.2.2.1, hs2.2.2.1, hsh_pk1, hsh, compI0_agreement, Option.getD_some, ← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp1.2.2.2 x hxc
      · exact hs2.2.2.2 x hxc
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s1_id))
        (dagShape opOf dagSize_p s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s2_id),
           sk := dagShape opOf dagSize_p s1_id } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk,
        _root_.DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg : gamma' compI0 S g
        (({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s2_id),
             sk := dagShape opOf dagSize_p s1_id } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
        concretizeDh compI0
          { pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s2_id),
             sk := dagShape opOf dagSize_p s1_id }
          (fun y _ => gamma' compI0 S g y) :=
      DY.Bytes.rec_eq (concretizeDh compI0) (concretizeAll compI0 S g) _
    apply termAt_of_node hid
      (cs := [gamma' compI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize_p s2_id)),
              gamma' compI0 S g (dagShape opOf dagSize_p s1_id)])
    · rw [hg]; unfold concretizeDh; dsimp only
      rw [hp2.2.1, hs1.2.1, hp2.2.2.1, hs1.2.2.1, hsh_pk2, hsh, compI0_agreement, Option.getD_some,
        hbpk2, compLookupDh_comm, ← hbpk1, ← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp2.2.2.2 x hxc
      · exact hs1.2.2.2 x hxc

theorem termAt_dh_symm (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : DY.Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize_p) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize_p s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize_p s2_id)
    (hs1 : TermAt dagSize_p opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize_p opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk2) sk1) id := by
  rw [DY.DiffieHellman.dh_commutes]
  exact termAt_dh hNodes hid hop hop_pk1 hop_pk2 hsh1 hsh2 hs1 hp1 hs2 hp2

theorem termAt_kdf (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {a b : DY.Bytes} {a_id b_id id : Nat} (hid : id < dagSize_p) (hop : opOf id = .kdf a_id b_id)
    (ha : TermAt dagSize_p opOf bytesOf S g pts a a_id)
    (hb : TermAt dagSize_p opOf bytesOf S g pts b b_id) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.KdfExtract.kdfExtract a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id =
      DY.KdfExtract.kdfExtract (dagShape opOf dagSize_p a_id) (dagShape opOf dagSize_p b_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg : gamma' compI0 S g (DY.KdfExtract.kdfExtract a b) =
      concretizeKdf compI0 { salt := a, ikm := b } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq (concretizeKdf compI0) (concretizeAll compI0 S g) { salt := a, ikm := b }
  apply termAt_of_node hid (cs := [gamma' compI0 S g a, gamma' compI0 S g b])
  · rw [hg]; unfold concretizeKdf; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_trunc8 (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {a : DY.Bytes} {a_id id : Nat} (hid : id < dagSize_p) (hop : opOf id = .trunc8 a_id)
    (ha : TermAt dagSize_p opOf bytesOf S g pts a a_id) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.Trunc.trunc8 a) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id = DY.Trunc.trunc8 (dagShape opOf dagSize_p a_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg : gamma' compI0 S g (DY.Trunc.trunc8 a) =
      concretizeTrunc { input := a } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq concretizeTrunc (concretizeAll compI0 S g) { input := a }
  apply termAt_of_node hid (cs := [gamma' compI0 S g a])
  · rw [hg]; unfold concretizeTrunc; dsimp only
    rw [ha.2.1, ← hbok, ha.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact ha.2.2.2 x hxc

theorem termAt_symEncPt (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {k iv : DY.Bytes} {k_id iv_id ptTs id : Nat} {ptBs : HwBytes}
    (hid : id < dagSize_p) (hop : opOf id = .symEncPt k_id iv_id ptTs ptBs)
    (hk : TermAt dagSize_p opOf bytesOf S g pts k k_id)
    (hiv : TermAt dagSize_p opOf bytesOf S g pts iv iv_id)
    (hpt_mem : randTerm ptTs 32 ∈ pts) (hσ : g.σ ptTs 32 = ptBs) (hlen : ptBs.length < 8) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id =
      DY.SymEnc.symEnc (dagShape opOf dagSize_p k_id) (dagShape opOf dagSize_p iv_id) (randTerm ptTs 32) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hgpt := gamma'_randTerm compI0 S g ptTs 32 (by decide)
  have hpt_bs : (gamma' compI0 S g (randTerm ptTs 32)).bytes = ptBs := by rw [hgpt]; exact hσ
  have hpt_sh : (gamma' compI0 S g (randTerm ptTs 32)).shape = randTerm ptTs 32 := by rw [hgpt]
  have hpt_sm : SafeMemo dagSize_p opOf bytesOf S g pts (randTerm ptTs 32) :=
    safeMemo_plaintext hpt_mem (by rw [hσ]; exact hlen)
  have hg : gamma' compI0 S g (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) =
      concretizeSym compI0 { key := k, iv := iv, msg := randTerm ptTs 32 } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq (concretizeSym compI0) (concretizeAll compI0 S g) _
  apply termAt_of_node hid
    (cs := [gamma' compI0 S g k, gamma' compI0 S g iv, gamma' compI0 S g (randTerm ptTs 32)])
  · rw [hg]; unfold concretizeSym; dsimp only
    rw [hk.2.1, hiv.2.1, hpt_bs, hk.2.2.1, hiv.2.2.1, hpt_sh, hsh, compI0_aesEncrypt, Option.getD_some, ← hbok]
    rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hk.2.2.2 x hxc
    · exact hiv.2.2.2 x hxc
    · exact hpt_sm x hxc

theorem termAt_trWire (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {rk ct pq : DY.Bytes} {cnt prev : UInt32} {rk_id ct_id pq_id id : Nat} {addr : HwBytes}
    (hid : id < dagSize_p) (hop : opOf id = .trWire messageVersion rk_id cnt prev ct_id pq_id addr)
    (hrk : TermAt dagSize_p opOf bytesOf S g pts rk rk_id)
    (hct : TermAt dagSize_p opOf bytesOf S g pts ct ct_id)
    (hpq : TermAt dagSize_p opOf bytesOf S g pts pq pq_id)
    (haddr : g.addr (trHonestWireMsg rk cnt prev ct pq) = addr) :
    TermAt dagSize_p opOf bytesOf S g pts (trHonestWireMsg rk cnt prev ct pq) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id =
      DY.TrWire.trWireMsg messageVersion (dagShape opOf dagSize_p rk_id) cnt prev
        (dagShape opOf dagSize_p ct_id) (dagShape opOf dagSize_p pq_id)
        { canonicalVariation with fields := .extra 6 (.bytes addr) 0 0 :: canonicalVariation.fields } := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg : gamma' compI0 S g (trHonestWireMsg rk cnt prev ct pq) =
      concretizeTrWire g
        { version := messageVersion, senderRatchetKey := rk, counter := cnt,
           previousCounter := prev, ciphertext := ct, pqRatchet := pq,
           encodingVariation := DY.TrWire.canonicalVariation }
        (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll compI0 S g) _
  have haddr' : g.addr
      ({ version := messageVersion, senderRatchetKey := rk, counter := cnt,
          previousCounter := prev, ciphertext := ct, pqRatchet := pq,
          encodingVariation := DY.TrWire.canonicalVariation } :
        DY.TrWire.TrWireMsg.SubF DY.Bytes).pack = addr := haddr
  apply termAt_of_node hid
    (cs := [gamma' compI0 S g rk, gamma' compI0 S g ct, gamma' compI0 S g pq])
  · rw [hg]; unfold concretizeTrWire; dsimp only
    rw [haddr', hrk.2.1, hct.2.1, hpq.2.1, ← hbok, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hsh]; rfl
  · intro h
    have hw := assumedInjective_trWire'
      { version := messageVersion, senderRatchetKey := rk, counter := cnt,
         previousCounter := prev, ciphertext := ct, pqRatchet := pq,
         encodingVariation := DY.TrWire.canonicalVariation }
    change assumedInjective (trHonestWireMsg rk cnt prev ct pq) = false at hw
    rw [hw] at h; cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hrk.2.2.2 x hxc
    · exact hct.2.2.2 x hxc
    · exact hpq.2.2.2 x hxc

theorem termAt_kemEncap (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {pk e : DY.Bytes} {p_id e_id id1 id2 : Nat}
    (hid1 : id1 < dagSize_p) (hop1 : opOf id1 = .kemEncap p_id e_id)
    (hid2 : id2 < dagSize_p) (hop2 : opOf id2 = .kemSS p_id e_id)
    (hp : TermAt dagSize_p opOf bytesOf S g pts pk p_id)
    (he : TermAt dagSize_p opOf bytesOf S g pts e e_id) :
    TermAt dagSize_p opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).1 id1 ∧
      TermAt dagSize_p opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).2 id2 := by
  have hbok1 := bytesOk_of_nodes hNodes hid1
  rw [hop1] at hbok1
  simp only [compDagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok1
  have hbok2 := bytesOk_of_nodes hNodes hid2
  rw [hop2] at hbok2
  simp only [compDagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok2
  have hsh1 : dagShape opOf dagSize_p id1 =
      ({ pk := dagShape opOf dagSize_p p_id, entropy := dagShape opOf dagSize_p e_id } :
        DY.PQKem.Encap.SubF DY.Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid1]; simp only [evalDagShapeAux, hop1]; rfl
  have hsh2 : dagShape opOf dagSize_p id2 =
      ({ pk := dagShape opOf dagSize_p p_id, entropy := dagShape opOf dagSize_p e_id } :
        DY.PQKem.SharedSecret.SubF DY.Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid2]; simp only [evalDagShapeAux, hop2]; rfl
  constructor
  · have hg1 : gamma' compI0 S g (DY.PQKem.kemEncap pk e).1 =
        concretizeKemEncap compI0 { pk := pk, entropy := e } (fun y _ => gamma' compI0 S g y) :=
      DY.Bytes.rec_eq (concretizeKemEncap compI0) (concretizeAll compI0 S g) { pk := pk, entropy := e }
    apply termAt_of_node hid1 (cs := [gamma' compI0 S g pk, gamma' compI0 S g e])
    · rw [hg1]; unfold concretizeKemEncap; dsimp only
      simp only [he.2.1, hbok1.1, ↓reduceIte, compI0_kyberEncaps, Option.getD_some, hp.2.2.1, he.2.2.1, hsh1, ← hbok1.2]
      rfl
    · intro _; rw [hop1]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc
  · have hg2 : gamma' compI0 S g (DY.PQKem.kemEncap pk e).2 =
        concretizeKemSS compI0 S { pk := pk, entropy := e } (fun y _ => gamma' compI0 S g y) :=
      DY.Bytes.rec_eq (concretizeKemSS compI0 S) (concretizeAll compI0 S g) { pk := pk, entropy := e }
    apply termAt_of_node hid2 (cs := [gamma' compI0 S g pk, gamma' compI0 S g e])
    · rw [hg2]; unfold concretizeKemSS; dsimp only
      simp only [he.2.1, hbok2.1, ↓reduceIte, compI0_kyberEncaps, Option.getD_some, hp.2.2.1, he.2.2.1, hsh2, ← hbok2.2]
      rfl
    · intro _; rw [hop2]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc

theorem termAt_of_opaque (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {b : DY.Bytes} {v : HwBytes} {id : Nat} (hid : id < dagSize_p) (hop : opOf id = .lit v)
    (hbs : (gamma' compI0 S g b).bytes = v)
    (hsh_b : (gamma' compI0 S g b).shape = litOf v)
    (hsm : SafeMemo dagSize_p opOf bytesOf S g pts b) :
    TermAt dagSize_p opOf bytesOf S g pts b id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [compDagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize_p id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  exact ⟨hid, hbs.trans hbok.symm, hsh_b.trans hsh.symm, hsm⟩

theorem safeMemo_kemPk {sk : DY.Bytes}
    (hsk : SafeMemo dagSize_p opOf bytesOf S g pts sk) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.PQKem.kemPk sk) := by
  intro x hx
  unfold gamma' at hx
  rw [show DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeKemPk, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  exact hsk x hx

theorem safeMemo_vk {sk : DY.Bytes}
    (hsk : SafeMemo dagSize_p opOf bytesOf S g pts sk) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Signature.vk sk) := by
  intro x hx
  unfold gamma' at hx
  rw [show DY.Signature.vk sk = ({ sk := sk } : DY.Signature.Vk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeVk S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeVk, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  exact hsk x hx

theorem safeMemo_sign {sk nonce msg : DY.Bytes}
    (hsk : SafeMemo dagSize_p opOf bytesOf S g pts sk)
    (hn : SafeMemo dagSize_p opOf bytesOf S g pts nonce)
    (hm : SafeMemo dagSize_p opOf bytesOf S g pts msg) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Signature.sign sk nonce msg) := by
  intro x hx
  unfold gamma' at hx
  rw [show DY.Signature.sign sk nonce msg =
      ({ sk := sk, nonce := nonce, msg := msg } : DY.Signature.Sign.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeSign S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSign, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  rcases hx with h1 | h2 | h3
  · exact hsk x h1
  · exact hn x h2
  · exact hm x h3

theorem safeMemo_spqrInit {k p : DY.Bytes}
    (hk : SafeMemo dagSize_p opOf bytesOf S g pts k)
    (hp : SafeMemo dagSize_p opOf bytesOf S g pts p) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrInit k p) := by
  intro x hx
  unfold gamma' DY.Spqr.spqrInit at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  exact hx.elim (hk x) (hp x)

theorem safeMemo_spqrInit_elim {k p : DY.Bytes}
    (h : SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrInit k p)) :
    SafeMemo dagSize_p opOf bytesOf S g pts k ∧ SafeMemo dagSize_p opOf bytesOf S g pts p := by
  have hg : gamma' compI0 S g (DY.Spqr.spqrInit k p) =
      concretizeSpqrInit S { authKey := k, params := p } (fun y _ => gamma' compI0 S g y) :=
    DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI0 S g) _
  refine ⟨fun x hx => h x ?_, fun x hx => h x ?_⟩ <;>
    (rw [hg]; simp only [concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]; tauto)

theorem safeMemo_spqrChainKey {k p idx : DY.Bytes}
    (hk : SafeMemo dagSize_p opOf bytesOf S g pts k)
    (hp : SafeMemo dagSize_p opOf bytesOf S g pts p)
    (hi : SafeMemo dagSize_p opOf bytesOf S g pts idx) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrChainKey k p idx) := by
  intro x hx
  unfold gamma' DY.Spqr.spqrChainKey at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrChainKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  rcases hx with h1 | h2 | h3
  · exact hk x h1
  · exact hp x h2
  · exact hi x h3

theorem safeMemo_spqrSend {st coins : DY.Bytes}
    (hst : SafeMemo dagSize_p opOf bytesOf S g pts st)
    (hc : SafeMemo dagSize_p opOf bytesOf S g pts coins) :
    SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).1 ∧
      SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.1 ∧
      SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.2 := by
  have hs1 : SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).1 := by
    intro x hx
    unfold gamma' DY.Spqr.spqrSend at hx; dsimp only at hx
    rw [DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll compI0 S g)] at hx
    simp only [concretizeSpqrSendState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
    exact hx.elim (hst x) (hc x)
  have hs3 : SafeMemo dagSize_p opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.2 := by
    intro x hx
    unfold gamma' DY.Spqr.spqrSend at hx; dsimp only at hx
    rw [DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll compI0 S g)] at hx
    simp only [concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
    exact hx.elim (hst x) (hc x)
  refine ⟨hs1, ?_, hs3⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · next authKey params hx =>
    have hst' := hst
    rw [hx] at hpv; rw [← hpv] at hst'
    obtain ⟨ha, hp⟩ := safeMemo_spqrInit_elim hst'
    refine safeMemo_spqrChainKey ha hp ?_
    cases DY.Spqr.spqrParamsDir? params with
    | none => exact safeMemo_lit_short (by decide)
    | some d => cases d <;> exact safeMemo_lit_short (by decide)
  · intro x hx
    unfold gamma' at hx
    rw [DY.Bytes.rec_eq (concretizeSpqrSendKey S) (concretizeAll compI0 S g)] at hx
    simp only [concretizeSpqrSendKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
    exact hx.elim (hst x) (hc x)

theorem safeMemo_spqrRecvState_pack {st msg : DY.Bytes}
    (hst : SafeMemo dagSize_p opOf bytesOf S g pts st)
    (hmsg : SafeMemo dagSize_p opOf bytesOf S g pts msg) :
    SafeMemo dagSize_p opOf bytesOf S g pts (({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack) := by
  intro x hx
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrRecvState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  exact hx.elim (hst x) (hmsg x)

theorem safeMemo_spqrRecvKey_pack {st msg : DY.Bytes}
    (hst : SafeMemo dagSize_p opOf bytesOf S g pts st)
    (hmsg : SafeMemo dagSize_p opOf bytesOf S g pts msg) :
    SafeMemo dagSize_p opOf bytesOf S g pts (({ st := st, msg := msg } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) := by
  intro x hx
  unfold gamma' at hx
  rw [DY.Bytes.rec_eq (concretizeSpqrRecvKey S) (concretizeAll compI0 S g)] at hx
  simp only [concretizeSpqrRecvKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx
  exact hx.elim (hst x) (hmsg x)

theorem safeMemo_spqrRecv
    (hZero : SafeMemo dagSize_p opOf bytesOf S g pts DY.Spqr.zeroKey)
    {st msg st' key : DY.Bytes} {idx : UInt32}
    (hst : SafeMemo dagSize_p opOf bytesOf S g pts st)
    (hmsg : SafeMemo dagSize_p opOf bytesOf S g pts msg)
    (hrecv : DY.Spqr.spqrRecv st msg idx = some (st', key)) :
    SafeMemo dagSize_p opOf bytesOf S g pts st' ∧
      SafeMemo dagSize_p opOf bytesOf S g pts key := by
  unfold DY.Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
    cases hv : st.view? DY.Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'; injection hrecv' with hst_eq hkey
      subst hst_eq hkey
      exact ⟨safeMemo_spqrRecvState_pack hst hmsg, safeMemo_spqrRecvKey_pack hst hmsg⟩
    | some x =>
      rw [hv] at hrecv hp
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv hp
      have hst' := hst; rw [← hp] at hst'
      obtain ⟨hk, _⟩ := safeMemo_spqrInit_elim hst'
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'; injection hrecv' with hst_eq hkey
        subst hst_eq hkey
        refine ⟨safeMemo_spqrRecvState_pack hst hmsg, ?_⟩
        split
        · exact hZero
        · refine safeMemo_spqrChainKey hk ?_ ?_
          · cases dir <;> exact safeMemo_lit_short (by decide)
          · unfold DY.Spqr.encodeSpqrIndexTerm; exact safeMemo_lit_short (by simp [ByteArray.size])

theorem local_symDec_eq_some (key iv ct msg : DY.Bytes)
    (h : DY.SymEnc.symDec key iv ct = some msg) : ct = DY.SymEnc.symEnc key iv msg := by
  simp only [DY.SymEnc.symEnc, DY.SymEnc.symDec] at h ⊢
  split at h
  · rename_i key' iv' msg' heq
    have hp := DY.Bytes.pack_view? DY.SymEnc.Enc.SubF ct
    simp only [heq] at hp
    split at h <;> grind
  · cases h

theorem safeMemo_symDec {k iv ct pt : DY.Bytes}
    (hdec : DY.SymEnc.symDec k iv ct = some pt)
    (hct : SafeMemo dagSize_p opOf bytesOf S g pts ct) :
    SafeMemo dagSize_p opOf bytesOf S g pts pt := by
  rw [local_symDec_eq_some k iv ct pt hdec] at hct
  intro x hx
  apply hct x
  unfold gamma' at hx ⊢
  rw [show DY.SymEnc.symEnc k iv pt = ({ key := k, iv := iv, msg := pt } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (concretizeSym compI0) (concretizeAll compI0 S g)]
  simp only [concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr hx))

theorem termAt_computeMac (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {mk pIk mIk w : DY.Bytes} {mk_id pIk_id mIk_id w_id c1_id c2_id h_id t_id : Nat}
    (hc1 : c1_id < dagSize_p ∧ opOf c1_id = .concat mIk_id w_id)
    (hc2 : c2_id < dagSize_p ∧ opOf c2_id = .concat pIk_id c1_id)
    (hh : h_id < dagSize_p ∧ opOf h_id = .kdf mk_id c2_id)
    (ht : t_id < dagSize_p ∧ opOf t_id = .trunc8 h_id)
    (hmk : TermAt dagSize_p opOf bytesOf S g pts mk mk_id)
    (hpIk : TermAt dagSize_p opOf bytesOf S g pts pIk pIk_id)
    (hmIk : TermAt dagSize_p opOf bytesOf S g pts mIk mIk_id)
    (hw : TermAt dagSize_p opOf bytesOf S g pts w w_id) :
    TermAt dagSize_p opOf bytesOf S g pts (computeMac mk pIk mIk w) t_id := by
  unfold computeMac hmac
  exact termAt_trunc8 hNodes ht.1 ht.2
    (termAt_kdf hNodes hh.1 hh.2 hmk
      (termAt_concat hNodes hc2.1 hc2.2 hpIk
        (termAt_concat hNodes hc1.1 hc1.2 hmIk hw)))

theorem termAt_trMsgKeys (hNodes : ∀ i < dagSize_p, compDagNodeOk opOf bytesOf i = true)
    {salt seed : DY.Bytes}
    {info1_id info2_id info3_id salt_id seed_id prk_id ck_id c2_id mk_id c3_id iv_id : Nat}
    (hi1 : TermAt dagSize_p opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 1)) info1_id)
    (hi2 : TermAt dagSize_p opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 2)) info2_id)
    (hi3 : TermAt dagSize_p opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 3)) info3_id)
    (hprk : prk_id < dagSize_p ∧ opOf prk_id = .kdf salt_id seed_id)
    (hck : ck_id < dagSize_p ∧ opOf ck_id = .kdf prk_id info1_id)
    (hc2 : c2_id < dagSize_p ∧ opOf c2_id = .concat ck_id info2_id)
    (hmk : mk_id < dagSize_p ∧ opOf mk_id = .kdf prk_id c2_id)
    (hc3 : c3_id < dagSize_p ∧ opOf c3_id = .concat mk_id info3_id)
    (hiv : iv_id < dagSize_p ∧ opOf iv_id = .kdf prk_id c3_id)
    (hsalt : TermAt dagSize_p opOf bytesOf S g pts salt salt_id)
    (hseed : TermAt dagSize_p opOf bytesOf S g pts seed seed_id) :
    TermAt dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ck_id ∧
      TermAt dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).macKey mk_id ∧
      TermAt dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).iv iv_id := by
  unfold trMsgKeys hkdfBlock1 hkdfBlock2 hkdfBlock3 hmac; dsimp only
  have tprk := termAt_kdf hNodes hprk.1 hprk.2 hsalt hseed
  have tck := termAt_kdf hNodes hck.1 hck.2 tprk hi1
  have tmk := termAt_kdf hNodes hmk.1 hmk.2 tprk (termAt_concat hNodes hc2.1 hc2.2 tck hi2)
  have tiv := termAt_kdf hNodes hiv.1 hiv.2 tprk (termAt_concat hNodes hc3.1 hc3.2 tmk hi3)
  exact ⟨tck, tmk, tiv⟩

theorem safeMemo_trialTerms {salts : List DY.Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    (hextra : ∀ t ∈ ctx.extra, SafeMemo dagSize_p opOf bytesOf S g pts t)
    (hct : SafeMemo dagSize_p opOf bytesOf S g pts msg.ciphertext)
    (hbody : ∀ seed, ctx.seed? = some seed → ∀ salt ∈ salts,
      SafeMemo dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ∧
      SafeMemo dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).macKey ∧
      SafeMemo dagSize_p opOf bytesOf S g pts (trMsgKeys salt seed).iv ∧
      SafeMemo dagSize_p opOf bytesOf S g pts
        (computeMac (trMsgKeys salt seed).macKey ctx.peerIk ctx.myIk msg.wire)) :
    ∀ t ∈ trialTerms salts msg ctx, SafeMemo dagSize_p opOf bytesOf S g pts t := by
  intro t ht
  unfold trialTerms at ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hextra t ht
  · cases hs : ctx.seed? with
    | none => rw [hs] at ht; cases ht
    | some seed =>
      rw [hs, List.mem_flatMap] at ht
      rcases ht with ⟨salt, hsalt, ht⟩
      obtain ⟨hck, hmk, hiv, hmac_ok⟩ := hbody seed hs salt hsalt
      rw [List.mem_append] at ht
      rcases ht with ht | ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hck
        · exact hmk
        · exact hiv
        · exact hmac_ok
      · cases hdec : DY.SymEnc.symDec (trMsgKeys salt seed).cipherKey (trMsgKeys salt seed).iv msg.ciphertext with
        | none => rw [hdec] at ht; cases ht
        | some pt =>
          rw [hdec] at ht; simp only [Option.toList, List.mem_singleton] at ht; subst ht
          exact safeMemo_symDec hdec hct

end ParamCombinators

end Step1DagSafeMemo

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
