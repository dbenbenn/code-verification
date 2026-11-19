/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoCombinators
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Comparse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

/-!
# Per-Constructor `TermAt` and Opaque-Symbol `SafeMemo` Lemmas (`RecvMemoTermAt.lean`)

Provides compositional `TermAt` rules for all 11 `DagOp` constructors, opaque-node wrappers
(`kemPk`, `spqrInit`, `spqrSendState`, `spqrSendMsg`, `spqrChainKey`) valid for all
`S : OpaqueSymbolSemantics`, `eq_of_fast`, and `safeMemo_trState_of_anchor`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoTermAt

open scoped DY.Libsignal.Composed
open ByteSpecs (hmacWith)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol aesCbcEncryptSymbol sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost
   clamp ofByteArray litOf spqrKeyBytes trWireBytes
   node opaqueNode spqrKeyNode
   concretizeRandom concretizeLit concretizeConcat concretizeDhPk concretizeDh
   concretizeKdf concretizeSym concretizeTrunc concretizeKemPk concretizeKemEncap
   concretizeKemSS concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendMsg
   concretizeSpqrChainKey concretizeTrWire concretizeAll
   gamma' gamma assumedInjective)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
  (tRnd tLit tCat tDhPk tDh tKdf tSym tTr8 tKemEnc tKemSS tSInit tSSendSt tSSendM tSChain tTrW)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (beqBareOptFast beqBareOptFast_true)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (ai_lit_pack_eq ai_concat_eq ai_trWire_pack_eq
   concatPrefixes_nil concatPrefixes_cons slowNat_serialize_zero slowNat_serialize_succ
   slowString_serialize_eq serialize_local_pqxdh_eq_bridge)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
  (bool_serialize_singleton_head uint32_serialize_singleton_head)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compLookupDh)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhAesPt0)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagDefs
  (DagOp trWireShapeVar dagShape dagOpBytesOk dagNodeOk dagNodeOk_of_all)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData
  (dagSize opOf bytesOf shapeOf dagAllNodesOk)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoCombinators
  (notAnyAiNodeBytes noAiSuffix noStrictAiSuffix
   notAnyAiNodeBytes_of_noAiSuffix notAnyAiNodeBytes_of_noStrictAiSuffix
   SafeEntry SafeMemo TermAt)

section Unsealed
unseal DY.Bytes

theorem eq_of_fast {a b : DY.Bytes} (h : beqBareOptFast 256 a.val b.val = some true) : a = b :=
  Subtype.ext (beqBareOptFast_true 256 a.val b.val h)

private theorem ofByteArray_litOf_eq (bs : HwBytes) :
    ofByteArray ⟨(bs.map UInt8.ofBitVec).toArray⟩ = bs := by
  simp only [ofByteArray, List.map_map]
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [Function.comp, ih]

theorem literalToBytes_eq_tLit (ba : ByteArray) :
    DY.Literal.literalToBytes ba = tLit (ofByteArray ba) := by
  rcases ba with ⟨⟨lst⟩⟩
  have hl : (lst.map UInt8.toBitVec).map UInt8.ofBitVec = lst := by
    induction lst with
    | nil => rfl
    | cons u rest ih => simp [ih]
  dsimp only [DY.Literal.literalToBytes, DY.Literal.CanMkLiteral.literalToBytes,
    tLit, litOf, ofByteArray]
  rw [hl]

private theorem dagOpBytesOk_of_id {id : Nat} (hid : id < dagSize) :
    dagOpBytesOk bytesOf id (opOf id) (bytesOf id) = true := by
  have h := dagNodeOk_of_all dagAllNodesOk hid
  unfold dagNodeOk at h
  exact ((Bool.and_eq_true _ _).mp h).1

theorem safeMemo_randTerm_zero {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (ts : Nat) : SafeMemo S g pts (tRnd ts 0) := by
  intro x hx
  unfold gamma' at hx
  change x ∈ ((({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll dhRatchetI0 S g)).memo at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll dhRatchetI0 S g)
    ({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes)] at hx
  simp [concretizeRandom] at hx

theorem gamma'_plaintext_eq {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} (hg : g.σ ts 32 = dhAesPt0) :
    gamma' dhRatchetI0 S g (tRnd ts 32) =
      { bytes := dhAesPt0, shape := tRnd ts 32, memo := [(tRnd ts 32, tRnd ts 32, dhAesPt0)] } := by
  unfold gamma'
  change (({ timestamp := ts, size := 32 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll dhRatchetI0 S g) = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll dhRatchetI0 S g)
    ({ timestamp := ts, size := 32 } : DY.Random.Random DY.Bytes)]
  simp [concretizeRandom, node, hg, tRnd]

theorem safeMemo_plaintext {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {ts : Nat} (hmem : tRnd ts 32 ∈ pts) (hg : g.σ ts 32 = dhAesPt0) :
    SafeMemo S g pts (tRnd ts 32) := by
  intro x hx
  rw [gamma'_plaintext_eq hg] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inl ⟨hmem, rfl⟩

theorem termAt_lit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} {bs : HwBytes}
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide) :
    TermAt S g pts (tLit bs) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, beq_iff_eq] at hok
  have hg' : gamma' dhRatchetI0 S g (tLit bs) =
      { bytes := bs, shape := tLit bs, memo := [(tLit bs, tLit bs, bs)] } := by
    unfold gamma'
    change (({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll dhRatchetI0 S g) = _
    rw [DY.Bytes.rec_eq concretizeLit (concretizeAll dhRatchetI0 S g)
      ({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes)]
    simp [concretizeLit, node, ofByteArray_litOf_eq, tLit, litOf]
  have hsh : shapeOf id = tLit bs := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, ?_, ?_, ?_⟩
  · rw [hg', hok]
  · rw [hg', hsh]
  · intro x hx
    rw [hg'] at hx
    rcases List.mem_singleton.mp hx with rfl
    refine Or.inr (Or.inr ⟨id, hid, hsh.symm, hok, fun hai => ?_⟩)
    have hfalse : assumedInjective (tLit bs) = false := ai_lit_pack_eq _
    rw [hfalse] at hai; cases hai

theorem termAt_litByteArray {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} {ba : ByteArray} {bs : HwBytes}
    (hba : ofByteArray ba = bs)
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide) :
    TermAt S g pts (DY.Literal.literalToBytes ba) id := by
  rw [literalToBytes_eq_tLit, hba]
  exact termAt_lit hop hid

theorem termAt_rand {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id ts sz : Nat}
    (hop : opOf id = .rand ts sz := by decide) (hid : id < dagSize := by decide)
    (hg : g.σ ts sz = bytesOf id) :
    TermAt S g pts (tRnd ts sz) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, decide_eq_true_eq] at hok
  have hnz : sz ≠ 0 := Nat.ne_of_gt hok
  have hg' : gamma' dhRatchetI0 S g (tRnd ts sz) =
      { bytes := bytesOf id, shape := tRnd ts sz, memo := [(tRnd ts sz, tRnd ts sz, bytesOf id)] } := by
    unfold gamma'
    change (({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll dhRatchetI0 S g) = _
    rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll dhRatchetI0 S g)
      ({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes)]
    simp [concretizeRandom, hnz, node, hg, tRnd]
  have hsh : shapeOf id = tRnd ts sz := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, by rw [hg'], by rw [hg', hsh], fun x hx => ?_⟩
  rw [hg'] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inr (Or.inr ⟨id, hid, hsh.symm, rfl, fun _ => by rw [hop]; rfl⟩)

theorem termAt_concat {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id l r : Nat} {tl tr : DY.Bytes}
    (hop : opOf id = .concat l r := by decide) (hid : id < dagSize := by decide)
    (hl : TermAt S g pts tl l) (hr : TermAt S g pts tr r) :
    TermAt S g pts (tCat tl tr) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hlt, hrt⟩, hb_eq⟩ := hok
  have hg' : gamma' dhRatchetI0 S g (tCat tl tr) =
      node ((gamma' dhRatchetI0 S g tl).bytes ++ (gamma' dhRatchetI0 S g tr).bytes)
        (tCat tl tr)
        (tCat (gamma' dhRatchetI0 S g tl).shape (gamma' dhRatchetI0 S g tr).shape)
        [gamma' dhRatchetI0 S g tl, gamma' dhRatchetI0 S g tr] :=
    DY.Bytes.rec_eq concretizeConcat (concretizeAll dhRatchetI0 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)
  have hsh : shapeOf id = tCat (shapeOf l) (shapeOf r) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hlt, hrt]
  have hbytes : (gamma' dhRatchetI0 S g (tCat tl tr)).bytes = bytesOf id := by
    rw [hg']; dsimp only [node]; rw [hl.2.1, hr.2.1, hb_eq]
  have hshape : (gamma' dhRatchetI0 S g (tCat tl tr)).shape = shapeOf id := by
    rw [hg']; dsimp only [node]; rw [hl.2.2.1, hr.2.2.1, hsh]
  refine ⟨hid, hbytes, hshape, fun x hx => ?_⟩
  rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_cons.mp hx with rfl | hsub
  · refine Or.inr (Or.inr ⟨id, hid, ?_, ?_, fun hai => ?_⟩)
    · rw [hl.2.2.1, hr.2.2.1, hsh]
    · rw [hl.2.1, hr.2.1, hb_eq]
    · have hfalse : assumedInjective (tCat tl tr) = false := ai_concat_eq tl tr
      rw [hfalse] at hai; cases hai
  · rcases List.mem_append.mp hsub with hxl | hxr
    · exact hl.2.2.2 x hxl
    · exact hr.2.2.2 x hxr

theorem termAt_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id sk : Nat} {tsk : DY.Bytes}
    (hop : opOf id = .dhPk sk := by decide) (hid : id < dagSize := by decide)
    (hsk : TermAt S g pts tsk sk) :
    TermAt S g pts (tDhPk tsk) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨hsk_lt, hb_eq⟩ := hok
  have hg' : gamma' dhRatchetI0 S g (tDhPk tsk) =
      node ((dhRatchetI0 x25519PublicKeySymbol [clamp (gamma' dhRatchetI0 S g tsk).bytes]).getD [])
        (tDhPk tsk) (tDhPk (gamma' dhRatchetI0 S g tsk).shape)
        [gamma' dhRatchetI0 S g tsk] :=
    DY.Bytes.rec_eq (concretizeDhPk dhRatchetI0) (concretizeAll dhRatchetI0 S g)
      ({ sk := tsk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hi_eval : (dhRatchetI0 x25519PublicKeySymbol [clamp (bytesOf sk)]).getD [] = bytesOf id := by
    unfold dhRatchetI0; simp [x25519PublicKeySymbol, hb_eq]
  have hsh : shapeOf id = tDhPk (shapeOf sk) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hsk_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hsk.2.1, hi_eval]
  · rw [hg']; dsimp only [node]; rw [hsk.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, by rw [hsk.2.2.1, hsh], by rw [hsk.2.1, hi_eval],
        fun _ => by rw [hop]; rfl⟩)
    · exact hsk.2.2.2 x hsub

theorem shapeOf_rand {id ts sz : Nat} (hop : opOf id = .rand ts sz := by decide) :
    tRnd ts sz = shapeOf id := by
  unfold shapeOf; rw [dagShape]; simp [hop]

theorem termAt_dh_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk1 sk1 pk2 sk2 : Nat} {tsk1 tsk2 : DY.Bytes}
    (hop : opOf id = .dh pk1 sk2 := by decide) (hid : id < dagSize := by decide)
    (hcomm : compLookupDh (clamp (bytesOf sk1)) (bytesOf pk2) = bytesOf id := by decide)
    (hsh1 : tsk1 = shapeOf sk1 := by rfl) (hsh2 : tsk2 = shapeOf sk2 := by rfl)
    (hsk1 : TermAt S g pts tsk1 sk1) (hpk1 : TermAt S g pts (DY.DiffieHellman.dhPk tsk1) pk1)
    (hsk2 : TermAt S g pts tsk2 sk2) (hpk2 : TermAt S g pts (DY.DiffieHellman.dhPk tsk2) pk2) :
    TermAt S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hpk1_lt, hsk2_lt⟩, hb_eq⟩ := hok
  have hg'_raw : ∀ (tpk tsk : DY.Bytes),
      gamma' dhRatchetI0 S g (tDh tpk tsk) =
        node ((dhRatchetI0 x25519AgreementSymbol
            [clamp (gamma' dhRatchetI0 S g tsk).bytes, (gamma' dhRatchetI0 S g tpk).bytes]).getD [])
          (tDh tpk tsk)
          (tDh (gamma' dhRatchetI0 S g tpk).shape (gamma' dhRatchetI0 S g tsk).shape)
          [gamma' dhRatchetI0 S g tpk, gamma' dhRatchetI0 S g tsk] :=
    fun tpk tsk =>
      DY.Bytes.rec_eq (concretizeDh dhRatchetI0) (concretizeAll dhRatchetI0 S g)
        ({ pk := tpk, sk := tsk } : DY.DiffieHellman.Dh.SubF DY.Bytes)
  have hg_pk : ∀ (tsk : DY.Bytes) (sk : Nat), tsk = shapeOf sk → TermAt S g pts tsk sk →
      (gamma' dhRatchetI0 S g (DY.DiffieHellman.dhPk tsk)).shape = DY.DiffieHellman.dhPk tsk := by
    intro tsk sk hsh hsk
    have hr : gamma' dhRatchetI0 S g (DY.DiffieHellman.dhPk tsk) =
        node ((dhRatchetI0 x25519PublicKeySymbol [clamp (gamma' dhRatchetI0 S g tsk).bytes]).getD [])
          (tDhPk tsk) (tDhPk (gamma' dhRatchetI0 S g tsk).shape)
          [gamma' dhRatchetI0 S g tsk] :=
      DY.Bytes.rec_eq (concretizeDhPk dhRatchetI0) (concretizeAll dhRatchetI0 S g)
        ({ sk := tsk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    rw [hr]; dsimp only [node]; rw [hsk.2.2.1, ← hsh]; rfl
  have hg_pk1 := hg_pk tsk1 sk1 hsh1 hsk1
  have hg_pk2 := hg_pk tsk2 sk2 hsh2 hsk2
  have hsh_pk1 : shapeOf pk1 = DY.DiffieHellman.dhPk tsk1 := hpk1.2.2.1.symm.trans hg_pk1
  have hsh_raw : shapeOf id = DY.DiffieHellman.dh (shapeOf pk1) (shapeOf sk2) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hpk1_lt, hsk2_lt]
  have hsh_id : shapeOf id = DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2 := by
    rw [hsh_raw, hsh_pk1, ← hsh2]
  have hdh_unfold : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2 =
      (if tsk2 ≤ tsk1 then tDh (DY.DiffieHellman.dhPk tsk1) tsk2
       else tDh (DY.DiffieHellman.dhPk tsk2) tsk1) := by
    simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
      DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk, DY.BytesView.view_pack]
    rfl
  have hne : x25519AgreementSymbol ≠ x25519PublicKeySymbol := by decide
  by_cases hle : tsk2 ≤ tsk1
  · have hterm : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2 =
        tDh (DY.DiffieHellman.dhPk tsk1) tsk2 := by
      rw [hdh_unfold]; simp only [hle, ↓reduceIte]
    have hsh_eq : shapeOf id = tDh (DY.DiffieHellman.dhPk tsk1) tsk2 := hsh_id.trans hterm
    have hi_eval : (dhRatchetI0 x25519AgreementSymbol [clamp (bytesOf sk2), bytesOf pk1]).getD [] =
        bytesOf id := by unfold dhRatchetI0; simp [hne, hb_eq]
    rw [hterm]
    have hg' := hg'_raw (DY.DiffieHellman.dhPk tsk1) tsk2
    refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
    · rw [hg']; dsimp only [node]; rw [hsk2.2.1, hpk1.2.1, hi_eval]
    · rw [hg']; dsimp only [node]; rw [hg_pk1, hsk2.2.2.1, ← hsh2, hsh_eq]
    · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
      rcases List.mem_cons.mp hx with rfl | hsub
      · exact Or.inr (Or.inr ⟨id, hid, by rw [hg_pk1, hsk2.2.2.1, ← hsh2, hsh_eq],
          by rw [hsk2.2.1, hpk1.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
      · rcases List.mem_append.mp hsub with hxp | hxs
        · exact hpk1.2.2.2 x hxp
        · exact hsk2.2.2.2 x hxs
  · have hterm : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2 =
        tDh (DY.DiffieHellman.dhPk tsk2) tsk1 := by
      rw [hdh_unfold]; simp only [hle, ↓reduceIte]
    have hsh_eq : shapeOf id = tDh (DY.DiffieHellman.dhPk tsk2) tsk1 := hsh_id.trans hterm
    have hi_eval : (dhRatchetI0 x25519AgreementSymbol [clamp (bytesOf sk1), bytesOf pk2]).getD [] =
        bytesOf id := by unfold dhRatchetI0; simp [hne, hcomm]
    rw [hterm]
    have hg' := hg'_raw (DY.DiffieHellman.dhPk tsk2) tsk1
    refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
    · rw [hg']; dsimp only [node]; rw [hsk1.2.1, hpk2.2.1, hi_eval]
    · rw [hg']; dsimp only [node]; rw [hg_pk2, hsk1.2.2.1, ← hsh1, hsh_eq]
    · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
      rcases List.mem_cons.mp hx with rfl | hsub
      · exact Or.inr (Or.inr ⟨id, hid, by rw [hg_pk2, hsk1.2.2.1, ← hsh1, hsh_eq],
          by rw [hsk1.2.1, hpk2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
      · rcases List.mem_append.mp hsub with hxp | hxs
        · exact hpk2.2.2.2 x hxp
        · exact hsk1.2.2.2 x hxs

theorem termAt_kdf {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id salt ikm : Nat} {tsalt tikm : DY.Bytes}
    (hop : opOf id = .kdf salt ikm := by decide) (hid : id < dagSize := by decide)
    (hsalt : TermAt S g pts tsalt salt) (hikm : TermAt S g pts tikm ikm) :
    TermAt S g pts (tKdf tsalt tikm) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hs_lt, hi_lt⟩, hb_eq⟩ := hok
  have hg' : gamma' dhRatchetI0 S g (tKdf tsalt tikm) =
      node (hmacWith (sha256CompressFunction dhRatchetI0)
          (gamma' dhRatchetI0 S g tsalt).bytes (gamma' dhRatchetI0 S g tikm).bytes)
        (tKdf tsalt tikm)
        (tKdf (gamma' dhRatchetI0 S g tsalt).shape (gamma' dhRatchetI0 S g tikm).shape)
        [gamma' dhRatchetI0 S g tsalt, gamma' dhRatchetI0 S g tikm] :=
    DY.Bytes.rec_eq (concretizeKdf dhRatchetI0) (concretizeAll dhRatchetI0 S g)
      ({ salt := tsalt, ikm := tikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes)
  have hsh : shapeOf id = tKdf (shapeOf salt) (shapeOf ikm) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hs_lt, hi_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hsalt.2.1, hikm.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [hsalt.2.2.1, hikm.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, by rw [hsalt.2.2.1, hikm.2.2.1, hsh],
        by rw [hsalt.2.1, hikm.2.1, hb_eq], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxs | hxi
      · exact hsalt.2.2.2 x hxs
      · exact hikm.2.2.2 x hxi

theorem termAt_trunc8 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id inp : Nat} {tinp : DY.Bytes}
    (hop : opOf id = .trunc8 inp := by decide) (hid : id < dagSize := by decide)
    (hinp : TermAt S g pts tinp inp) :
    TermAt S g pts (tTr8 tinp) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨hi_lt, hb_eq⟩ := hok
  have hg' : gamma' dhRatchetI0 S g (tTr8 tinp) =
      node ((gamma' dhRatchetI0 S g tinp).bytes.take 8)
        (tTr8 tinp) (tTr8 (gamma' dhRatchetI0 S g tinp).shape)
        [gamma' dhRatchetI0 S g tinp] :=
    DY.Bytes.rec_eq concretizeTrunc (concretizeAll dhRatchetI0 S g)
      ({ input := tinp } : DY.Trunc.Trunc8.SubF DY.Bytes)
  have hsh : shapeOf id = tTr8 (shapeOf inp) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hi_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hinp.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [hinp.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, by rw [hinp.2.2.1, hsh], by rw [hinp.2.1, hb_eq],
        fun _ => by rw [hop]; rfl⟩)
    · exact hinp.2.2.2 x hsub

theorem termAt_symEncPt {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id key iv ts : Nat} {tkey tiv : DY.Bytes}
    (hop : opOf id = .symEncPt key iv ts dhAesPt0 := by decide) (hid : id < dagSize := by decide)
    (hkey : TermAt S g pts tkey key) (hiv : TermAt S g pts tiv iv)
    (hpt_mem : tRnd ts 32 ∈ pts) (hg_pt : g.σ ts 32 = dhAesPt0) :
    TermAt S g pts (tSym tkey tiv (tRnd ts 32)) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hk_lt, hiv_lt⟩, hb_eq⟩ := hok
  have hg' : gamma' dhRatchetI0 S g (tSym tkey tiv (tRnd ts 32)) =
      node ((dhRatchetI0 aesCbcEncryptSymbol
          [(gamma' dhRatchetI0 S g (tRnd ts 32)).bytes,
           (gamma' dhRatchetI0 S g tkey).bytes,
           (gamma' dhRatchetI0 S g tiv).bytes.take 16]).getD [])
        (tSym tkey tiv (tRnd ts 32))
        (tSym (gamma' dhRatchetI0 S g tkey).shape (gamma' dhRatchetI0 S g tiv).shape
          (gamma' dhRatchetI0 S g (tRnd ts 32)).shape)
        [gamma' dhRatchetI0 S g tkey, gamma' dhRatchetI0 S g tiv,
         gamma' dhRatchetI0 S g (tRnd ts 32)] :=
    DY.Bytes.rec_eq (concretizeSym dhRatchetI0) (concretizeAll dhRatchetI0 S g)
      ({ key := tkey, iv := tiv, msg := tRnd ts 32 } : DY.SymEnc.Enc.SubF DY.Bytes)
  have hpt_g := gamma'_plaintext_eq (S := S) hg_pt
  have hi_eval : (dhRatchetI0 aesCbcEncryptSymbol
      [dhAesPt0, bytesOf key, (bytesOf iv).take 16]).getD [] = bytesOf id := by
    unfold dhRatchetI0
    have h1 : aesCbcEncryptSymbol ≠ x25519PublicKeySymbol := by decide
    have h2 : aesCbcEncryptSymbol ≠ x25519AgreementSymbol := by decide
    have h3 : aesCbcEncryptSymbol ≠ DY.Libsignal.Refinement.x25519TorsionSymbol := by decide
    simp [h1, h2, h3, hb_eq]
  have hsh : shapeOf id = tSym (shapeOf key) (shapeOf iv) (tRnd ts 32) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hk_lt, hiv_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg', hpt_g]; dsimp only [node]; rw [hkey.2.1, hiv.2.1, hi_eval]
  · rw [hg', hpt_g]; dsimp only [node]; rw [hkey.2.2.1, hiv.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · rw [hpt_g]
      exact Or.inr (Or.inr ⟨id, hid, by rw [hkey.2.2.1, hiv.2.2.1, hsh],
        by rw [hkey.2.1, hiv.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxk | rest
      · exact hkey.2.2.2 x hxk
      · rcases List.mem_append.mp rest with hxi | hxp
        · exact hiv.2.2.2 x hxi
        · exact safeMemo_plaintext hpt_mem hg_pt x hxp

theorem termAt_trWire {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} {ver : UInt8} {rk : Nat} {cnt prev : UInt32} {ct pq : Nat} {addr : HwBytes}
    {trk tct tpq : DY.Bytes}
    (hop : opOf id = .trWire ver rk cnt prev ct pq addr := by decide)
    (hid : id < dagSize := by decide)
    (hrk : TermAt S g pts trk rk) (hct : TermAt S g pts tct ct) (hpq : TermAt S g pts tpq pq)
    (haddr : g.addr (tTrW ver trk cnt prev tct tpq DY.TrWire.canonicalVariation) = addr) :
    TermAt S g pts (tTrW ver trk cnt prev tct tpq DY.TrWire.canonicalVariation) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hrk_lt, hct_lt⟩, hpq_lt⟩, hb_eq⟩ := hok
  let tw := tTrW ver trk cnt prev tct tpq DY.TrWire.canonicalVariation
  have hg' : gamma' dhRatchetI0 S g tw =
      node (trWireBytes (g.addr tw) DY.TrWire.canonicalVariation
          { version := ver.toNat, ratchetKey := (gamma' dhRatchetI0 S g trk).bytes,
            counter := cnt.toNat, previousCounter := prev.toNat,
            ciphertext := (gamma' dhRatchetI0 S g tct).bytes }
          (gamma' dhRatchetI0 S g tpq).bytes)
        tw
        (tTrW ver (gamma' dhRatchetI0 S g trk).shape cnt prev
          (gamma' dhRatchetI0 S g tct).shape (gamma' dhRatchetI0 S g tpq).shape
          (trWireShapeVar (g.addr tw)))
        [gamma' dhRatchetI0 S g trk, gamma' dhRatchetI0 S g tct, gamma' dhRatchetI0 S g tpq] :=
    DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll dhRatchetI0 S g)
      ({ version := ver, senderRatchetKey := trk, counter := cnt, previousCounter := prev,
         ciphertext := tct, pqRatchet := tpq,
         encodingVariation := DY.TrWire.canonicalVariation } : DY.TrWire.TrWireMsg.SubF DY.Bytes)
  have hsh : shapeOf id =
      tTrW ver (shapeOf rk) cnt prev (shapeOf ct) (shapeOf pq) (trWireShapeVar addr) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hrk_lt, hct_lt, hpq_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [haddr, hrk.2.1, hct.2.1, hpq.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [haddr, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · refine Or.inr (Or.inr ⟨id, hid, ?_, ?_, fun hai => ?_⟩)
      · rw [haddr, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hsh]
      · rw [haddr, hrk.2.1, hct.2.1, hpq.2.1, hb_eq]
      · have hfalse : assumedInjective tw = false := ai_trWire_pack_eq _
        rw [hfalse] at hai; cases hai
    · rcases List.mem_append.mp hsub with hxr | rest
      · exact hrk.2.2.2 x hxr
      · rcases List.mem_append.mp rest with hxc | hxp
        · exact hct.2.2.2 x hxc
        · exact hpq.2.2.2 x hxp

theorem termAt_kemEncap {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk ent : Nat} {tpk tent : DY.Bytes}
    (hop : opOf id = .kemEncap pk ent := by decide) (hid : id < dagSize := by decide)
    (hpk : TermAt S g pts tpk pk) (hent : TermAt S g pts tent ent) :
    TermAt S g pts (tKemEnc tpk tent) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpk_lt, hent_lt⟩, hlen_beq⟩, hb_eq⟩ := hok
  have hlen32 : (bytesOf ent).length = 32 := Nat.beq_eq.mp hlen_beq
  have hg' : gamma' dhRatchetI0 S g (tKemEnc tpk tent) =
      if (gamma' dhRatchetI0 S g tent).bytes.length = 32 then
        node (((dhRatchetI0 kyberEncapsSymbol
            [(gamma' dhRatchetI0 S g tpk).bytes, (gamma' dhRatchetI0 S g tent).bytes]).getD []).take 1568)
          (tKemEnc tpk tent)
          (tKemEnc (gamma' dhRatchetI0 S g tpk).shape (gamma' dhRatchetI0 S g tent).shape)
          [gamma' dhRatchetI0 S g tpk, gamma' dhRatchetI0 S g tent]
      else opaqueNode [] [gamma' dhRatchetI0 S g tpk, gamma' dhRatchetI0 S g tent] :=
    DY.Bytes.rec_eq (concretizeKemEncap dhRatchetI0) (concretizeAll dhRatchetI0 S g)
      ({ pk := tpk, entropy := tent } : DY.PQKem.Encap.SubF DY.Bytes)
  have hi_eval : ((dhRatchetI0 kyberEncapsSymbol [bytesOf pk, bytesOf ent]).getD []).take 1568 =
      bytesOf id := by
    unfold dhRatchetI0
    have h1 : kyberEncapsSymbol ≠ x25519PublicKeySymbol := by decide
    have h2 : kyberEncapsSymbol ≠ x25519AgreementSymbol := by decide
    have h3 : kyberEncapsSymbol ≠ DY.Libsignal.Refinement.x25519TorsionSymbol := by decide
    have h4 : kyberEncapsSymbol ≠ aesCbcEncryptSymbol := by decide
    have h5 : kyberEncapsSymbol ≠ DY.Libsignal.Refinement.aesCbcDecryptSymbol := by decide
    simp [h1, h2, h3, h4, h5, hb_eq]
  have hsh : shapeOf id = tKemEnc (shapeOf pk) (shapeOf ent) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hpk_lt, hent_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; simp [hent.2.1, hlen32, node, hpk.2.1, hi_eval]
  · rw [hg']; simp [hent.2.1, hlen32, node, hpk.2.2.1, hent.2.2.1, hsh]
  · rw [hg'] at hx; simp only [hent.2.1, hlen32, ↓reduceIte, node,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, by rw [hpk.2.2.1, hent.2.2.1, hsh],
        by rw [hpk.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxp | hxe
      · exact hpk.2.2.2 x hxp
      · exact hent.2.2.2 x hxe

theorem termAt_kemSS {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk ent : Nat} {tpk tent : DY.Bytes}
    (hop : opOf id = .kemSS pk ent := by decide) (hid : id < dagSize := by decide)
    (hpk : TermAt S g pts tpk pk) (hent : TermAt S g pts tent ent) :
    TermAt S g pts (tKemSS tpk tent) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpk_lt, hent_lt⟩, hlen_beq⟩, hb_eq⟩ := hok
  have hlen32 : (bytesOf ent).length = 32 := Nat.beq_eq.mp hlen_beq
  have hg' : gamma' dhRatchetI0 S g (tKemSS tpk tent) =
      if (gamma' dhRatchetI0 S g tent).bytes.length = 32 then
        node (((dhRatchetI0 kyberEncapsSymbol
            [(gamma' dhRatchetI0 S g tpk).bytes, (gamma' dhRatchetI0 S g tent).bytes]).getD []).drop 1568)
          (tKemSS tpk tent)
          (tKemSS (gamma' dhRatchetI0 S g tpk).shape (gamma' dhRatchetI0 S g tent).shape)
          [gamma' dhRatchetI0 S g tpk, gamma' dhRatchetI0 S g tent]
      else opaqueNode (S.kemDecap (gamma' dhRatchetI0 S g tpk).bytes (gamma' dhRatchetI0 S g tent).bytes)
        [gamma' dhRatchetI0 S g tpk, gamma' dhRatchetI0 S g tent] :=
    DY.Bytes.rec_eq (concretizeKemSS dhRatchetI0 S) (concretizeAll dhRatchetI0 S g)
      ({ pk := tpk, entropy := tent } : DY.PQKem.SharedSecret.SubF DY.Bytes)
  have hi_eval : ((dhRatchetI0 kyberEncapsSymbol [bytesOf pk, bytesOf ent]).getD []).drop 1568 =
      bytesOf id := by
    unfold dhRatchetI0
    have h1 : kyberEncapsSymbol ≠ x25519PublicKeySymbol := by decide
    have h2 : kyberEncapsSymbol ≠ x25519AgreementSymbol := by decide
    have h3 : kyberEncapsSymbol ≠ DY.Libsignal.Refinement.x25519TorsionSymbol := by decide
    have h4 : kyberEncapsSymbol ≠ aesCbcEncryptSymbol := by decide
    have h5 : kyberEncapsSymbol ≠ DY.Libsignal.Refinement.aesCbcDecryptSymbol := by decide
    simp [h1, h2, h3, h4, h5, hb_eq]
  have hsh : shapeOf id = tKemSS (shapeOf pk) (shapeOf ent) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hpk_lt, hent_lt]
  refine ⟨hid, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; simp [hent.2.1, hlen32, node, hpk.2.1, hi_eval]
  · rw [hg']; simp [hent.2.1, hlen32, node, hpk.2.2.1, hent.2.2.1, hsh]
  · rw [hg'] at hx; simp only [hent.2.1, hlen32, ↓reduceIte, node,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, by rw [hpk.2.2.1, hent.2.2.1, hsh],
        by rw [hpk.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxp | hxe
      · exact hpk.2.2.2 x hxp
      · exact hent.2.2.2 x hxe

/-! ## Opaque-Node `TermAt` & `SafeMemo` Wrappers (Parametric in `∀ S`) -/

theorem termAt_of_opaque_pinned {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {t : DY.Bytes} {id : Nat} {bs : HwBytes}
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide)
    (hsh_lit : (gamma' dhRatchetI0 S g t).shape = tLit (gamma dhRatchetI0 S g t))
    (hgam : gamma dhRatchetI0 S g t = bytesOf id)
    (hmemo : SafeMemo S g pts t) :
    TermAt S g pts t id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, beq_iff_eq] at hok
  have hsh : shapeOf id = tLit bs := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, hgam, ?_, hmemo⟩
  rw [hsh_lit, hgam, ← hok, hsh]

theorem opaque_kemPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {sk : DY.Bytes} (hsk : SafeMemo S g pts sk) :
    (gamma' dhRatchetI0 S g (DY.PQKem.kemPk sk)).shape =
      tLit (gamma dhRatchetI0 S g (DY.PQKem.kemPk sk)) ∧
    SafeMemo S g pts (DY.PQKem.kemPk sk) := by
  have hg' : gamma' dhRatchetI0 S g (DY.PQKem.kemPk sk) =
      opaqueNode (S.kemPk (gamma' dhRatchetI0 S g sk).bytes) [gamma' dhRatchetI0 S g sk] :=
    DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll dhRatchetI0 S g)
      ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx; simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    exact hsk x hx

theorem safeMemo_spqrInit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {a p : DY.Bytes} (ha : SafeMemo S g pts a) (hp : SafeMemo S g pts p) :
    SafeMemo S g pts (DY.Spqr.spqrInit a p) := by
  have hg' : gamma' dhRatchetI0 S g (DY.Spqr.spqrInit a p) =
      opaqueNode (S.init (gamma' dhRatchetI0 S g a).bytes (gamma' dhRatchetI0 S g p).bytes)
        [gamma' dhRatchetI0 S g a, gamma' dhRatchetI0 S g p] :=
    DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll dhRatchetI0 S g)
      ({ authKey := a, params := p } : DY.Spqr.InitState.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_append.mp hx with hxa | hxp
  · exact ha x hxa
  · exact hp x hxp

theorem safeMemo_spqrSendState {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {st c : DY.Bytes} (hst : SafeMemo S g pts st) (hc : SafeMemo S g pts c) :
    SafeMemo S g pts (tSSendSt st c) := by
  have hg' : gamma' dhRatchetI0 S g (tSSendSt st c) =
      opaqueNode (S.sendState (gamma' dhRatchetI0 S g st).bytes (gamma' dhRatchetI0 S g c).bytes)
        [gamma' dhRatchetI0 S g st, gamma' dhRatchetI0 S g c] :=
    DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll dhRatchetI0 S g)
      ({ st := st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_append.mp hx with hxs | hxc
  · exact hst x hxs
  · exact hc x hxc

theorem opaque_spqrSendMsg {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {st c : DY.Bytes} (hst : SafeMemo S g pts st) (hc : SafeMemo S g pts c) :
    (gamma' dhRatchetI0 S g (tSSendM st c)).shape =
      tLit (gamma dhRatchetI0 S g (tSSendM st c)) ∧
    SafeMemo S g pts (tSSendM st c) := by
  have hg' : gamma' dhRatchetI0 S g (tSSendM st c) =
      opaqueNode (S.sendMsg (gamma' dhRatchetI0 S g st).bytes (gamma' dhRatchetI0 S g c).bytes)
        [gamma' dhRatchetI0 S g st, gamma' dhRatchetI0 S g c] :=
    DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll dhRatchetI0 S g)
      ({ st := st, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx
    simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_append.mp hx with hxs | hxc
    · exact hst x hxs
    · exact hc x hxc

theorem opaque_spqrChainKey {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {a p idx : DY.Bytes}
    (ha : SafeMemo S g pts a) (hp : SafeMemo S g pts p) (hidx : SafeMemo S g pts idx) :
    (gamma' dhRatchetI0 S g (DY.Spqr.spqrChainKey a p idx)).shape =
      tLit (gamma dhRatchetI0 S g (DY.Spqr.spqrChainKey a p idx)) ∧
    SafeMemo S g pts (DY.Spqr.spqrChainKey a p idx) ∧
    (gamma dhRatchetI0 S g (DY.Spqr.spqrChainKey a p idx)).length = 32 := by
  have hg' : gamma' dhRatchetI0 S g (DY.Spqr.spqrChainKey a p idx) =
      spqrKeyNode (S.chainKey (gamma' dhRatchetI0 S g a).bytes (gamma' dhRatchetI0 S g p).bytes
        (gamma' dhRatchetI0 S g idx).bytes)
        [gamma' dhRatchetI0 S g a, gamma' dhRatchetI0 S g p, gamma' dhRatchetI0 S g idx] :=
    DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll dhRatchetI0 S g)
      ({ authKey := a, params := p, idx := idx } : DY.Spqr.ChainKey.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_, ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx
    simp only [spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_append.mp hx with hxa | rest
    · exact ha x hxa
    · rcases List.mem_append.mp rest with hxp | hxi
      · exact hp x hxp
      · exact hidx x hxi
  · unfold gamma; rw [hg']
    simp [spqrKeyNode, opaqueNode, spqrKeyBytes]

/-! ## Non-AI Literal, Concat, and `Comparse` `SafeMemo` Helpers -/

theorem gamma'_tLit_eq {S : OpaqueSymbolSemantics} {g : Ghost} (bs : HwBytes) :
    gamma' dhRatchetI0 S g (tLit bs) =
      { bytes := bs, shape := tLit bs, memo := [(tLit bs, tLit bs, bs)] } := by
  unfold gamma'
  change (({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll dhRatchetI0 S g) = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll dhRatchetI0 S g)
    ({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes)]
  simp [concretizeLit, node, ofByteArray_litOf_eq, tLit, litOf]

theorem gamma_literalToBytes {S : OpaqueSymbolSemantics} {g : Ghost} (ba : ByteArray) :
    gamma dhRatchetI0 S g (DY.Literal.literalToBytes ba) = ofByteArray ba := by
  rw [literalToBytes_eq_tLit]; unfold gamma; rw [gamma'_tLit_eq]

theorem safeMemo_lit_nonAI {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {ba : ByteArray} (hno : notAnyAiNodeBytes (ofByteArray ba) = true) :
    SafeMemo S g pts (DY.Literal.literalToBytes ba) := by
  rw [literalToBytes_eq_tLit]
  intro x hx
  rw [gamma'_tLit_eq] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inr (Or.inl ⟨ai_lit_pack_eq _, hno⟩)

theorem gamma_concat {S : OpaqueSymbolSemantics} {g : Ghost} (tl tr : DY.Bytes) :
    gamma dhRatchetI0 S g (tCat tl tr) =
      gamma dhRatchetI0 S g tl ++ gamma dhRatchetI0 S g tr := by
  unfold gamma
  rw [show gamma' dhRatchetI0 S g (tCat tl tr) = _ from
    DY.Bytes.rec_eq concretizeConcat (concretizeAll dhRatchetI0 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)]
  rfl

theorem safeMemo_concat_nonAI {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {tl tr : DY.Bytes}
    (hl : SafeMemo S g pts tl) (hr : SafeMemo S g pts tr)
    (hno : notAnyAiNodeBytes (gamma dhRatchetI0 S g tl ++ gamma dhRatchetI0 S g tr) = true) :
    SafeMemo S g pts (tCat tl tr) := by
  have hg' : gamma' dhRatchetI0 S g (tCat tl tr) =
      node ((gamma' dhRatchetI0 S g tl).bytes ++ (gamma' dhRatchetI0 S g tr).bytes)
        (tCat tl tr)
        (tCat (gamma' dhRatchetI0 S g tl).shape (gamma' dhRatchetI0 S g tr).shape)
        [gamma' dhRatchetI0 S g tl, gamma' dhRatchetI0 S g tr] :=
    DY.Bytes.rec_eq concretizeConcat (concretizeAll dhRatchetI0 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_cons.mp hx with rfl | hsub
  · exact Or.inr (Or.inl ⟨ai_concat_eq tl tr, hno⟩)
  · rcases List.mem_append.mp hsub with hxl | hxr
    · exact hl x hxl
    · exact hr x hxr

theorem safeMemo_bytesLike_empty {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} :
    SafeMemo S g pts (_root_.Comparse.BytesLike.empty : DY.Bytes) ∧
    gamma dhRatchetI0 S g (_root_.Comparse.BytesLike.empty : DY.Bytes) = [] := by
  change SafeMemo S g pts (DY.Literal.literalToBytes .empty) ∧
    gamma dhRatchetI0 S g (DY.Literal.literalToBytes .empty) = []
  have hempty : ofByteArray .empty = [] := rfl
  refine ⟨safeMemo_lit_nonAI ?_, by rw [gamma_literalToBytes, hempty]⟩
  rw [hempty]; decide +kernel

theorem safeMemo_mem_bool {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (b : Bool) {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b) :
    SafeMemo S g pts p ∧
    gamma dhRatchetI0 S g p = (if b then [1#8] else [0#8]) ∧
    0 < (gamma dhRatchetI0 S g p).length := by
  obtain ⟨ba, _, hba, hser⟩ := bool_serialize_singleton_head b
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hba ⊢
    subst hba
    have hob : ofByteArray ⟨#[0]⟩ = [0#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      by rw [gamma_literalToBytes, hob], by rw [gamma_literalToBytes, hob]; decide⟩
  · simp only [↓reduceIte] at hba ⊢
    subst hba
    have hob : ofByteArray ⟨#[1]⟩ = [1#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      by rw [gamma_literalToBytes, hob], by rw [gamma_literalToBytes, hob]; decide⟩

theorem safeMemo_mem_slowNat {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} :
    ∀ (n : Nat) {p : DY.Bytes},
      p ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n →
      SafeMemo S g pts p ∧ 0 < (gamma dhRatchetI0 S g p).length
  | 0, _, hp => by
    rw [slowNat_serialize_zero] at hp
    have h := safeMemo_mem_bool (S := S) (g := g) (pts := pts) false hp
    exact ⟨h.1, h.2.2⟩
  | n + 1, _, hp => by
    rw [slowNat_serialize_succ] at hp
    rcases List.mem_append.mp hp with h1 | h2
    · have h := safeMemo_mem_bool (S := S) (g := g) (pts := pts) true h1
      exact ⟨h.1, h.2.2⟩
    · exact safeMemo_mem_slowNat n h2

theorem safeMemo_mem_slowString {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {str : String}
    (hno : notAnyAiNodeBytes (ofByteArray str.toUTF8) = true)
    (hne : 0 < (ofByteArray str.toUTF8).length)
    {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize str) :
    SafeMemo S g pts p ∧ 0 < (gamma dhRatchetI0 S g p).length := by
  rw [slowString_serialize_eq] at hp
  rcases List.mem_append.mp hp with h1 | h2
  · exact safeMemo_mem_slowNat _ h1
  · rcases List.mem_singleton.mp h2 with rfl
    exact ⟨safeMemo_lit_nonAI hno, by rw [gamma_literalToBytes]; exact hne⟩

def IsU32SmallBytes (u : HwBytes) : Prop :=
  u = [0#8, 0#8, 0#8, 0#8] ∨ u = [0#8, 0#8, 0#8, 1#8] ∨ u = [1#8, 0#8, 0#8, 0#8] ∨
  u = [0#8, 0#8, 0#8, 2#8] ∨ u = [2#8, 0#8, 0#8, 0#8]

theorem safeMemo_mem_uint32_small {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {x : UInt32} (hx : x = 0 ∨ x = 1 ∨ x = 2) {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x) :
    SafeMemo S g pts p ∧ ∃ u : HwBytes, IsU32SmallBytes u ∧ gamma dhRatchetI0 S g p = u := by
  obtain ⟨ba, _, hba, hser⟩ := uint32_serialize_singleton_head x hx
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl
  rcases hba with rfl | rfl | rfl | rfl | rfl
  · have hob : ofByteArray ⟨#[0, 0, 0, 0]⟩ = [0#8, 0#8, 0#8, 0#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      [0#8, 0#8, 0#8, 0#8], Or.inl rfl, by rw [gamma_literalToBytes, hob]⟩
  · have hob : ofByteArray ⟨#[0, 0, 0, 1]⟩ = [0#8, 0#8, 0#8, 1#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      [0#8, 0#8, 0#8, 1#8], Or.inr (Or.inl rfl), by rw [gamma_literalToBytes, hob]⟩
  · have hob : ofByteArray ⟨#[1, 0, 0, 0]⟩ = [1#8, 0#8, 0#8, 0#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      [1#8, 0#8, 0#8, 0#8], Or.inr (Or.inr (Or.inl rfl)), by rw [gamma_literalToBytes, hob]⟩
  · have hob : ofByteArray ⟨#[0, 0, 0, 2]⟩ = [0#8, 0#8, 0#8, 2#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      [0#8, 0#8, 0#8, 2#8], Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [gamma_literalToBytes, hob]⟩
  · have hob : ofByteArray ⟨#[2, 0, 0, 0]⟩ = [2#8, 0#8, 0#8, 0#8] := rfl
    exact ⟨safeMemo_lit_nonAI (by rw [hob]; decide +kernel),
      [2#8, 0#8, 0#8, 0#8], Or.inr (Or.inr (Or.inr (Or.inr rfl))), by rw [gamma_literalToBytes, hob]⟩

theorem safeMemo_recvTailTerm_0_1 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (rk ck : DY.Bytes) :
    let c : DY.Libsignal.TripleRatchet.RecvChain :=
      { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }
    SafeMemo S g pts (recvTailTerm c) ∧
    ∃ u : HwBytes, IsU32SmallBytes u ∧
      gamma dhRatchetI0 S g (recvTailTerm c) = u ++ [1#8, 0#8] := by
  dsimp only [recvTailTerm]
  obtain ⟨ba0, _, hba0, hu0⟩ := uint32_serialize_singleton_head 0 (Or.inl rfl)
  obtain ⟨bat, _, hbat, hbt⟩ := bool_serialize_singleton_head true
  obtain ⟨baf, _, hbaf, hbf⟩ := bool_serialize_singleton_head false
  have hsn1 : (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize 1 =
      [DY.Literal.literalToBytes bat, DY.Literal.literalToBytes baf] := by
    rw [slowNat_serialize_succ, slowNat_serialize_zero, hbt, hbf]; rfl
  rw [hu0, hsn1]
  simp only [List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
  have hp0 := safeMemo_mem_uint32_small (S := S) (g := g) (pts := pts) (x := 0) (Or.inl rfl)
    (by rw [hu0]; exact List.mem_singleton.mpr rfl)
  obtain ⟨hs0, u, hu, hg0⟩ := hp0
  have hpt := safeMemo_mem_bool (S := S) (g := g) (pts := pts) true
    (by rw [hbt]; exact List.mem_singleton.mpr rfl)
  have hpf := safeMemo_mem_bool (S := S) (g := g) (pts := pts) false
    (by rw [hbf]; exact List.mem_singleton.mpr rfl)
  have hemp := safeMemo_bytesLike_empty (S := S) (g := g) (pts := pts)
  let t1 := tCat (DY.Literal.literalToBytes baf) _root_.Comparse.BytesLike.empty
  have hg1 : gamma dhRatchetI0 S g t1 = [0#8] := by
    dsimp only [t1]; rw [gamma_concat, hpf.2.1, hemp.2]; rfl
  have hs1 : SafeMemo S g pts t1 := by
    apply safeMemo_concat_nonAI hpf.1 hemp.1
    rw [hpf.2.1, hemp.2]; decide +kernel
  let t2 := tCat (DY.Literal.literalToBytes bat) t1
  have hg2 : gamma dhRatchetI0 S g t2 = [1#8, 0#8] := by
    dsimp only [t2]; rw [gamma_concat, hpt.2.1, hg1]; rfl
  have hs2 : SafeMemo S g pts t2 := by
    apply safeMemo_concat_nonAI hpt.1 hs1
    rw [hpt.2.1, hg1]; decide +kernel
  let t3 := tCat (DY.Literal.literalToBytes ba0) t2
  have hg3 : gamma dhRatchetI0 S g t3 = u ++ [1#8, 0#8] := by
    dsimp only [t3]; rw [gamma_concat, hg0, hg2]
  have hs3 : SafeMemo S g pts t3 := by
    apply safeMemo_concat_nonAI hs0 hs2
    rw [hg0, hg2]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨hs3, u, hu, hg3⟩

theorem safeMemo_concatPrefixes_strict {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (ps : List DY.Bytes) {s : DY.Bytes}
    (hps : ∀ p ∈ ps, SafeMemo S g pts p ∧ 0 < (gamma dhRatchetI0 S g p).length)
    (hs : SafeMemo S g pts s)
    (hstrict : noStrictAiSuffix (gamma dhRatchetI0 S g s) = true) :
    SafeMemo S g pts (_root_.Comparse.concatPrefixes ps s) ∧
    gamma dhRatchetI0 S g s <:+ gamma dhRatchetI0 S g (_root_.Comparse.concatPrefixes ps s) := by
  induction ps with
  | nil =>
    rw [concatPrefixes_nil]
    exact ⟨hs, List.suffix_rfl⟩
  | cons p ps ih =>
    rw [concatPrefixes_cons]
    obtain ⟨hrest, hsuf⟩ := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    obtain ⟨hp_safe, hp_pos⟩ := hps p List.mem_cons_self
    have hsuf' : gamma dhRatchetI0 S g s <:+
        gamma dhRatchetI0 S g p ++ gamma dhRatchetI0 S g (_root_.Comparse.concatPrefixes ps s) :=
      hsuf.trans (List.suffix_append _ _)
    have hle : (gamma dhRatchetI0 S g s).length ≤
        (gamma dhRatchetI0 S g (_root_.Comparse.concatPrefixes ps s)).length := hsuf.length_le
    have hlt : (gamma dhRatchetI0 S g s).length <
        (gamma dhRatchetI0 S g p ++
          gamma dhRatchetI0 S g (_root_.Comparse.concatPrefixes ps s)).length := by
      rw [List.length_append]; omega
    refine ⟨safeMemo_concat_nonAI hp_safe hrest
      (notAnyAiNodeBytes_of_noStrictAiSuffix hstrict hlt hsuf'), ?_⟩
    change gamma dhRatchetI0 S g s <:+
      gamma dhRatchetI0 S g (tCat p (_root_.Comparse.concatPrefixes ps s))
    rw [gamma_concat]
    exact hsuf'

theorem safeMemo_serialize_local_pqxdh {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    (ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
    (hpart : notAnyAiNodeBytes (ofByteArray ls.participant.toUTF8) = true)
    (hpne : 0 < (ofByteArray ls.participant.toUTF8).length)
    (hsk : SafeMemo S g pts ls.state.sk)
    (hstrict : noStrictAiSuffix (gamma dhRatchetI0 S g ls.state.sk) = true) :
    SafeMemo S g pts (DY.Comparse.serialize ls) := by
  rw [serialize_local_pqxdh_eq_bridge ls]
  refine (safeMemo_concatPrefixes_strict _ (fun p hp => ?_) hsk hstrict).1
  rcases List.mem_append.mp hp with hs | hb
  · exact safeMemo_mem_slowString hpart hpne hs
  · rcases List.mem_append.mp hb with hb1 | hb2
    · have h := safeMemo_mem_bool (S := S) (g := g) (pts := pts) ls.state.kind.toBits.1 hb1
      exact ⟨h.1, h.2.2⟩
    · have h := safeMemo_mem_bool (S := S) (g := g) (pts := pts) ls.state.kind.toBits.2 hb2
      exact ⟨h.1, h.2.2⟩

theorem safeMemo_trState_of_noAiSuffix {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {ls : DY.PersistentLocalState.LocalState TRState}
    (hanc : noAiSuffix (gamma dhRatchetI0 S g (stateAnchorPair ls).1 ++
                        gamma dhRatchetI0 S g (stateAnchorPair ls).2) = true)
    (hroots : ∀ p ∈ trStateProxyRoots ls, SafeMemo S g pts p) :
    SafeMemo S g pts (DY.Comparse.serialize ls) := by
  intro x hx
  rcases serialize_localTR_memo dhRatchetI0 S g ls hx with ⟨p, hp, hxp⟩ | ⟨hinj, hsfx⟩
  · exact hroots p hp x hxp
  · exact Or.inr (Or.inl ⟨hinj, notAnyAiNodeBytes_of_noAiSuffix hanc hsfx⟩)

end Unsealed

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoTermAt
