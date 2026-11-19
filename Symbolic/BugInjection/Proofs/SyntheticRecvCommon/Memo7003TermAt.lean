/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Comparse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

/-!
# Per-Constructor `TermAt` and Opaque-Symbol `SafeMemo` Lemmas (`Memo7003TermAt.lean`)

Provides compositional `TermAt` rules for all 11 `DagOp` constructors (including non-canonical
`ev4Variation` `TrWireMsg`), opaque-node wrappers (`kemPk`, `spqrInit`, `spqrSendState`,
`spqrRecvState`, `spqrSendMsg`, `spqrChainKey`) valid for all `S : OpaqueSymbolSemantics`,
and `TRState` / `PQXDHState` serialization helpers for `compI7003`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt

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
   concretizeSpqrRecvState concretizeSpqrChainKey concretizeTrWire concretizeAll
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
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
  (compI7003 compLookupDh)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs
  (DagOp trWireEvOf trWireShapeVar dagShape dagOpBytesOk dagNodeOk dagNodeOk_of_all)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
  (dagSize opOf bytesOf shapeOf skipIdOf dagAllNodesOk)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
  (notAnyAiNodeBytes noAiSuffix noStrictAiSuffix
   notAnyAiNodeBytes_of_noAiSuffix notAnyAiNodeBytes_of_noStrictAiSuffix
   IsPt7003Bytes SafeEntry SafeMemo TermAt)

macro "skip_ok" : tactic => `(tactic| first | decide | (cases ‹Bool› <;> decide))

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

theorem safeMemo_randTerm_zero {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (ts : Nat) : SafeMemo mode S g pts (tRnd ts 0) := by
  intro x hx
  unfold gamma' at hx
  change x ∈ ((({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes).pack).rec
    (concretizeAll compI7003 S g)).memo at hx
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI7003 S g)
    ({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes)] at hx
  simp [concretizeRandom] at hx

theorem gamma'_plaintext_eq {S : OpaqueSymbolSemantics} {g : Ghost}
    {ts : Nat} {pt : HwBytes} (hg : g.σ ts 32 = pt) :
    gamma' compI7003 S g (tRnd ts 32) =
      { bytes := pt, shape := tRnd ts 32, memo := [(tRnd ts 32, tRnd ts 32, pt)] } := by
  unfold gamma'
  change (({ timestamp := ts, size := 32 } : DY.Random.Random DY.Bytes).pack).rec
    (concretizeAll compI7003 S g) = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI7003 S g)
    ({ timestamp := ts, size := 32 } : DY.Random.Random DY.Bytes)]
  simp [concretizeRandom, node, hg, tRnd]

theorem safeMemo_plaintext {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {ts : Nat} {pt : HwBytes}
    (hmem : tRnd ts 32 ∈ pts) (hpt : IsPt7003Bytes pt) (hg : g.σ ts 32 = pt) :
    SafeMemo mode S g pts (tRnd ts 32) := by
  intro x hx
  rw [gamma'_plaintext_eq hg] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inl ⟨hmem, hpt⟩

theorem termAt_lit {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} {bs : HwBytes}
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok) :
    TermAt mode S g pts (tLit bs) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, beq_iff_eq] at hok
  have hg' : gamma' compI7003 S g (tLit bs) =
      { bytes := bs, shape := tLit bs, memo := [(tLit bs, tLit bs, bs)] } := by
    unfold gamma'
    change (({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
      (concretizeAll compI7003 S g) = _
    rw [DY.Bytes.rec_eq concretizeLit (concretizeAll compI7003 S g)
      ({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes)]
    simp [concretizeLit, node, ofByteArray_litOf_eq, tLit, litOf]
  have hsh : shapeOf id = tLit bs := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, hskp, by rw [hg', hok], by rw [hg', hsh], fun x hx => ?_⟩
  rw [hg'] at hx
  rcases List.mem_singleton.mp hx with rfl
  refine Or.inr (Or.inr ⟨id, hid, hskp, hsh.symm, hok, fun hai => ?_⟩)
  have hfalse : assumedInjective (tLit bs) = false := ai_lit_pack_eq _
  rw [hfalse] at hai; cases hai

theorem termAt_litByteArray {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {id : Nat} {ba : ByteArray} {bs : HwBytes}
    (hba : ofByteArray ba = bs)
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok) :
    TermAt mode S g pts (DY.Literal.literalToBytes ba) id := by
  rw [literalToBytes_eq_tLit, hba]
  exact termAt_lit hop hid hskp


theorem termAt_rand {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id ts sz : Nat}
    (hop : opOf id = .rand ts sz := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hg : g.σ ts sz = bytesOf id) :
    TermAt mode S g pts (tRnd ts sz) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, decide_eq_true_eq] at hok
  have hnz : sz ≠ 0 := Nat.ne_of_gt hok
  have hg' : gamma' compI7003 S g (tRnd ts sz) =
      { bytes := bytesOf id, shape := tRnd ts sz, memo := [(tRnd ts sz, tRnd ts sz, bytesOf id)] } := by
    unfold gamma'
    change (({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec
      (concretizeAll compI7003 S g) = _
    rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll compI7003 S g)
      ({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes)]
    simp [concretizeRandom, hnz, node, hg, tRnd]
  have hsh : shapeOf id = tRnd ts sz := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, hskp, by rw [hg'], by rw [hg', hsh], fun x hx => ?_⟩
  rw [hg'] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inr (Or.inr ⟨id, hid, hskp, hsh.symm, rfl, fun _ => by rw [hop]; rfl⟩)

theorem termAt_concat {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id l r : Nat} {tl tr : DY.Bytes}
    (hop : opOf id = .concat l r := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hl : TermAt mode S g pts tl l) (hr : TermAt mode S g pts tr r) :
    TermAt mode S g pts (tCat tl tr) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hlt, hrt⟩, hb_eq⟩ := hok
  have hg' : gamma' compI7003 S g (tCat tl tr) =
      node ((gamma' compI7003 S g tl).bytes ++ (gamma' compI7003 S g tr).bytes)
        (tCat tl tr)
        (tCat (gamma' compI7003 S g tl).shape (gamma' compI7003 S g tr).shape)
        [gamma' compI7003 S g tl, gamma' compI7003 S g tr] :=
    DY.Bytes.rec_eq concretizeConcat (concretizeAll compI7003 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)
  have hsh : shapeOf id = tCat (shapeOf l) (shapeOf r) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hlt, hrt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hl.2.2.1, hr.2.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [hl.2.2.2.1, hr.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · refine Or.inr (Or.inr ⟨id, hid, hskp, ?_, ?_, fun hai => ?_⟩)
      · rw [hl.2.2.2.1, hr.2.2.2.1, hsh]
      · rw [hl.2.2.1, hr.2.2.1, hb_eq]
      · have hfalse : assumedInjective (tCat tl tr) = false := ai_concat_eq tl tr
        rw [hfalse] at hai; cases hai
    · rcases List.mem_append.mp hsub with hxl | hxr
      · exact hl.2.2.2.2 x hxl
      · exact hr.2.2.2.2 x hxr

theorem termAt_dhPk {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id sk : Nat} {tsk : DY.Bytes}
    (hop : opOf id = .dhPk sk := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hsk : TermAt mode S g pts tsk sk) :
    TermAt mode S g pts (tDhPk tsk) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨hsk_lt, hb_eq⟩ := hok
  have hg' : gamma' compI7003 S g (tDhPk tsk) =
      node ((compI7003 x25519PublicKeySymbol [clamp (gamma' compI7003 S g tsk).bytes]).getD [])
        (tDhPk tsk) (tDhPk (gamma' compI7003 S g tsk).shape)
        [gamma' compI7003 S g tsk] :=
    DY.Bytes.rec_eq (concretizeDhPk compI7003) (concretizeAll compI7003 S g)
      ({ sk := tsk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hi_eval : (compI7003 x25519PublicKeySymbol [clamp (bytesOf sk)]).getD [] = bytesOf id := by
    unfold compI7003; simp [x25519PublicKeySymbol, hb_eq]
  have hsh : shapeOf id = tDhPk (shapeOf sk) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hsk_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hsk.2.2.1, hi_eval]
  · rw [hg']; dsimp only [node]; rw [hsk.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hsk.2.2.2.1, hsh], by rw [hsk.2.2.1, hi_eval],
        fun _ => by rw [hop]; rfl⟩)
    · exact hsk.2.2.2.2 x hsub

theorem shapeOf_rand {id ts sz : Nat} (hop : opOf id = .rand ts sz := by decide) :
    tRnd ts sz = shapeOf id := by
  unfold shapeOf; rw [dagShape]; simp [hop]

theorem termAt_dh_dhPk {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk1 sk1 pk2 sk2 : Nat} {tsk1 tsk2 : DY.Bytes}
    (hop : opOf id = .dh pk1 sk2 := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hcomm : compLookupDh (clamp (bytesOf sk1)) (bytesOf pk2) = bytesOf id := by decide)
    (hsh1 : tsk1 = shapeOf sk1 := by rfl) (hsh2 : tsk2 = shapeOf sk2 := by rfl)
    (hsk1 : TermAt mode S g pts tsk1 sk1) (hpk1 : TermAt mode S g pts (DY.DiffieHellman.dhPk tsk1) pk1)
    (hsk2 : TermAt mode S g pts tsk2 sk2) (hpk2 : TermAt mode S g pts (DY.DiffieHellman.dhPk tsk2) pk2) :
    TermAt mode S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hpk1_lt, hsk2_lt⟩, hb_eq⟩ := hok
  have hg'_raw : ∀ (tpk tsk : DY.Bytes),
      gamma' compI7003 S g (tDh tpk tsk) =
        node ((compI7003 x25519AgreementSymbol
            [clamp (gamma' compI7003 S g tsk).bytes, (gamma' compI7003 S g tpk).bytes]).getD [])
          (tDh tpk tsk)
          (tDh (gamma' compI7003 S g tpk).shape (gamma' compI7003 S g tsk).shape)
          [gamma' compI7003 S g tpk, gamma' compI7003 S g tsk] :=
    fun tpk tsk =>
      DY.Bytes.rec_eq (concretizeDh compI7003) (concretizeAll compI7003 S g)
        ({ pk := tpk, sk := tsk } : DY.DiffieHellman.Dh.SubF DY.Bytes)
  have hg_pk : ∀ (tsk : DY.Bytes) (sk : Nat), tsk = shapeOf sk → TermAt mode S g pts tsk sk →
      (gamma' compI7003 S g (DY.DiffieHellman.dhPk tsk)).shape = DY.DiffieHellman.dhPk tsk := by
    intro tsk sk hsh hsk
    have hr : gamma' compI7003 S g (DY.DiffieHellman.dhPk tsk) =
        node ((compI7003 x25519PublicKeySymbol [clamp (gamma' compI7003 S g tsk).bytes]).getD [])
          (tDhPk tsk) (tDhPk (gamma' compI7003 S g tsk).shape)
          [gamma' compI7003 S g tsk] :=
      DY.Bytes.rec_eq (concretizeDhPk compI7003) (concretizeAll compI7003 S g)
        ({ sk := tsk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
    rw [hr]; dsimp only [node]; rw [hsk.2.2.2.1, ← hsh]; rfl
  have hg_pk1 := hg_pk tsk1 sk1 hsh1 hsk1
  have hg_pk2 := hg_pk tsk2 sk2 hsh2 hsk2
  have hsh_pk1 : shapeOf pk1 = DY.DiffieHellman.dhPk tsk1 := hpk1.2.2.2.1.symm.trans hg_pk1
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
    have hi_eval : (compI7003 x25519AgreementSymbol [clamp (bytesOf sk2), bytesOf pk1]).getD [] =
        bytesOf id := by unfold compI7003; simp [hne, hb_eq]
    rw [hterm]
    have hg' := hg'_raw (DY.DiffieHellman.dhPk tsk1) tsk2
    refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
    · rw [hg']; dsimp only [node]; rw [hsk2.2.2.1, hpk1.2.2.1, hi_eval]
    · rw [hg']; dsimp only [node]; rw [hg_pk1, hsk2.2.2.2.1, ← hsh2, hsh_eq]
    · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
      rcases List.mem_cons.mp hx with rfl | hsub
      · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hg_pk1, hsk2.2.2.2.1, ← hsh2, hsh_eq],
          by rw [hsk2.2.2.1, hpk1.2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
      · rcases List.mem_append.mp hsub with hxp | hxs
        · exact hpk1.2.2.2.2 x hxp
        · exact hsk2.2.2.2.2 x hxs
  · have hterm : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk tsk1) tsk2 =
        tDh (DY.DiffieHellman.dhPk tsk2) tsk1 := by
      rw [hdh_unfold]; simp only [hle, ↓reduceIte]
    have hsh_eq : shapeOf id = tDh (DY.DiffieHellman.dhPk tsk2) tsk1 := hsh_id.trans hterm
    have hi_eval : (compI7003 x25519AgreementSymbol [clamp (bytesOf sk1), bytesOf pk2]).getD [] =
        bytesOf id := by unfold compI7003; simp [hne, hcomm]
    rw [hterm]
    have hg' := hg'_raw (DY.DiffieHellman.dhPk tsk2) tsk1
    refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
    · rw [hg']; dsimp only [node]; rw [hsk1.2.2.1, hpk2.2.2.1, hi_eval]
    · rw [hg']; dsimp only [node]; rw [hg_pk2, hsk1.2.2.2.1, ← hsh1, hsh_eq]
    · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
      rcases List.mem_cons.mp hx with rfl | hsub
      · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hg_pk2, hsk1.2.2.2.1, ← hsh1, hsh_eq],
          by rw [hsk1.2.2.1, hpk2.2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
      · rcases List.mem_append.mp hsub with hxp | hxs
        · exact hpk2.2.2.2.2 x hxp
        · exact hsk1.2.2.2.2 x hxs

theorem termAt_kdf {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id salt ikm : Nat} {tsalt tikm : DY.Bytes}
    (hop : opOf id = .kdf salt ikm := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hsalt : TermAt mode S g pts tsalt salt) (hikm : TermAt mode S g pts tikm ikm) :
    TermAt mode S g pts (tKdf tsalt tikm) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hs_lt, hi_lt⟩, hb_eq⟩ := hok
  have hg' : gamma' compI7003 S g (tKdf tsalt tikm) =
      node (hmacWith (sha256CompressFunction compI7003)
          (gamma' compI7003 S g tsalt).bytes (gamma' compI7003 S g tikm).bytes)
        (tKdf tsalt tikm)
        (tKdf (gamma' compI7003 S g tsalt).shape (gamma' compI7003 S g tikm).shape)
        [gamma' compI7003 S g tsalt, gamma' compI7003 S g tikm] :=
    DY.Bytes.rec_eq (concretizeKdf compI7003) (concretizeAll compI7003 S g)
      ({ salt := tsalt, ikm := tikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes)
  have hsh : shapeOf id = tKdf (shapeOf salt) (shapeOf ikm) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hs_lt, hi_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hsalt.2.2.1, hikm.2.2.1]; exact hb_eq
  · rw [hg']; dsimp only [node]; rw [hsalt.2.2.2.1, hikm.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hsalt.2.2.2.1, hikm.2.2.2.1, hsh],
        by rw [hsalt.2.2.1, hikm.2.2.1]; exact hb_eq, fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxs | hxi
      · exact hsalt.2.2.2.2 x hxs
      · exact hikm.2.2.2.2 x hxi

theorem termAt_trunc8 {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id inp : Nat} {tinp : DY.Bytes}
    (hop : opOf id = .trunc8 inp := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hinp : TermAt mode S g pts tinp inp) :
    TermAt mode S g pts (tTr8 tinp) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨hi_lt, hb_eq⟩ := hok
  have hg' : gamma' compI7003 S g (tTr8 tinp) =
      node ((gamma' compI7003 S g tinp).bytes.take 8)
        (tTr8 tinp) (tTr8 (gamma' compI7003 S g tinp).shape)
        [gamma' compI7003 S g tinp] :=
    DY.Bytes.rec_eq concretizeTrunc (concretizeAll compI7003 S g)
      ({ input := tinp } : DY.Trunc.Trunc8.SubF DY.Bytes)
  have hsh : shapeOf id = tTr8 (shapeOf inp) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hi_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [hinp.2.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [hinp.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hinp.2.2.2.1, hsh],
        by rw [hinp.2.2.1, hb_eq], fun _ => by rw [hop]; rfl⟩)
    · exact hinp.2.2.2.2 x hsub

theorem termAt_symEncPt {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id key iv ts : Nat} {pt : HwBytes} {tkey tiv : DY.Bytes}
    (hop : opOf id = .symEncPt key iv ts pt := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hkey : TermAt mode S g pts tkey key) (hiv : TermAt mode S g pts tiv iv)
    (hpt_mem : tRnd ts 32 ∈ pts) (hpt_bs : IsPt7003Bytes pt) (hg_pt : g.σ ts 32 = pt) :
    TermAt mode S g pts (tSym tkey tiv (tRnd ts 32)) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨hk_lt, hiv_lt⟩, hb_eq⟩ := hok
  have hg' : gamma' compI7003 S g (tSym tkey tiv (tRnd ts 32)) =
      node ((compI7003 aesCbcEncryptSymbol
          [(gamma' compI7003 S g (tRnd ts 32)).bytes,
           (gamma' compI7003 S g tkey).bytes,
           (gamma' compI7003 S g tiv).bytes.take 16]).getD [])
        (tSym tkey tiv (tRnd ts 32))
        (tSym (gamma' compI7003 S g tkey).shape (gamma' compI7003 S g tiv).shape
          (gamma' compI7003 S g (tRnd ts 32)).shape)
        [gamma' compI7003 S g tkey, gamma' compI7003 S g tiv,
         gamma' compI7003 S g (tRnd ts 32)] :=
    DY.Bytes.rec_eq (concretizeSym compI7003) (concretizeAll compI7003 S g)
      ({ key := tkey, iv := tiv, msg := tRnd ts 32 } : DY.SymEnc.Enc.SubF DY.Bytes)
  have hpt_g := gamma'_plaintext_eq (S := S) hg_pt
  have hi_eval : (compI7003 aesCbcEncryptSymbol
      [pt, bytesOf key, (bytesOf iv).take 16]).getD [] = bytesOf id := by
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws.compI7003_aesEncrypt]
    exact hb_eq
  have hsh : shapeOf id = tSym (shapeOf key) (shapeOf iv) (tRnd ts 32) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hk_lt, hiv_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg', hpt_g]; dsimp only [node]; rw [hkey.2.2.1, hiv.2.2.1, hi_eval]
  · rw [hg', hpt_g]; dsimp only [node]; rw [hkey.2.2.2.1, hiv.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · rw [hpt_g]
      exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hkey.2.2.2.1, hiv.2.2.2.1, hsh],
        by rw [hkey.2.2.1, hiv.2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxk | rest
      · exact hkey.2.2.2.2 x hxk
      · rcases List.mem_append.mp rest with hxi | hxp
        · exact hiv.2.2.2.2 x hxi
        · exact safeMemo_plaintext hpt_mem hpt_bs hg_pt x hxp

theorem termAt_trWire {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id : Nat} {ver : UInt8} {rk : Nat} {cnt prev : UInt32} {ct pq : Nat} {addr : HwBytes}
    {useEv4Var : Bool} {trk tct tpq : DY.Bytes}
    (hop : opOf id = .trWire ver rk cnt prev ct pq addr useEv4Var := by decide)
    (hid : id < dagSize := by decide) (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hrk : TermAt mode S g pts trk rk) (hct : TermAt mode S g pts tct ct)
    (hpq : TermAt mode S g pts tpq pq)
    (haddr : g.addr (tTrW ver trk cnt prev tct tpq (trWireEvOf useEv4Var)) = addr) :
    TermAt mode S g pts (tTrW ver trk cnt prev tct tpq (trWireEvOf useEv4Var)) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hrk_lt, hct_lt⟩, hpq_lt⟩, hb_eq⟩ := hok
  let ev := trWireEvOf useEv4Var
  let tw := tTrW ver trk cnt prev tct tpq ev
  have hg' : gamma' compI7003 S g tw =
      node (trWireBytes (g.addr tw) ev
          { version := ver.toNat, ratchetKey := (gamma' compI7003 S g trk).bytes,
            counter := cnt.toNat, previousCounter := prev.toNat,
            ciphertext := (gamma' compI7003 S g tct).bytes }
          (gamma' compI7003 S g tpq).bytes)
        tw
        (tTrW ver (gamma' compI7003 S g trk).shape cnt prev
          (gamma' compI7003 S g tct).shape (gamma' compI7003 S g tpq).shape
          (trWireShapeVar (g.addr tw) useEv4Var))
        [gamma' compI7003 S g trk, gamma' compI7003 S g tct, gamma' compI7003 S g tpq] :=
    DY.Bytes.rec_eq (concretizeTrWire g) (concretizeAll compI7003 S g)
      ({ version := ver, senderRatchetKey := trk, counter := cnt, previousCounter := prev,
         ciphertext := tct, pqRatchet := tpq,
         encodingVariation := ev } : DY.TrWire.TrWireMsg.SubF DY.Bytes)
  have hsh : shapeOf id =
      tTrW ver (shapeOf rk) cnt prev (shapeOf ct) (shapeOf pq) (trWireShapeVar addr useEv4Var) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hrk_lt, hct_lt, hpq_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; dsimp only [node]; rw [haddr, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hb_eq]
  · rw [hg']; dsimp only [node]; rw [haddr, hrk.2.2.2.1, hct.2.2.2.1, hpq.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · refine Or.inr (Or.inr ⟨id, hid, hskp, ?_, ?_, fun hai => ?_⟩)
      · rw [haddr, hrk.2.2.2.1, hct.2.2.2.1, hpq.2.2.2.1, hsh]
      · rw [haddr, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hb_eq]
      · have hfalse : assumedInjective tw = false := ai_trWire_pack_eq _
        rw [hfalse] at hai; cases hai
    · rcases List.mem_append.mp hsub with hxr | rest
      · exact hrk.2.2.2.2 x hxr
      · rcases List.mem_append.mp rest with hxc | hxp
        · exact hct.2.2.2.2 x hxc
        · exact hpq.2.2.2.2 x hxp

theorem termAt_kemEncap {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk ent : Nat} {tpk tent : DY.Bytes}
    (hop : opOf id = .kemEncap pk ent := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hpk : TermAt mode S g pts tpk pk) (hent : TermAt mode S g pts tent ent) :
    TermAt mode S g pts (tKemEnc tpk tent) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpk_lt, hent_lt⟩, hlen_beq⟩, hb_eq⟩ := hok
  have hlen32 : (bytesOf ent).length = 32 := Nat.beq_eq.mp hlen_beq
  have hg' : gamma' compI7003 S g (tKemEnc tpk tent) =
      if (gamma' compI7003 S g tent).bytes.length = 32 then
        node (((compI7003 kyberEncapsSymbol
            [(gamma' compI7003 S g tpk).bytes, (gamma' compI7003 S g tent).bytes]).getD []).take 1568)
          (tKemEnc tpk tent)
          (tKemEnc (gamma' compI7003 S g tpk).shape (gamma' compI7003 S g tent).shape)
          [gamma' compI7003 S g tpk, gamma' compI7003 S g tent]
      else opaqueNode [] [gamma' compI7003 S g tpk, gamma' compI7003 S g tent] :=
    DY.Bytes.rec_eq (concretizeKemEncap compI7003) (concretizeAll compI7003 S g)
      ({ pk := tpk, entropy := tent } : DY.PQKem.Encap.SubF DY.Bytes)
  have hi_eval : ((compI7003 kyberEncapsSymbol [bytesOf pk, bytesOf ent]).getD []).take 1568 =
      bytesOf id := by
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws.compI7003_kyberEncaps]
    exact hb_eq
  have hsh : shapeOf id = tKemEnc (shapeOf pk) (shapeOf ent) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hpk_lt, hent_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; simp [hent.2.2.1, hlen32, node, hpk.2.2.1, hi_eval]
  · rw [hg']; simp [hent.2.2.1, hlen32, node, hpk.2.2.2.1, hent.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [hent.2.2.1, hlen32, ↓reduceIte, node,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hpk.2.2.2.1, hent.2.2.2.1, hsh],
        by rw [hpk.2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxp | hxe
      · exact hpk.2.2.2.2 x hxp
      · exact hent.2.2.2.2 x hxe

theorem termAt_kemSS {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {id pk ent : Nat} {tpk tent : DY.Bytes}
    (hop : opOf id = .kemSS pk ent := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hpk : TermAt mode S g pts tpk pk) (hent : TermAt mode S g pts tent ent) :
    TermAt mode S g pts (tKemSS tpk tent) id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpk_lt, hent_lt⟩, hlen_beq⟩, hb_eq⟩ := hok
  have hlen32 : (bytesOf ent).length = 32 := Nat.beq_eq.mp hlen_beq
  have hg' : gamma' compI7003 S g (tKemSS tpk tent) =
      if (gamma' compI7003 S g tent).bytes.length = 32 then
        node (((compI7003 kyberEncapsSymbol
            [(gamma' compI7003 S g tpk).bytes, (gamma' compI7003 S g tent).bytes]).getD []).drop 1568)
          (tKemSS tpk tent)
          (tKemSS (gamma' compI7003 S g tpk).shape (gamma' compI7003 S g tent).shape)
          [gamma' compI7003 S g tpk, gamma' compI7003 S g tent]
      else opaqueNode (S.kemDecap (gamma' compI7003 S g tpk).bytes (gamma' compI7003 S g tent).bytes)
        [gamma' compI7003 S g tpk, gamma' compI7003 S g tent] :=
    DY.Bytes.rec_eq (concretizeKemSS compI7003 S) (concretizeAll compI7003 S g)
      ({ pk := tpk, entropy := tent } : DY.PQKem.SharedSecret.SubF DY.Bytes)
  have hi_eval : ((compI7003 kyberEncapsSymbol [bytesOf pk, bytesOf ent]).getD []).drop 1568 =
      bytesOf id := by
    rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws.compI7003_kyberEncaps]
    exact hb_eq
  have hsh : shapeOf id = tKemSS (shapeOf pk) (shapeOf ent) := by
    unfold shapeOf; rw [dagShape]; simp [hop, hpk_lt, hent_lt]
  refine ⟨hid, hskp, ?_, ?_, fun x hx => ?_⟩
  · rw [hg']; simp [hent.2.2.1, hlen32, node, hpk.2.2.1, hi_eval]
  · rw [hg']; simp [hent.2.2.1, hlen32, node, hpk.2.2.2.1, hent.2.2.2.1, hsh]
  · rw [hg'] at hx; simp only [hent.2.2.1, hlen32, ↓reduceIte, node,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hsub
    · exact Or.inr (Or.inr ⟨id, hid, hskp, by rw [hpk.2.2.2.1, hent.2.2.2.1, hsh],
        by rw [hpk.2.2.1, hi_eval], fun _ => by rw [hop]; rfl⟩)
    · rcases List.mem_append.mp hsub with hxp | hxe
      · exact hpk.2.2.2.2 x hxp
      · exact hent.2.2.2.2 x hxe

/-! ## Opaque-Node `TermAt` & `SafeMemo` Wrappers (Parametric in `∀ S`) -/

theorem termAt_of_opaque_pinned {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {t : DY.Bytes} {id : Nat} {bs : HwBytes}
    (hop : opOf id = .lit bs := by decide) (hid : id < dagSize := by decide)
    (hskp : id ≠ skipIdOf mode := by skip_ok)
    (hsh_lit : (gamma' compI7003 S g t).shape = tLit (gamma compI7003 S g t))
    (hgam : gamma compI7003 S g t = bytesOf id)
    (hmemo : SafeMemo mode S g pts t) :
    TermAt mode S g pts t id := by
  have hok := dagOpBytesOk_of_id hid
  rw [hop] at hok
  simp only [dagOpBytesOk, beq_iff_eq] at hok
  have hsh : shapeOf id = tLit bs := by
    unfold shapeOf; rw [dagShape]; simp [hop]
  refine ⟨hid, hskp, hgam, ?_, hmemo⟩
  rw [hsh_lit, hgam, ← hok, hsh]

theorem opaque_kemPk {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {sk : DY.Bytes} (hsk : SafeMemo mode S g pts sk) :
    (gamma' compI7003 S g (DY.PQKem.kemPk sk)).shape =
      tLit (gamma compI7003 S g (DY.PQKem.kemPk sk)) ∧
    SafeMemo mode S g pts (DY.PQKem.kemPk sk) := by
  have hg' : gamma' compI7003 S g (DY.PQKem.kemPk sk) =
      opaqueNode (S.kemPk (gamma' compI7003 S g sk).bytes) [gamma' compI7003 S g sk] :=
    DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll compI7003 S g)
      ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx; simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    exact hsk x hx

theorem safeMemo_spqrInit {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {a p : DY.Bytes}
    (ha : SafeMemo mode S g pts a) (hp : SafeMemo mode S g pts p) :
    SafeMemo mode S g pts (DY.Spqr.spqrInit a p) := by
  have hg' : gamma' compI7003 S g (DY.Spqr.spqrInit a p) =
      opaqueNode (S.init (gamma' compI7003 S g a).bytes (gamma' compI7003 S g p).bytes)
        [gamma' compI7003 S g a, gamma' compI7003 S g p] :=
    DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll compI7003 S g)
      ({ authKey := a, params := p } : DY.Spqr.InitState.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_append.mp hx with hxa | hxp
  · exact ha x hxa
  · exact hp x hxp

theorem safeMemo_spqrSendState {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {st c : DY.Bytes}
    (hst : SafeMemo mode S g pts st) (hc : SafeMemo mode S g pts c) :
    SafeMemo mode S g pts (tSSendSt st c) := by
  have hg' : gamma' compI7003 S g (tSSendSt st c) =
      opaqueNode (S.sendState (gamma' compI7003 S g st).bytes (gamma' compI7003 S g c).bytes)
        [gamma' compI7003 S g st, gamma' compI7003 S g c] :=
    DY.Bytes.rec_eq (concretizeSpqrSendState S) (concretizeAll compI7003 S g)
      ({ st := st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_append.mp hx with hxs | hxc
  · exact hst x hxs
  · exact hc x hxc

theorem safeMemo_spqrRecvState {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {st m : DY.Bytes}
    (hst : SafeMemo mode S g pts st) (hm : SafeMemo mode S g pts m) :
    SafeMemo mode S g pts (({ st := st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes).pack) := by
  have hg' : gamma' compI7003 S g (({ st := st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes).pack) =
      opaqueNode (S.recvState (gamma' compI7003 S g st).bytes (gamma' compI7003 S g m).bytes)
        [gamma' compI7003 S g st, gamma' compI7003 S g m] :=
    DY.Bytes.rec_eq (concretizeSpqrRecvState S) (concretizeAll compI7003 S g)
      ({ st := st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_append.mp hx with hxs | hxm
  · exact hst x hxs
  · exact hm x hxm

theorem opaque_spqrSendMsg {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {st c : DY.Bytes}
    (hst : SafeMemo mode S g pts st) (hc : SafeMemo mode S g pts c) :
    (gamma' compI7003 S g (tSSendM st c)).shape =
      tLit (gamma compI7003 S g (tSSendM st c)) ∧
    SafeMemo mode S g pts (tSSendM st c) := by
  have hg' : gamma' compI7003 S g (tSSendM st c) =
      opaqueNode (S.sendMsg (gamma' compI7003 S g st).bytes (gamma' compI7003 S g c).bytes)
        [gamma' compI7003 S g st, gamma' compI7003 S g c] :=
    DY.Bytes.rec_eq (concretizeSpqrSendMsg S) (concretizeAll compI7003 S g)
      ({ st := st, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx
    simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_append.mp hx with hxs | hxc
    · exact hst x hxs
    · exact hc x hxc

theorem opaque_spqrSendKey {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {st c : DY.Bytes}
    (hst : SafeMemo mode S g pts st) (hc : SafeMemo mode S g pts c) :
    (gamma' compI7003 S g (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack)).shape =
      tLit (gamma compI7003 S g (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack)) ∧
    SafeMemo mode S g pts (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack) := by
  have hg' : gamma' compI7003 S g (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack) =
      spqrKeyNode (S.sendKey (gamma' compI7003 S g st).bytes (gamma' compI7003 S g c).bytes)
        [gamma' compI7003 S g st, gamma' compI7003 S g c] :=
    DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S)
      (concretizeAll compI7003 S g) ({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes)
  refine ⟨?_, fun x hx => ?_⟩
  · unfold gamma; rw [hg']; rfl
  · rw [hg'] at hx
    simp only [spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    rcases List.mem_append.mp hx with hxs | hxc
    · exact hst x hxs
    · exact hc x hxc

theorem opaque_spqrChainKey {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {a p idx : DY.Bytes}
    (ha : SafeMemo mode S g pts a) (hp : SafeMemo mode S g pts p)
    (hidx : SafeMemo mode S g pts idx) :
    (gamma' compI7003 S g (DY.Spqr.spqrChainKey a p idx)).shape =
      tLit (gamma compI7003 S g (DY.Spqr.spqrChainKey a p idx)) ∧
    SafeMemo mode S g pts (DY.Spqr.spqrChainKey a p idx) ∧
    (gamma compI7003 S g (DY.Spqr.spqrChainKey a p idx)).length = 32 := by
  have hg' : gamma' compI7003 S g (DY.Spqr.spqrChainKey a p idx) =
      spqrKeyNode (S.chainKey (gamma' compI7003 S g a).bytes (gamma' compI7003 S g p).bytes
        (gamma' compI7003 S g idx).bytes)
        [gamma' compI7003 S g a, gamma' compI7003 S g p, gamma' compI7003 S g idx] :=
    DY.Bytes.rec_eq (concretizeSpqrChainKey S) (concretizeAll compI7003 S g)
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
    gamma' compI7003 S g (tLit bs) =
      { bytes := bs, shape := tLit bs, memo := [(tLit bs, tLit bs, bs)] } := by
  unfold gamma'
  change (({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack).rec
    (concretizeAll compI7003 S g) = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll compI7003 S g)
    ({ lit := ⟨(bs.map UInt8.ofBitVec).toArray⟩ } : DY.Literal.Literal.SubF DY.Bytes)]
  simp [concretizeLit, node, ofByteArray_litOf_eq, tLit, litOf]

theorem gamma_literalToBytes {S : OpaqueSymbolSemantics} {g : Ghost} (ba : ByteArray) :
    gamma compI7003 S g (DY.Literal.literalToBytes ba) = ofByteArray ba := by
  rw [literalToBytes_eq_tLit]; unfold gamma; rw [gamma'_tLit_eq]

theorem safeMemo_lit_nonAI {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {ba : ByteArray}
    (hno : notAnyAiNodeBytes (ofByteArray ba) = true) :
    SafeMemo mode S g pts (DY.Literal.literalToBytes ba) := by
  rw [literalToBytes_eq_tLit]
  intro x hx
  rw [gamma'_tLit_eq] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact Or.inr (Or.inl ⟨ai_lit_pack_eq _, hno⟩)

theorem gamma_concat {S : OpaqueSymbolSemantics} {g : Ghost} (tl tr : DY.Bytes) :
    gamma compI7003 S g (tCat tl tr) =
      gamma compI7003 S g tl ++ gamma compI7003 S g tr := by
  unfold gamma
  rw [show gamma' compI7003 S g (tCat tl tr) = _ from
    DY.Bytes.rec_eq concretizeConcat (concretizeAll compI7003 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)]
  rfl

theorem safeMemo_concat_nonAI {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {tl tr : DY.Bytes}
    (hl : SafeMemo mode S g pts tl) (hr : SafeMemo mode S g pts tr)
    (hno : notAnyAiNodeBytes (gamma compI7003 S g tl ++ gamma compI7003 S g tr) = true) :
    SafeMemo mode S g pts (tCat tl tr) := by
  have hg' : gamma' compI7003 S g (tCat tl tr) =
      node ((gamma' compI7003 S g tl).bytes ++ (gamma' compI7003 S g tr).bytes)
        (tCat tl tr)
        (tCat (gamma' compI7003 S g tl).shape (gamma' compI7003 S g tr).shape)
        [gamma' compI7003 S g tl, gamma' compI7003 S g tr] :=
    DY.Bytes.rec_eq concretizeConcat (concretizeAll compI7003 S g)
      ({ lhs := tl, rhs := tr } : DY.Concat.Concat.SubF DY.Bytes)
  intro x hx
  rw [hg'] at hx
  simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  rcases List.mem_cons.mp hx with rfl | hsub
  · exact Or.inr (Or.inl ⟨ai_concat_eq tl tr, hno⟩)
  · rcases List.mem_append.mp hsub with hxl | hxr
    · exact hl x hxl
    · exact hr x hxr

theorem safeMemo_bytesLike_empty {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} :
    SafeMemo mode S g pts (_root_.Comparse.BytesLike.empty : DY.Bytes) ∧
    gamma compI7003 S g (_root_.Comparse.BytesLike.empty : DY.Bytes) = [] := by
  change SafeMemo mode S g pts (DY.Literal.literalToBytes .empty) ∧
    gamma compI7003 S g (DY.Literal.literalToBytes .empty) = []
  have hempty : ofByteArray .empty = [] := rfl
  refine ⟨safeMemo_lit_nonAI ?_, by rw [gamma_literalToBytes, hempty]⟩
  rw [hempty]; decide +kernel

theorem safeMemo_mem_bool {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (b : Bool) {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize b) :
    SafeMemo mode S g pts p ∧
    gamma compI7003 S g p = (if b then [1#8] else [0#8]) ∧
    0 < (gamma compI7003 S g p).length := by
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

theorem safeMemo_mem_slowNat {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} :
    ∀ (n : Nat) {p : DY.Bytes},
      p ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n →
      SafeMemo mode S g pts p ∧ 0 < (gamma compI7003 S g p).length
  | 0, _, hp => by
    rw [slowNat_serialize_zero] at hp
    have h := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) false hp
    exact ⟨h.1, h.2.2⟩
  | n + 1, _, hp => by
    rw [slowNat_serialize_succ] at hp
    rcases List.mem_append.mp hp with h1 | h2
    · have h := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) true h1
      exact ⟨h.1, h.2.2⟩
    · exact safeMemo_mem_slowNat n h2

theorem safeMemo_mem_slowString {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {str : String}
    (hno : notAnyAiNodeBytes (ofByteArray str.toUTF8) = true)
    (hne : 0 < (ofByteArray str.toUTF8).length)
    {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize str) :
    SafeMemo mode S g pts p ∧ 0 < (gamma compI7003 S g p).length := by
  rw [slowString_serialize_eq] at hp
  rcases List.mem_append.mp hp with h1 | h2
  · exact safeMemo_mem_slowNat _ h1
  · rcases List.mem_singleton.mp h2 with rfl
    exact ⟨safeMemo_lit_nonAI hno, by rw [gamma_literalToBytes]; exact hne⟩

def IsU32SmallBytes (u : HwBytes) : Prop :=
  u = [0#8, 0#8, 0#8, 0#8] ∨ u = [0#8, 0#8, 0#8, 1#8] ∨ u = [1#8, 0#8, 0#8, 0#8] ∨
  u = [0#8, 0#8, 0#8, 2#8] ∨ u = [2#8, 0#8, 0#8, 0#8]

theorem safeMemo_mem_uint32_small {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {x : UInt32} (hx : x = 0 ∨ x = 1 ∨ x = 2) {p : DY.Bytes}
    (hp : p ∈ (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := DY.Bytes)).serialize x) :
    SafeMemo mode S g pts p ∧ ∃ u : HwBytes, IsU32SmallBytes u ∧ gamma compI7003 S g p = u := by
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

theorem safeMemo_recvTailTerm_0_1 {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (rk ck : DY.Bytes) :
    let c : DY.Libsignal.TripleRatchet.RecvChain :=
      { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }
    SafeMemo mode S g pts (recvTailTerm c) ∧
    ∃ u : HwBytes, IsU32SmallBytes u ∧
      gamma compI7003 S g (recvTailTerm c) = u ++ [1#8, 0#8] := by
  dsimp only [recvTailTerm]
  obtain ⟨ba0, _, _, hu0⟩ := uint32_serialize_singleton_head 0 (Or.inl rfl)
  obtain ⟨bat, _, _, hbt⟩ := bool_serialize_singleton_head true
  obtain ⟨baf, _, _, hbf⟩ := bool_serialize_singleton_head false
  have hsn1 : (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize 1 =
      [DY.Literal.literalToBytes bat, DY.Literal.literalToBytes baf] := by
    rw [slowNat_serialize_succ, slowNat_serialize_zero, hbt, hbf]; rfl
  rw [hu0, hsn1]
  simp only [List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
  obtain ⟨hs0, u, hu, hg0⟩ := safeMemo_mem_uint32_small (mode := mode) (S := S) (g := g)
    (pts := pts) (x := 0) (Or.inl rfl) (by rw [hu0]; exact List.mem_singleton.mpr rfl)
  have hpt := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) true
    (by rw [hbt]; exact List.mem_singleton.mpr rfl)
  have hpf := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) false
    (by rw [hbf]; exact List.mem_singleton.mpr rfl)
  have hemp := safeMemo_bytesLike_empty (mode := mode) (S := S) (g := g) (pts := pts)
  let t1 := tCat (DY.Literal.literalToBytes baf) _root_.Comparse.BytesLike.empty
  have hg1 : gamma compI7003 S g t1 = [0#8] := by
    dsimp only [t1]; rw [gamma_concat, hpf.2.1, hemp.2]; rfl
  have hs1 : SafeMemo mode S g pts t1 :=
    safeMemo_concat_nonAI hpf.1 hemp.1 (by rw [hpf.2.1, hemp.2]; decide +kernel)
  let t2 := tCat (DY.Literal.literalToBytes bat) t1
  have hg2 : gamma compI7003 S g t2 = [1#8, 0#8] := by
    dsimp only [t2]; rw [gamma_concat, hpt.2.1, hg1]; rfl
  have hs2 : SafeMemo mode S g pts t2 :=
    safeMemo_concat_nonAI hpt.1 hs1 (by rw [hpt.2.1, hg1]; decide +kernel)
  let t3 := tCat (DY.Literal.literalToBytes ba0) t2
  have hg3 : gamma compI7003 S g t3 = u ++ [1#8, 0#8] := by
    dsimp only [t3]; rw [gamma_concat, hg0, hg2]
  have hs3 : SafeMemo mode S g pts t3 := by
    apply safeMemo_concat_nonAI hs0 hs2
    rw [hg0, hg2]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨hs3, u, hu, hg3⟩

theorem safeMemo_recvTailTerm_1_2 {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (rk ck : DY.Bytes) :
    let c : DY.Libsignal.TripleRatchet.RecvChain :=
      { ratchetKey := rk, chainKey := ck, index := 1, rIdx := 2 }
    SafeMemo mode S g pts (recvTailTerm c) ∧
    ∃ u : HwBytes, IsU32SmallBytes u ∧
      gamma compI7003 S g (recvTailTerm c) = u ++ [1#8, 1#8, 0#8] := by
  dsimp only [recvTailTerm]
  obtain ⟨ba1, _, _, hu1⟩ := uint32_serialize_singleton_head 1 (Or.inr (Or.inl rfl))
  obtain ⟨bat, _, _, hbt⟩ := bool_serialize_singleton_head true
  obtain ⟨baf, _, _, hbf⟩ := bool_serialize_singleton_head false
  have hsn2 : (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize 2 =
      [DY.Literal.literalToBytes bat, DY.Literal.literalToBytes bat,
       DY.Literal.literalToBytes baf] := by
    rw [slowNat_serialize_succ, slowNat_serialize_succ, slowNat_serialize_zero, hbt, hbf]; rfl
  rw [hu1, hsn2]
  simp only [List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
  obtain ⟨hs1, u, hu, hg1⟩ := safeMemo_mem_uint32_small (mode := mode) (S := S) (g := g)
    (pts := pts) (x := 1) (Or.inr (Or.inl rfl)) (by rw [hu1]; exact List.mem_singleton.mpr rfl)
  have hpt := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) true
    (by rw [hbt]; exact List.mem_singleton.mpr rfl)
  have hpf := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) false
    (by rw [hbf]; exact List.mem_singleton.mpr rfl)
  have hemp := safeMemo_bytesLike_empty (mode := mode) (S := S) (g := g) (pts := pts)
  let t1 := tCat (DY.Literal.literalToBytes baf) _root_.Comparse.BytesLike.empty
  have hgt1 : gamma compI7003 S g t1 = [0#8] := by
    dsimp only [t1]; rw [gamma_concat, hpf.2.1, hemp.2]; rfl
  have hst1 : SafeMemo mode S g pts t1 :=
    safeMemo_concat_nonAI hpf.1 hemp.1 (by rw [hpf.2.1, hemp.2]; decide +kernel)
  let t2 := tCat (DY.Literal.literalToBytes bat) t1
  have hgt2 : gamma compI7003 S g t2 = [1#8, 0#8] := by
    dsimp only [t2]; rw [gamma_concat, hpt.2.1, hgt1]; rfl
  have hst2 : SafeMemo mode S g pts t2 :=
    safeMemo_concat_nonAI hpt.1 hst1 (by rw [hpt.2.1, hgt1]; decide +kernel)
  let t3 := tCat (DY.Literal.literalToBytes bat) t2
  have hgt3 : gamma compI7003 S g t3 = [1#8, 1#8, 0#8] := by
    dsimp only [t3]; rw [gamma_concat, hpt.2.1, hgt2]; rfl
  have hst3 : SafeMemo mode S g pts t3 :=
    safeMemo_concat_nonAI hpt.1 hst2 (by rw [hpt.2.1, hgt2]; decide +kernel)
  let t4 := tCat (DY.Literal.literalToBytes ba1) t3
  have hgt4 : gamma compI7003 S g t4 = u ++ [1#8, 1#8, 0#8] := by
    dsimp only [t4]; rw [gamma_concat, hg1, hgt3]
  have hst4 : SafeMemo mode S g pts t4 := by
    apply safeMemo_concat_nonAI hs1 hst3
    rw [hg1, hgt3]
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨hst4, u, hu, hgt4⟩

theorem safeMemo_concatPrefixes_strict {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (ps : List DY.Bytes) {s : DY.Bytes}
    (hps : ∀ p ∈ ps, SafeMemo mode S g pts p ∧ 0 < (gamma compI7003 S g p).length)
    (hs : SafeMemo mode S g pts s)
    (hstrict : noStrictAiSuffix (gamma compI7003 S g s) = true) :
    SafeMemo mode S g pts (_root_.Comparse.concatPrefixes ps s) ∧
    gamma compI7003 S g s <:+ gamma compI7003 S g (_root_.Comparse.concatPrefixes ps s) := by
  induction ps with
  | nil =>
    rw [concatPrefixes_nil]
    exact ⟨hs, List.suffix_rfl⟩
  | cons p ps ih =>
    rw [concatPrefixes_cons]
    obtain ⟨hrest, hsuf⟩ := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
    obtain ⟨hp_safe, hp_pos⟩ := hps p List.mem_cons_self
    have hsuf' : gamma compI7003 S g s <:+
        gamma compI7003 S g p ++ gamma compI7003 S g (_root_.Comparse.concatPrefixes ps s) :=
      hsuf.trans (List.suffix_append _ _)
    have hle : (gamma compI7003 S g s).length ≤
        (gamma compI7003 S g (_root_.Comparse.concatPrefixes ps s)).length := hsuf.length_le
    have hlt : (gamma compI7003 S g s).length <
        (gamma compI7003 S g p ++
          gamma compI7003 S g (_root_.Comparse.concatPrefixes ps s)).length := by
      rw [List.length_append]; omega
    refine ⟨safeMemo_concat_nonAI hp_safe hrest
      (notAnyAiNodeBytes_of_noStrictAiSuffix hstrict hlt hsuf'), ?_⟩
    change gamma compI7003 S g s <:+
      gamma compI7003 S g (tCat p (_root_.Comparse.concatPrefixes ps s))
    rw [gamma_concat]
    exact hsuf'

theorem safeMemo_serialize_local_pqxdh {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} (ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)
    (hpart : notAnyAiNodeBytes (ofByteArray ls.participant.toUTF8) = true)
    (hpne : 0 < (ofByteArray ls.participant.toUTF8).length)
    (hsk : SafeMemo mode S g pts ls.state.sk)
    (hstrict : noStrictAiSuffix (gamma compI7003 S g ls.state.sk) = true) :
    SafeMemo mode S g pts (DY.Comparse.serialize ls) := by
  rw [serialize_local_pqxdh_eq_bridge ls]
  refine (safeMemo_concatPrefixes_strict _ (fun p hp => ?_) hsk hstrict).1
  rcases List.mem_append.mp hp with hs | hb
  · exact safeMemo_mem_slowString hpart hpne hs
  · rcases List.mem_append.mp hb with hb1 | hb2
    · have h := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) ls.state.kind.toBits.1 hb1
      exact ⟨h.1, h.2.2⟩
    · have h := safeMemo_mem_bool (mode := mode) (S := S) (g := g) (pts := pts) ls.state.kind.toBits.2 hb2
      exact ⟨h.1, h.2.2⟩

theorem safeMemo_trState_of_noAiSuffix {mode : Bool} {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {ls : DY.PersistentLocalState.LocalState TRState}
    (hanc : noAiSuffix (gamma compI7003 S g (stateAnchorPair ls).1 ++
                        gamma compI7003 S g (stateAnchorPair ls).2) = true)
    (hroots : ∀ p ∈ trStateProxyRoots ls, SafeMemo mode S g pts p) :
    SafeMemo mode S g pts (DY.Comparse.serialize ls) := by
  intro x hx
  rcases serialize_localTR_memo compI7003 S g ls hx with ⟨p, hp, hxp⟩ | ⟨hinj, hsfx⟩
  · exact hroots p hp x hxp
  · exact Or.inr (Or.inl ⟨hinj, notAnyAiNodeBytes_of_noAiSuffix hanc hsfx⟩)

end Unsealed

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt
