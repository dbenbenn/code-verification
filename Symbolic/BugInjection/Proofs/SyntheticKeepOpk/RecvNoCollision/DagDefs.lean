/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
public import Symbolic.Proofs.Tests.Shared.Composed.Runs
import Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue
import DY.Bytes.Basic
import Comparse.Basic
import DY.Comparse
import DY.Actions.PersistentLocalState
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Comparse

/-!
# Concrete DAG Certificate Types, `TermAt` Combinators, and `SafeMemo2` (`DagDefs.lean`)

Provides for `keepOpkI0`:
1. `DagOp`, `dagOpBytesOk`, `dagNodeOk`, `evalDagShapeAux`, `packBytesKey`, `bucketNoCollision`,
   and `endsWith0100`.
2. `dagShape`, `SafeEntry`, `SafeMemo`, `TermAt`, and `termAt_*` / `safeMemo_*` combinators.
3. `SafeEntry2`, `SafeMemo2`, `not_memoCollisionOn_of_safeMemo2`, and `safeMemo2_trState_of_dr`.
4. `encMsg_pins_pqKey_and_pqMsg` for pinning `spqrSend` keys and messages from `encMsg` bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.DagDefs

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

open DY (Bytes ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (canonicalVariation sha256CompressFunction WireFields paddedVarint encodeField)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain TRSignalMsg trHonestWireMsg messageVersion spqrA2B spqrB2A lit litByte
   hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys kdfCk computeMac)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry ConcretizedTerm TrialCtx trialTerms
   node concretizeRandom concretizeSym concretizeTrWire
   gRandom gLit0 gConcat0 gDhPk gDh gKdf0 gSym0 gTrunc0 gTrWire0
   gSpqrChainKey gAll
   gamma' gamma randTerm litOf clamp trWireBytes trWireBytes_canonical
   assumedInjective MemoCollisionOn prefixTerms plaintextTerms)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (bytesToNat compTag4)
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj (eq_of_bytesToNat_eq)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (MemoOK bytes_rec_gAll memoOK_kemPk memoOK_spqrInit memoOK_spqrInit_elim memoOK_spqrChainKey
   memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg memoOK_spqrRecvState_pack)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_concat ms_pack_dhPk ms_pack_dh
   ms_pack_kdf ms_pack_sym ms_pack_trunc ms_pack_trWire)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (assumedInjective_lit memoOK_symEnc_elim)
open Symbolic.BugInjection.Proofs.Common443.CompC2KdfInjRest
  (assumedInjective_concat assumedInjective_trWire)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encMsg recvSt)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (trStateProxyRoots stateAnchorPair recvTailTerm serialize_localTR_memo)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (ai_concat_eq bool_serialize_singleton slowNat_serialize_zero slowNat_serialize_succ
   slowString_serialize_eq uint32_serialize_singleton concatPrefixes_cons concatPrefixes_nil
   concatPrefixes_append_eq alice_utf8_sizes bob_utf8_sizes)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue (bool_serialize_singleton_head)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
  (gamma'_kemEncap_of_len32 gamma'_kemSS_of_len32)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkLookupPub keepOpkLookupDh keepOpkAesPerm keepOpkKyberEncaps)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
  (keepOpkLookupDh_comm gamma_concatK gamma_trunc8K gamma_hmacK gamma_hmacK_length
   spqrKeyBytes_length gamma_spqrSendKey_length gamma_trMsgKeys_congr_prk
   computeMac_pins_salt_and_seed)

/-! ## 1. Concrete DAG Node Types & Bucket Evaluators -/

inductive DagOp where
  | rand (ts sz : Nat)
  | lit (bs : HwBytes)
  | concat (l r : Nat)
  | dhPk (s : Nat)
  | dh (pk sk : Nat)
  | kdf (a b : Nat)
  | symEncPt (k iv ptTs : Nat) (ptBs : HwBytes)
  | trunc8 (a : Nat)
  | trWire (ver : UInt8) (rk : Nat) (cnt prev : UInt32) (ct pq : Nat) (addr : HwBytes)
  | kemEncap (p e : Nat)
  | kemSS (p e : Nat)

def DagOp.isAI : DagOp → Bool
  | .lit _ | .concat _ _ | .trWire .. => false
  | _ => true

def DagOp.childrenLt (id : Nat) : DagOp → Bool
  | .rand _ _ | .lit _ => true
  | .concat l r => decide (l < id) && decide (r < id)
  | .dhPk s => decide (s < id)
  | .dh s1 s2 => decide (s1 < id) && decide (s2 < id)
  | .kdf a b => decide (a < id) && decide (b < id)
  | .symEncPt k iv _ _ => decide (k < id) && decide (iv < id)
  | .trunc8 a => decide (a < id)
  | .trWire _ rk _ _ ct pq _ => decide (rk < id) && decide (ct < id) && decide (pq < id)
  | .kemEncap p e => decide (p < id) && decide (e < id)
  | .kemSS p e => decide (p < id) && decide (e < id)

def dagOpBytesOk (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) : Bool :=
  let v := bytesOf id
  match op with
  | .rand _ sz => decide (sz ≠ 0)
  | .lit bs => v == bs
  | .concat l r => v == bytesOf l ++ bytesOf r
  | .dhPk s => v == keepOpkLookupPub (clamp (bytesOf s))
  | .dh pk sk => v == keepOpkLookupDh (clamp (bytesOf sk)) (bytesOf pk)
  | .kdf a b => v == hmacWith (sha256CompressFunction keepOpkI0) (bytesOf a) (bytesOf b)
  | .symEncPt k iv _ ptBs => v == keepOpkAesPerm (bytesOf k) ((bytesOf iv).take 16) ptBs
  | .trunc8 a => v == (bytesOf a).take 8
  | .trWire ver rk cnt prev ct pq addr =>
      v == trWireBytes addr canonicalVariation
        { version := ver.toNat, ratchetKey := bytesOf rk, counter := cnt.toNat,
          previousCounter := prev.toNat, ciphertext := bytesOf ct } (bytesOf pq)
  | .kemEncap _ e =>
      decide ((bytesOf e).length = 32) && v == (keepOpkKyberEncaps (bytesOf e)).take 1568
  | .kemSS _ e =>
      decide ((bytesOf e).length = 32) && v == (keepOpkKyberEncaps (bytesOf e)).drop 1568

def dagNodeOk (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes) (id : Nat) : Bool :=
  let op := opOf id
  let v := bytesOf id
  op.childrenLt id &&
  decide (v.length < 2048) &&
  dagOpBytesOk bytesOf id op &&
  (!op.isAI || (decide (8 ≤ v.length) &&
    !(decide (38 ≤ v.length) && (v.drop (v.length - 2) == [0x01#8, 0x00#8]))))

def evalDagShapeAux (opOf : Nat → DagOp) : Nat → Nat → Bytes
  | 0, _ => litOf []
  | fuel + 1, id =>
    match opOf id with
    | .rand ts sz => randTerm ts sz
    | .lit bs => litOf bs
    | .concat l r => DY.Concat.concat (evalDagShapeAux opOf fuel l) (evalDagShapeAux opOf fuel r)
    | .dhPk s => DY.DiffieHellman.dhPk (evalDagShapeAux opOf fuel s)
    | .dh pk sk => DY.DiffieHellman.dh (evalDagShapeAux opOf fuel pk) (evalDagShapeAux opOf fuel sk)
    | .kdf a b => DY.KdfExtract.kdfExtract (evalDagShapeAux opOf fuel a) (evalDagShapeAux opOf fuel b)
    | .symEncPt k iv ptTs _ =>
        DY.SymEnc.symEnc (evalDagShapeAux opOf fuel k) (evalDagShapeAux opOf fuel iv) (randTerm ptTs 32)
    | .trunc8 a => DY.Trunc.trunc8 (evalDagShapeAux opOf fuel a)
    | .trWire ver rk cnt prev ct pq addr =>
        DY.TrWire.trWireMsg ver (evalDagShapeAux opOf fuel rk) cnt prev
          (evalDagShapeAux opOf fuel ct) (evalDagShapeAux opOf fuel pq)
          { canonicalVariation with
            fields := .extra 6 (.bytes addr) 0 0 :: canonicalVariation.fields }
    | .kemEncap p e =>
        ({ pk := evalDagShapeAux opOf fuel p, entropy := evalDagShapeAux opOf fuel e } :
          DY.PQKem.Encap.SubF Bytes).pack
    | .kemSS p e =>
        ({ pk := evalDagShapeAux opOf fuel p, entropy := evalDagShapeAux opOf fuel e } :
          DY.PQKem.SharedSecret.SubF Bytes).pack

theorem evalDagShapeAux_irrel (opOf : Nat → DagOp)
    (htopo : ∀ i, (opOf i).childrenLt i = true) :
    ∀ (f₁ f₂ id : Nat), id < f₁ → id < f₂ →
      evalDagShapeAux opOf f₁ id = evalDagShapeAux opOf f₂ id
  | 0, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _, 0, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | f₁ + 1, f₂ + 1, id, h1, h2 => by
    have hc := htopo id
    have ih : ∀ c, c < id → evalDagShapeAux opOf f₁ c = evalDagShapeAux opOf f₂ c :=
      fun c hlt => evalDagShapeAux_irrel opOf htopo f₁ f₂ c (by omega) (by omega)
    cases hop : opOf id <;> rw [hop] at hc <;>
      simp only [DagOp.childrenLt, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
      simp only [evalDagShapeAux, hop]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc]
    · rw [ih _ hc.1.1, ih _ hc.1.2, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]
    · rw [ih _ hc.1, ih _ hc.2]

def packBytesKey (bs : HwBytes) : Nat :=
  bs.length + 2048 * bytesToNat bs

theorem packBytesKey_inj {a b : HwBytes}
    (ha : a.length < 2048) (hb : b.length < 2048)
    (heq : packBytesKey a = packBytesKey b) : a = b := by
  unfold packBytesKey at heq
  have hlen : a.length = b.length := by omega
  have hnat : bytesToNat a = bytesToNat b := by omega
  exact eq_of_bytesToNat_eq hlen hnat

def bytesBucketIdx (bs : HwBytes) : Nat :=
  match bs with
  | [] => 0
  | b :: _ => b.toNat

def bucketNoCollision (entries : List (Nat × Bool × Nat)) : Bool :=
  entries.all fun (id₁, ai₁, k₁) =>
    !ai₁ || entries.all fun (id₂, _, k₂) =>
      decide (k₁ ≠ k₂) || decide (id₁ = id₂)

theorem bucketNoCollision_sound {entries : List (Nat × Bool × Nat)}
    (h : bucketNoCollision entries = true)
    {id₁ id₂ : Nat} {ai₁ ai₂ : Bool} {k : Nat}
    (h₁ : (id₁, ai₁, k) ∈ entries) (h₂ : (id₂, ai₂, k) ∈ entries)
    (hai : ai₁ = true ∨ ai₂ = true) : id₁ = id₂ := by
  unfold bucketNoCollision at h
  rcases hai with rfl | rfl
  · have h1 := List.all_eq_true.mp h (id₁, true, k) h₁
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 (id₂, ai₂, k) h₂
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq] at h2
    exact h2
  · have h1 := List.all_eq_true.mp h (id₂, true, k) h₂
    simp only [Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.mp h1 (id₁, ai₁, k) h₁
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or, decide_eq_true_eq] at h2
    exact h2.symm

def endsWith0100 (bs : HwBytes) : Bool :=
  decide (2 ≤ bs.length) && (bs.drop (bs.length - 2) == [0x01#8, 0x00#8])

theorem dag_no_ai_0100_of_all {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    (hall : (List.range dagSize).all (fun id => !(opOf id).isAI || !endsWith0100 (bytesOf id)) = true)
    {id : Nat} (hid : id < dagSize) (hai : (opOf id).isAI = true) :
    ¬ ([0x01#8, 0x00#8] <:+ bytesOf id) := by
  have hok := List.all_eq_true.mp hall id (List.mem_range.mpr hid)
  rw [hai, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hok
  rintro ⟨pfx, heq⟩
  have h2 : 2 ≤ (bytesOf id).length := by
    rw [← heq, List.length_append]; simp
  have hd : (bytesOf id).drop ((bytesOf id).length - 2) = [0x01#8, 0x00#8] := by
    rw [← heq]
    have hsub : (pfx ++ [0x01#8, 0x00#8]).length - 2 = pfx.length := by
      rw [List.length_append]; simp
    rw [hsub, List.drop_append, List.drop_eq_nil_of_le (Nat.le_refl pfx.length),
      List.nil_append, Nat.sub_self, List.drop_zero]
  unfold endsWith0100 at hok
  simp [h2, hd] at hok

/-! ## 2. `dagShape`, `SafeMemo`, and `TermAt` Combinators -/

def dagShape (opOf : Nat → DagOp) (dagSize id : Nat) : Bytes :=
  evalDagShapeAux opOf dagSize id

theorem dagShape_unfold {opOf : Nat → DagOp} {dagSize id : Nat}
    (htopo : ∀ i < dagSize, (opOf i).childrenLt i = true)
    (hid : id < dagSize) :
    dagShape opOf dagSize id = evalDagShapeAux opOf (dagSize + 1) id := by
  let opSafe : Nat → DagOp := fun i => if i < dagSize then opOf i else .lit []
  have htopoSafe : ∀ i, (opSafe i).childrenLt i = true := by
    intro i; dsimp only [opSafe]; split_ifs with hi
    · exact htopo i hi
    · rfl
  have heq : ∀ f j, j < dagSize → j < f → evalDagShapeAux opOf f j = evalDagShapeAux opSafe f j := by
    intro f; induction f with
    | zero => intro j _ hj; exact absurd hj (Nat.not_lt_zero _)
    | succ f ih =>
      intro j hj hlt
      have hc := htopo j hj
      have hop : opSafe j = opOf j := by simp [opSafe, hj]
      cases hop' : opOf j <;> rw [hop'] at hc hop <;>
        simp only [DagOp.childrenLt, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
        simp only [evalDagShapeAux, hop, hop']
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      · rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
  unfold dagShape
  rw [heq dagSize id hid hid, heq (dagSize + 1) id hid (by omega)]
  exact evalDagShapeAux_irrel opSafe htopoSafe dagSize (dagSize + 1) id hid (by omega)

def SafeEntry (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (pts : List Bytes) (x : Bytes × Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨
     (38 ≤ x.2.2.length ∧ x.2.2.drop (x.2.2.length - 2) = [0x01#8, 0x00#8]))) ∨
  (∃ id < dagSize, x.2.1 = dagShape opOf dagSize id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

def SafeMemo (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) : Prop :=
  MemoOK keepOpkI0 S g (SafeEntry dagSize opOf bytesOf pts) b

def TermAt (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) (id : Nat) : Prop :=
  id < dagSize ∧
  (gamma' keepOpkI0 S g b).bytes = bytesOf id ∧
  (gamma' keepOpkI0 S g b).shape = dagShape opOf dagSize id ∧
  SafeMemo dagSize opOf bytesOf S g pts b

theorem TermAt.safeMemo {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    SafeMemo dagSize opOf bytesOf S g pts b := h.2.2.2

theorem TermAt.gamma_eq {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    gamma keepOpkI0 S g b = bytesOf id := h.2.1

section Combinators

variable {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
variable {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}

theorem safeMemo_plaintext {ts : Nat}
    (hmem : randTerm ts 32 ∈ pts) (hlen : (g.σ ts 32).length < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 32) := by
  intro x hx
  unfold randTerm at hx
  rw [ms_pack_random keepOpkI0 S g ⟨ts, 32⟩] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [Nat.reduceEqDiff, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  exact Or.inl ⟨hmem, hlen⟩

theorem safeMemo_symDec {k iv ct m : Bytes}
    (hdec : DY.SymEnc.symDec k iv ct = some m)
    (hct : SafeMemo dagSize opOf bytesOf S g pts ct) :
    SafeMemo dagSize opOf bytesOf S g pts m := by
  dsimp only [DY.SymEnc.symDec, DY.SymEnc.instCanSymEncBytes] at hdec
  split at hdec <;> try cases hdec
  next key' iv' msg hx =>
    split_ifs at hdec
    cases hdec
    have hpv := DY.Bytes.pack_view? DY.SymEnc.Enc.SubF ct
    change ct.view? DY.SymEnc.Enc.SubF = some { key := key', iv := iv', msg := m } at hx
    rw [hx] at hpv; rw [← hpv] at hct
    exact memoOK_symEnc_elim (e := ⟨key', iv', m⟩) hct

theorem safeMemo_lit_short {ba : ByteArray} (hlen : ba.size < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Literal.literalToBytes ba) := by
  intro x hx
  have hg := ms_pack_lit keepOpkI0 S g ⟨ba⟩
  change gamma' keepOpkI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  rw [hg] at hx
  unfold gLit0 DY.Libsignal.Composed.Refinement.concretizeLit node at hx
  simp only [List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  refine Or.inr (Or.inl ⟨assumedInjective_lit ba, Or.inl ?_⟩)
  dsimp only [DY.Libsignal.Composed.Refinement.ofByteArray]
  rw [List.length_map, Array.length_toList]
  exact hlen

theorem safeMemo_randTerm_zero (ts : Nat) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 0) := by
  intro x hx
  have hg := ms_pack_random keepOpkI0 S g ⟨ts, 0⟩
  change gamma' keepOpkI0 S g (randTerm ts 0) = _ at hg
  rw [hg] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [↓reduceIte] at hx
  cases hx

private theorem topo_of_nodes (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true) :
    ∀ i < dagSize, (opOf i).childrenLt i = true := by
  intro i hi; have h := hNodes i hi; unfold dagNodeOk at h
  simp only [Bool.and_eq_true] at h; exact h.1.1.1

private theorem bytesOk_of_nodes (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {id : Nat} (hid : id < dagSize) :
    dagOpBytesOk bytesOf id (opOf id) = true := by
  have h := hNodes id hid; unfold dagNodeOk at h
  simp only [Bool.and_eq_true] at h; exact h.1.2

private theorem termAt_of_node {b : Bytes} {id : Nat} {cs : List ConcretizedTerm}
    (hid : id < dagSize)
    (hg : gamma' keepOpkI0 S g b = node (bytesOf id) b (dagShape opOf dagSize id) cs)
    (hai : assumedInjective b = true → (opOf id).isAI = true)
    (hcs : ∀ c ∈ cs, ∀ x ∈ c.memo, SafeEntry dagSize opOf bytesOf pts x) :
    TermAt dagSize opOf bytesOf S g pts b id := by
  refine ⟨hid, by rw [hg]; rfl, by rw [hg]; rfl, ?_⟩
  intro x hx; rw [hg] at hx
  simp only [node, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨c, hc, hxc⟩
  · exact Or.inr (Or.inr ⟨id, hid, rfl, rfl, hai⟩)
  · exact hcs c hc x hxc

theorem termAt_lit (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ba : ByteArray} {id : Nat} (hid : id < dagSize)
    (hop : opOf id = .lit (DY.Libsignal.Composed.Refinement.ofByteArray ba)) :
    TermAt dagSize opOf bytesOf S g pts (DY.Literal.literalToBytes ba) id := by
  set v := DY.Libsignal.Composed.Refinement.ofByteArray ba
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  have hba : DY.Literal.literalToBytes ba = litOf v := by
    unfold litOf DY.Literal.literalToBytes; congr 1; apply ByteArray.ext
    change ba.data = (v.map UInt8.ofBitVec).toArray
    rw [← Array.toList_inj, List.toList_toArray]
    change ba.data.toList = (ba.data.toList.map UInt8.toBitVec).map UInt8.ofBitVec
    induction ba.data.toList with
    | nil => rfl
    | cons u us ih => exact congrArg (u :: ·) ih
  have hg := ms_pack_lit keepOpkI0 S g { lit := ba }
  change gamma' keepOpkI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  apply termAt_of_node hid (cs := [])
  · rw [hg]; unfold gLit0 DY.Libsignal.Composed.Refinement.concretizeLit
    change node v (DY.Literal.literalToBytes ba) (DY.Literal.literalToBytes ba) [] = _
    rw [← hbok, hsh, ← hba]
  · intro h; rw [assumedInjective_lit ba] at h; cases h
  · intro _ hc; cases hc

theorem termAt_litOf (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {v : HwBytes} {id : Nat} (hid : id < dagSize) (hop : opOf id = .lit v) :
    TermAt dagSize opOf bytesOf S g pts (litOf v) id := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons b bs ih => exact congrArg (b :: ·) ih
  let ba := ByteArray.mk (v.map UInt8.ofBitVec).toArray
  have hv : DY.Libsignal.Composed.Refinement.ofByteArray ba = v := hv_aux v
  exact termAt_lit hNodes hid (hop.trans (congrArg DagOp.lit hv.symm))

theorem randTerm_eq_dagShape (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize) (hop : opOf id = .rand ts sz) :
    randTerm ts sz = dagShape opOf dagSize id := by
  rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]

theorem termAt_rand (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {ts sz id : Nat} (hid : id < dagSize) (hop : opOf id = .rand ts sz)
    (hσ : g.σ ts sz = bytesOf id) :
    TermAt dagSize opOf bytesOf S g pts (randTerm ts sz) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, decide_eq_true_eq] at hbok
  have hsh : dagShape opOf dagSize id = randTerm ts sz := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  have hg := ms_pack_random keepOpkI0 S g ⟨ts, sz⟩
  change gamma' keepOpkI0 S g (randTerm ts sz) = _ at hg
  apply termAt_of_node hid (cs := [])
  · rw [hg]; dsimp only [gRandom, concretizeRandom]
    simp only [hbok, ↓reduceIte, hσ, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro _ hc; cases hc

theorem termAt_concat (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a b : Bytes} {l r id : Nat} (hid : id < dagSize) (hop : opOf id = .concat l r)
    (ha : TermAt dagSize opOf bytesOf S g pts a l)
    (hb : TermAt dagSize opOf bytesOf S g pts b r) :
    TermAt dagSize opOf bytesOf S g pts (DY.Concat.concat a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.Concat.concat (dagShape opOf dagSize l) (dagShape opOf dagSize r) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_concat keepOpkI0 S g ⟨a, b⟩
  change gamma' keepOpkI0 S g (DY.Concat.concat a b) = _ at hg
  apply termAt_of_node hid (cs := [gamma' keepOpkI0 S g a, gamma' keepOpkI0 S g b])
  · rw [hg]; unfold gConcat0 DY.Libsignal.Composed.Refinement.concretizeConcat; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro h; rw [assumedInjective_concat] at h; cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_dhPk (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk : Bytes} {s id : Nat} (hid : id < dagSize) (hop : opOf id = .dhPk s)
    (hs : TermAt dagSize opOf bytesOf S g pts sk s) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_dhPk keepOpkI0 S g ⟨sk⟩
  change gamma' keepOpkI0 S g (DY.DiffieHellman.dhPk sk) = _ at hg
  apply termAt_of_node hid (cs := [gamma' keepOpkI0 S g sk])
  · rw [hg]; unfold gDhPk DY.Libsignal.Composed.Refinement.concretizeDhPk; dsimp only
    rw [hs.2.1, hs.2.2.1, hsh]
    change node (keepOpkLookupPub (clamp (bytesOf s))) _ _ _ = _
    rw [← hbok]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact hs.2.2.2 x hxc

theorem termAt_dh (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize s2_id)
    (hs1 : TermAt dagSize opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk1) sk2) id := by
  subst hsh1 hsh2
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hbpk1 := bytesOk_of_nodes hNodes hp1.1
  rw [hop_pk1] at hbpk1; simp only [dagOpBytesOk, beq_iff_eq] at hbpk1
  have hbpk2 := bytesOk_of_nodes hNodes hp2.1
  rw [hop_pk2] at hbpk2; simp only [dagOpBytesOk, beq_iff_eq] at hbpk2
  have hsh_pk1 : dagShape opOf dagSize pk1_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp1.1]; simp only [evalDagShapeAux, hop_pk1]; rfl
  have hsh_pk2 : dagShape opOf dagSize pk2_id = DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hp2.1]; simp only [evalDagShapeAux, hop_pk2]; rfl
  have hsh_id : dagShape opOf dagSize id =
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
    change DY.DiffieHellman.dh (dagShape opOf dagSize pk1_id) (dagShape opOf dagSize s2_id) = _
    rw [hsh_pk1]
  by_cases hge : dagShape opOf dagSize s2_id ≤ dagShape opOf dagSize s1_id
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id),
           sk := dagShape opOf dagSize s2_id } : DY.DiffieHellman.Dh.SubF Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk, DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg := ms_pack_dh keepOpkI0 S g
      ⟨DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id), dagShape opOf dagSize s2_id⟩
    apply termAt_of_node hid
      (cs := [gamma' keepOpkI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id)),
              gamma' keepOpkI0 S g (dagShape opOf dagSize s2_id)])
    · rw [hg]; unfold gDh DY.Libsignal.Composed.Refinement.concretizeDh; dsimp only
      rw [hp1.2.1, hs2.2.1, hp1.2.2.1, hs2.2.2.1, hsh_pk1, hsh]
      change node (keepOpkLookupDh (clamp (bytesOf s2_id)) (bytesOf pk1_id)) _ _ _ = _
      rw [← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp1.2.2.2 x hxc
      · exact hs2.2.2.2 x hxc
  · have heq : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (dagShape opOf dagSize s1_id))
        (dagShape opOf dagSize s2_id) =
        ({ pk := DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id),
           sk := dagShape opOf dagSize s1_id } : DY.DiffieHellman.Dh.SubF Bytes).pack := by
      simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh,
        DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk, DY.BytesView.view_pack, hge, ↓reduceIte]
    have hsh := hsh_id.trans heq
    rw [heq]
    have hg := ms_pack_dh keepOpkI0 S g
      ⟨DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id), dagShape opOf dagSize s1_id⟩
    apply termAt_of_node hid
      (cs := [gamma' keepOpkI0 S g (DY.DiffieHellman.dhPk (dagShape opOf dagSize s2_id)),
              gamma' keepOpkI0 S g (dagShape opOf dagSize s1_id)])
    · rw [hg]; unfold gDh DY.Libsignal.Composed.Refinement.concretizeDh; dsimp only
      rw [hp2.2.1, hs1.2.1, hp2.2.2.1, hs1.2.2.1, hsh_pk2, hsh]
      change node (keepOpkLookupDh (clamp (bytesOf s1_id)) (bytesOf pk2_id)) _ _ _ = _
      rw [hbpk2, keepOpkLookupDh_comm, ← hbpk1, ← hbok]
    · intro _; rw [hop]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp2.2.2.2 x hxc
      · exact hs1.2.2.2 x hxc

theorem termAt_dh_symm (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {sk1 sk2 : Bytes} {s1_id pk1_id s2_id pk2_id id : Nat}
    (hid : id < dagSize) (hop : opOf id = .dh pk1_id s2_id)
    (hop_pk1 : opOf pk1_id = .dhPk s1_id)
    (hop_pk2 : opOf pk2_id = .dhPk s2_id)
    (hsh1 : sk1 = dagShape opOf dagSize s1_id)
    (hsh2 : sk2 = dagShape opOf dagSize s2_id)
    (hs1 : TermAt dagSize opOf bytesOf S g pts sk1 s1_id)
    (hp1 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk1) pk1_id)
    (hs2 : TermAt dagSize opOf bytesOf S g pts sk2 s2_id)
    (hp2 : TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dhPk sk2) pk2_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk sk2) sk1) id := by
  rw [DY.DiffieHellman.dh_commutes]
  exact termAt_dh hNodes hid hop hop_pk1 hop_pk2 hsh1 hsh2 hs1 hp1 hs2 hp2

theorem termAt_kdf (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a b : Bytes} {a_id b_id id : Nat} (hid : id < dagSize) (hop : opOf id = .kdf a_id b_id)
    (ha : TermAt dagSize opOf bytesOf S g pts a a_id)
    (hb : TermAt dagSize opOf bytesOf S g pts b b_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.KdfExtract.kdfExtract a b) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.KdfExtract.kdfExtract (dagShape opOf dagSize a_id) (dagShape opOf dagSize b_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_kdf keepOpkI0 S g ⟨a, b⟩
  change gamma' keepOpkI0 S g (DY.KdfExtract.kdfExtract a b) = _ at hg
  apply termAt_of_node hid (cs := [gamma' keepOpkI0 S g a, gamma' keepOpkI0 S g b])
  · rw [hg]; unfold gKdf0 DY.Libsignal.Composed.Refinement.concretizeKdf; dsimp only
    rw [ha.2.1, hb.2.1, ← hbok, ha.2.2.1, hb.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.2.2.2 x hxc
    · exact hb.2.2.2 x hxc

theorem termAt_trunc8 (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {a : Bytes} {a_id id : Nat} (hid : id < dagSize) (hop : opOf id = .trunc8 a_id)
    (ha : TermAt dagSize opOf bytesOf S g pts a a_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.Trunc.trunc8 a) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = DY.Trunc.trunc8 (dagShape opOf dagSize a_id) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hg := ms_pack_trunc keepOpkI0 S g ⟨a⟩
  change gamma' keepOpkI0 S g (DY.Trunc.trunc8 a) = _ at hg
  apply termAt_of_node hid (cs := [gamma' keepOpkI0 S g a])
  · rw [hg]; unfold gTrunc0 DY.Libsignal.Composed.Refinement.concretizeTrunc; dsimp only
    rw [ha.2.1, ← hbok, ha.2.2.1, hsh]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_singleton] at hc; subst hc
    exact ha.2.2.2 x hxc

theorem termAt_symEncPt (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {k iv : Bytes} {k_id iv_id ptTs id : Nat} {ptBs : HwBytes}
    (hid : id < dagSize) (hop : opOf id = .symEncPt k_id iv_id ptTs ptBs)
    (hk : TermAt dagSize opOf bytesOf S g pts k k_id)
    (hiv : TermAt dagSize opOf bytesOf S g pts iv iv_id)
    (hpt_mem : randTerm ptTs 32 ∈ pts)
    (hσ : g.σ ptTs 32 = ptBs)
    (hlen : ptBs.length < 8) :
    TermAt dagSize opOf bytesOf S g pts (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.SymEnc.symEnc (dagShape opOf dagSize k_id) (dagShape opOf dagSize iv_id) (randTerm ptTs 32) := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have hgpt := ms_pack_random keepOpkI0 S g ⟨ptTs, 32⟩
  change gamma' keepOpkI0 S g (randTerm ptTs 32) = _ at hgpt
  have hpt_bs : (gamma' keepOpkI0 S g (randTerm ptTs 32)).bytes = ptBs := by
    rw [hgpt]; dsimp only [gRandom, concretizeRandom]; simp only [Nat.reduceEqDiff, ↓reduceIte, node]; exact hσ
  have hpt_sh : (gamma' keepOpkI0 S g (randTerm ptTs 32)).shape = randTerm ptTs 32 := by
    rw [hgpt]; dsimp only [gRandom, concretizeRandom]; simp only [Nat.reduceEqDiff, ↓reduceIte, node]; rfl
  have hpt_sm : SafeMemo dagSize opOf bytesOf S g pts (randTerm ptTs 32) :=
    safeMemo_plaintext hpt_mem (by rw [hσ]; exact hlen)
  have hg := ms_pack_sym keepOpkI0 S g ⟨k, iv, randTerm ptTs 32⟩
  change gamma' keepOpkI0 S g (DY.SymEnc.symEnc k iv (randTerm ptTs 32)) = _ at hg
  apply termAt_of_node hid
    (cs := [gamma' keepOpkI0 S g k, gamma' keepOpkI0 S g iv, gamma' keepOpkI0 S g (randTerm ptTs 32)])
  · rw [hg]; unfold gSym0 DY.Libsignal.Composed.Refinement.concretizeSym; dsimp only
    rw [hk.2.1, hiv.2.1, hpt_bs, hk.2.2.1, hiv.2.2.1, hpt_sh, hsh]
    change node (keepOpkAesPerm (bytesOf k_id) ((bytesOf iv_id).take 16) ptBs) _ _ _ = _
    rw [← hbok]; rfl
  · intro _; rw [hop]; rfl
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hk.2.2.2 x hxc
    · exact hiv.2.2.2 x hxc
    · exact hpt_sm x hxc

theorem termAt_trWire (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {rk ct pq : Bytes} {cnt prev : UInt32} {rk_id ct_id pq_id id : Nat} {addr : HwBytes}
    (hid : id < dagSize) (hop : opOf id = .trWire messageVersion rk_id cnt prev ct_id pq_id addr)
    (hrk : TermAt dagSize opOf bytesOf S g pts rk rk_id)
    (hct : TermAt dagSize opOf bytesOf S g pts ct ct_id)
    (hpq : TermAt dagSize opOf bytesOf S g pts pq pq_id)
    (haddr : g.addr (trHonestWireMsg rk cnt prev ct pq) = addr) :
    TermAt dagSize opOf bytesOf S g pts (trHonestWireMsg rk cnt prev ct pq) id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id =
      DY.TrWire.trWireMsg messageVersion (dagShape opOf dagSize rk_id) cnt prev
        (dagShape opOf dagSize ct_id) (dagShape opOf dagSize pq_id)
        { canonicalVariation with fields := .extra 6 (.bytes addr) 0 0 :: canonicalVariation.fields } := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]; rfl
  have haddr' : g.addr (DY.BytesView.pack (SubF := DY.TrWire.TrWireMsg.SubF)
      ⟨messageVersion, rk, cnt, prev, ct, pq, canonicalVariation⟩) = addr := haddr
  have hg := ms_pack_trWire keepOpkI0 S g ⟨messageVersion, rk, cnt, prev, ct, pq, canonicalVariation⟩
  change gamma' keepOpkI0 S g (trHonestWireMsg rk cnt prev ct pq) = _ at hg
  apply termAt_of_node hid
    (cs := [gamma' keepOpkI0 S g rk, gamma' keepOpkI0 S g ct, gamma' keepOpkI0 S g pq])
  · rw [hg]; unfold gTrWire0 DY.Libsignal.Composed.Refinement.concretizeTrWire; dsimp only
    rw [haddr', hrk.2.1, hct.2.1, hpq.2.1, ← hbok, hrk.2.2.1, hct.2.2.1, hpq.2.2.1, hsh]; rfl
  · intro h
    have hw := assumedInjective_trWire messageVersion rk cnt prev ct pq canonicalVariation
    change assumedInjective (trHonestWireMsg rk cnt prev ct pq) = false at hw
    rw [hw] at h; cases h
  · intro c hc x hxc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hrk.2.2.2 x hxc
    · exact hct.2.2.2 x hxc
    · exact hpq.2.2.2 x hxc

theorem termAt_kemEncap (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {pk e : Bytes} {p_id e_id id1 id2 : Nat}
    (hid1 : id1 < dagSize) (hop1 : opOf id1 = .kemEncap p_id e_id)
    (hid2 : id2 < dagSize) (hop2 : opOf id2 = .kemSS p_id e_id)
    (hp : TermAt dagSize opOf bytesOf S g pts pk p_id)
    (he : TermAt dagSize opOf bytesOf S g pts e e_id) :
    TermAt dagSize opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).1 id1 ∧
      TermAt dagSize opOf bytesOf S g pts (DY.PQKem.kemEncap pk e).2 id2 := by
  have hbok1 := bytesOk_of_nodes hNodes hid1
  rw [hop1] at hbok1
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok1
  have hbok2 := bytesOk_of_nodes hNodes hid2
  rw [hop2] at hbok2
  simp only [dagOpBytesOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbok2
  have he_g : gamma keepOpkI0 S g e = bytesOf e_id := he.2.1
  have helen : (gamma keepOpkI0 S g e).length = 32 := by rw [he_g, hbok1.1]
  have hsh1 : dagShape opOf dagSize id1 =
      ({ pk := dagShape opOf dagSize p_id, entropy := dagShape opOf dagSize e_id } :
        DY.PQKem.Encap.SubF Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid1]; simp only [evalDagShapeAux, hop1]; rfl
  have hsh2 : dagShape opOf dagSize id2 =
      ({ pk := dagShape opOf dagSize p_id, entropy := dagShape opOf dagSize e_id } :
        DY.PQKem.SharedSecret.SubF Bytes).pack := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid2]; simp only [evalDagShapeAux, hop2]; rfl
  constructor
  · apply termAt_of_node hid1 (cs := [gamma' keepOpkI0 S g pk, gamma' keepOpkI0 S g e])
    · rw [gamma'_kemEncap_of_len32 (i := keepOpkI0) (S := S) (g := g) helen]
      rw [he_g, hp.2.2.1, he.2.2.1, hsh1]
      change node ((keepOpkKyberEncaps (bytesOf e_id)).take 1568) _ _ _ = _
      rw [← hbok1.2]
    · intro _; rw [hop1]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc
  · apply termAt_of_node hid2 (cs := [gamma' keepOpkI0 S g pk, gamma' keepOpkI0 S g e])
    · rw [gamma'_kemSS_of_len32 (i := keepOpkI0) (S := S) (g := g) helen]
      rw [he_g, hp.2.2.1, he.2.2.1, hsh2]
      change node ((keepOpkKyberEncaps (bytesOf e_id)).drop 1568) _ _ _ = _
      rw [← hbok2.2]
    · intro _; rw [hop2]; rfl
    · intro c hc x hxc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hp.2.2.2 x hxc
      · exact he.2.2.2 x hxc

theorem termAt_of_opaque (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {b : Bytes} {v : HwBytes} {id : Nat} (hid : id < dagSize) (hop : opOf id = .lit v)
    (hbs : (gamma' keepOpkI0 S g b).bytes = v)
    (hsh_b : (gamma' keepOpkI0 S g b).shape = litOf v)
    (hsm : SafeMemo dagSize opOf bytesOf S g pts b) :
    TermAt dagSize opOf bytesOf S g pts b id := by
  have hbok := bytesOk_of_nodes hNodes hid
  rw [hop] at hbok; simp only [dagOpBytesOk, beq_iff_eq] at hbok
  have hsh : dagShape opOf dagSize id = litOf v := by
    rw [dagShape_unfold (topo_of_nodes hNodes) hid]; simp only [evalDagShapeAux, hop]
  exact ⟨hid, hbs.trans hbok.symm, hsh_b.trans hsh.symm, hsm⟩

theorem safeMemo_kemPk {sk : Bytes} (hsk : SafeMemo dagSize opOf bytesOf S g pts sk) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.PQKem.kemPk sk) := memoOK_kemPk hsk

theorem safeMemo_spqrInit {k p : Bytes}
    (hk : SafeMemo dagSize opOf bytesOf S g pts k)
    (hp : SafeMemo dagSize opOf bytesOf S g pts p) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrInit k p) := memoOK_spqrInit hk hp

theorem safeMemo_recvSt {st msg : Bytes}
    (hst : SafeMemo dagSize opOf bytesOf S g pts st)
    (hmsg : SafeMemo dagSize opOf bytesOf S g pts msg) :
    SafeMemo dagSize opOf bytesOf S g pts (recvSt st msg) := memoOK_spqrRecvState_pack hst hmsg

theorem safeMemo_spqrSend {st coins : Bytes}
    (hst : SafeMemo dagSize opOf bytesOf S g pts st)
    (hc : SafeMemo dagSize opOf bytesOf S g pts coins) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).1 ∧
      SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.1 ∧
      SafeMemo dagSize opOf bytesOf S g pts (DY.Spqr.spqrSend st coins).2.2 := by
  refine ⟨memoOK_spqrSendState hst hc, ?_, memoOK_spqrSendMsg hst hc⟩
  have hpv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · next authKey params hx =>
    have hst' := hst; rw [hx] at hpv; rw [← hpv] at hst'
    obtain ⟨ha, hp⟩ := memoOK_spqrInit_elim (s := ⟨authKey, params⟩) hst'
    refine memoOK_spqrChainKey ha hp ?_
    cases DY.Spqr.spqrParamsDir? params with
    | none => exact safeMemo_lit_short (by decide)
    | some d => cases d <;> exact safeMemo_lit_short (by decide)
  · exact memoOK_spqrSendKey_pack hst hc

theorem termAt_computeMac (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {mk pIk mIk w : Bytes} {mk_id pIk_id mIk_id w_id c1_id c2_id h_id t_id : Nat}
    (hc1 : c1_id < dagSize ∧ opOf c1_id = .concat mIk_id w_id)
    (hc2 : c2_id < dagSize ∧ opOf c2_id = .concat pIk_id c1_id)
    (hh : h_id < dagSize ∧ opOf h_id = .kdf mk_id c2_id)
    (ht : t_id < dagSize ∧ opOf t_id = .trunc8 h_id)
    (hmk : TermAt dagSize opOf bytesOf S g pts mk mk_id)
    (hpIk : TermAt dagSize opOf bytesOf S g pts pIk pIk_id)
    (hmIk : TermAt dagSize opOf bytesOf S g pts mIk mIk_id)
    (hw : TermAt dagSize opOf bytesOf S g pts w w_id) :
    TermAt dagSize opOf bytesOf S g pts (computeMac mk pIk mIk w) t_id := by
  unfold computeMac hmac
  exact termAt_trunc8 hNodes ht.1 ht.2
    (termAt_kdf hNodes hh.1 hh.2 hmk
      (termAt_concat hNodes hc2.1 hc2.2 hpIk
        (termAt_concat hNodes hc1.1 hc1.2 hmIk hw)))

theorem termAt_trMsgKeys (hNodes : ∀ i < dagSize, dagNodeOk opOf bytesOf i = true)
    {salt seed : Bytes}
    {info1_id info2_id info3_id salt_id seed_id prk_id ck_id c2_id mk_id c3_id iv_id : Nat}
    (hi1 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 1)) info1_id)
    (hi2 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 2)) info2_id)
    (hi3 : TermAt dagSize opOf bytesOf S g pts
      (DY.Concat.concat (lit "WhisperMessageKeys") (litByte 3)) info3_id)
    (hprk : prk_id < dagSize ∧ opOf prk_id = .kdf salt_id seed_id)
    (hck : ck_id < dagSize ∧ opOf ck_id = .kdf prk_id info1_id)
    (hc2 : c2_id < dagSize ∧ opOf c2_id = .concat ck_id info2_id)
    (hmk : mk_id < dagSize ∧ opOf mk_id = .kdf prk_id c2_id)
    (hc3 : c3_id < dagSize ∧ opOf c3_id = .concat mk_id info3_id)
    (hiv : iv_id < dagSize ∧ opOf iv_id = .kdf prk_id c3_id)
    (hsalt : TermAt dagSize opOf bytesOf S g pts salt salt_id)
    (hseed : TermAt dagSize opOf bytesOf S g pts seed seed_id) :
    TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ck_id ∧
      TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).macKey mk_id ∧
      TermAt dagSize opOf bytesOf S g pts (trMsgKeys salt seed).iv iv_id := by
  unfold trMsgKeys hkdfBlock1 hkdfBlock2 hkdfBlock3 hmac; dsimp only
  have tprk := termAt_kdf hNodes hprk.1 hprk.2 hsalt hseed
  have tck := termAt_kdf hNodes hck.1 hck.2 tprk hi1
  have tmk := termAt_kdf hNodes hmk.1 hmk.2 tprk (termAt_concat hNodes hc2.1 hc2.2 tck hi2)
  have tiv := termAt_kdf hNodes hiv.1 hiv.2 tprk (termAt_concat hNodes hc3.1 hc3.2 tmk hi3)
  exact ⟨tck, tmk, tiv⟩

theorem safeMemo_trialTerms {salts : List Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    (hextra : ∀ t ∈ ctx.extra, SafeMemo dagSize opOf bytesOf S g pts t)
    (hct : SafeMemo dagSize opOf bytesOf S g pts msg.ciphertext)
    (hbody : ∀ seed, ctx.seed? = some seed → ∀ salt ∈ salts,
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).cipherKey ∧
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).macKey ∧
      SafeMemo dagSize opOf bytesOf S g pts (trMsgKeys salt seed).iv ∧
      SafeMemo dagSize opOf bytesOf S g pts
        (computeMac (trMsgKeys salt seed).macKey ctx.peerIk ctx.myIk msg.wire)) :
    ∀ t ∈ trialTerms salts msg ctx, SafeMemo dagSize opOf bytesOf S g pts t := by
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

end Combinators

/-! ## 3. `SafeMemo2`, `not_memoCollisionOn_of_safeMemo2`, and `TRState` Serialization -/

section StateSafe

variable {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}

def SafeEntry2 (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (pts : List Bytes) (x : Bytes × Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨ [0x01#8, 0x00#8] <:+ x.2.2)) ∨
  (∃ id < dagSize, x.2.1 = dagShape opOf dagSize id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

def SafeMemo2 (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) : Prop :=
  MemoOK keepOpkI0 S g (SafeEntry2 dagSize opOf bytesOf pts) b

theorem safeMemo_toSafeMemo2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes}
    (h : SafeMemo dagSize opOf bytesOf S g pts b) :
    SafeMemo2 dagSize opOf bytesOf S g pts b := by
  intro x hx
  rcases h x hx with hpt | ⟨hnai, hlt | ⟨_, hd⟩⟩ | hdag
  · exact Or.inl hpt
  · exact Or.inr (Or.inl ⟨hnai, Or.inl hlt⟩)
  · refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨x.2.2.take (x.2.2.length - 2), ?_⟩⟩)
    rw [← hd, List.take_append_drop]
  · exact Or.inr (Or.inr hdag)

theorem not_memoCollisionOn_of_safeMemo2
    (hNodes : ∀ id < dagSize, dagNodeOk opOf bytesOf id = true)
    (hNoColl : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
      ((opOf id₁).isAI = true ∨ (opOf id₂).isAI = true) →
      bytesOf id₁ = bytesOf id₂ → id₁ = id₂)
    (hNo0100 : ∀ {id : Nat}, id < dagSize → (opOf id).isAI = true →
      ¬ ([0x01#8, 0x00#8] <:+ bytesOf id))
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {known : Bytes → Prop}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List Bytes}
    (hPref : ∀ t ∈ prefixTerms r tr vis,
      SafeMemo2 dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t)
    (hNew : ∀ t ∈ newTerms,
      SafeMemo2 dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t) :
    ¬ MemoCollisionOn keepOpkI0 r S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  set pts := plaintextTerms vis ++ newPts
  have hs₁ : SafeEntry2 dagSize opOf bytesOf pts x₁ := by
    obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
    exact hNew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry2 dagSize opOf bytesOf pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_p | hx₂_n
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_p
      exact hPref t₂ ht₂ x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_n
      exact hNew t₂ ht₂ x₂ hmx₂
  have hAiLen : ∀ {id : Nat}, id < dagSize → (opOf id).isAI = true → 8 ≤ (bytesOf id).length := by
    intro id hid hai
    have hn := hNodes id hid; unfold dagNodeOk at hn
    simp only [hai, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hn
    exact hn.2.1
  rcases hs₁ with ⟨hm₁, hlen₁⟩ | ⟨hnai₁, hni₁⟩ | ⟨id₁, hid₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have := (hpt₁ hm₁).2.1; rw [hnai₂] at this; cases this
    · have h8 := hAiLen hid₂ (hai₂ (hpt₁ hm₁).2.1)
      rw [hbytes, hb₂] at hlen₁; omega
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · have := (hpt₂ hm₂).2.1; rw [hnai₁] at this; cases this
    · rcases hinj with h | h <;> simp_all
    · have hai₂' : (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · rw [hnai₁] at h; cases h
        · exact hai₂ h
      rcases hni₁ with hlt₁ | hsfx₁
      · have h8 := hAiLen hid₂ hai₂'; rw [hbytes, hb₂] at hlt₁; omega
      · rw [hbytes, hb₂] at hsfx₁; exact hNo0100 hid₂ hai₂' hsfx₁
  · rcases hs₂ with ⟨hm₂, hlen₂⟩ | ⟨hnai₂, hni₂⟩ | ⟨id₂, hid₂, hsh₂, hb₂, hai₂⟩
    · have h8 := hAiLen hid₁ (hai₁ (hpt₂ hm₂).2.1)
      rw [← hbytes, hb₁] at hlen₂; omega
    · have hai₁' : (opOf id₁).isAI = true := by
        rcases hinj with h | h
        · exact hai₁ h
        · rw [hnai₂] at h; cases h
      rcases hni₂ with hlt₂ | hsfx₂
      · have h8 := hAiLen hid₁ hai₁'; rw [← hbytes, hb₁] at hlt₂; omega
      · rw [← hbytes, hb₁] at hsfx₂; exact hNo0100 hid₁ hai₁' hsfx₂
    · have hor : (opOf id₁).isAI = true ∨ (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · exact Or.inl (hai₁ h)
        · exact Or.inr (hai₂ h)
      have hideq := hNoColl id₁ hid₁ id₂ hid₂ hor (hb₁.symm.trans (hbytes.trans hb₂))
      subst hideq
      exact hsh (hsh₁.trans hsh₂.symm)

private theorem safeMemo_bool_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (b : Bool) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize b,
      SafeMemo dagSize opOf bytesOf S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := bool_serialize_singleton b
  rw [heq]; intro u hu; rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

private theorem safeMemo_slowNat_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    ∀ (n : Nat) (u : Bytes),
      u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize n →
      SafeMemo dagSize opOf bytesOf S g pts u
  | 0, u, hu => by rw [slowNat_serialize_zero] at hu; exact safeMemo_bool_serialize false u hu
  | n + 1, u, hu => by
    rw [slowNat_serialize_succ, List.mem_append] at hu
    rcases hu with hu | hu
    · exact safeMemo_bool_serialize true u hu
    · exact safeMemo_slowNat_serialize n u hu

private theorem safeMemo_slowString_party {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {p : String} (hp : p = "alice" ∨ p = "bob") :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowString (Bytes := Bytes)).serialize p,
      SafeMemo dagSize opOf bytesOf S g pts u := by
  rw [slowString_serialize_eq]; intro u hu; rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact safeMemo_slowNat_serialize p.utf8ByteSize u hu
  · rw [List.mem_singleton] at hu; subst hu
    rcases hp with rfl | rfl
    · exact safeMemo_lit_short (by rw [alice_utf8_sizes.2]; omega)
    · exact safeMemo_lit_short (by rw [bob_utf8_sizes.2]; omega)

private theorem safeMemo_uint32_serialize {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (x : UInt32) :
    ∀ u ∈ (_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := Bytes)).serialize x,
      SafeMemo dagSize opOf bytesOf S g pts u := by
  obtain ⟨ba, hsz, heq⟩ := uint32_serialize_singleton x
  rw [heq]; intro u hu; rw [List.mem_singleton] at hu; subst hu
  exact safeMemo_lit_short (by omega)

private theorem memo_concat_cases {S : OpaqueSymbolSemantics} {g : Ghost} {a b : Bytes}
    {x : Bytes × Bytes × HwBytes}
    (hx : x ∈ (gamma' keepOpkI0 S g (DY.Concat.concat a b)).memo) :
    (x.1 = DY.Concat.concat a b ∧ x.2.2 = gamma keepOpkI0 S g a ++ gamma keepOpkI0 S g b) ∨
    x ∈ (gamma' keepOpkI0 S g a).memo ∨
    x ∈ (gamma' keepOpkI0 S g b).memo := by
  unfold gamma' at hx
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF Bytes).pack from rfl,
    DY.Bytes.rec_eq gConcat0 (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S g)] at hx
  dsimp only [gConcat0, DY.Libsignal.Composed.Refinement.concretizeConcat, node] at hx
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl hxa)
  · exact Or.inr (Or.inr hxb)

private theorem safeMemo2_concatPrefixes_suffix {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} :
    ∀ (ps : List Bytes) {s : Bytes},
      (∀ p ∈ ps, SafeMemo2 dagSize opOf bytesOf S g pts p) →
      SafeMemo2 dagSize opOf bytesOf S g pts s →
      [0x01#8, 0x00#8] <:+ gamma keepOpkI0 S g s →
      SafeMemo2 dagSize opOf bytesOf S g pts (_root_.Comparse.concatPrefixes ps s) ∧
        [0x01#8, 0x00#8] <:+ gamma keepOpkI0 S g (_root_.Comparse.concatPrefixes ps s)
  | [], s, _, hs, hsfx => by rw [concatPrefixes_nil]; exact ⟨hs, hsfx⟩
  | p :: ps, s, hps, hs, hsfx => by
    rw [concatPrefixes_cons]
    obtain ⟨ih_sm, pfx, hpfx⟩ := safeMemo2_concatPrefixes_suffix ps
      (fun q hq => hps q (List.mem_cons_of_mem p hq)) hs hsfx
    have hsfx_new :
        [0x01#8, 0x00#8] <:+ gamma keepOpkI0 S g (DY.Concat.concat p (_root_.Comparse.concatPrefixes ps s)) := by
      rw [gamma_concatK]
      exact ⟨gamma keepOpkI0 S g p ++ pfx, by rw [List.append_assoc, hpfx]⟩
    refine ⟨?_, hsfx_new⟩
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxp | hxr
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concatK]; exact hsfx_new
    · exact hps p List.mem_cons_self x hxp
    · exact ih_sm x hxr

private theorem bool_ser_false :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize false =
      [litByte 0] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head false; exact heq

private theorem bool_ser_true :
    (_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true =
      [litByte 1] := by
  obtain ⟨ba, _, rfl, heq⟩ := bool_serialize_singleton_head true; exact heq

private theorem slowNat_pos_split :
    ∀ (r : Nat),
      ∃ mid : List Bytes,
        (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize (r + 1) =
          mid ++ [litByte 1, litByte 0]
  | 0 =>
    ⟨[], by rw [slowNat_serialize_succ, slowNat_serialize_zero, bool_ser_true, bool_ser_false]; rfl⟩
  | r + 1 => by
    obtain ⟨mid, ih⟩ := slowNat_pos_split r
    exact ⟨(_root_.Comparse.NonExtensibleMessageFormat.bool (Bytes := Bytes)).serialize true ++ mid,
      by rw [slowNat_serialize_succ, ih, List.append_assoc]⟩

private theorem gamma_lit_ba (S : OpaqueSymbolSemantics) (g : Ghost) (ba : ByteArray) :
    gamma keepOpkI0 S g (DY.Literal.literalToBytes ba) =
      DY.Libsignal.Composed.Refinement.ofByteArray ba := by
  have hg := ms_pack_lit keepOpkI0 S g { lit := ba }
  change gamma' keepOpkI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  unfold gamma; rw [hg]; rfl

theorem safeMemo2_recvTail {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {c : RecvChain} (hr : 1 ≤ c.rIdx) :
    SafeMemo2 dagSize opOf bytesOf S g pts (recvTailTerm c) ∧
      [0x01#8, 0x00#8] <:+ gamma keepOpkI0 S g (recvTailTerm c) := by
  have hr_eq : c.rIdx = (c.rIdx - 1) + 1 := by omega
  obtain ⟨mid, hmid⟩ := slowNat_pos_split (c.rIdx - 1)
  have temp_sm : SafeMemo dagSize opOf bytesOf S g pts (_root_.Comparse.BytesLike.empty : Bytes) :=
    safeMemo_lit_short (ba := ByteArray.empty) (by decide)
  have tb0_sm : SafeMemo dagSize opOf bytesOf S g pts (litByte 0) :=
    safeMemo_lit_short (ba := ⟨#[0]⟩) (by decide)
  have tb1_sm : SafeMemo dagSize opOf bytesOf S g pts (litByte 1) :=
    safeMemo_lit_short (ba := ⟨#[1]⟩) (by decide)
  set s0 := DY.Concat.concat (litByte 0) _root_.Comparse.BytesLike.empty
  set s1 := DY.Concat.concat (litByte 1) s0
  have hs0_g : gamma keepOpkI0 S g s0 = [0x00#8] := by
    dsimp only [s0]; rw [gamma_concatK]
    change gamma keepOpkI0 S g (DY.Literal.literalToBytes ⟨#[0]⟩) ++
      gamma keepOpkI0 S g (DY.Literal.literalToBytes ByteArray.empty) = [0x00#8]
    rw [gamma_lit_ba, gamma_lit_ba]; rfl
  have hs0_sm : SafeMemo2 dagSize opOf bytesOf S g pts s0 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inl ?_⟩)
      rw [hx2, ← gamma_concatK, hs0_g]; decide
    · exact safeMemo_toSafeMemo2 tb0_sm x hxa
    · exact safeMemo_toSafeMemo2 temp_sm x hxb
  have hs1_g : gamma keepOpkI0 S g s1 = [0x01#8, 0x00#8] := by
    dsimp only [s1]; rw [gamma_concatK]
    change gamma keepOpkI0 S g (DY.Literal.literalToBytes ⟨#[1]⟩) ++ gamma keepOpkI0 S g s0 = _
    rw [gamma_lit_ba, hs0_g]; rfl
  have hs1_sfx : [0x01#8, 0x00#8] <:+ gamma keepOpkI0 S g s1 :=
    ⟨[], by rw [List.nil_append, hs1_g]⟩
  have hs1_sm : SafeMemo2 dagSize opOf bytesOf S g pts s1 := by
    intro x hx
    rcases memo_concat_cases hx with ⟨hx1, hx2⟩ | hxa | hxb
    · refine Or.inr (Or.inl ⟨by rw [hx1]; exact ai_concat_eq _ _, Or.inr ?_⟩)
      rw [hx2, ← gamma_concatK]; exact hs1_sfx
    · exact safeMemo_toSafeMemo2 tb1_sm x hxa
    · exact hs0_sm x hxb
  have htail_eq : recvTailTerm c =
      _root_.Comparse.concatPrefixes
        ((_root_.Comparse.NonExtensibleMessageFormat.uint32 (Bytes := Bytes)).serialize c.index ++ mid) s1 := by
    unfold recvTailTerm
    rw [hr_eq, hmid, ← List.append_assoc, ← concatPrefixes_append_eq]
    simp only [concatPrefixes_cons, concatPrefixes_nil, s1, s0]
  rw [htail_eq]
  refine safeMemo2_concatPrefixes_suffix _ (fun u hu => ?_) hs1_sm hs1_sfx
  rcases List.mem_append.mp hu with hu32 | hmid_u
  · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hu32)
  · have hsn : u ∈ (_root_.Comparse.NonExtensibleMessageFormat.slowNat (Bytes := Bytes)).serialize c.rIdx := by
      rw [hr_eq, hmid]; exact List.mem_append_left _ hmid_u
    exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hsn)

private theorem mem_of_getLast? {α : Type} : ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [x], a, h => by simp at h; subst h; exact List.mem_cons_self
  | x :: y :: zs, a, h => List.mem_cons_of_mem x (mem_of_getLast? h)

theorem safeMemo2_trState_of_dr {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState} {cLast : RecvChain}
    (hpart : ls.participant = ls₀.participant)
    (hdr : ls.state.toDRState = ls₀.state.toDRState)
    (hp_party : ls₀.participant = "alice" ∨ ls₀.participant = "bob")
    (hp_peer : ls₀.state.peer = "alice" ∨ ls₀.state.peer = "bob")
    (hspqr : SafeMemo dagSize opOf bytesOf S g pts ls.state.spqr)
    (hcore : ∀ u ∈ [ls₀.state.myIk, ls₀.state.peerIk, ls₀.state.rk,
                     ls₀.state.dhs, ls₀.state.cks, ls₀.state.sid],
      SafeMemo dagSize opOf bytesOf S g pts u)
    (hrecv : ∀ c ∈ ls₀.state.recv,
      SafeMemo dagSize opOf bytesOf S g pts c.ratchetKey ∧
      SafeMemo dagSize opOf bytesOf S g pts c.chainKey)
    (hlast : ls₀.state.recv.getLast? = some cLast)
    (hrIdx : 1 ≤ cLast.rIdx) :
    SafeMemo2 dagSize opOf bytesOf S g pts (DY.Comparse.serialize ls) := by
  have hrecv_eq : ls.state.recv = ls₀.state.recv := congrArg (·.recv) hdr
  have hanchor : stateAnchorPair ls = (cLast.chainKey, recvTailTerm cLast) := by
    unfold stateAnchorPair; rw [hrecv_eq, hlast]
  obtain ⟨htail_sm2, pfx_tail, htail_sfx⟩ :=
    safeMemo2_recvTail (dagSize := dagSize) (opOf := opOf) (bytesOf := bytesOf)
      (S := S) (g := g) (pts := pts) hrIdx
  have hck_sm : SafeMemo dagSize opOf bytesOf S g pts cLast.chainKey :=
    (hrecv cLast (mem_of_getLast? hlast)).2
  intro x hx
  rcases serialize_localTR_memo keepOpkI0 S g ls hx with ⟨u, hu, hmx⟩ | ⟨hnai, pfx_sp, hsp⟩
  · have hu_sm2 : SafeMemo2 dagSize opOf bytesOf S g pts u := by
      unfold trStateProxyRoots at hu
      rw [hanchor, hpart] at hu; dsimp only at hu
      have hpeer : ls.state.peer = ls₀.state.peer := congrArg (·.peer) hdr
      have hmyIk : ls.state.myIk = ls₀.state.myIk := congrArg (·.myIk) hdr
      have hpeerIk : ls.state.peerIk = ls₀.state.peerIk := congrArg (·.peerIk) hdr
      have hrk : ls.state.rk = ls₀.state.rk := congrArg (·.rk) hdr
      have hdhs : ls.state.dhs = ls₀.state.dhs := congrArg (·.dhs) hdr
      have hcks : ls.state.cks = ls₀.state.cks := congrArg (·.cks) hdr
      have hsid : ls.state.sid = ls₀.state.sid := congrArg (·.sid) hdr
      rw [hpeer, hmyIk, hpeerIk, hrk, hdhs, hcks, hsid, hrecv_eq] at hu
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_flatMap] at hu
      rcases hu with (((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize true u h1)
      · exact safeMemo_toSafeMemo2 (safeMemo_bool_serialize false u h2)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_party u h3)
      · exact safeMemo_toSafeMemo2 (safeMemo_slowString_party hp_peer u h4)
      · rcases h5 with rfl | rfl | rfl | rfl | rfl <;>
          exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.ns u h6)
      · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize ls.state.pn u h7)
      · subst h8; exact safeMemo_toSafeMemo2 (hcore _ (by simp))
      · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize ls.state.rIdx u h9)
      · rcases h10 with rfl | rfl | rfl | rfl
        · exact safeMemo_toSafeMemo2 hspqr
        · exact safeMemo_toSafeMemo2 (safeMemo_lit_short (ba := ByteArray.empty) (by decide))
        · exact safeMemo_toSafeMemo2 hck_sm
        · exact htail_sm2
      · obtain ⟨c, hc_mem, hc_u⟩ := h11
        rcases hc_u with ((rfl | rfl) | hidx) | hridx
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).1
        · exact safeMemo_toSafeMemo2 (hrecv c hc_mem).2
        · exact safeMemo_toSafeMemo2 (safeMemo_uint32_serialize c.index u hidx)
        · exact safeMemo_toSafeMemo2 (safeMemo_slowNat_serialize c.rIdx u hridx)
    exact hu_sm2 x hmx
  · rw [hanchor] at hsp; dsimp only at hsp
    refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨pfx_sp ++ gamma keepOpkI0 S g cLast.chainKey ++ pfx_tail, ?_⟩⟩)
    rw [List.append_assoc, List.append_assoc, htail_sfx, hsp]

end StateSafe

/-! ## 4. Pinning `pqKey` and `pqMsg` from `encMsg` Bytes -/

theorem append_inj_right_len {α : Type} {l₁ r₁ l₂ r₂ : List α}
    (h : l₁ ++ r₁ = l₂ ++ r₂) (hr : r₁.length = r₂.length) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hlen : (l₁ ++ r₁).length = (l₂ ++ r₂).length := congrArg List.length h
  rw [List.length_append, List.length_append, hr] at hlen
  exact List.append_inj h (Nat.add_right_cancel hlen)

private theorem paddedVarint_len_check :
    ((List.range 2048).all fun n =>
      (paddedVarint n 0).length == (if n < 128 then 1 else 2)) = true := by
  decide +kernel

private theorem paddedVarint_len_lt2048 {n : Nat} (hn : n < 2048) :
    (paddedVarint n 0).length = (if n < 128 then 1 else 2) :=
  beq_iff_eq.mp (List.all_eq_true.mp paddedVarint_len_check n (List.mem_range.mpr hn))

theorem trWireBytes_canonical_pq_inj {addr pq pq₀ : HwBytes} {f : WireFields}
    (hlen₀ : (trWireBytes addr canonicalVariation f pq₀).length < 2048)
    (heq : trWireBytes addr canonicalVariation f pq =
           trWireBytes addr canonicalVariation f pq₀) :
    pq = pq₀ := by
  have htot : (trWireBytes addr canonicalVariation f pq).length < 2048 := heq ▸ hlen₀
  rw [trWireBytes_canonical] at heq htot hlen₀
  rw [trWireBytes_canonical] at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hmid := (append_inj_right_len (List.append_cancel_left heq) rfl).1
  have hpv42 : (paddedVarint 42 0).length = 1 := paddedVarint_len_lt2048 (by decide)
  by_cases hpq : pq = [] <;> by_cases hpq₀ : pq₀ = []
  · rw [hpq, hpq₀]
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0; omega
  · simp only [hpq, hpq₀, ↓reduceIte, encodeField] at hmid
    have h0 := congrArg List.length hmid
    simp only [List.length_nil, List.length_append, hpv42] at h0; omega
  · have hp_lt : pq.length < 2048 := by
      simp only [hpq, ↓reduceIte, List.length_append, encodeField] at htot; omega
    have hp₀_lt : pq₀.length < 2048 := by
      simp only [hpq₀, ↓reduceIte, List.length_append, encodeField] at hlen₀; omega
    simp only [hpq, hpq₀, ↓reduceIte, encodeField, List.append_assoc] at hmid
    have hvp := List.append_cancel_left hmid
    have hlen := congrArg List.length hvp
    rw [List.length_append, List.length_append,
        paddedVarint_len_lt2048 hp_lt, paddedVarint_len_lt2048 hp₀_lt] at hlen
    have hl_eq : pq.length = pq₀.length := by
      by_cases h1 : pq.length < 128 <;> by_cases h2 : pq₀.length < 128 <;>
        simp only [h1, h2, ↓reduceIte] at hlen <;> omega
    rw [hl_eq] at hvp
    exact List.append_cancel_left hvp

theorem gamma_litOf (S : OpaqueSymbolSemantics) (g : Ghost) (b : HwBytes) :
    gamma keepOpkI0 S g (litOf b) = b := by
  have hv_aux : ∀ l : HwBytes, (l.map UInt8.ofBitVec).map UInt8.toBitVec = l := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih
  let ba := ByteArray.mk (b.map UInt8.ofBitVec).toArray
  have hg := ms_pack_lit keepOpkI0 S g { lit := ba }
  change gamma' keepOpkI0 S g (litOf b) = _ at hg
  unfold gamma; rw [hg]
  exact hv_aux b

theorem gamma_randTerm_ne_zero (S : OpaqueSymbolSemantics) (g : Ghost) {ts sz : Nat}
    (hsz : sz ≠ 0) :
    gamma keepOpkI0 S g (randTerm ts sz) = g.σ ts sz := by
  have hg := ms_pack_random keepOpkI0 S g ⟨ts, sz⟩
  unfold gamma randTerm; rw [hg]; dsimp only [gRandom, concretizeRandom]
  simp only [hsz, ↓reduceIte]; rfl

theorem spqrSend_shapes (S : OpaqueSymbolSemantics) (g : Ghost) (spqr coins : Bytes) :
    (gamma' keepOpkI0 S g (DY.Spqr.spqrSend spqr coins).2.1).shape =
      litOf (gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr coins).2.1) ∧
    (gamma' keepOpkI0 S g (DY.Spqr.spqrSend spqr coins).2.2).shape =
      litOf (gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr coins).2.2) := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · constructor
    · unfold gamma gamma'; dsimp only [DY.Spqr.spqrChainKey]
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S g)]; rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S g)]; rfl
  · constructor
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S g)]; rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll keepOpkI0 S g)]; rfl

theorem gamma_spqrSend_key_length (S : OpaqueSymbolSemantics) (g : Ghost) (spqr c : Bytes) :
    (gamma keepOpkI0 S g (DY.Spqr.spqrSend spqr c).2.1).length = 32 := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · unfold gamma gamma' DY.Spqr.spqrChainKey
    rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll keepOpkI0 S g)]
    exact spqrKeyBytes_length _
  · exact gamma_spqrSendKey_length S g spqr c

theorem encMsg_pins_pqKey_and_pqMsg
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {coins : Bytes} {ptTs : Nat}
    {salt₀ seed₀ rk₀ myIk₀ peerIk₀ pt₀ addr₀ pqm₀ ckey₀ iv₀ ct₀ wire₀ mac₀ : HwBytes}
    (hmsg : gamma keepOpkI0 S g
        (encMsg st coins (DY.Spqr.spqrSend st.spqr coins).2.1 (randTerm ptTs 32)) =
      wire₀ ++ mac₀)
    (hmac_len : mac₀.length = 8)
    (hsalt_len : salt₀.length = 32)
    (huntag : mac₀.take 4 ≠ compTag4)
    (hseed : gamma keepOpkI0 S g (kdfCk st.cks).2 = seed₀)
    (hrk : gamma keepOpkI0 S g (dhPk st.dhs) = rk₀)
    (hpt : g.σ ptTs 32 = pt₀)
    (haddr : g.addr
      (trHonestWireMsg (dhPk st.dhs) st.ns st.pn
        (DY.SymEnc.symEnc
          (trMsgKeys (DY.Spqr.spqrSend st.spqr coins).2.1 (kdfCk st.cks).2).cipherKey
          (trMsgKeys (DY.Spqr.spqrSend st.spqr coins).2.1 (kdfCk st.cks).2).iv
          (randTerm ptTs 32))
        (DY.Spqr.spqrSend st.spqr coins).2.2) = addr₀)
    (hmac₀_eq : mac₀ =
      gamma keepOpkI0 S g
        (computeMac (trMsgKeys (litOf salt₀) (litOf seed₀)).macKey
          (litOf myIk₀) (litOf peerIk₀) (litOf wire₀)))
    (hckey₀ : gamma keepOpkI0 S g (trMsgKeys (litOf salt₀) (litOf seed₀)).cipherKey = ckey₀)
    (hiv₀ : gamma keepOpkI0 S g (trMsgKeys (litOf salt₀) (litOf seed₀)).iv = iv₀)
    (hct₀ : keepOpkAesPerm ckey₀ (iv₀.take 16) pt₀ = ct₀)
    (hwire₀ : trWireBytes addr₀ canonicalVariation
      { version := messageVersion.toNat, ratchetKey := rk₀, counter := st.ns.toNat,
        previousCounter := st.pn.toNat, ciphertext := ct₀ } pqm₀ = wire₀)
    (hwire₀_lt : wire₀.length < 2048) :
    gamma keepOpkI0 S g (DY.Spqr.spqrSend st.spqr coins).2.1 = salt₀ ∧
    gamma keepOpkI0 S g (DY.Spqr.spqrSend st.spqr coins).2.2 = pqm₀ := by
  set pq := (DY.Spqr.spqrSend st.spqr coins).2.1
  set pqm := (DY.Spqr.spqrSend st.spqr coins).2.2
  set keys := trMsgKeys pq (kdfCk st.cks).2
  set wire := trHonestWireMsg (dhPk st.dhs) st.ns st.pn
    (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) pqm
  unfold encMsg at hmsg
  rw [gamma_concatK] at hmsg
  have hgmac_len : (gamma keepOpkI0 S g (computeMac keys.macKey st.myIk st.peerIk wire)).length = 8 := by
    unfold computeMac
    rw [gamma_trunc8K, List.length_take, gamma_hmacK_length]; rfl
  obtain ⟨hwire_eq, hmac_eq⟩ := append_inj_right_len hmsg (hgmac_len.trans hmac_len.symm)
  have hlit_len : (gamma keepOpkI0 S g (litOf salt₀)).length = 32 := by
    rw [gamma_litOf]; exact hsalt_len
  have hpq_len : (gamma keepOpkI0 S g pq).length = 32 :=
    gamma_spqrSend_key_length S g st.spqr coins
  have hpins := computeMac_pins_salt_and_seed hpq_len hlit_len
    (hmac_eq.symm ▸ huntag) (hmac_eq.trans hmac₀_eq)
  have hpq_pin : gamma keepOpkI0 S g pq = salt₀ :=
    hpins.1.trans (gamma_litOf S g salt₀)
  have hprk_eq : gamma keepOpkI0 S g (hmac pq (kdfCk st.cks).2) =
      gamma keepOpkI0 S g (hmac (litOf salt₀) (litOf seed₀)) := by
    rw [gamma_hmacK, gamma_hmacK, hpq_pin, hseed, gamma_litOf, gamma_litOf]
  obtain ⟨hck_eq, _, hiv_eq⟩ := gamma_trMsgKeys_congr_prk hprk_eq
  have hct_eq : gamma keepOpkI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) = ct₀ := by
    have hg := ms_pack_sym keepOpkI0 S g ⟨keys.cipherKey, keys.iv, randTerm ptTs 32⟩
    change gamma' keepOpkI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) = _ at hg
    unfold gamma
    rw [hg]; dsimp only [gSym0, concretizeSym, node]
    change keepOpkAesPerm (gamma keepOpkI0 S g keys.cipherKey)
      ((gamma keepOpkI0 S g keys.iv).take 16)
      (gamma keepOpkI0 S g (randTerm ptTs 32)) = ct₀
    rw [hck_eq, hckey₀, hiv_eq, hiv₀, gamma_randTerm_ne_zero S g (by decide), hpt, hct₀]
  have hgw : gamma keepOpkI0 S g wire =
      trWireBytes addr₀ canonicalVariation
        { version := messageVersion.toNat, ratchetKey := rk₀, counter := st.ns.toNat,
          previousCounter := st.pn.toNat, ciphertext := ct₀ }
        (gamma keepOpkI0 S g pqm) := by
    have hg := ms_pack_trWire keepOpkI0 S g
      ⟨messageVersion, dhPk st.dhs, st.ns, st.pn,
       DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32), pqm, canonicalVariation⟩
    change gamma' keepOpkI0 S g wire = _ at hg
    have haddr' : g.addr (DY.BytesView.pack (SubF := DY.TrWire.TrWireMsg.SubF)
      ⟨messageVersion, dhPk st.dhs, st.ns, st.pn,
       DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32), pqm, canonicalVariation⟩) = addr₀ := haddr
    unfold gamma
    rw [hg]; dsimp only [gTrWire0, concretizeTrWire, node]
    rw [haddr']
    change trWireBytes addr₀ canonicalVariation
      { version := messageVersion.toNat,
        ratchetKey := gamma keepOpkI0 S g (dhPk st.dhs),
        counter := st.ns.toNat,
        previousCounter := st.pn.toNat,
        ciphertext := gamma keepOpkI0 S g (DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm ptTs 32)) }
      (gamma keepOpkI0 S g pqm) = _
    rw [hrk, hct_eq]; rfl
  have hpqm_pin : gamma keepOpkI0 S g pqm = pqm₀ :=
    trWireBytes_canonical_pq_inj (hwire₀.symm ▸ hwire₀_lt) (hgw.symm.trans (hwire_eq.trans hwire₀.symm))
  exact ⟨hpq_pin, hpqm_pin⟩

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.DagDefs
