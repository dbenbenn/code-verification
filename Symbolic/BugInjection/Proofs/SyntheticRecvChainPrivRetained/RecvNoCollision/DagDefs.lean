/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
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
# Concrete DAG Certificate Types, Evaluator, and `SafeMemo` Combinators (`RecvNoCollision/DagDefs.lean`)

Defines `DagOp`, topological fuel-based `dagShape`, concrete byte evaluator `dagNodeOk`,
collision checker `bucketNoCollision`, and the `SafeEntry` / `SafeMemo` / `TermAt` framework
used to certify absence of `MemoCollisionOn` across all clean prefixes and receiver trials.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs

open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (canonicalVariation sha256CompressFunction FieldItem PbValue)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain hmac hkdfBlock1 hkdfBlock2 hkdfBlock3
   kdfRk createChain kdfCk trMsgKeys computeMac trHonestWireMsg)
open DY.Libsignal.PQXDH (PQXDHState agree encodeEC encodeKEM serializedIk)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry
   node concretizeRandom gRandom
   gamma' gamma randTerm litOf clamp trWireBytes
   assumedInjective MemoCollisionOn prefixTerms plaintextTerms)
open ByteSpecs (hmacWith)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compKyberEncaps bytesToNat)
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj (eq_of_bytesToNat_eq)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo
  (MemoOK memoOK_dhPk_elim memoOK_spqrInit memoOK_spqrInit_elim memoOK_spqrChainKey
   memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg memoOK_spqrRecvState_pack)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_random ms_pack_lit ms_pack_kdf)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
  (assumedInjective_lit bytes_rec_gAll memoOK_symEnc_elim memoOK_spqrRecvKey_pack)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (recvTailTerm stateAnchorPair trStateProxyRoots serialize_localTR_memo suffix_drop_eq)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprLookupPub rcprLookupDh rcprAesPerm)

/-- Structural constructor of a deduplicated concrete DAG node. -/
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

/-- Whether a `DagOp` head has `assumedInjective = true`. -/
def DagOp.isAI : DagOp → Bool
  | .lit _ | .concat _ _ | .trWire .. => false
  | _ => true

/-- Checks that every child index of `op` is strictly less than `id`. -/
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

/-- Concrete byte evaluation check for a single `DagOp` node `id`. -/
def dagOpBytesOk (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) : Bool :=
  let v := bytesOf id
  match op with
  | .rand _ sz => decide (sz ≠ 0)
  | .lit bs => v == bs
  | .concat l r => v == bytesOf l ++ bytesOf r
  | .dhPk s => v == rcprLookupPub (clamp (bytesOf s))
  | .dh pk sk => v == rcprLookupDh (clamp (bytesOf sk)) (bytesOf pk)
  | .kdf a b => v == hmacWith (sha256CompressFunction rcprI0) (bytesOf a) (bytesOf b)
  | .symEncPt k iv _ ptBs => v == rcprAesPerm (bytesOf k) ((bytesOf iv).take 16) ptBs
  | .trunc8 a => v == (bytesOf a).take 8
  | .trWire ver rk cnt prev ct pq addr =>
      v == trWireBytes addr canonicalVariation
        { version := ver.toNat, ratchetKey := bytesOf rk, counter := cnt.toNat,
          previousCounter := prev.toNat, ciphertext := bytesOf ct } (bytesOf pq)
  | .kemEncap _ e =>
      decide ((bytesOf e).length = 32) && v == (compKyberEncaps (bytesOf e)).take 1568
  | .kemSS _ e =>
      decide ((bytesOf e).length = 32) && v == (compKyberEncaps (bytesOf e)).drop 1568

/-- Full per-node certificate: topological order, byte evaluation, length bound `< 2048`,
and for `isAI = true`, length `≥ 8` and non-matching `TRState` `[0x01, 0x00]` spine suffix. -/
def dagNodeOk (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes) (id : Nat) : Bool :=
  let op := opOf id
  let v := bytesOf id
  op.childrenLt id &&
  decide (v.length < 2048) &&
  dagOpBytesOk bytesOf id op &&
  (!op.isAI || (decide (8 ≤ v.length) &&
    !(decide (38 ≤ v.length) && (v.drop (v.length - 2) == [0x01#8, 0x00#8]))))

/-- Fuel-bounded evaluator reconstructing the symbolic `ConcretizedTerm.shape` of `id`. -/
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

/-- Injective integer key for `HwBytes` of length `< 2048`. -/
def packBytesKey (bs : HwBytes) : Nat :=
  bs.length + 2048 * bytesToNat bs

theorem packBytesKey_inj {a b : HwBytes}
    (ha : a.length < 2048) (hb : b.length < 2048)
    (heq : packBytesKey a = packBytesKey b) : a = b := by
  unfold packBytesKey at heq
  have hlen : a.length = b.length := by omega
  have hnat : bytesToNat a = bytesToNat b := by omega
  exact eq_of_bytesToNat_eq hlen hnat

/-- Bucket index `0..255` from first byte (`0` on empty). -/
def bytesBucketIdx (bs : HwBytes) : Nat :=
  match bs with
  | [] => 0
  | b :: _ => b.toNat

/-- Checks that within a list of `(id, isAI, packedKey)` triples, no `isAI = true` entry
shares `packedKey` with any distinct `id' ≠ id`. -/
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

/-- Canonical `.shape` reconstructed from `opOf` at fuel `dagSize`. -/
def dagShape (opOf : Nat → DagOp) (dagSize id : Nat) : Bytes :=
  evalDagShapeAux opOf dagSize id

theorem dagShape_unfold {opOf : Nat → DagOp} {dagSize id : Nat}
    (htopo : ∀ i < dagSize, (opOf i).childrenLt i = true)
    (hid : id < dagSize) :
    dagShape opOf dagSize id =
      evalDagShapeAux opOf (dagSize + 1) id := by
  let opSafe : Nat → DagOp := fun i => if i < dagSize then opOf i else .lit []
  have htopoSafe : ∀ i, (opSafe i).childrenLt i = true := by
    intro i; dsimp only [opSafe]
    split_ifs with hi
    · exact htopo i hi
    · rfl
  have heq : ∀ f j, j < dagSize → j < f → evalDagShapeAux opOf f j = evalDagShapeAux opSafe f j := by
    intro f
    induction f with
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

/-- Three-branch invariant classifying every memo entry `x = (term, shape, bytes)`. -/
def SafeEntry (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (pts : List Bytes) (x : Bytes × Bytes × HwBytes) : Prop :=
  (x.1 ∈ pts ∧ x.2.2.length < 8) ∨
  (assumedInjective x.1 = false ∧
    (x.2.2.length < 8 ∨
     (38 ≤ x.2.2.length ∧ x.2.2.drop (x.2.2.length - 2) = [0x01#8, 0x00#8]))) ∨
  (∃ id < dagSize, x.2.1 = dagShape opOf dagSize id ∧ x.2.2 = bytesOf id ∧
    (assumedInjective x.1 = true → (opOf id).isAI = true))

/-- Every memo entry of `b` under `(rcprI0, S, g)` satisfies `SafeEntry`. -/
def SafeMemo (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) : Prop :=
  MemoOK rcprI0 S g (SafeEntry dagSize opOf bytesOf pts) b

/-- Exact DAG node witness for `b`: pins `.bytes`, `.shape`, and `SafeMemo`. -/
def TermAt (dagSize : Nat) (opOf : Nat → DagOp) (bytesOf : Nat → HwBytes)
    (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) (b : Bytes) (id : Nat) : Prop :=
  id < dagSize ∧
  (gamma' rcprI0 S g b).bytes = bytesOf id ∧
  (gamma' rcprI0 S g b).shape = dagShape opOf dagSize id ∧
  SafeMemo dagSize opOf bytesOf S g pts b

theorem TermAt.safeMemo {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    SafeMemo dagSize opOf bytesOf S g pts b :=
  h.2.2.2

theorem TermAt.gamma_eq {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {b : Bytes} {id : Nat}
    (h : TermAt dagSize opOf bytesOf S g pts b id) :
    gamma rcprI0 S g b = bytesOf id :=
  h.2.1

/-- Master refutation of `MemoCollisionOn` from certified `dagNodeOk`, `hNoColl`, and `SafeMemo`. -/
theorem not_memoCollisionOn_of_safeMemo
    {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    (hNodes : ∀ id < dagSize, dagNodeOk opOf bytesOf id = true)
    (hNoColl : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
      ((opOf id₁).isAI = true ∨ (opOf id₂).isAI = true) →
      bytesOf id₁ = bytesOf id₂ → id₁ = id₂)
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {known : Bytes → Prop}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List Bytes}
    (hPref : ∀ t ∈ prefixTerms r tr vis,
      SafeMemo dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t)
    (hNew : ∀ t ∈ newTerms,
      SafeMemo dagSize opOf bytesOf S g (plaintextTerms vis ++ newPts) t) :
    ¬ MemoCollisionOn rcprI0 r S g known tr vis newTerms newPts := by
  rintro ⟨x₁, hx₁_raw, x₂, hx₂_raw, hsh, hinj, hpt₁, hpt₂, hbytes⟩
  set pts := plaintextTerms vis ++ newPts
  have hs₁ : SafeEntry dagSize opOf bytesOf pts x₁ := by
    obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
    exact hNew t₁ ht₁ x₁ hmx₁
  have hs₂ : SafeEntry dagSize opOf bytesOf pts x₂ := by
    rcases List.mem_append.mp hx₂_raw with hx₂_p | hx₂_n
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_p
      exact hPref t₂ ht₂ x₂ hmx₂
    · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_n
      exact hNew t₂ ht₂ x₂ hmx₂
  have hAiProp : ∀ {id : Nat}, id < dagSize → (opOf id).isAI = true →
      8 ≤ (bytesOf id).length ∧
      ¬(38 ≤ (bytesOf id).length ∧ (bytesOf id).drop ((bytesOf id).length - 2) = [0x01#8, 0x00#8]) := by
    intro id hid hai
    have hn := hNodes id hid
    unfold dagNodeOk at hn
    simp only [hai, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hn
    obtain ⟨_, h8, hnsfx⟩ := hn
    exact ⟨h8, fun ⟨h38, hd⟩ => by rcases hnsfx with h1 | h2; exact h1 h38; exact h2 hd⟩
  rcases hs₁ with ⟨hm₁, hlen₁⟩ | ⟨hnai₁, hni₁⟩ | ⟨id₁, hid₁, hsh₁, hb₁, hai₁⟩
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · exact (hpt₁ hm₁).1 hm₂
    · have := (hpt₁ hm₁).2.1; rw [hnai₂] at this; cases this
    · have ⟨h8, _⟩ := hAiProp hid₂ (hai₂ (hpt₁ hm₁).2.1)
      rw [hbytes, hb₂] at hlen₁; omega
  · rcases hs₂ with ⟨hm₂, _⟩ | ⟨hnai₂, _⟩ | ⟨id₂, hid₂, _, hb₂, hai₂⟩
    · have := (hpt₂ hm₂).2.1; rw [hnai₁] at this; cases this
    · rcases hinj with h | h <;> simp_all
    · have hai₂' : (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · rw [hnai₁] at h; cases h
        · exact hai₂ h
      have ⟨h8, hnsfx⟩ := hAiProp hid₂ hai₂'
      rcases hni₁ with hlt₁ | ⟨h38₁, hd₁⟩
      · rw [hbytes, hb₂] at hlt₁; omega
      · rw [hbytes, hb₂] at h38₁ hd₁; exact hnsfx ⟨h38₁, hd₁⟩
  · rcases hs₂ with ⟨hm₂, hlen₂⟩ | ⟨hnai₂, hni₂⟩ | ⟨id₂, hid₂, hsh₂, hb₂, hai₂⟩
    · have ⟨h8, _⟩ := hAiProp hid₁ (hai₁ (hpt₂ hm₂).2.1)
      rw [← hbytes, hb₁] at hlen₂; omega
    · have hai₁' : (opOf id₁).isAI = true := by
        rcases hinj with h | h
        · exact hai₁ h
        · rw [hnai₂] at h; cases h
      have ⟨h8, hnsfx⟩ := hAiProp hid₁ hai₁'
      rcases hni₂ with hlt₂ | ⟨h38₂, hd₂⟩
      · rw [← hbytes, hb₁] at hlt₂; omega
      · rw [← hbytes, hb₁] at h38₂ hd₂; exact hnsfx ⟨h38₂, hd₂⟩
    · have hor : (opOf id₁).isAI = true ∨ (opOf id₂).isAI = true := by
        rcases hinj with h | h
        · exact Or.inl (hai₁ h)
        · exact Or.inr (hai₂ h)
      have hideq := hNoColl id₁ hid₁ id₂ hid₂ hor (hb₁.symm.trans (hbytes.trans hb₂))
      subst hideq
      exact hsh (hsh₁.trans hsh₂.symm)

theorem safeMemo_mono_pts {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts₁ pts₂ : List Bytes} {b : Bytes}
    (hsub : ∀ p ∈ pts₁, p ∈ pts₂)
    (h : SafeMemo dagSize opOf bytesOf S g pts₁ b) :
    SafeMemo dagSize opOf bytesOf S g pts₂ b := by
  intro x hx
  rcases h x hx with ⟨hm, hl⟩ | hsp | hdag
  · exact Or.inl ⟨hsub _ hm, hl⟩
  · exact Or.inr (Or.inl hsp)
  · exact Or.inr (Or.inr hdag)

theorem safeMemo_plaintext {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {ts : Nat}
    (hmem : randTerm ts 32 ∈ pts)
    (hlen : (g.σ ts 32).length < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 32) := by
  intro x hx
  unfold randTerm at hx
  rw [ms_pack_random rcprI0 S g ⟨ts, 32⟩] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [Nat.reduceEqDiff, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  exact Or.inl ⟨hmem, hlen⟩

theorem safeMemo_symDec {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {k iv ct m : Bytes}
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
    rw [hx] at hpv
    rw [← hpv] at hct
    exact memoOK_symEnc_elim (e := ⟨key', iv', m⟩) hct

theorem safeMemo_serialize_localTR {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    (ls : DY.PersistentLocalState.LocalState TRState)
    (hroots : ∀ r ∈ trStateProxyRoots ls, SafeMemo dagSize opOf bytesOf S g pts r)
    (hlen : 38 ≤ (gamma rcprI0 S g (stateAnchorPair ls).1 ++
      gamma rcprI0 S g (stateAnchorPair ls).2).length)
    (hsfx : (gamma rcprI0 S g (stateAnchorPair ls).1 ++
      gamma rcprI0 S g (stateAnchorPair ls).2).drop
      ((gamma rcprI0 S g (stateAnchorPair ls).1 ++
        gamma rcprI0 S g (stateAnchorPair ls).2).length - 2) = [0x01#8, 0x00#8]) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Comparse.serialize ls) := by
  intro x hx
  rcases serialize_localTR_memo rcprI0 S g ls hx with ⟨r, hr, hmx⟩ | ⟨hnai, hsuff⟩
  · exact hroots r hr x hmx
  · refine Or.inr (Or.inl ⟨hnai, Or.inr ⟨?_, ?_⟩⟩)
    · have := hsuff.length_le; omega
    · rcases hsuff with ⟨pfx, heq⟩
      rw [← heq]
      have hsub : (pfx ++ (gamma rcprI0 S g (stateAnchorPair ls).1 ++
          gamma rcprI0 S g (stateAnchorPair ls).2)).length - 2 =
          pfx.length + ((gamma rcprI0 S g (stateAnchorPair ls).1 ++
            gamma rcprI0 S g (stateAnchorPair ls).2).length - 2) := by
        rw [List.length_append]; omega
      rw [hsub, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right pfx.length _),
        List.nil_append, Nat.add_sub_cancel_left, hsfx]

theorem safeMemo_lit_short {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} {ba : ByteArray}
    (hlen : ba.size < 8) :
    SafeMemo dagSize opOf bytesOf S g pts (DY.Literal.literalToBytes ba) := by
  intro x hx
  have hg := ms_pack_lit rcprI0 S g ⟨ba⟩
  change gamma' rcprI0 S g (DY.Literal.literalToBytes ba) = _ at hg
  rw [hg] at hx
  unfold DY.Libsignal.Composed.Refinement.gLit0 DY.Libsignal.Composed.Refinement.concretizeLit node at hx
  simp only [List.flatMap_nil, List.mem_singleton] at hx
  subst hx
  refine Or.inr (Or.inl ⟨assumedInjective_lit ba, Or.inl ?_⟩)
  dsimp only [DY.Libsignal.Composed.Refinement.ofByteArray]
  rw [List.length_map, Array.length_toList]
  exact hlen

theorem safeMemo_randTerm_zero {dagSize : Nat} {opOf : Nat → DagOp} {bytesOf : Nat → HwBytes}
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes} (ts : Nat) :
    SafeMemo dagSize opOf bytesOf S g pts (randTerm ts 0) := by
  intro x hx
  have hg := ms_pack_random rcprI0 S g ⟨ts, 0⟩
  change gamma' rcprI0 S g (randTerm ts 0) = _ at hg
  rw [hg] at hx
  dsimp only [gRandom, concretizeRandom] at hx
  simp only [↓reduceIte] at hx
  cases hx

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs
