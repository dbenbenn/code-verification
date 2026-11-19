/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionEval

/-!
# Certified Symbolic-SPQR DAG Definitions for Seed 7003 (`Dag7003Defs.lean`)

Defines the 11-constructor concrete node algebra `DagOp` (including non-canonical wire encoding
flag `useEv4Var` for `ev4Variation`), shape reconstruction `dagShape`, per-node byte/invariant
checker `dagNodeOk` under `compI7003`, and `Trie`-bucketed `O(N)` pairwise non-collision checker
`dagPairwiseOk`, parametric over all `S : OpaqueSymbolSemantics`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs

open scoped DY.Libsignal.Composed
open ByteSpecs (hmacWith)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (clamp trWireBytes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
  (compLookupPub compLookupDh compAesPerm compKyberEncaps)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws (F7)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
  (pt1M1Bytes pt1M2Bytes pt3M2Bytes ev4Variation)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
  (tRnd tLit tCat tDhPk tDh tKdf tSym tTr8 tKemEnc tKemSS tTrW)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (Trie emptyTrie trieBucket trieInsert foldl_memoTrie_mem forceTrieOnce forceTrieOnce_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag (firstTwoBytesKey)

inductive DagOp where
  | lit (bs : HwBytes)
  | rand (ts sz : Nat)
  | concat (l r : Nat)
  | dhPk (sk : Nat)
  | dh (pk sk : Nat)
  | kdf (salt ikm : Nat)
  | trunc8 (inp : Nat)
  | symEncPt (key iv ts : Nat) (pt : HwBytes)
  | trWire (ver : UInt8) (rk : Nat) (cnt prev : UInt32) (ct pq : Nat)
      (addr : HwBytes) (useEv4Var : Bool)
  | kemEncap (pk ent : Nat)
  | kemSS (pk ent : Nat)
  deriving DecidableEq

def DagOp.isAI : DagOp → Bool
  | .lit _ | .concat _ _ | .trWire _ _ _ _ _ _ _ _ => false
  | _ => true

def trWireEvOf (useEv4Var : Bool) : DY.TrWire.EncodingVariation :=
  if useEv4Var then ev4Variation else DY.TrWire.canonicalVariation

def trWireShapeVar (addr : HwBytes) (useEv4Var : Bool) : DY.TrWire.EncodingVariation :=
  let ev := trWireEvOf useEv4Var
  { ev with fields := .extra 6 (.bytes addr) 0 0 :: ev.fields }

def dagShape (opOf : Nat → DagOp) (id : Nat) : DY.Bytes :=
  match opOf id with
  | .lit bs => tLit bs
  | .rand ts sz => tRnd ts sz
  | .concat l r =>
    tCat (if l < id then dagShape opOf l else tLit [])
         (if r < id then dagShape opOf r else tLit [])
  | .dhPk sk =>
    tDhPk (if sk < id then dagShape opOf sk else tLit [])
  | .dh pk sk =>
    DY.DiffieHellman.dh
      (if pk < id then dagShape opOf pk else tLit [])
      (if sk < id then dagShape opOf sk else tLit [])
  | .kdf salt ikm =>
    tKdf (if salt < id then dagShape opOf salt else tLit [])
         (if ikm < id then dagShape opOf ikm else tLit [])
  | .trunc8 inp =>
    tTr8 (if inp < id then dagShape opOf inp else tLit [])
  | .symEncPt key iv ts _ =>
    tSym (if key < id then dagShape opOf key else tLit [])
         (if iv < id then dagShape opOf iv else tLit [])
         (tRnd ts 32)
  | .trWire ver rk cnt prev ct pq addr useEv4Var =>
    tTrW ver
      (if rk < id then dagShape opOf rk else tLit [])
      cnt prev
      (if ct < id then dagShape opOf ct else tLit [])
      (if pq < id then dagShape opOf pq else tLit [])
      (trWireShapeVar addr useEv4Var)
  | .kemEncap pk ent =>
    tKemEnc (if pk < id then dagShape opOf pk else tLit [])
            (if ent < id then dagShape opOf ent else tLit [])
  | .kemSS pk ent =>
    tKemSS (if pk < id then dagShape opOf pk else tLit [])
           (if ent < id then dagShape opOf ent else tLit [])
termination_by id

def dagOpBytesOk (bOf : Nat → HwBytes) (id : Nat) (op : DagOp) (v : HwBytes) : Bool :=
  match op with
  | .lit bs => bs == v
  | .rand _ sz => decide (0 < sz)
  | .concat l r => decide (l < id) && decide (r < id) && (bOf l ++ bOf r == v)
  | .dhPk sk => decide (sk < id) && (compLookupPub (clamp (bOf sk)) == v)
  | .dh pk sk =>
    decide (pk < id) && decide (sk < id) && (compLookupDh (clamp (bOf sk)) (bOf pk) == v)
  | .kdf salt ikm =>
    decide (salt < id) && decide (ikm < id) && (hmacWith F7 (bOf salt) (bOf ikm) == v)
  | .trunc8 inp => decide (inp < id) && ((bOf inp).take 8 == v)
  | .symEncPt key iv _ pt =>
    decide (key < id) && decide (iv < id) &&
      (compAesPerm (bOf key) ((bOf iv).take 16) pt == v)
  | .trWire ver rk cnt prev ct pq addr useEv4Var =>
    decide (rk < id) && decide (ct < id) && decide (pq < id) &&
      (trWireBytes addr (trWireEvOf useEv4Var)
        { version := ver.toNat, ratchetKey := bOf rk, counter := cnt.toNat,
          previousCounter := prev.toNat, ciphertext := bOf ct } (bOf pq) == v)
  | .kemEncap pk ent =>
    decide (pk < id) && decide (ent < id) && Nat.beq (bOf ent).length 32 &&
      ((compKyberEncaps (bOf ent)).take 1568 == v)
  | .kemSS pk ent =>
    decide (pk < id) && decide (ent < id) && Nat.beq (bOf ent).length 32 &&
      ((compKyberEncaps (bOf ent)).drop 1568 == v)

def dagNodeOk (opOf : Nat → DagOp) (bOf : Nat → HwBytes) (id : Nat) : Bool :=
  let op := opOf id
  let v := bOf id
  dagOpBytesOk bOf id op v &&
    (!op.isAI || (!(v == pt1M1Bytes) && !(v == pt1M2Bytes) && !(v == pt3M2Bytes)))

def checkAllDagNodes (dagSize : Nat) (opOf : Nat → DagOp) (bOf : Nat → HwBytes) : Bool :=
  (List.range dagSize).all (dagNodeOk opOf bOf)

def dagPairwiseOkExcept (dagSize : Nat) (opOf : Nat → DagOp) (bOf : Nat → HwBytes)
    (skipId : Nat) : Bool :=
  let ids := (List.range dagSize).filter (· != skipId)
  forceTrieOnce
    (ids.foldl (fun mt i => trieInsert mt (firstTwoBytesKey (bOf i)) i) (emptyTrie 8))
    fun mt =>
      ids.all fun i =>
        (trieBucket mt (firstTwoBytesKey (bOf i))).all fun j =>
          Nat.beq i j || (!(opOf i).isAI && !(opOf j).isAI) || !(bOf i == bOf j)

theorem dagNodeOk_of_all {dagSize : Nat} {opOf : Nat → DagOp} {bOf : Nat → HwBytes}
    (hall : checkAllDagNodes dagSize opOf bOf = true)
    {id : Nat} (hid : id < dagSize) :
    dagNodeOk opOf bOf id = true :=
  List.all_eq_true.mp hall id (List.mem_range.mpr hid)

theorem ai_not_pts {dagSize : Nat} {opOf : Nat → DagOp} {bOf : Nat → HwBytes}
    (hall : checkAllDagNodes dagSize opOf bOf = true)
    {id : Nat} (hid : id < dagSize) (hai : (opOf id).isAI = true) :
    bOf id ≠ pt1M1Bytes ∧ bOf id ≠ pt1M2Bytes ∧ bOf id ≠ pt3M2Bytes := by
  have hok := dagNodeOk_of_all hall hid
  unfold dagNodeOk at hok
  simp only [Bool.and_eq_true, hai, Bool.not_true, Bool.false_or] at hok
  obtain ⟨_, ⟨h1, h2⟩, h3⟩ := hok
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem dagPairwiseOkExcept_eq_of_ai {dagSize : Nat} {opOf : Nat → DagOp} {bOf : Nat → HwBytes}
    {skipId : Nat}
    (hpw : dagPairwiseOkExcept dagSize opOf bOf skipId = true)
    {i j : Nat} (hi : i < dagSize) (hiskip : i ≠ skipId)
    (hj : j < dagSize) (hjskip : j ≠ skipId)
    (hai : (opOf i).isAI = true ∨ (opOf j).isAI = true)
    (hbytes : bOf i = bOf j) : i = j := by
  unfold dagPairwiseOkExcept at hpw
  rw [forceTrieOnce_eq] at hpw
  have hmem_i : i ∈ (List.range dagSize).filter (· != skipId) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, bne_iff_ne.mpr hiskip⟩
  have hmem_j : j ∈ (List.range dagSize).filter (· != skipId) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hj, bne_iff_ne.mpr hjskip⟩
  have hkey : firstTwoBytesKey (bOf i) = firstTwoBytesKey (bOf j) := by rw [hbytes]
  have hbuck : j ∈ trieBucket
      (((List.range dagSize).filter (· != skipId)).foldl
        (fun mt k => trieInsert mt (firstTwoBytesKey (bOf k)) k) (emptyTrie 8))
      (firstTwoBytesKey (bOf i)) := by
    rw [hkey]
    exact foldl_memoTrie_mem (fun k => firstTwoBytesKey (bOf k)) _ (emptyTrie 8) j
      (Or.inl hmem_j)
  have hij := List.all_eq_true.mp (List.all_eq_true.mp hpw i hmem_i) j hbuck
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hij
  rcases hij with (heq | ⟨hni, hnj⟩) | hne
  · exact Nat.beq_eq.mp heq
  · rcases hai with h1 | h2 <;> simp_all
  · exact absurd hbytes hne

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs
