/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBucketData
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert0
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert1
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert2
import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagCert3

/-!
# Certified Node Validity and Bucket Collision Freedom

Combines the 4 node-certificate shards (`RecvDagCert0`–`RecvDagCert3`) into `dag_nodes_ok`,
checks bucket coverage and per-bucket non-collision across all 512 hash buckets using the
unboxed 54-bit prefix hash `fastBytesKey`, and proves `dag_no_collision`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets

open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (btGet)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagNodeOk bucketNoCollision bucketNoCollision_sound)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagTree dagOp dagBytes fastBucketIdx rangeAll rangeAll_trans)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBucketData
  (dagBucketIds dagNodeBkt)

theorem dag_nodes_ok : ∀ id < dagSize, dagNodeOk dagOp dagBytes id = true := by
  intro id hid
  if h0 : id < 1680 then
    exact RecvDagCert0.certRangeOk_0 (by omega) h0
  else if h1 : id < 3360 then
    exact RecvDagCert1.certRangeOk_1 (by omega) h1
  else if h2 : id < 5040 then
    exact RecvDagCert2.certRangeOk_2 (by omega) h2
  else
    exact RecvDagCert3.certRangeOk_3 (by omega) hid

private def fastElem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys =>
    match Nat.beq x y with
    | true => true
    | false => fastElem x ys

private theorem fastElem_mem {x : Nat} : ∀ {ys : List Nat}, fastElem x ys = true → x ∈ ys
  | [], h => by contradiction
  | y :: ys, h => by
    unfold fastElem at h
    cases hxy : Nat.beq x y with
    | true => rw [Nat.beq_eq.mp hxy]; exact .head _
    | false => rw [hxy] at h; exact .tail _ (fastElem_mem h)

private def byteAtOr0 (bs : DY.Libsignal.HwBytes) : Nat → Nat
  | 0 => match bs with | b :: _ => b.toFin.val | [] => 0
  | n + 1 => match bs with | _ :: rest => byteAtOr0 rest n | [] => 0

private def pack11 (tag b0 b4 b5 b6 b8 b12 b13 b19 b21 b28 b29 : Nat) : Nat :=
  b4 + 256 * (b5 + 256 * (b6 + 256 * (b8 + 256 * (b12 + 256 *
    (b13 + 256 * (b19 + 256 * (b21 + 256 * (b28 + 256 * (b29 + 256 *
      (b0 + 256 * tag))))))))))

private def fastKey : DY.Libsignal.HwBytes → Nat
  | b0 :: _ :: _ :: _ :: b4 :: b5 :: b6 :: _ ::
    b8 :: _ :: _ :: _ :: b12 :: b13 :: _ :: _ ::
    _ :: _ :: _ :: b19 :: _ :: b21 :: _ :: _ ::
    _ :: _ :: _ :: _ :: b28 :: b29 :: _ :: _ :: rest =>
    let tag := match rest with | [] => 1 | _ :: _ => 2
    pack11 tag b0.toFin.val b4.toFin.val b5.toFin.val b6.toFin.val b8.toFin.val
      b12.toFin.val b13.toFin.val b19.toFin.val b21.toFin.val b28.toFin.val b29.toFin.val
  | bs =>
    pack11 (32 + bs.length) (byteAtOr0 bs 0) (byteAtOr0 bs 4) (byteAtOr0 bs 5)
      (byteAtOr0 bs 6) (byteAtOr0 bs 8) (byteAtOr0 bs 12) (byteAtOr0 bs 13)
      (byteAtOr0 bs 19) (byteAtOr0 bs 21) (byteAtOr0 bs 28) (byteAtOr0 bs 29)

private def fastIdCovered (id : Nat) : Bool :=
  let b := dagNodeBkt id
  Nat.ble (b + 1) 512 && fastElem id (dagBucketIds b)

private theorem covAll : rangeAll fastIdCovered 0 6720 = true := by decide +kernel

private theorem id_in_nodeBkt {id : Nat} (hid : id < dagSize) :
    dagNodeBkt id < 512 ∧ id ∈ dagBucketIds (dagNodeBkt id) := by
  have h := covAll
  unfold rangeAll at h
  have hk := List.all_eq_true.mp h id (List.mem_range.mpr hid)
  rw [Nat.zero_add] at hk
  obtain ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp hk
  exact ⟨Nat.le_of_ble_eq_true hb, fastElem_mem hm⟩

private def fastNodeMeta (id : Nat) : Bool × Nat :=
  match btGet 13 dagTree id with
  | some (op, bs) => (op.isAI, fastKey bs)
  | none => (false, fastKey [])

private theorem fastNodeMeta_eq (id : Nat) :
    fastNodeMeta id = ((dagOp id).isAI, fastKey (dagBytes id)) := by
  unfold fastNodeMeta dagOp dagBytes
  cases btGet 13 dagTree id <;> rfl

private def dagBucketEntries (b : Nat) : List (Nat × Bool × Nat) :=
  (dagBucketIds b).map fun id => (id, (dagOp id).isAI, fastKey (dagBytes id))

private def fastBucketEntries (b : Nat) : List (Nat × Bool × Nat) :=
  (dagBucketIds b).map fun id =>
    let m := fastNodeMeta id
    (id, m.1, m.2)

private theorem fastBucketEntries_eq (b : Nat) :
    fastBucketEntries b = dagBucketEntries b := by
  unfold fastBucketEntries dagBucketEntries
  congr 1; funext id
  rw [fastNodeMeta_eq]

private def fastBucketNoCollision (entries : List (Nat × Bool × Nat)) : Bool :=
  entries.all fun (id₁, ai₁, k₁) =>
    !ai₁ || entries.all fun (id₂, _, k₂) =>
      !Nat.beq k₁ k₂ || Nat.beq id₁ id₂

private theorem fastBucketNoCollision_eq (entries : List (Nat × Bool × Nat)) :
    fastBucketNoCollision entries = bucketNoCollision entries := by
  unfold fastBucketNoCollision bucketNoCollision
  apply congrArg (List.all entries); funext ⟨id₁, ai₁, k₁⟩
  dsimp only
  apply congrArg (Bool.or (!ai₁)); apply congrArg (List.all entries); funext ⟨id₂, _, k₂⟩
  dsimp only
  have hk0 : Nat.beq k₁ k₂ = decide (k₁ = k₂) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.beq_eq]
  have hk : (!Nat.beq k₁ k₂) = decide (k₁ ≠ k₂) := by
    rw [hk0]; by_cases h : k₁ = k₂ <;> simp [h]
  have hi : Nat.beq id₁ id₂ = decide (id₁ = id₂) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.beq_eq]
  rw [hk, hi]

private def fastBktOk (b : Nat) : Bool :=
  let entries := fastBucketEntries b
  (entries.all fun (_, _, k) => Nat.beq (fastBucketIdx k) b) &&
    fastBucketNoCollision entries

private theorem bkt0 : rangeAll fastBktOk 0 128 = true := by decide +kernel
private theorem bkt1 : rangeAll fastBktOk 128 256 = true := by decide +kernel
private theorem bkt2 : rangeAll fastBktOk 256 384 = true := by decide +kernel
private theorem bkt3 : rangeAll fastBktOk 384 512 = true := by decide +kernel

private theorem bktAll : rangeAll fastBktOk 0 512 = true :=
  rangeAll_trans (rangeAll_trans (rangeAll_trans bkt0 bkt1) bkt2) bkt3

private theorem bucket_ok_of_lt {b : Nat} (hb : b < 512) :
    ((dagBucketEntries b).all fun (_, _, k) => Nat.beq (fastBucketIdx k) b) = true ∧
      bucketNoCollision (dagBucketEntries b) = true := by
  have h := bktAll
  unfold rangeAll at h
  have hk := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  rw [Nat.zero_add] at hk
  unfold fastBktOk at hk
  dsimp only at hk
  rw [fastBucketNoCollision_eq, fastBucketEntries_eq] at hk
  exact Bool.and_eq_true_iff.mp hk

private theorem id_covered_mem {id : Nat} (hid : id < dagSize) :
    id ∈ dagBucketIds (fastBucketIdx (fastKey (dagBytes id))) := by
  obtain ⟨hb, hm⟩ := id_in_nodeBkt hid
  have hmem : (id, (dagOp id).isAI, fastKey (dagBytes id)) ∈ dagBucketEntries (dagNodeBkt id) :=
    List.mem_map_of_mem hm
  have hall := (bucket_ok_of_lt hb).1
  have hbeq := List.all_eq_true.mp hall _ hmem
  dsimp only at hbeq
  rwa [Nat.beq_eq.mp hbeq]

private theorem bucket_collision_free {b : Nat} (hb : b < 512) :
    bucketNoCollision (dagBucketEntries b) = true :=
  (bucket_ok_of_lt hb).2

/-- Distinct nodes below `dagSize` cannot share `dagBytes` when at least one has `isAI = true`. -/
theorem dag_no_collision : ∀ id₁ < dagSize, ∀ id₂ < dagSize,
    ((dagOp id₁).isAI = true ∨ (dagOp id₂).isAI = true) →
    dagBytes id₁ = dagBytes id₂ → id₁ = id₂ := by
  intro id₁ h₁ id₂ h₂ hai hbs
  have hid₁ := id_covered_mem h₁
  have hid₂ := id_covered_mem h₂
  rw [← hbs] at hid₂
  let f := fun id : Nat => (id, (dagOp id).isAI, fastKey (dagBytes id))
  have hmem₁ : f id₁ ∈ dagBucketEntries (fastBucketIdx (fastKey (dagBytes id₁))) :=
    List.mem_map_of_mem hid₁
  have hmem₂' : f id₂ ∈ dagBucketEntries (fastBucketIdx (fastKey (dagBytes id₁))) :=
    List.mem_map_of_mem hid₂
  have hmem₂ : (id₂, (dagOp id₂).isAI, fastKey (dagBytes id₁)) ∈
      dagBucketEntries (fastBucketIdx (fastKey (dagBytes id₁))) := by
    dsimp only [f] at hmem₂'; rwa [← hbs] at hmem₂'
  have hlt : fastBucketIdx (fastKey (dagBytes id₁)) < 512 := Nat.mod_lt _ (by decide)
  have hb := bucket_collision_free hlt
  exact bucketNoCollision_sound hb hmem₁ hmem₂ hai

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
