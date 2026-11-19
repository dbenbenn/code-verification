/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData1
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData2
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData3
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData4
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData5
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData6
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData7
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData8
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData9
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData10
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData11
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData12
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData13
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData14
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData15
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData16
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData17
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData18
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData19
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData20
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData21
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData22
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData23
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData24
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData25
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData26
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData27
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData28
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData29
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData30
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData31

/-! # Concrete DAG Dispatch and Named Node IDs

Combines the 32 low-bit `BinTree` stripes into `dagTree`, defines `dagOp` and `dagBytes` node
lookup together with `certRangeOk` range checks, and names root and protocol node IDs. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData

open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
  (fastTreeNodeOk fastTreeNodeOk_sound)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)

def dagSize : Nat := 6720

def dagTree : BinTree (DagOp × HwBytes) :=
  .branch (.branch (.branch (.branch (.branch (RecvDagData0.subTree0) (RecvDagData16.subTree16)) (.branch (RecvDagData8.subTree8) (RecvDagData24.subTree24))) (.branch (.branch (RecvDagData4.subTree4) (RecvDagData20.subTree20)) (.branch (RecvDagData12.subTree12) (RecvDagData28.subTree28)))) (.branch (.branch (.branch (RecvDagData2.subTree2) (RecvDagData18.subTree18)) (.branch (RecvDagData10.subTree10) (RecvDagData26.subTree26))) (.branch (.branch (RecvDagData6.subTree6) (RecvDagData22.subTree22)) (.branch (RecvDagData14.subTree14) (RecvDagData30.subTree30))))) (.branch (.branch (.branch (.branch (RecvDagData1.subTree1) (RecvDagData17.subTree17)) (.branch (RecvDagData9.subTree9) (RecvDagData25.subTree25))) (.branch (.branch (RecvDagData5.subTree5) (RecvDagData21.subTree21)) (.branch (RecvDagData13.subTree13) (RecvDagData29.subTree29)))) (.branch (.branch (.branch (RecvDagData3.subTree3) (RecvDagData19.subTree19)) (.branch (RecvDagData11.subTree11) (RecvDagData27.subTree27))) (.branch (.branch (RecvDagData7.subTree7) (RecvDagData23.subTree23)) (.branch (RecvDagData15.subTree15) (RecvDagData31.subTree31)))))

def dagOp (id : Nat) : DagOp :=
  match btGet 13 dagTree id with
  | some p => p.1
  | none => .lit []

def dagBytes (id : Nat) : HwBytes :=
  match btGet 13 dagTree id with
  | some p => p.2
  | none => []

/-- Unboxed 54-bit polynomial hash over up to 64 prefix bytes, collision-free on `isAI` nodes. -/
def fastByteHash64 : Nat → Nat → HwBytes → Nat
  | 0, acc, _ => acc
  | _, acc, [] => acc
  | fuel + 1, acc, b :: bs =>
    fastByteHash64 fuel ((acc * 131 + b.toFin.val + 1) % 18014398509481984) bs

def fastBytesKey (bs : HwBytes) : Nat :=
  fastByteHash64 64 0 bs

def fastBucketIdx (hk : Nat) : Nat := hk % 512

def rangeAll (f : Nat → Bool) (lo hi : Nat) : Bool :=
  (List.range (hi - lo)).all fun k => f (lo + k)

theorem rangeAll_trans {f : Nat → Bool} {a b c : Nat}
    (h1 : rangeAll f a b = true) (h2 : rangeAll f b c = true)
    (hab : a ≤ b := by decide) (hbc : b ≤ c := by decide) :
    rangeAll f a c = true := by
  unfold rangeAll at h1 h2 ⊢
  have hsub : c - a = (b - a) + (c - b) := by omega
  rw [hsub, List.range_add, List.all_append, h1, Bool.true_and, List.all_map]
  apply List.all_eq_true.mpr
  intro k hk
  have heq : a + (b - a + k) = b + k := by omega
  simpa [Function.comp_def, heq] using List.all_eq_true.mp h2 k hk

def certRangeOk (lo hi : Nat) : Bool :=
  rangeAll (fastTreeNodeOk dagTree dagBytes) lo hi

theorem certRangeOk_trans {a b c : Nat}
    (h1 : certRangeOk a b = true) (h2 : certRangeOk b c = true)
    (hab : a ≤ b := by decide) (hbc : b ≤ c := by decide) :
    certRangeOk a c = true :=
  rangeAll_trans h1 h2 hab hbc

private theorem dagOp_of_btGet {id : Nat} (p : DagOp × HwBytes)
    (h : btGet 13 dagTree id = some p) : dagOp id = p.1 := by
  simp [dagOp, h]

private theorem dagBytes_of_btGet {id : Nat} (p : DagOp × HwBytes)
    (h : btGet 13 dagTree id = some p) : dagBytes id = p.2 := by
  simp [dagBytes, h]

theorem dagNodeOk_of_certRangeOk {lo hi : Nat} (h : certRangeOk lo hi = true)
    {i : Nat} (hlo : lo ≤ i) (hhi : i < hi) :
    dagNodeOk dagOp dagBytes i = true := by
  unfold certRangeOk rangeAll at h
  have hmem : i - lo ∈ List.range (hi - lo) := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (i - lo) hmem
  have heq : lo + (i - lo) = i := by omega
  rw [heq] at hk
  exact fastTreeNodeOk_sound dagOp_of_btGet dagBytes_of_btGet hk

def wmkInfo1Id : Nat := 13
def wmkInfo2Id : Nat := 14
def wmkInfo3Id : Nat := 15
def honestSaltIds : List Nat := [8, 100, 120, 165, 258, 414, 649, 979, 1420, 1988, 2699, 3569, 4614]
end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
