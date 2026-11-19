/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem -- proof-setup: allow-public-import

/-!
# Multi-Lane Spatial Slot and Counter Predicates (`SampleNttLoop.LaneMem`)

Separating-conjunction assertions (`MultiLaneSlots`, `MultiLaneSampled`), load/store framing
lemmas, and multi-lane slot invariants (`MultiLaneRawInv`, `MultiLaneClampedInv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  RejSlotClampedInv RejSlotRawInv clampSampled packHalfwordsLE rejSlotClampedInv_init)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkMem (RejBufReadable)

/-- Generic separating conjunction of `cnt` indexed lane assertions starting at `start`. -/
@[expose] def MultiLaneSepFrom {α : Type} (cell : Nat → α → SepProp) (start : Nat) :
    Nat → (Nat → α) → SepProp
  | 0, _ => emp
  | c + 1, vals => cell start (vals start) ∗ MultiLaneSepFrom cell (start + 1) c vals

theorem MultiLaneSepFrom.congr {α : Type} {cell : Nat → α → SepProp} {start cnt : Nat}
    {v1 v2 : Nat → α} (h : ∀ i, start ≤ i → i < start + cnt → v1 i = v2 i) :
    MultiLaneSepFrom cell start cnt v1 = MultiLaneSepFrom cell start cnt v2 := by
  induction cnt generalizing start with
  | zero => rfl
  | succ c ih =>
    simp only [MultiLaneSepFrom]
    rw [h start (Nat.le_refl _) (by omega), ih (start := start + 1) fun i _ _ => h i (by omega) (by omega)]

theorem MultiLaneSepFrom.focus {α : Type} {cell : Nat → α → SepProp} {start cnt k : Nat}
    (hlo : start ≤ k) (hhi : k < start + cnt) (vals : Nat → α) :
    ∃ Frame : SepProp,
      MultiLaneSepFrom cell start cnt vals = cell k (vals k) ∗ Frame ∧
      ∀ v' : α, cell k v' ∗ Frame =
        MultiLaneSepFrom cell start cnt (fun i => if i = k then v' else vals i) := by
  induction cnt generalizing start with
  | zero => exact absurd hhi (by omega)
  | succ c ih =>
    by_cases hk : k = start
    · subst hk
      refine ⟨MultiLaneSepFrom cell (k + 1) c vals, rfl, fun v' => ?_⟩
      simp only [MultiLaneSepFrom, ↓reduceIte]
      congr 1; exact MultiLaneSepFrom.congr fun i hi1 _ => by simp [show i ≠ k by omega]
    · rcases ih (start := start + 1) (by omega) (by omega) with ⟨F, hF, hUpd⟩
      refine ⟨cell start (vals start) ∗ F, ?_, fun v' => ?_⟩
      · simp only [MultiLaneSepFrom, hF]
        rw [← sepConj_assoc, sepConj_comm (cell start (vals start)), sepConj_assoc]
      · rw [← sepConj_assoc, sepConj_comm (cell k v'), sepConj_assoc, hUpd v']
        simp [MultiLaneSepFrom, show start ≠ k by omega]

/-- Separating conjunction of `N` `272`-halfword polynomial scratch slots (`i = 0 .. N - 1`). -/
@[expose] def MultiLaneSlots (slotsBase : BitVec 64) (slotStride N : Nat)
    (hws : Nat → List (BitVec 16)) : SepProp :=
  MultiLaneSepFrom (fun i hw => (slotsBase + BitVec.ofNat 64 (slotStride * i)) ↦ₛ packHalfwordsLE hw) 0 N hws

theorem MultiLaneSlots.congr {slotsBase : BitVec 64} {slotStride N : Nat}
    {h1 h2 : Nat → List (BitVec 16)} (h : ∀ i, i < N → h1 i = h2 i) :
    MultiLaneSlots slotsBase slotStride N h1 = MultiLaneSlots slotsBase slotStride N h2 :=
  MultiLaneSepFrom.congr fun i _ hi => h i (by omega)

theorem MultiLaneSlots.focus {slotsBase : BitVec 64} {slotStride N k : Nat} (hk : k < N)
    (hws : Nat → List (BitVec 16)) :
    ∃ Frame : SepProp,
      MultiLaneSlots slotsBase slotStride N hws =
        ((slotsBase + BitVec.ofNat 64 (slotStride * k)) ↦ₛ packHalfwordsLE (hws k)) ∗ Frame ∧
      ∀ hws' : List (BitVec 16),
        ((slotsBase + BitVec.ofNat 64 (slotStride * k)) ↦ₛ packHalfwordsLE hws') ∗ Frame =
          MultiLaneSlots slotsBase slotStride N (fun i => if i = k then hws' else hws i) :=
  MultiLaneSepFrom.focus (Nat.zero_le k) (by omega) hws

/-- Separating conjunction of `N` 64-bit `sampled` counters (`i = 0 .. N - 1`). -/
@[expose] def MultiLaneSampled (sampBase : BitVec 64) (N : Nat) (sampled : Nat → Nat) : SepProp :=
  MultiLaneSepFrom (fun i s => (sampBase + BitVec.ofNat 64 (8 * i)) ↦₆₄ BitVec.ofNat 64 s) 0 N sampled

theorem MultiLaneSampled.congr {sampBase : BitVec 64} {N : Nat} {s1 s2 : Nat → Nat}
    (h : ∀ i, i < N → s1 i = s2 i) :
    MultiLaneSampled sampBase N s1 = MultiLaneSampled sampBase N s2 :=
  MultiLaneSepFrom.congr fun i _ hi => h i (by omega)

theorem MultiLaneSampled.focus {sampBase : BitVec 64} {N k : Nat} (hk : k < N)
    (sampled : Nat → Nat) :
    ∃ Frame : SepProp,
      MultiLaneSampled sampBase N sampled =
        ((sampBase + BitVec.ofNat 64 (8 * k)) ↦₆₄ BitVec.ofNat 64 (sampled k)) ∗ Frame ∧
      ∀ s' : Nat,
        ((sampBase + BitVec.ofNat 64 (8 * k)) ↦₆₄ BitVec.ofNat 64 s') ∗ Frame =
          MultiLaneSampled sampBase N (fun i => if i = k then s' else sampled i) :=
  MultiLaneSepFrom.focus (Nat.zero_le k) (by omega) sampled

theorem sepLoad64_multiLaneSampled {ea sampBase : BitVec 64} {N k : Nat} {sampled : Nat → Nat}
    {P F : SepProp} (hk : k < N) (hP : P = MultiLaneSampled sampBase N sampled ∗ F)
    (hea : sampBase + BitVec.ofNat 64 (8 * k) = ea) :
    SepLoad64 ea P (BitVec.ofNat 64 (sampled k)) := by
  rcases MultiLaneSampled.focus hk sampled with ⟨Fm, hFm, _⟩
  exact SepLoad64.of_eq_addr (by rw [hP, hFm, sepConj_assoc]) hea

theorem sepStore64_multiLaneSampled {ea sampBase : BitVec 64} {N k s' : Nat} {sampled : Nat → Nat}
    {P P' F : SepProp} (hk : k < N) (hP : P = MultiLaneSampled sampBase N sampled ∗ F)
    (hP' : P' = MultiLaneSampled sampBase N (fun i => if i = k then s' else sampled i) ∗ F)
    (hea : sampBase + BitVec.ofNat 64 (8 * k) = ea) :
    SepStore64 ea (BitVec.ofNat 64 s') P P' := by
  rcases MultiLaneSampled.focus hk sampled with ⟨Fm, hFm, hUpd⟩
  exact SepStore64.of_eq_addr (by rw [hP, hFm, sepConj_assoc])
    (by rw [hP', ← hUpd s', sepConj_assoc]) hea

theorem rejBufReadable_of_eq_slice {base sqBase : BitVec 64} {full buf : List (BitVec 8)}
    {off nChunks : Nat} {Pbuf F : SepProp} (hP : Pbuf = (base ↦ₛ full) ∗ F)
    (hbase : base + BitVec.ofNat 64 off = sqBase) (hlen : off + 24 * nChunks ≤ full.length)
    (hbuf : (full.drop off).take (24 * nChunks) = buf.take (24 * nChunks)) :
    RejBufReadable sqBase buf nChunks Pbuf := fun j hj => by
  have hget : full.getD (off + j) 0#8 = buf.getD j 0#8 := by
    have hc := congrArg (fun l => l.getD j 0#8) hbuf
    simpa [List.getD_eq_getElem?_getD, List.getElem?_drop, hj] using hc
  exact (SepLoad8.of_pointsToBytes hP (off := off + j) (by omega)
    (by subst hbase; rw [BitVec.add_assoc, ← BitVec.ofNat_add])).congr_val hget

/-- Unclamped `N`-lane slot invariant (`∀ i < N, RejSlotRawInv (cands i) (sampled i) (hws i)`). -/
@[expose] def MultiLaneRawInv (N : Nat) (cands : Nat → List Nat) (sampled : Nat → Nat)
    (hws : Nat → List (BitVec 16)) : Prop :=
  ∀ i, i < N → RejSlotRawInv (cands i) (sampled i) (hws i)

/-- Clamped `N`-lane slot invariant (`∀ i < N, RejSlotClampedInv (cands i) (sampled i) (hws i)`). -/
@[expose] def MultiLaneClampedInv (N : Nat) (cands : Nat → List Nat) (sampled : Nat → Nat)
    (hws : Nat → List (BitVec 16)) : Prop :=
  ∀ i, i < N → RejSlotClampedInv (cands i) (sampled i) (hws i)

theorem MultiLaneClampedInv.toRaw {N : Nat} {cands : Nat → List Nat} {sampled : Nat → Nat}
    {hws : Nat → List (BitVec 16)} (h : MultiLaneClampedInv N cands sampled hws) :
    MultiLaneRawInv N cands sampled hws := fun i hi => (h i hi).1

theorem MultiLaneRawInv.clamp {N : Nat} {cands : Nat → List Nat} {sampled : Nat → Nat}
    {hws : Nat → List (BitVec 16)} (h : MultiLaneRawInv N cands sampled hws) :
    MultiLaneClampedInv N cands (fun i => clampSampled (sampled i)) hws :=
  fun i hi => (h i hi).clamp

theorem MultiLaneClampedInv.init_zero (N : Nat) :
    MultiLaneClampedInv N (fun _ => []) (fun _ => 0) (fun _ => List.replicate 272 0#16) :=
  fun _ _ => rejSlotClampedInv_init

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem
