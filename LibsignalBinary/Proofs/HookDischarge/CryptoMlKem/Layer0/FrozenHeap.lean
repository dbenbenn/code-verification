/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import ProofLib.SepLogic.Model

/-!
# Frozen-Heap RW-to-RO Recovery

Defines `OnlyRW`, `IsROPair`, and `rw_to_ro_preserve` to freeze RW spatial ownership inside
a caller frame `R'` across read-only callees that preserve `NonSyscallPreserved`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRO
  Keccak2SlicesRW
)

private def toROHeap (h : Heap) : Heap where
  phys a :=
    match h.phys a with
    | some (.rw b) => some (.ro b)
    | other => other
  auth := h.auth
  frag := h.frag
  mapped := h.mapped

/-- Assertion whose heaps own exclusively physical `.rw` byte cells (with empty ghost/mapped slots). -/
def OnlyRW (P : SepProp) : Prop :=
  ∀ h : Heap, P.holds h →
    (∀ a c, h.phys a = some c → ∃ b, c = .rw b) ∧
    (∀ γ k, h.auth γ k = none) ∧
    (∀ γ k, h.frag γ k = none) ∧
    (∀ a, h.mapped a = false)

/-- Read-write assertion `P_rw` paired with its read-only counterpart `P_ro` via `toROHeap`. -/
def IsROPair (P_rw P_ro : SepProp) : Prop :=
  OnlyRW P_rw ∧ ∀ h : Heap, P_rw.holds h → P_ro.holds (toROHeap h)

theorem onlyRW_emp : OnlyRW emp := by
  intro h hh
  rw [SepProp.holds_emp_iff] at hh
  subst hh
  unfold Heap.empty
  exact ⟨fun _ _ hc => (by cases hc), fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem onlyRW_of_isBlock {P : SepProp} {b : BitVec 64} {n : Nat} {Φ : Memory → Prop}
    (hb : IsBlock P b n Φ) : OnlyRW P := by
  intro h hp
  obtain ⟨m, -, rfl⟩ := (hb.iff h).mp hp
  unfold regionHeap
  refine ⟨fun a c hc => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  dsimp only at hc
  split at hc
  · injection hc with hc'; exact ⟨m.read8 a, hc'.symm⟩
  · cases hc

theorem onlyRW_sepConj {P Q : SepProp} (hP : OnlyRW P) (hQ : OnlyRW Q) : OnlyRW (P ∗ Q) := by
  intro h hh
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨c1, a1, f1, m1⟩ := hP h1 hp1
  obtain ⟨c2, a2, f2, m2⟩ := hQ h2 hp2
  unfold Heap.union
  refine ⟨fun a c hc => ?_, fun γ k => by dsimp only; rw [a1, a2],
    fun γ k => by dsimp only; rw [f1, f2], fun a => by dsimp only; rw [m1, m2]; rfl⟩
  dsimp only at hc
  cases hh1 : h1.phys a with
  | some x => rw [hh1] at hc; injection hc with hc'; subst hc'; exact c1 a x hh1
  | none => rw [hh1] at hc; exact c2 a c hc

private theorem toROHeap_regionHeap (b : BitVec 64) (n : Nat) (m : Memory) :
    toROHeap (regionHeap b n m) = regionHeapRO b n m := by
  unfold toROHeap regionHeap regionHeapRO
  refine Heap.ext (funext fun a => ?_) rfl rfl rfl
  dsimp only
  by_cases ha : InRegion b n a <;> simp [ha]

theorem isROPair_pointsTo64 (a v : BitVec 64) : IsROPair (a ↦₆₄ v) (a ↦₆₄ᵣ v) := by
  refine ⟨onlyRW_of_isBlock (IsBlock.pointsTo64 a v), fun h hp => ?_⟩
  obtain ⟨m, hm, rfl⟩ := ((IsBlock.pointsTo64 a v).iff h).mp hp
  rw [toROHeap_regionHeap]
  exact ((IsBlockRO.pointsTo64RO a v).iff _).mpr ⟨m, hm, rfl⟩

theorem isROPair_pointsToBytes (a : BitVec 64) (bs : List (BitVec 8)) :
    IsROPair (a ↦ₛ bs) (a ↦ᵣ bs) := by
  refine ⟨onlyRW_of_isBlock (IsBlock.pointsToBytes a bs), fun h hp => ?_⟩
  obtain ⟨m, ⟨hlen, hm⟩, rfl⟩ := ((IsBlock.pointsToBytes a bs).iff h).mp hp
  rw [toROHeap_regionHeap]
  exact ((IsBlockRO.pointsToBytesRO a bs hlen).iff _).mpr ⟨m, hm, rfl⟩

theorem isROPair_sepConj {P₁ Q₁ P₂ Q₂ : SepProp}
    (h1 : IsROPair P₁ Q₁) (h2 : IsROPair P₂ Q₂) :
    IsROPair (P₁ ∗ P₂) (Q₁ ∗ Q₂) := by
  refine ⟨onlyRW_sepConj h1.1 h2.1, fun h hp => ?_⟩
  obtain ⟨hp1, hp2, hd, rfl, hh1, hh2⟩ := SepProp.holds_sepConj_iff.mp hp
  obtain ⟨c1, a1, f1, m1⟩ := h1.1 hp1 hh1
  obtain ⟨c2, a2, f2, m2⟩ := h2.1 hp2 hh2
  unfold Heap.Disjoint at hd
  have hd_ro : (toROHeap hp1).Disjoint (toROHeap hp2) := by
    unfold Heap.Disjoint toROHeap
    refine ⟨fun x => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h' => ?_, fun x => ?_⟩
    · dsimp only
      rcases hd.1 x with hx1 | hx2 | ⟨b, hx1, _⟩
      · rw [hx1]; exact Or.inl rfl
      · rw [hx2]; exact Or.inr (Or.inl rfl)
      · obtain ⟨_, hc⟩ := c1 x (.ro b) hx1; cases hc
    · dsimp only; rw [a1]; exact Or.inl rfl
    · dsimp only; rw [f1]; exact Or.inl rfl
    · dsimp only at h'
      rcases h' with ⟨ha, _⟩ | ⟨_, hf⟩
      · rw [a1] at ha; cases ha
      · rw [f1] at hf; cases hf
    · dsimp only; rw [m1]; exact Or.inl rfl
  have hunion : toROHeap (hp1.union hp2) = (toROHeap hp1).union (toROHeap hp2) := by
    unfold toROHeap Heap.union
    refine Heap.ext (funext fun x => ?_) rfl rfl rfl
    dsimp only
    cases hx : hp1.phys x with
    | none => rfl
    | some c => obtain ⟨b, rfl⟩ := c1 x c hx; rfl
  rw [hunion]
  exact SepProp.holds_sepConj_iff.mpr ⟨toROHeap hp1, toROHeap hp2, hd_ro, rfl,
    h1.2 hp1 hh1, h2.2 hp2 hh2⟩

theorem isROPair_keccak2Slices (slicesPtr ptr0 ptr1 : BitVec 64) (len0 len1 : Nat) :
    IsROPair (Keccak2SlicesRW slicesPtr ptr0 ptr1 len0 len1)
      (Keccak2SlicesRO slicesPtr ptr0 ptr1 len0 len1) :=
  isROPair_sepConj (isROPair_pointsTo64 _ _)
    (isROPair_sepConj (isROPair_pointsTo64 _ _)
      (isROPair_sepConj (isROPair_pointsTo64 _ _) (isROPair_pointsTo64 _ _)))

/-- Freeze an RW assertion `P_rw` as `toROHeap h_P` inside a custom caller frame `R'` across any
    callee that reads `P_ro`, transforms `W0` to `Wf` (`OnlyRW Wf`), and preserves `NonSyscallPreserved`. -/
theorem rw_to_ro_preserve {P_rw P_ro W0 Wf R : SepProp} {s0 : State}
    (hpair : IsROPair P_rw P_ro)
    (hWf : OnlyRW Wf)
    (hpre : s0.mem ⊨ P_rw ∗ (W0 ∗ R)) :
    ∃ R' : SepProp,
      (s0.mem ⊨ P_ro ∗ (W0 ∗ R')) ∧
      ∀ {sf : State},
        ProofLib.NonSyscallPreserved s0 sf →
        (sf.mem ⊨ Wf ∗ R') →
        (sf.mem ⊨ P_rw ∗ (Wf ∗ R)) := by
  obtain ⟨h_all, hh_all, hm_all⟩ := SepProp.satisfies_iff.mp hpre
  obtain ⟨h_P, h_WR, hd_P_WR, rfl, hp_P, hh_WR⟩ := SepProp.holds_sepConj_iff.mp hh_all
  obtain ⟨h_W0, h_R, hd_W0_R, rfl, hp_W0, hp_R⟩ := SepProp.holds_sepConj_iff.mp hh_WR
  obtain ⟨cP, aP, fP, mP⟩ := hpair.1 h_P hp_P
  let h_Pro := toROHeap h_P
  have hp_Pro : P_ro.holds h_Pro := hpair.2 h_P hp_P
  let R' : SepProp := ⟨fun h => h = h_Pro.union h_R⟩
  have hm_P_s0 : h_P.Matches s0.mem := Heap.Matches.of_union_left hm_all
  have hm_WR_s0 : (h_W0.union h_R).Matches s0.mem :=
    Heap.Matches.of_union_right hd_P_WR hm_all
  have hm_W0_s0 : h_W0.Matches s0.mem := Heap.Matches.of_union_left hm_WR_s0
  have hm_R_s0 : h_R.Matches s0.mem := Heap.Matches.of_union_right hd_W0_R hm_WR_s0
  have hphys_none_WR : ∀ x b, h_P.phys x = some (.rw b) →
      h_W0.phys x = none ∧ h_R.phys x = none := by
    intro x b hx
    unfold Heap.Disjoint Heap.union at hd_P_WR
    rcases hd_P_WR.1 x with h1 | h2 | ⟨_, h1, _⟩
    · rw [hx] at h1; cases h1
    · dsimp only at h2
      cases hw : h_W0.phys x with
      | none => rw [hw] at h2; exact ⟨rfl, h2⟩
      | some _ => rw [hw] at h2; cases h2
    · rw [hx] at h1; cases h1
  have hd_Pro_R : h_Pro.Disjoint h_R := by
    unfold Heap.Disjoint
    refine ⟨fun x => ?_, fun γ k => Or.inl (aP γ k), fun γ k => Or.inl (fP γ k),
      fun γ k _ _ h' => ?_, fun x => Or.inl (mP x)⟩
    · cases hx : h_P.phys x with
      | none => exact Or.inl (by simp [h_Pro, toROHeap, hx])
      | some c =>
        obtain ⟨b, rfl⟩ := cP x c hx
        exact Or.inr (Or.inl (hphys_none_WR x b hx).2)
    · rcases h' with ⟨ha, _⟩ | ⟨_, hf⟩
      · change h_P.auth γ k = _ at ha; rw [aP] at ha; cases ha
      · change h_P.frag γ k = _ at hf; rw [fP] at hf; cases hf
  have hd_W0_R' : h_W0.Disjoint (h_Pro.union h_R) := by
    unfold Heap.Disjoint at hd_W0_R ⊢
    refine ⟨fun x => ?_,
      fun γ k => by unfold Heap.union; dsimp only [h_Pro, toROHeap]; rw [aP]; exact hd_W0_R.2.1 γ k,
      fun γ k => by unfold Heap.union; dsimp only [h_Pro, toROHeap]; rw [fP]; exact hd_W0_R.2.2.1 γ k,
      fun γ k oa v h' => ?_,
      fun x => by unfold Heap.union; dsimp only [h_Pro, toROHeap]; rw [mP, Bool.false_or]; exact hd_W0_R.2.2.2.2 x⟩
    · unfold Heap.union; dsimp only
      cases hx : h_P.phys x with
      | none =>
        have hnone : h_Pro.phys x = none := by simp [h_Pro, toROHeap, hx]
        rw [hnone]; exact hd_W0_R.1 x
      | some c =>
        obtain ⟨b, rfl⟩ := cP x c hx
        exact Or.inl (hphys_none_WR x b hx).1
    · unfold Heap.union at h'
      dsimp only [h_Pro, toROHeap] at h'
      rw [aP, fP] at h'
      exact hd_W0_R.2.2.2.1 γ k oa v h'
  have hd_Pro_W0R' : h_Pro.Disjoint (h_W0.union (h_Pro.union h_R)) := by
    unfold Heap.Disjoint
    refine ⟨fun x => ?_, fun γ k => Or.inl (aP γ k), fun γ k => Or.inl (fP γ k),
      fun γ k _ _ h' => ?_, fun x => Or.inl (mP x)⟩
    · cases hx : h_P.phys x with
      | none => exact Or.inl (by simp [h_Pro, toROHeap, hx])
      | some c =>
        obtain ⟨b, rfl⟩ := cP x c hx
        have hw0 := (hphys_none_WR x b hx).1
        have hro_x : h_Pro.phys x = some (.ro b) := by simp [h_Pro, toROHeap, hx]
        refine Or.inr (Or.inr ⟨b, hro_x, ?_⟩)
        unfold Heap.union; dsimp only; rw [hw0, hro_x]
    · rcases h' with ⟨ha, _⟩ | ⟨_, hf⟩
      · change h_P.auth γ k = _ at ha; rw [aP] at ha; cases ha
      · change h_P.frag γ k = _ at hf; rw [fP] at hf; cases hf
  have hm_Pro_s0 : h_Pro.Matches s0.mem := by
    unfold Heap.Matches at hm_P_s0 ⊢
    refine ⟨fun x c hc => ?_,
      ⟨0, fun γ _ k => ⟨aP γ k, fP γ k⟩⟩,
      fun x hm => by change h_P.mapped x = true at hm; rw [mP] at hm; cases hm⟩
    dsimp only [h_Pro, toROHeap] at hc
    cases hx : h_P.phys x with
    | none => rw [hx] at hc; cases hc
    | some c0 =>
      obtain ⟨b, rfl⟩ := cP x c0 hx
      rw [hx] at hc; injection hc with hc'; subst hc'
      obtain ⟨hr, hp_rw, hlf⟩ := hm_P_s0.1 x (.rw b) hx
      exact ⟨hr, by rw [hp_rw]; rfl, hlf⟩
  refine ⟨R', ?_, ?_⟩
  · refine SepProp.satisfies_iff.mpr ⟨h_Pro.union (h_W0.union (h_Pro.union h_R)),
      SepProp.holds_sepConj_iff.mpr ⟨h_Pro, h_W0.union (h_Pro.union h_R), hd_Pro_W0R', rfl, hp_Pro,
        SepProp.holds_sepConj_iff.mpr ⟨h_W0, h_Pro.union h_R, hd_W0_R', rfl, hp_W0, rfl⟩⟩,
      Heap.Matches.union hm_Pro_s0
        (Heap.Matches.union hm_W0_s0 (Heap.Matches.union hm_Pro_s0 hm_R_s0))⟩
  · intro sf hnsp hpost_sf
    obtain ⟨h_out, hh_out, hm_out⟩ := SepProp.satisfies_iff.mp hpost_sf
    obtain ⟨h_Wf, h_R', hd_Wf_R', rfl, hp_Wf, hh_R'⟩ := SepProp.holds_sepConj_iff.mp hh_out
    change h_R' = h_Pro.union h_R at hh_R'
    subst hh_R'
    obtain ⟨cWf, _, _, _⟩ := hWf h_Wf hp_Wf
    have hm_Wf_sf : h_Wf.Matches sf.mem := Heap.Matches.of_union_left hm_out
    have hm_R'_sf : (h_Pro.union h_R).Matches sf.mem :=
      Heap.Matches.of_union_right hd_Wf_R' hm_out
    have hm_Pro_sf : h_Pro.Matches sf.mem := Heap.Matches.of_union_left hm_R'_sf
    have hm_R_sf : h_R.Matches sf.mem := Heap.Matches.of_union_right hd_Pro_R hm_R'_sf
    have hm_P_sf : h_P.Matches sf.mem := by
      unfold Heap.Matches at hm_P_s0 hm_Pro_sf ⊢
      refine ⟨fun x c hx => ?_, hm_P_s0.2.1,
        fun x hm => by rw [mP] at hm; cases hm⟩
      obtain ⟨b, rfl⟩ := cP x c hx
      have hro_x : h_Pro.phys x = some (.ro b) := by simp [h_Pro, toROHeap, hx]
      obtain ⟨hr_sf, _, _⟩ := hm_Pro_sf.1 x (.ro b) hro_x
      obtain ⟨_, hp_s0, hlf_s0⟩ := hm_P_s0.1 x (.rw b) hx
      exact ⟨hr_sf, (congrFun hnsp.2.1 x).trans hp_s0, hnsp.2.2.2.2.2.1.2 x hlf_s0⟩
    have hd_Wf_R : h_Wf.Disjoint h_R := by
      unfold Heap.Disjoint at hd_Wf_R' ⊢
      refine ⟨fun x => ?_,
        fun γ k => by
          have h := hd_Wf_R'.2.1 γ k
          unfold Heap.union at h; dsimp only [h_Pro, toROHeap] at h; rwa [aP] at h,
        fun γ k => by
          have h := hd_Wf_R'.2.2.1 γ k
          unfold Heap.union at h; dsimp only [h_Pro, toROHeap] at h; rwa [fP] at h,
        fun γ k oa v h' => by
          apply hd_Wf_R'.2.2.2.1 γ k oa v
          unfold Heap.union; dsimp only [h_Pro, toROHeap]; rwa [aP, fP],
        fun x => by
          have h := hd_Wf_R'.2.2.2.2 x
          unfold Heap.union at h; dsimp only [h_Pro, toROHeap] at h
          rwa [mP, Bool.false_or] at h⟩
      rcases hd_Wf_R'.1 x with h1 | h2 | ⟨b, h1, _⟩
      · exact Or.inl h1
      · unfold Heap.union at h2; dsimp only at h2
        cases hpro : h_Pro.phys x with
        | none => rw [hpro] at h2; exact Or.inr (Or.inl h2)
        | some _ => rw [hpro] at h2; cases h2
      · obtain ⟨_, hc⟩ := cWf x (.ro b) h1; cases hc
    have hd_P_WfR : h_P.Disjoint (h_Wf.union h_R) := by
      unfold Heap.Disjoint
      refine ⟨fun x => ?_, fun γ k => Or.inl (aP γ k), fun γ k => Or.inl (fP γ k),
        fun γ k _ _ h' => ?_, fun x => Or.inl (mP x)⟩
      · cases hx : h_P.phys x with
        | none => exact Or.inl rfl
        | some c =>
          obtain ⟨b, rfl⟩ := cP x c hx
          have hro_x : (h_Pro.union h_R).phys x = some (.ro b) := by
            unfold Heap.union; dsimp only [h_Pro, toROHeap]; simp [hx]
          have hwf_none : h_Wf.phys x = none := by
            unfold Heap.Disjoint at hd_Wf_R'
            rcases hd_Wf_R'.1 x with h1 | h2 | ⟨b', h1, _⟩
            · exact h1
            · rw [hro_x] at h2; cases h2
            · obtain ⟨_, hc⟩ := cWf x (.ro b') h1; cases hc
          have hr_none := (hphys_none_WR x b hx).2
          exact Or.inr (Or.inl (by unfold Heap.union; dsimp only; rw [hwf_none, hr_none]))
      · rcases h' with ⟨ha, _⟩ | ⟨_, hf⟩
        · rw [aP] at ha; cases ha
        · rw [fP] at hf; cases hf
    exact SepProp.satisfies_iff.mpr ⟨h_P.union (h_Wf.union h_R),
      SepProp.holds_sepConj_iff.mpr ⟨h_P, h_Wf.union h_R, hd_P_WfR, rfl, hp_P,
        SepProp.holds_sepConj_iff.mpr ⟨h_Wf, h_R, hd_Wf_R, rfl, hp_Wf, hp_R⟩⟩,
      Heap.Matches.union hm_P_sf (Heap.Matches.union hm_Wf_sf hm_R_sf)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap
