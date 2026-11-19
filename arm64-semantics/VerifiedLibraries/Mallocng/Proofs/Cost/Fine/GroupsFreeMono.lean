/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Defs

/-!
# Fine Group-List Monotonicity (`VerifiedLibraries.Mallocng.Proofs.Cost.Fine.GroupsFreeMono`)

- **Layer & Role**: `Role::Proof` (untrusted). Pure group-list relation preserved across all
  non-allocating group transitions (`nontrivial_free` queue/mask/retire steps and intra-`alloc_slot`
  rotate/dequeue/activate/bump/fast-pop steps).
- **Key Exports**: `SlotUserSub`, `GroupsFreeMono` (`refl`, `trans`, `of_eq`, `map_witness`,
  `map_eq`, `map_ite`), `SlotUserSub.set_nonUser`, `SlotUserSub.ofFn_nonUser`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-- Every `.liveUser p req eff` slot of `ss'` was already `.liveUser p req eff` at the same index
    in `ss` (so non-user transitions `.liveUser ↦ .claimed`, `.claimed ↦ .freeInactive`,
    `.freeInactive ↦ .freeAvail`, `.freeAvail ↦ .claimed`, `.liveNested ↦ .claimed` all satisfy
    `SlotUserSub`). -/
def SlotUserSub (ss' ss : List SlotState) : Prop :=
  ss'.length = ss.length ∧
  ∀ (i : Nat) (hi' : i < ss'.length) (hi : i < ss.length) (p : BitVec 64) (req eff : Nat),
    ss'[i]'hi' = .liveUser p req eff → ss[i]'hi = .liveUser p req eff

theorem SlotUserSub.refl (ss : List SlotState) : SlotUserSub ss ss :=
  ⟨rfl, fun _ _ _ _ _ _ h => h⟩

theorem SlotUserSub.trans {s1 s2 s3 : List SlotState}
    (h12 : SlotUserSub s2 s1) (h23 : SlotUserSub s3 s2) : SlotUserSub s3 s1 :=
  ⟨h23.1.trans h12.1, fun i hi3 hi1 p req eff h => by
    have hi2 : i < s2.length := h12.1.symm ▸ hi1
    exact h12.2 i hi2 hi1 p req eff (h23.2 i hi3 hi2 p req eff h)⟩

theorem SlotUserSub.of_eq {ss' ss : List SlotState} (h : ss' = ss) : SlotUserSub ss' ss :=
  h ▸ SlotUserSub.refl ss

/-- Setting any slot to a non-`.liveUser` state preserves `SlotUserSub`. -/
theorem SlotUserSub.set_nonUser (ss : List SlotState) (idx : Nat) (sNew : SlotState)
    (hNonUser : ∀ p req eff, sNew ≠ .liveUser p req eff) :
    SlotUserSub (ss.set idx sNew) ss := by
  refine ⟨List.length_set, fun i hi' hi p req eff hEq => ?_⟩
  by_cases hIdx : idx = i
  · subst hIdx
    rw [List.getElem_set_self] at hEq
    exact absurd hEq (hNonUser p req eff)
  · rwa [List.getElem_set_ne hIdx] at hEq

/-- Pointwise `List.ofFn` update that never introduces `.liveUser` preserves `SlotUserSub`. -/
theorem SlotUserSub.ofFn_keepUser (ss : List SlotState) (f : Fin ss.length → SlotState)
    (hf : ∀ (i : Fin ss.length) (p : BitVec 64) (req eff : Nat),
      f i = .liveUser p req eff → ss[i.1]'i.2 = .liveUser p req eff) :
    SlotUserSub (List.ofFn f) ss := by
  refine ⟨List.length_ofFn, fun i hi' hi p req eff hEq => ?_⟩
  rw [List.getElem_ofFn] at hEq
  exact hf ⟨i, hi⟩ p req eff hEq

/-- Every group `g' ∈ gs'` originates from a group `g ∈ gs` with the same `metaPtr`, `sc`, `cnt`,
    `maplen`, and `parentMeta`, and with `SlotUserSub g'.slots g.slots`. Under `(gs.map metaPtr).Nodup`
    and `(gs'.map metaPtr).Nodup`, this embeds `gs'` injectively into `gs`, preserving `GroupFineGeom`,
    `stClassBound`, and all live-user slot sums. -/
def GroupsFreeMono (gs gs' : List GroupDesc) : Prop :=
  ∀ g' ∈ gs', ∃ g ∈ gs,
    g'.metaPtr = g.metaPtr ∧
    g'.sc = g.sc ∧
    g'.cnt = g.cnt ∧
    g'.maplen = g.maplen ∧
    g'.parentMeta = g.parentMeta ∧
    SlotUserSub g'.slots g.slots

theorem GroupsFreeMono.refl (gs : List GroupDesc) : GroupsFreeMono gs gs :=
  fun g hg => ⟨g, hg, rfl, rfl, rfl, rfl, rfl, SlotUserSub.refl g.slots⟩

theorem GroupsFreeMono.of_eq {gs gs' : List GroupDesc} (h : gs' = gs) : GroupsFreeMono gs gs' :=
  h ▸ GroupsFreeMono.refl gs

theorem GroupsFreeMono.trans {gs1 gs2 gs3 : List GroupDesc}
    (h12 : GroupsFreeMono gs1 gs2) (h23 : GroupsFreeMono gs2 gs3) :
    GroupsFreeMono gs1 gs3 := by
  intro g3 hg3
  obtain ⟨g2, hg2, hm23, hsc23, hcnt23, hml23, hpar23, hsl23⟩ := h23 g3 hg3
  obtain ⟨g1, hg1, hm12, hsc12, hcnt12, hml12, hpar12, hsl12⟩ := h12 g2 hg2
  exact ⟨g1, hg1, hm23.trans hm12, hsc23.trans hsc12, hcnt23.trans hcnt12,
    hml23.trans hml12, hpar23.trans hpar12, hsl12.trans hsl23⟩

theorem GroupsFreeMono.map_witness {gs : List GroupDesc} (f : GroupDesc → GroupDesc)
    (hf : ∀ h ∈ gs, ∃ h0 ∈ gs,
      (f h).metaPtr = h0.metaPtr ∧ (f h).sc = h0.sc ∧ (f h).cnt = h0.cnt ∧
      (f h).maplen = h0.maplen ∧ (f h).parentMeta = h0.parentMeta ∧
      SlotUserSub (f h).slots h0.slots) :
    GroupsFreeMono gs (gs.map f) := by
  intro g' hg'
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg'
  exact hf h hh

theorem GroupsFreeMono.map_eq {gs : List GroupDesc} (f : GroupDesc → GroupDesc)
    (hf : ∀ h ∈ gs,
      (f h).metaPtr = h.metaPtr ∧ (f h).sc = h.sc ∧ (f h).cnt = h.cnt ∧
      (f h).maplen = h.maplen ∧ (f h).parentMeta = h.parentMeta ∧
      SlotUserSub (f h).slots h.slots) :
    GroupsFreeMono gs (gs.map f) :=
  GroupsFreeMono.map_witness f fun h hh => ⟨h, hh, hf h hh⟩

theorem GroupsFreeMono.map_ite {gs : List GroupDesc} {g g1 : GroupDesc} (hg : g ∈ gs) (m : BitVec 64)
    (hMeta : g1.metaPtr = g.metaPtr) (hSc : g1.sc = g.sc) (hCnt : g1.cnt = g.cnt)
    (hMl : g1.maplen = g.maplen) (hPar : g1.parentMeta = g.parentMeta)
    (hSl : SlotUserSub g1.slots g.slots) :
    GroupsFreeMono gs (gs.map fun h => if h.metaPtr == m then g1 else h) := by
  refine GroupsFreeMono.map_witness _ fun h hh => ?_
  by_cases hc : (h.metaPtr == m) = true
  · simp only [hc, ↓reduceIte]
    exact ⟨g, hg, hMeta, hSc, hCnt, hMl, hPar, hSl⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h, hh, rfl, rfl, rfl, rfl, rfl, SlotUserSub.refl h.slots⟩

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
