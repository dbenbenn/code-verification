/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# Hook `RunsToE` Steppers for SPQR KDF

Subroutine `RunsToE` steppers for `compress256`, read-only / read-write `memcpy`, and `memset`
derived from `SpqrKdfHooksExt` at `extHookStack` (`16384` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout

namespace SpqrKdfExt

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

private theorem satisfies_two_blocks {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hn2 : n2 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hdisj12 : h1.Disjoint h2 := regionHeap_disjoint m hd12 hn2
  exact Satisfies.sepConj_intro hdisj12 hp1 hp2 (Heap.Matches.union hm1 hm2)

private theorem isBlock_two_none_outside {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) {a : BitVec 64}
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) :
    h a = none := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  have hn1 : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have hn2 : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  simp [Heap.union, regionHeap, hn1, hn2]

private theorem isBlock_two_mapped_false {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} (hp : (P1 ∗ P2) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  simp [Heap.union, regionHeap]

private theorem isBlock_two_s2frame_aux {P1 P2 : SepProp} {b1 b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2)
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hp : (P1 ∗ P2) h) (hm : h.Matches m)
    (hmc : ∀ a c, (fullComplementHeap h m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap h m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    (∀ a, (m.perm a).mapped = true ∧ m.isAnon a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) ∧
    (∀ a, m.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m'.perm a = some Perm.protNone ∧
      (m.isLazyFree a = false → m'.read8 a = m.read8 a ∧ m'.isLazyFree a = false)) := by
  refine ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩
  · have hm0 : h.mapped a = false := isBlock_two_mapped_false hb1 hb2 hp a
    exact hmc_map a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      unfold Heap.Matches at hm
      obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeap b2 n2 m2)) a with
      | none => rfl
      | some c =>
        have hperm := hm.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            simp [Heap.union, regionHeap, h1, h2] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

private theorem isBlock_two_s2frame {P1 P1' P2 R1 R2 : SepProp}
    {dst b2 : BitVec 64} {n1 n2 : ℕ}
    {Φ1 Φ1' Φ2 : Memory → Prop}
    (hb1 : IsBlock P1 dst n1 Φ1) (hb1' : IsBlock P1' dst n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2)
    (hmc : ∀ a c, (fullComplementHeap hP m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap hP m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    S2Frame m m' [(dst, n1), (b2, n2)] := by
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     isBlock_two_s2frame_aux hb1 hb2 hpP hmP hmc hmc_map⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion dst n1 a := ha (dst, n1) (by simp)
    have ha2 : OutsideRegion b2 n2 a := ha (b2, n2) (by simp)
    have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc a _ hca).1
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.permNoLazy_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion dst n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2.perm_rw hpost_2 hin2
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hlf_a : m.isLazyFree a = true
        · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact hmc a .lazy hca
        · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_f]
          exact (hmc a _ hca).2.1
  · by_cases hin1 : InRegion dst n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨by rw [hb2.perm_rw hpost_2 hin2]; rfl, hb2.isLazyFree_false hpost_2 hin2⟩
      · have ha1 : OutsideRegion dst n1 a := (outsideRegion_iff_not_inRegion dst n1 a).mpr hin1
        have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
        have hnone : hP a = none := isBlock_two_none_outside hb1 hb2 hpP ha1 ha2
        by_cases hrw_a : m.perm a = some Perm.rw
        · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact ⟨by rw [hp']; rfl, hlf'⟩
        · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact ⟨hp', hlf'⟩

private theorem regionHeap_disjoint_opt {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} (m : Memory)
    (hd : n₁ = 0 ∨ n₂ = 0 ∨ DisjointRegions b₁ n₁ b₂ n₂) (hn₂ : n₂ ≤ 2 ^ 64) :
    (regionHeap b₁ n₁ m).Disjoint (regionHeap b₂ n₂ m) := by
  rcases hd with rfl | rfl | hd
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inl (by simp [regionHeap, InRegion])
  · apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl); intro a
    exact Or.inr (Or.inl (by simp [regionHeap, InRegion]))
  · exact regionHeap_disjoint m hd hn₂

private theorem satisfies_three_blocks_opt {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64}
    {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : n1 = 0 ∨ n2 = 0 ∨ DisjointRegions b1 n1 b2 n2)
    (hd13 : n1 = 0 ∨ n3 = 0 ∨ DisjointRegions b1 n1 b3 n3)
    (hd23 : n2 = 0 ∨ n3 = 0 ∨ DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeap b2 n2 m
  let h3 := regionHeap b3 n3 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hp3 : P3 h3 := (hb3.iff h3).mpr ⟨m, hΦ3, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := IsBlock.regionHeap_matches b2 n2 m hrw2
  have hm3 : h3.Matches m := IsBlock.regionHeap_matches b3 n3 m hrw3
  have hdisj23 : h2.Disjoint h3 := regionHeap_disjoint_opt m hd23 hn3
  have hm23 : (h2.union h3).Matches m := Heap.Matches.union hm2 hm3
  have hdisj1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hdisj23).mpr
      ⟨regionHeap_disjoint_opt m hd12 hn2, regionHeap_disjoint_opt m hd13 hn3⟩
  exact Satisfies.sepConj_intro hdisj1_23 hp1 (SepProp.holds_sepConj_intro hdisj23 hp2 hp3)
    (Heap.Matches.union hm1 hm23)

private theorem regionHeap_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) : regionHeap b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeap, hni]

private theorem regionHeapRO_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) : regionHeapRO b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeapRO, hni]

private theorem matches_regionHeapRO_of_readable {b : BitVec 64} {n : ℕ} {m : Memory}
    (hr : m.Readable b n) : (regionHeapRO b n m).Matches m := by
  apply Heap.Matches.of_phys (ha := rfl) (hf := rfl) (hm := rfl)
  intro a cv hcv
  dsimp [regionHeapRO] at hcv
  split at hcv
  · rename_i ha; cases hcv; exact ⟨rfl, (hr a ha).1, (hr a ha).2⟩
  · contradiction

private theorem disjoint_regionHeap_regionHeapRO {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} {m₁ m₂ : Memory}
    (hout : ∀ a, InRegion b₂ n₂ a → OutsideRegion b₁ n₁ a) :
    (regionHeap b₁ n₁ m₁).Disjoint (regionHeapRO b₂ n₂ m₂) := by
  apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
  intro a
  by_cases ha₂ : InRegion b₂ n₂ a
  · have hni : ¬ InRegion b₁ n₁ a := (outsideRegion_iff_not_inRegion b₁ n₁ a).mp (hout a ha₂)
    exact Or.inl (by simp [regionHeap, hni])
  · exact Or.inr (Or.inl (by simp [regionHeapRO, ha₂]))

private theorem disjoint_regionHeapRO_regionHeap {b₁ b₂ : BitVec 64} {n₁ n₂ : ℕ} {m₁ m₂ : Memory}
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    (regionHeapRO b₁ n₁ m₁).Disjoint (regionHeap b₂ n₂ m₂) := by
  apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
  intro a
  by_cases ha₁ : InRegion b₁ n₁ a
  · have hni : ¬ InRegion b₂ n₂ a := (outsideRegion_iff_not_inRegion b₂ n₂ a).mp (hout a ha₁)
    exact Or.inr (Or.inl (by simp [regionHeap, hni]))
  · exact Or.inl (by simp [regionHeapRO, ha₁])

private theorem satisfies_two_rw_one_ro {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hread2 : m.Readable b2 n2) (hrw3 : RW m b3 n3)
    (hd13 : n1 = 0 ∨ DisjointRegions b1 n1 b3 n3)
    (hn3 : n3 ≤ 2 ^ 64)
    (hout21 : ∀ a, InRegion b2 n2 a → OutsideRegion b1 n1 a)
    (hout23 : ∀ a, InRegion b2 n2 a → OutsideRegion b3 n3 a) :
    m ⊨ P1 ∗ P2 ∗ P3 := by
  let h1 := regionHeap b1 n1 m
  let h2 := regionHeapRO b2 n2 m
  let h3 := regionHeap b3 n3 m
  have hp1 : P1 h1 := (hb1.iff h1).mpr ⟨m, hΦ1, rfl⟩
  have hp2 : P2 h2 := (hb2.iff h2).mpr ⟨m, hΦ2, rfl⟩
  have hp3 : P3 h3 := (hb3.iff h3).mpr ⟨m, hΦ3, rfl⟩
  have hm1 : h1.Matches m := IsBlock.regionHeap_matches b1 n1 m hrw1
  have hm2 : h2.Matches m := matches_regionHeapRO_of_readable hread2
  have hm3 : h3.Matches m := IsBlock.regionHeap_matches b3 n3 m hrw3
  have hd_23 : h2.Disjoint h3 := disjoint_regionHeapRO_regionHeap hout23
  have hd_12 : h1.Disjoint h2 := disjoint_regionHeap_regionHeapRO hout21
  have hd_13 : h1.Disjoint h3 := regionHeap_disjoint_opt m (hd13.imp id Or.inr) hn3
  have hd_1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hd_23).mpr ⟨hd_12, hd_13⟩
  exact Satisfies.sepConj_intro hd_1_23 hp1 (SepProp.holds_sepConj_intro hd_23 hp2 hp3)
    (Heap.Matches.union hm1 (Heap.Matches.union hm2 hm3))

private theorem isBlock_two_rw_one_ro_none_outside {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {a : BitVec 64}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h)
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap_none_of_outside b1 n1 m1 a ha1,
    regionHeapRO_none_of_outside b2 n2 m2 a ha2,
    regionHeap_none_of_outside b3 n3 m3 a ha3]

private theorem isBlock_two_rw_one_ro_mapped_false {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {h : Heap}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap, regionHeapRO]

private theorem isBlock_two_rw_one_ro_s2frame_aux {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (hm : h.Matches m)
    (hmc : (fullComplementHeap h m).Matches m') :
    (∀ a, (m.perm a).mapped = true ∧ m.isAnon a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) ∧
    (∀ a, m.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m'.perm a = some Perm.protNone ∧
      (m.isLazyFree a = false → m'.read8 a = m.read8 a ∧ m'.isLazyFree a = false)) := by
  unfold Heap.Matches at hm hmc
  refine ⟨fun a ⟨hm_a, han_a⟩ => ?_, fun a hpn_a _ => ?_⟩
  · have hm0 : h.mapped a = false := isBlock_two_rw_one_ro_mapped_false hb1 hb2 hb3 hp a
    exact hmc.2.2 a (by simp [fullComplementHeap, hm0, hm_a, han_a])
  · have hnone : h a = none := by
      obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
      obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
      obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
      obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
      obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
      cases ha : (regionHeap b1 n1 m1 |>.union (regionHeapRO b2 n2 m2 |>.union (regionHeap b3 n3 m3))) a with
      | none => rfl
      | some c =>
        have hperm := hm.1 a c ha
        cases c with
        | rw v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | ro v => have hperm := hperm.2.1; rw [hpn_a] at hperm; cases hperm
        | protNone v =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            by_cases h3 : InRegion b3 n3 a <;>
            simp [Heap.union, regionHeap, regionHeapRO, h1, h2, h3] at ha
        | lazy => rw [hpn_a] at hperm; cases hperm
        | protNoneLazy =>
          by_cases h1 : InRegion b1 n1 a <;>
            by_cases h2 : InRegion b2 n2 a <;>
            by_cases h3 : InRegion b3 n3 a <;>
            simp [Heap.union, regionHeap, regionHeapRO, h1, h2, h3] at ha
    by_cases hlf : m.isLazyFree a = true
    · have hca : (fullComplementHeap h m).phys a = some .protNoneLazy := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf]; rfl
      exact ⟨hmc.1 a .protNoneLazy hca, fun hlf_f => by rw [hlf] at hlf_f; cases hlf_f⟩
    · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf
      have hca : (fullComplementHeap h m).phys a = some (.protNone (m.read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hnone, hpn_a, hlf_f]; rfl
      obtain ⟨hr, hp', hlf'⟩ := hmc.1 a (.protNone (m.read8 a)) hca
      exact ⟨hp', fun _ => ⟨hr, hlf'⟩⟩

private theorem shaStateBytes_len (st : ShaState) : (shaStateBytes st).length = 32 := by
  rcases st with ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem chunks64_single_of_len_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    HMAC.chunks64 bs = [bs] := by simp [HMAC.chunks64, h]

end SpqrKdfExt

end CryptoVerification.SpqrV1.Kdf
