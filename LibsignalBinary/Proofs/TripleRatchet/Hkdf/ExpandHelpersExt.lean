/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extended-Stack Frame and State Helpers for `expand_multi_info`

Defines `S2FrameRO`, the read-only `memcpy` step bridge `memcpyRO_subroutine_runsTo`, and
the `extHookStack` state invariants `ExpandFrameX`, `ExpandPreX`, and `ExpandCommonX`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

abbrev memcpyROLocalSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

attribute [scoped simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

/-- Permission-weakening-aware frame relation with a read-only source region `(roBase, roLen)`. -/
@[expose] def S2FrameRO (roBase : BitVec 64) (roLen : ℕ) (m₁ m₂ : Memory)
    (regs : List (BitVec 64 × ℕ)) : Prop :=
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (∀ r ∈ regs, OutsideRegion r.1 r.2 a) → m₂.read8 a = m₁.read8 a) ∧
  (((∀ a, OutsideRegion roBase roLen a → m₁.permNoLazy a = some Perm.rw → m₂.permNoLazy a = some Perm.rw) ∧
    (∀ a, OutsideRegion roBase roLen a → m₁.perm a = some Perm.rw → m₂.perm a = some Perm.rw)) ∧
   ((∀ a, (m₁.perm a).mapped = true ∧ m₁.isAnon a = true →
      (m₂.perm a).mapped = true ∧ m₂.isAnon a = true) ∧
    (∀ a, m₁.perm a = some Perm.protNone →
      (∀ r ∈ regs, OutsideRegion r.1 r.2 a) →
      m₂.perm a = some Perm.protNone ∧
      (m₁.isLazyFree a = false → m₂.read8 a = m₁.read8 a ∧ m₂.isLazyFree a = false)))) ∧
  (∀ a, (m₁.perm a).r = true → m₁.isLazyFree a = false →
    (m₂.perm a).r = true ∧ m₂.isLazyFree a = false)

namespace S2FrameRO

theorem refl (roBase : BitVec 64) (roLen : ℕ) (m : Memory) (regs : List (BitVec 64 × ℕ)) :
    S2FrameRO roBase roLen m m regs :=
  ⟨fun _ _ _ _ => rfl,
   ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, ⟨fun _ h => h, fun _ h _ => ⟨h, fun hlf => ⟨rfl, hlf⟩⟩⟩⟩,
   fun _ hr hlf => ⟨hr, hlf⟩⟩

theorem of_s2frame {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : S2Frame m₁ m₂ regs) :
    S2FrameRO roBase roLen m₁ m₂ regs :=
  ⟨h.1, ⟨⟨fun a _ hnl => h.2.1.1.1 a hnl, fun a _ hrw => h.2.1.1.2 a hrw⟩, h.2.1.2⟩, h.2.2⟩

theorem of_frame {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)} (h : Frame m₁ m₂ regs) :
    S2FrameRO roBase roLen m₁ m₂ regs :=
  of_s2frame (S2Frame.of_frame h)

theorem trans {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ m₃ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h12 : S2FrameRO roBase roLen m₁ m₂ regs)
    (h23 : S2FrameRO roBase roLen m₂ m₃ regs) :
    S2FrameRO roBase roLen m₁ m₃ regs :=
  ⟨fun a hr hlf hout =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     (h23.1 a hr₂ hlf₂ hout).trans (h12.1 a hr hlf hout),
   ⟨⟨fun a hro hnl => h23.2.1.1.1 a hro (h12.2.1.1.1 a hro hnl),
     fun a hro hrw => h23.2.1.1.2 a hro (h12.2.1.1.2 a hro hrw)⟩,
    ⟨fun a hm => h23.2.1.2.1 a (h12.2.1.2.1 a hm),
     fun a hpn hout =>
       let ⟨hp₁, hlf₁⟩ := h12.2.1.2.2 a hpn hout
       let ⟨hp₂, hlf₂⟩ := h23.2.1.2.2 a hp₁ hout
       ⟨hp₂, fun hlf =>
         let ⟨hr₁, hlf₁'⟩ := hlf₁ hlf
         let ⟨hr₂, hlf₂'⟩ := hlf₂ hlf₁'
         ⟨hr₂.trans hr₁, hlf₂'⟩⟩⟩⟩,
   fun a hr hlf =>
     let ⟨hr₂, hlf₂⟩ := h12.2.2 a hr hlf
     h23.2.2 a hr₂ hlf₂⟩

theorem mono {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs₁ regs₂ : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs₁)
    (hsub : ∀ a, (∀ r ∈ regs₂, OutsideRegion r.1 r.2 a) → ∀ r ∈ regs₁, OutsideRegion r.1 r.2 a) :
    S2FrameRO roBase roLen m₁ m₂ regs₂ :=
  ⟨fun a hr hlf hout => h.1 a hr hlf (hsub a hout),
   ⟨h.2.1.1,
    ⟨h.2.1.2.1, fun a hpn hout => h.2.1.2.2 a hpn (hsub a hout)⟩⟩,
   h.2.2⟩

theorem readable_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hr : m₁.Readable a n) : m₂.Readable a n :=
  fun x hx => h.2.2 x (hr x hx).1 (hr x hx).2

theorem rw_of_rw {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (h : S2FrameRO roBase roLen m₁ m₂ regs) (a : BitVec 64) (n : ℕ)
    (hout : ∀ x, InRegion roBase roLen x → OutsideRegion a n x)
    (hrw : RW m₁ a n) : RW m₂ a n := by
  intro x hx
  have hro : OutsideRegion roBase roLen x := by
    rw [outsideRegion_iff_not_inRegion]
    intro hin
    exact (outsideRegion_iff_not_inRegion a n x).mp (hout x hin) hx
  exact h.2.1.1.1 x hro (hrw x hx)

theorem readBytes_eq_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hread : m₁.Readable addr len)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < len := by simpa using h1
  have hin : InRegion addr len (addr + BitVec.ofNat 64 i) :=
    inRegion_base_add addr len i hi hlen
  exact hf.1 _ (hread _ hin).1 (hread _ hin).2 (fun r hr => (hd r hr).outside hin hlen)

theorem read64_eq_of_readable {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64}
    (hread : m₁.Readable addr 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr := by
  have hbytes := hf.readBytes_eq_of_readable hread hd (by decide)
  rw [Bytes.readBytes_8_eq, Bytes.readBytes_8_eq] at hbytes
  simp only [List.cons.injEq, and_true] at hbytes
  rcases hbytes with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]

theorem readBytes_eq {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64} {len : ℕ}
    (hrw : RW m₁ addr len)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr len) (hlen : len ≤ 2 ^ 64 := by decide) :
    m₂.readBytes addr len = m₁.readBytes addr len :=
  hf.readBytes_eq_of_readable hrw.readable hd hlen

theorem read64_eq {roBase : BitVec 64} {roLen : ℕ} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf : S2FrameRO roBase roLen m₁ m₂ regs) {addr : BitVec 64}
    (hrw : RW m₁ addr 8)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 addr 8) :
    m₂.read64 addr = m₁.read64 addr :=
  hf.read64_eq_of_readable hrw.readable hd

/-- Update two `IsBlock` regions across an `S2FrameRO` while preserving `P_ro ∗ R`
when `hro : IsBlockRO P_ro roBase roLen Φ_ro`. -/
theorem update_two_blocks {P1 P1' P2 P2' P_ro R : SepProp}
    {b1 b2 roBase : BitVec 64} {n1 n2 roLen : ℕ}
    {Φ1 Φ1' Φ2 Φ2' Φ_ro : Memory → Prop}
    {m m' : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hro : IsBlockRO P_ro roBase roLen Φ_ro)
    (h : m ⊨ P1 ∗ (P2 ∗ (P_ro ∗ R)))
    (hf : S2FrameRO roBase roLen m m' [(b1, n1), (b2, n2)])
    (hΦ1' : Φ1' m') (hΦ2' : Φ2' m') :
    m' ⊨ P1' ∗ (P2' ∗ (P_ro ∗ R)) := by
  have hrw1 : RW m b1 n1 := fun a ha => hb1.permNoLazy_rw h ha
  have h_swap : m ⊨ P2 ∗ (P1 ∗ (P_ro ∗ R)) := by rw [sepConj_left_comm]; exact h
  have hrw2 : RW m b2 n2 := fun a ha => hb2.permNoLazy_rw h_swap ha
  obtain ⟨h1, h2R, hd1, hp1, hp2R, hm⟩ := Satisfies.sepConj_elim h
  obtain ⟨h2, hR, hd2, rfl, hp2, hpR⟩ := SepProp.holds_sepConj_elim hp2R
  have hm2R : (h2.union hR).Matches m := Heap.Matches.of_union_right hd1 hm
  have hmR : hR.Matches m := Heap.Matches.of_union_right hd2 hm2R
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨h_ro, h_rest, hd_ro, hR_eq, hp_ro, hp_rest⟩ := SepProp.holds_sepConj_elim hpR
  obtain ⟨m_ro, hΦ_ro, rfl⟩ := (hro.iff h_ro).mp hp_ro
  have hout_ro_1 : ∀ a, InRegion roBase roLen a → OutsideRegion b1 n1 a := by
    intro a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha1
    unfold Heap.Disjoint at hd1
    have hRa : hR a = some (.ro (m_ro.read8 a)) := by
      rw [hR_eq]; simp [Heap.union, regionHeapRO, ha_ro]
    rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
    · simp [regionHeap, ha1] at h1n
    · by_cases ha2 : InRegion b2 n2 a
      · simp [Heap.union, regionHeap, ha2] at h2Rn
      · simp [Heap.union, regionHeap, ha2, hRa] at h2Rn
    · simp [regionHeap, ha1] at h1ro
  have hout_ro_2 : ∀ a, InRegion roBase roLen a → OutsideRegion b2 n2 a := by
    intro a ha_ro
    rw [outsideRegion_iff_not_inRegion]
    intro ha2
    unfold Heap.Disjoint at hd2
    have hRa : hR a = some (.ro (m_ro.read8 a)) := by
      rw [hR_eq]; simp [Heap.union, regionHeapRO, ha_ro]
    rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
    · simp [regionHeap, ha2] at h2n
    · rw [hRa] at hRn; cases hRn
    · simp [regionHeap, ha2] at h2ro
  have hrw1' : RW m' b1 n1 := hf.rw_of_rw b1 n1 hout_ro_1 hrw1
  have hrw2' : RW m' b2 n2 := hf.rw_of_rw b2 n2 hout_ro_2 hrw2
  let h1' := regionHeap b1 n1 m'
  let h2' := regionHeap b2 n2 m'
  have hp1' : P1' h1' := (hb1'.iff h1').mpr ⟨m', hΦ1', rfl⟩
  have hp2' : P2' h2' := (hb2'.iff h2').mpr ⟨m', hΦ2', rfl⟩
  have hm1' : h1'.Matches m' := IsBlock.regionHeap_matches b1 n1 m' hrw1'
  have hm2' : h2'.Matches m' := IsBlock.regionHeap_matches b2 n2 m' hrw2'
  have hd2' : h2'.Disjoint hR := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha2 : InRegion b2 n2 a
    · rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · exact Or.inr (Or.inl hRn)
      · simp [regionHeap, ha2] at h2ro
    · exact Or.inl (by simp [h2', regionHeap, ha2])
  have hd1' : h1'.Disjoint (h2'.union hR) := by
    apply Heap.Disjoint.of_phys_left (ha := rfl) (hf := rfl) (hm := rfl)
    intro a
    by_cases ha1 : InRegion b1 n1 a
    · rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · refine Or.inr (Or.inl ?_)
        by_cases ha2 : InRegion b2 n2 a
        · simp [Heap.union, regionHeap, ha2] at h2Rn
        · simp [Heap.union, regionHeap, ha2] at h2Rn
          simp [Heap.union, h2', regionHeap, ha2, h2Rn]
      · simp [regionHeap, ha1] at h1ro
    · exact Or.inl (by simp [h1', regionHeap, ha1])
  have hmR' : hR.Matches m' := by
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => hf.2.1.2.1 a (hmR.2.2 a hmap)⟩
    have hn2 : ¬ InRegion b2 n2 a := by
      intro ha2
      unfold Heap.Disjoint at hd2
      rcases hd2.1 a with h2n | hRn | ⟨_, h2ro, _⟩
      · simp [regionHeap, ha2] at h2n
      · rw [hc] at hRn; cases hRn
      · simp [regionHeap, ha2] at h2ro
    have hn1 : ¬ InRegion b1 n1 a := by
      intro ha1
      unfold Heap.Disjoint at hd1
      rcases hd1.1 a with h1n | h2Rn | ⟨_, h1ro, _⟩
      · simp [regionHeap, ha1] at h1n
      · simp [Heap.union, regionHeap, hn2, hc] at h2Rn
      · simp [regionHeap, ha1] at h1ro
    have ha_out : ∀ r ∈ [(b1, n1), (b2, n2)], OutsideRegion r.1 r.2 a := by
      intro r hr_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl
      · exact (outsideRegion_iff_not_inRegion b1 n1 a).mpr hn1
      · exact (outsideRegion_iff_not_inRegion b2 n2 a).mpr hn2
    cases c with
    | rw v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.rw v) hc
      have hr_true : (m.perm a).r = true := by rw [hperm]; rfl
      have hout_ro : OutsideRegion roBase roLen a := by
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        have hRa : hR a = some (.ro (m_ro.read8 a)) := by
          rw [hR_eq]; simp [Heap.union, regionHeapRO, hin_ro]
        rw [hRa] at hc
        cases hc
      have hnl : m.permNoLazy a = some Perm.rw :=
        Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨hperm', hlf'⟩ :=
        Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hout_ro hnl)
      exact ⟨(hf.1 a hr_true hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | ro v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.ro v) hc
      obtain ⟨hperm', hlf'⟩ := hf.2.2 a hperm hlf
      exact ⟨(hf.1 a hperm hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | protNone v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.protNone v) hc
      obtain ⟨hperm_m', hlf_fn⟩ := hf.2.1.2.2 a hperm ha_out
      obtain ⟨hr_m', hlf_m'⟩ := hlf_fn hlf
      exact ⟨hr_m'.trans hr_eq, hperm_m', hlf_m'⟩
    | lazy =>
      have hperm := hmR.1 a .lazy hc
      have hout_ro : OutsideRegion roBase roLen a := by
        rw [outsideRegion_iff_not_inRegion]
        intro hin_ro
        have hRa : hR a = some (.ro (m_ro.read8 a)) := by
          rw [hR_eq]; simp [Heap.union, regionHeapRO, hin_ro]
        rw [hRa] at hc
        cases hc
      exact hf.2.1.1.2 a hout_ro hperm
    | protNoneLazy =>
      have hperm := hmR.1 a .protNoneLazy hc
      exact (hf.2.1.2.2 a hperm ha_out).1
  exact Satisfies.sepConj_intro hd1' hp1' (SepProp.holds_sepConj_intro hd2' hp2' hpR)
    (Heap.Matches.union hm1' (Heap.Matches.union hm2' hmR'))

end S2FrameRO

private theorem regionHeap_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) :
    regionHeap b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeap, hni]

private theorem regionHeapRO_none_of_outside (b : BitVec 64) (n : ℕ) (m : Memory) (a : BitVec 64)
    (ha : OutsideRegion b n a) :
    regionHeapRO b n m a = none := by
  have hni : ¬ InRegion b n a := (outsideRegion_iff_not_inRegion b n a).mp ha
  simp [regionHeapRO, hni]

private theorem matches_regionHeapRO_of_readable {b : BitVec 64} {n : ℕ} {m : Memory}
    (hr : m.Readable b n) : (regionHeapRO b n m).Matches m := by
  apply Heap.Matches.of_phys (ha := rfl) (hf := rfl) (hm := rfl)
  intro a cv hcv
  dsimp [regionHeapRO] at hcv
  split at hcv
  · rename_i ha
    cases hcv
    exact ⟨rfl, (hr a ha).1, (hr a ha).2⟩
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

/-- Build `m ⊨ P1 ∗ P2 ∗ P3` where `P1`, `P3` are `IsBlock` (RW) and `P2` is `IsBlockRO` (RO). -/
theorem satisfies_two_rw_one_ro {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hread2 : m.Readable b2 n2) (hrw3 : RW m b3 n3)
    (hd13 : DisjointRegions b1 n1 b3 n3)
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
  have hd_13 : h1.Disjoint h3 := regionHeap_disjoint m hd13 hn3
  have hd_1_23 : h1.Disjoint (h2.union h3) :=
    (Heap.disjoint_union_right hd_23).mpr ⟨hd_12, hd_13⟩
  exact Satisfies.sepConj_intro hd_1_23 hp1 (SepProp.holds_sepConj_intro hd_23 hp2 hp3)
    (Heap.Matches.union hm1 (Heap.Matches.union hm2 hm3))

theorem isBlock_two_rw_one_ro_none_outside {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {a : BitVec 64}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h)
    (ha1 : OutsideRegion b1 n1 a)
    (ha2 : OutsideRegion b2 n2 a)
    (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  have h1n : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have h2n : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  have h3n : ¬ InRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mp ha3
  simp [Heap.union, regionHeap, regionHeapRO, h1n, h2n, h3n]

theorem isBlock_two_rw_one_ro_mapped_false {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
    (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap, regionHeapRO]

theorem isBlock_two_rw_one_ro_s2frame_aux {P1 P2 P3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ2 Φ3 : Memory → Prop}
    {h : Heap} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hb1 : IsBlock P1 b1 n1 Φ1)
    (hb2 : IsBlockRO P2 b2 n2 Φ2)
    (hb3 : IsBlock P3 b3 n3 Φ3)
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

theorem isBlock_two_rw_one_ro_s2frameRO {P1 P1' P2 P3 R1 R2 R3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ1' Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlockRO P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2 ∗ P3) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2 ∗ R2) (hpost_3 : m' ⊨ P3 ∗ R3)
    (hn2 : n2 ≤ 2 ^ 64)
    (hsrc_eq : m'.readBytes b2 n2 = m.readBytes b2 n2)
    (hmc_full : (fullComplementHeap hP m).Matches m') :
    S2FrameRO b2 n2 m m' [(b1, n1), (b3, n3)] := by
  have hmc := hmc_full
  unfold Heap.Matches at hmc
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a ha2 hnl_a => ?_, fun a ha2 hrw_a => ?_⟩,
     isBlock_two_rw_one_ro_s2frame_aux hb1 hb2 hb3 hpP hmP hmc_full⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion b1 n1 a := ha (b1, n1) (by simp)
    have ha3 : OutsideRegion b3 n3 a := ha (b3, n3) (by simp)
    by_cases hin2 : InRegion b2 n2 a
    · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset b2 n2 a hn2).mp hin2
      exact read8_eq_of_readBytes_eq hsrc_eq hi
    · have ha2 : OutsideRegion b2 n2 a :=
        (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
      have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
      by_cases hrw_a : m.perm a = some Perm.rw
      · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        exact (hmc.1 a _ hca).1
      · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
        exact (hmc.1 a _ hca).1
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin3 : InRegion b3 n3 a
      · exact hb3.permNoLazy_rw hpost_3 hin3
      · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
        have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
        have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
        obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
        have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
          simp [fullComplementHeap, hnone, hrw_a, hlf_a]
        obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
        exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin3 : InRegion b3 n3 a
      · exact hb3.perm_rw hpost_3 hin3
      · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
        have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
        have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
        by_cases hlf_a : m.isLazyFree a = true
        · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          exact hmc.1 a .lazy hca
        · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_f]
          exact (hmc.1 a _ hca).2.1
  · by_cases hin1 : InRegion b1 n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨hb2.perm_r hpost_2 hin2, hb2.isLazyFree_false hpost_2 hin2⟩
      · by_cases hin3 : InRegion b3 n3 a
        · exact ⟨by rw [hb3.perm_rw hpost_3 hin3]; rfl, hb3.isLazyFree_false hpost_3 hin3⟩
        · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
          have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_two_rw_one_ro_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hrw_a : m.perm a = some Perm.rw
          · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
            exact ⟨by rw [hp']; rfl, hlf'⟩
          · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc.1 a _ hca
            exact ⟨hp', hlf'⟩

/-- Extended stack frame of `expand_multi_info` at `17024` B. -/
abbrev ExpandFrameX (infoPtr : BitVec 64) (infoLen okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2FrameRO infoPtr infoLen s₀.mem m [(s₀.readReg64 .x2, okmLen), (s₀.sp - 17024#64, 17024)]

/-- Common state invariant across cuts of `expand_multi_info` at `17024` B stack. -/
structure ExpandCommonX (infoPtr : BitVec 64) (infoLen okmLen : ℕ) (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = esp s₀
  x29_eq : s.readReg64 .x29 = esp s₀ + 400#64
  x27_eq : s.readReg64 .x27 = esp s₀ + 64#64
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x0
  m8_eq  : s.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1
  m16_eq : s.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64
  saved  : ExpandSaved s₀ s.mem
  frame  : ExpandFrameX infoPtr infoLen okmLen s₀ s.mem

theorem readable_sub {m : Memory} {a : BitVec 64} {n : ℕ} (hr : m.Readable a n)
    {b : BitVec 64} {k : ℕ} (hsub : (b - a).toNat + k ≤ n) :
    m.Readable b k := by
  intro x hx
  apply hr x
  simp only [InRegion] at hx ⊢
  bv_omega

theorem ExpandFrameX.of_agreesOutside_esp {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hA : AgreesOutside m m' (esp s₀ + off) sz)
    (hoff : off.toNat + sz ≤ 496) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_frame (frame_of_agreesOutside hA)).mono fun a ha => ?_)
  have hstack : OutsideRegion (s₀.sp - 17024#64) 17024 a :=
    ha (s₀.sp - 17024#64, 17024) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  unfold esp at *
  simp only [OutsideRegion] at hstack ⊢
  bv_omega

theorem ExpandFrameX.of_agreesOutside_x2 {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ : State} {m m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hf : ExpandFrameX infoPtr infoLen okmLen s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : off.toNat + sz ≤ okmLen) :
    ExpandFrameX infoPtr infoLen okmLen s₀ m' := by
  refine hf.trans ((S2FrameRO.of_frame (frame_of_agreesOutside hA)).mono fun a ha => ?_)
  have hx2 : OutsideRegion (s₀.readReg64 .x2) okmLen a :=
    ha (s₀.readReg64 .x2, okmLen) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hx2 ⊢
  bv_omega

theorem ExpandCommonX.of_agreesOutside_low32 {infoPtr : BitVec 64} {infoLen okmLen : ℕ}
    {s₀ s s' : State} {off : BitVec 64} {sz : ℕ}
    (hc : ExpandCommonX infoPtr infoLen okmLen s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (esp s₀ + off) sz)
    (hoff  : decide (32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400) = true) :
    ExpandCommonX infoPtr infoLen okmLen s₀ s' := by
  have ⟨h1, h2, h3⟩ : 32 ≤ off.toNat ∧ 0 < sz ∧ off.toNat + sz ≤ 400 := of_decide_eq_true hoff
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_low hc.saved hA ⟨h2, h3⟩,
    ExpandFrameX.of_agreesOutside_esp hc.frame hA (by omega)⟩

theorem ExpandSaved_of_s2frame_disj {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : ExpandSaved s₀ m) (hrw_esp : m.RW (esp s₀) 496)
    (hfr : S2Frame m m' regs)
    (hd_saved : ∀ r ∈ regs, DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96) :
    ExpandSaved s₀ m' := by
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496) = true →
      m'.read64 (esp s₀ + off) = m.read64 (esp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_esp.sub (by bv_omega)) ?_
    intro r hr
    exact (hd_saved r hr).sub_right (esp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact
    { m400 := (h_saved_eq 400#64 (by decide)).trans h0
      m408 := (h_saved_eq 408#64 (by decide)).trans h1
      m416 := (h_saved_eq 416#64 (by decide)).trans h2
      m424 := (h_saved_eq 424#64 (by decide)).trans h3
      m432 := (h_saved_eq 432#64 (by decide)).trans h4
      m440 := (h_saved_eq 440#64 (by decide)).trans h5
      m448 := (h_saved_eq 448#64 (by decide)).trans h6
      m456 := (h_saved_eq 456#64 (by decide)).trans h7
      m464 := (h_saved_eq 464#64 (by decide)).trans h8
      m472 := (h_saved_eq 472#64 (by decide)).trans h9
      m480 := (h_saved_eq 480#64 (by decide)).trans h10
      m488 := (h_saved_eq 488#64 (by decide)).trans h11 }

theorem ExpandSaved_of_s2frameRO_disj {roBase : BitVec 64} {roLen : ℕ}
    {s₀ : State} {m m' : Memory} {regs : List (BitVec 64 × ℕ)}
    (hs : ExpandSaved s₀ m) (hrw_esp : m.RW (esp s₀) 496)
    (hfr : S2FrameRO roBase roLen m m' regs)
    (hd_saved : ∀ r ∈ regs, DisjointRegions r.1 r.2 (esp s₀ + 400#64) 96) :
    ExpandSaved s₀ m' := by
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (400 ≤ off.toNat ∧ off.toNat + 8 ≤ 496) = true →
      m'.read64 (esp s₀ + off) = m.read64 (esp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_esp.sub (by bv_omega)) ?_
    intro r hr
    exact (hd_saved r hr).sub_right (esp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact
    { m400 := (h_saved_eq 400#64 (by decide)).trans h0
      m408 := (h_saved_eq 408#64 (by decide)).trans h1
      m416 := (h_saved_eq 416#64 (by decide)).trans h2
      m424 := (h_saved_eq 424#64 (by decide)).trans h3
      m432 := (h_saved_eq 432#64 (by decide)).trans h4
      m440 := (h_saved_eq 440#64 (by decide)).trans h5
      m448 := (h_saved_eq 448#64 (by decide)).trans h6
      m456 := (h_saved_eq 456#64 (by decide)).trans h7
      m464 := (h_saved_eq 464#64 (by decide)).trans h8
      m472 := (h_saved_eq 472#64 (by decide)).trans h9
      m480 := (h_saved_eq 480#64 (by decide)).trans h10
      m488 := (h_saved_eq 488#64 (by decide)).trans h11 }

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
