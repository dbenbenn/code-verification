/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import ProofLib.Hoare.SubroutineHook
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extended-Stack Cut Predicates and Segments 1a–2b of `finalize_fixed`

Defines `AgreesOn`, three-region `S2Frame` update lemmas, cut predicates `StateF0pX`–`StateF5X`,
and segments 1a–2b of `Hmac<Sha256>::finalize_fixed` on `tripleRatchetProgAtExt`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Arm64.SepProp
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union Heap.Matches Heap.complement
  SepProp.Satisfies SepProp.Entails SepProp.emp SepProp.pure SepProp.sepConj SepProp.sepImp
  SepProp.sepExists pointsTo8 pointsToBytes regionHeap regionHeapRO regionBlock memRegion

theorem runsTo_toE {prog : Program} {s₀ : State} {P : State → Prop} (h : RunsTo prog s₀ P) :
    RunsToE prog s₀ P :=
  fun hL => by
    obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
    exact ⟨sf, hst, htr, hP, hLf⟩

/-! ## `AgreesOn` and Three-Region `S2Frame` Helpers -/

/-- Pointwise byte agreement on a predicate `P : BitVec 64 → Prop`. -/
@[expose] def AgreesOn (P : BitVec 64 → Prop) (m₁ m₂ : Memory) : Prop :=
  ∀ a, P a → m₁.read8 a = m₂.read8 a

namespace AgreesOn

theorem readBytes_eq {P : BitVec 64 → Prop} {m₁ m₂ : Memory} (h : AgreesOn P m₁ m₂)
    (base : BitVec 64) (len : ℕ) (hlen : len ≤ 2 ^ 64)
    (hP : ∀ a, InRegion base len a → P a) :
    m₁.readBytes base len = m₂.readBytes base len :=
  Memory.readBytes_congr_region hlen fun a ha => h a (hP a ha)

theorem read64_eq {P : BitVec 64 → Prop} {m₁ m₂ : Memory} (h : AgreesOn P m₁ m₂)
    (base : BitVec 64) (hP : ∀ a, InRegion base 8 a → P a) :
    m₁.read64 base = m₂.read64 base :=
  Memory.read64_congr fun a ha => h a (hP a ha)

theorem finSaved_of {P : BitVec 64 → Prop} {s0 : State} {fsp : BitVec 64} {m₁ m₂ : Memory}
    (h : AgreesOn P m₁ m₂) (hs : FinSaved s0 fsp m₂)
    (hP : ∀ a, InRegion (fsp + 0x40#64) 0x50 a → P a) :
    FinSaved s0 fsp m₁ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hsub (off : BitVec 64) (hoff : (off - (fsp + 0x40#64)).toNat + 8 ≤ 0x50) :
      ∀ a, InRegion off 8 a → P a := by
    intro a ha
    apply hP
    unfold InRegion at ha ⊢
    bv_omega
  exact ⟨(h.read64_eq (fsp + 0x40#64) (hsub _ (by bv_omega))).trans h1,
         (h.read64_eq (fsp + 0x48#64) (hsub _ (by bv_omega))).trans h2,
         (h.read64_eq (fsp + 0x50#64) (hsub _ (by bv_omega))).trans h3,
         (h.read64_eq (fsp + 0x60#64) (hsub _ (by bv_omega))).trans h4,
         (h.read64_eq (fsp + 0x68#64) (hsub _ (by bv_omega))).trans h5,
         (h.read64_eq (fsp + 0x70#64) (hsub _ (by bv_omega))).trans h6,
         (h.read64_eq (fsp + 0x78#64) (hsub _ (by bv_omega))).trans h7,
         (h.read64_eq (fsp + 0x80#64) (hsub _ (by bv_omega))).trans h8,
         (h.read64_eq (fsp + 0x88#64) (hsub _ (by bv_omega))).trans h9⟩

theorem hmacSt_of {P : BitVec 64 → Prop} {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key msg : List (BitVec 8)}
    (h : AgreesOn P m₁ m₂) (hst : HmacSt m₂ hm F key msg)
    (hP : ∀ a, InRegion hm 0x90 a → P a) :
    HmacSt m₁ hm F key msg := by
  rcases hst with ⟨hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  have hsub (off : BitVec 64) (sz : ℕ) (hoff : 0 < sz ∧ (off - hm).toNat + sz ≤ 0x90) :
      ∀ a, InRegion off sz a → P a := by
    intro a ha
    apply hP
    rcases hoff with ⟨_, _⟩
    unfold InRegion at ha ⊢
    bv_omega
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : msg.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · exact (h.readBytes_eq hm msg.length (by omega)
        (hsub hm msg.length ⟨by omega, by simp; omega⟩)).trans hmsg
  · exact (h (hm + 0x3f#64) (hP _ (by unfold InRegion; bv_omega))).trans hpos
  · exact (h.readBytes_eq (hm + 0x40#64) 32 (by decide)
      (hsub (hm + 0x40#64) 32 ⟨by decide, by bv_omega⟩)).trans hin
  · exact (h.read64_eq (hm + 0x60#64)
      (hsub (hm + 0x60#64) 8 ⟨by decide, by bv_omega⟩)).trans hibl
  · exact (h.readBytes_eq (hm + 0x68#64) 32 (by decide)
      (hsub (hm + 0x68#64) 32 ⟨by decide, by bv_omega⟩)).trans hout
  · exact (h.read64_eq (hm + 0x88#64)
      (hsub (hm + 0x88#64) 8 ⟨by decide, by bv_omega⟩)).trans hobl

/-- If `s'` modifies only `(dst, bs.length)` and `(stk, stkLen)` relative to `m` via `S2Frame`,
and `m'.readBytes dst bs.length = bs`, then `m'` agrees with `m.writeBytes dst bs` on all
addresses `a` that are readable in `m` and outside `(stk, stkLen)`. -/
theorem of_s2Frame_writeBytes {m m' : Memory} {dst stk : BitVec 64} {bs : List (BitVec 8)}
    {stkLen : ℕ}
    (hdst : m'.readBytes dst bs.length = bs)
    (hframe : S2Frame m m' [(dst, bs.length), (stk, stkLen)])
    (hlen : bs.length ≤ 2 ^ 64) :
    AgreesOn (fun a => m.permNoLazy a = some Perm.rw ∧ OutsideRegion stk stkLen a)
      m' (m.writeBytes dst bs) := by
  intro a ⟨hnl, hstk⟩
  by_cases hin : InRegion dst bs.length a
  · obtain ⟨i, hi, rfl⟩ := (inRegion_iff_exists_offset dst bs.length a hlen).mp hin
    have hwb : (m.writeBytes dst bs).readBytes dst bs.length = bs :=
      Memory.readBytes_writeBytes_same m dst bs hlen
    exact read8_eq_of_readBytes_eq (hdst.trans hwb.symm) hi
  · have hout_dst : OutsideRegion dst bs.length a :=
      (outsideRegion_iff_not_inRegion dst bs.length a).mpr hin
    obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    have hr : (m.perm a).r = true := by rw [hrw]; rfl
    have h1 : m'.read8 a = m.read8 a := by
      refine hframe.1 a hr hlf fun r hr_mem => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl
      · exact hout_dst
      · exact hstk
    have h2 : (m.writeBytes dst bs).read8 a = m.read8 a :=
      (ProofLib.AgreesOutside.writeBytes_self m dst bs).1 a hout_dst
    exact h1.trans h2.symm

end AgreesOn

theorem satisfies_three_blocks {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hd13 : DisjointRegions b1 n1 b3 n3)
    (hd23 : DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 :=
  satisfies_three_blocks_opt hb1 hb2 hb3 hΦ1 hΦ2 hΦ3 hrw1 hrw2 hrw3
    (Or.inr (Or.inr hd12)) (Or.inr (Or.inr hd13)) (Or.inr (Or.inr hd23)) hn2 hn3

theorem isBlock_three_none_outside {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {h : Heap} (hp : (P1 ∗ P2 ∗ P3) h) {a : BitVec 64}
    (ha1 : OutsideRegion b1 n1 a) (ha2 : OutsideRegion b2 n2 a) (ha3 : OutsideRegion b3 n3 a) :
    h a = none := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  have hn1 : ¬ InRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mp ha1
  have hn2 : ¬ InRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mp ha2
  have hn3 : ¬ InRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mp ha3
  simp [Heap.union, regionHeap, hn1, hn2, hn3]

theorem isBlock_three_mapped_false {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    {h : Heap} (hp : (P1 ∗ P2 ∗ P3) h) (a : BitVec 64) :
    h.mapped a = false := by
  obtain ⟨h1, h23, _, rfl, hp1, hp23⟩ := SepProp.holds_sepConj_elim hp
  obtain ⟨h2, h3, _, rfl, hp2, hp3⟩ := SepProp.holds_sepConj_elim hp23
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  simp [Heap.union, regionHeap]

theorem isBlock_three_all_s2frame {P1 P1' P2 P2' P3 R1 R2 R3 : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ1' Φ2 Φ2' Φ3 : Memory → Prop}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hb3 : IsBlock P3 b3 n3 Φ3)
    {hP : Heap} {m m' : Memory}
    (hpP : (P1 ∗ P2 ∗ P3) hP) (hmP : hP.Matches m)
    (hpost_1 : m' ⊨ P1' ∗ R1) (hpost_2 : m' ⊨ P2' ∗ R2) (hpost_3 : m' ⊨ P3 ∗ R3)
    (hmc : ∀ a c, (fullComplementHeap hP m).phys a = some c →
      match c with
      | .rw b => m'.read8 a = b ∧ m'.perm a = some Perm.rw ∧ m'.isLazyFree a = false
      | .ro b => m'.read8 a = b ∧ (m'.perm a).r = true ∧ m'.isLazyFree a = false
      | .protNone b => m'.read8 a = b ∧ m'.perm a = some Perm.protNone ∧ m'.isLazyFree a = false
      | .lazy => m'.perm a = some Perm.rw
      | .protNoneLazy => m'.perm a = some Perm.protNone)
    (hmc_map : ∀ a, (fullComplementHeap hP m).mapped a = true →
      (m'.perm a).mapped = true ∧ m'.isAnon a = true) :
    S2Frame m m' [(b1, n1), (b2, n2), (b3, n3)] := by
  refine ⟨fun a hr_a hlf_a ha => ?_,
    ⟨⟨fun a hnl_a => ?_, fun a hrw_a => ?_⟩,
     Extract.isBlock_three_s2frame_aux hb1 hb2 hb3 hpP hmP hmc hmc_map⟩,
    fun a hr_a hlf_a => ?_⟩
  · have ha1 : OutsideRegion b1 n1 a := ha (b1, n1) (by simp)
    have ha2 : OutsideRegion b2 n2 a := ha (b2, n2) (by simp)
    have ha3 : OutsideRegion b3 n3 a := ha (b3, n3) (by simp)
    have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
    by_cases hrw_a : m.perm a = some Perm.rw
    · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hlf_a]
      exact (hmc a _ hca).1
    · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
        simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
      exact (hmc a _ hca).1
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.permNoLazy_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2'.permNoLazy_rw hpost_2 hin2
      · by_cases hin3 : InRegion b3 n3 a
        · exact hb3.permNoLazy_rw hpost_3 hin3
        · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
          have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          obtain ⟨hrw_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl_a
          have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
            simp [fullComplementHeap, hnone, hrw_a, hlf_a]
          obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
          exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hp', hlf'⟩
  · by_cases hin1 : InRegion b1 n1 a
    · exact hb1'.perm_rw hpost_1 hin1
    · by_cases hin2 : InRegion b2 n2 a
      · exact hb2'.perm_rw hpost_2 hin2
      · by_cases hin3 : InRegion b3 n3 a
        · exact hb3.perm_rw hpost_3 hin3
        · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
          have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hlf_a : m.isLazyFree a = true
          · have hca : (fullComplementHeap hP m).phys a = some .lazy := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            exact hmc a .lazy hca
          · have hlf_f : m.isLazyFree a = false := Bool.eq_false_iff.mpr hlf_a
            have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_f]
            exact (hmc a _ hca).2.1
  · by_cases hin1 : InRegion b1 n1 a
    · exact ⟨by rw [hb1'.perm_rw hpost_1 hin1]; rfl, hb1'.isLazyFree_false hpost_1 hin1⟩
    · by_cases hin2 : InRegion b2 n2 a
      · exact ⟨by rw [hb2'.perm_rw hpost_2 hin2]; rfl, hb2'.isLazyFree_false hpost_2 hin2⟩
      · by_cases hin3 : InRegion b3 n3 a
        · exact ⟨by rw [hb3.perm_rw hpost_3 hin3]; rfl, hb3.isLazyFree_false hpost_3 hin3⟩
        · have ha1 : OutsideRegion b1 n1 a := (outsideRegion_iff_not_inRegion b1 n1 a).mpr hin1
          have ha2 : OutsideRegion b2 n2 a := (outsideRegion_iff_not_inRegion b2 n2 a).mpr hin2
          have ha3 : OutsideRegion b3 n3 a := (outsideRegion_iff_not_inRegion b3 n3 a).mpr hin3
          have hnone : hP a = none := isBlock_three_none_outside hb1 hb2 hb3 hpP ha1 ha2 ha3
          by_cases hrw_a : m.perm a = some Perm.rw
          · have hca : (fullComplementHeap hP m).phys a = some (.rw (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hlf_a]
            obtain ⟨-, hp', hlf'⟩ := hmc a _ hca
            exact ⟨by rw [hp']; rfl, hlf'⟩
          · have hca : (fullComplementHeap hP m).phys a = some (.ro (m.read8 a)) := by
              simp [fullComplementHeap, hnone, hrw_a, hr_a, hlf_a]
            obtain ⟨-, hr', hlf'⟩ := hmc a _ hca
            exact ⟨hr', hlf'⟩

theorem S2Frame.update_three_blocks {P1 P1' P2 P2' P3 P3' R : SepProp}
    {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ} {Φ1 Φ1' Φ2 Φ2' Φ3 Φ3' : Memory → Prop}
    {m0 mf : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb1' : IsBlock P1' b1 n1 Φ1')
    (hb2 : IsBlock P2 b2 n2 Φ2) (hb2' : IsBlock P2' b2 n2 Φ2')
    (hb3 : IsBlock P3 b3 n3 Φ3) (hb3' : IsBlock P3' b3 n3 Φ3')
    (h0 : m0 ⊨ P1 ∗ (P2 ∗ (P3 ∗ R)))
    (hf : S2Frame m0 mf [(b1, n1), (b2, n2), (b3, n3)])
    (hΦ1' : Φ1' mf) (hΦ2' : Φ2' mf) (hΦ3' : Φ3' mf) :
    mf ⊨ P1' ∗ (P2' ∗ (P3' ∗ R)) := by
  have hrw1 : RW m0 b1 n1 := hb1.rw h0
  have h0_2 : m0 ⊨ P2 ∗ (P1 ∗ (P3 ∗ R)) := by ac_nf at h0 ⊢
  have hrw2 : RW m0 b2 n2 := hb2.rw h0_2
  have h0_3 : m0 ⊨ P3 ∗ (P1 ∗ (P2 ∗ R)) := by ac_nf at h0 ⊢
  have hrw3 : RW m0 b3 n3 := hb3.rw h0_3
  have hrw1' : RW mf b1 n1 := hf.rw_of_rw b1 n1 hrw1
  have hrw2' : RW mf b2 n2 := hf.rw_of_rw b2 n2 hrw2
  have hrw3' : RW mf b3 n3 := hf.rw_of_rw b3 n3 hrw3
  obtain ⟨h1, h23R, hd1, hp1, hp23R, hm⟩ := Satisfies.sepConj_elim h0
  obtain ⟨h2, h3R, hd2, rfl, hp2, hp3R⟩ := SepProp.holds_sepConj_elim hp23R
  obtain ⟨h3, hR, hd3, rfl, hp3, hpR⟩ := SepProp.holds_sepConj_elim hp3R
  have hm23R : (h2.union (h3.union hR)).Matches m0 := Heap.Matches.of_union_right hd1 hm
  have hm3R : (h3.union hR).Matches m0 := Heap.Matches.of_union_right hd2 hm23R
  have hmR : hR.Matches m0 := Heap.Matches.of_union_right hd3 hm3R
  obtain ⟨m1, -, rfl⟩ := (hb1.iff h1).mp hp1
  obtain ⟨m2, -, rfl⟩ := (hb2.iff h2).mp hp2
  obtain ⟨m3, -, rfl⟩ := (hb3.iff h3).mp hp3
  let h1' := regionHeap b1 n1 mf
  let h2' := regionHeap b2 n2 mf
  let h3' := regionHeap b3 n3 mf
  have hp1' : P1' h1' := (hb1'.iff h1').mpr ⟨mf, hΦ1', rfl⟩
  have hp2' : P2' h2' := (hb2'.iff h2').mpr ⟨mf, hΦ2', rfl⟩
  have hp3' : P3' h3' := (hb3'.iff h3').mpr ⟨mf, hΦ3', rfl⟩
  have hm1' : h1'.Matches mf := IsBlock.regionHeap_matches b1 n1 mf hrw1'
  have hm2' : h2'.Matches mf := IsBlock.regionHeap_matches b2 n2 mf hrw2'
  have hm3' : h3'.Matches mf := IsBlock.regionHeap_matches b3 n3 mf hrw3'
  have hd3' : h3'.Disjoint hR := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h3', regionHeap])
      (hf := by simp [h3', regionHeap]) (hm := by simp [h3', regionHeap]) fun a => ?_
    by_cases ha3 : InRegion b3 n3 a
    · exact Or.inr (Or.inl (Heap.eq_none_of_disjoint_regionHeap hd3 ha3))
    · exact Or.inl (by simp [h3', regionHeap, ha3])
  have hd2' : h2'.Disjoint (h3'.union hR) := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h2', regionHeap])
      (hf := by simp [h2', regionHeap]) (hm := by simp [h2', regionHeap]) fun a => ?_
    by_cases ha2 : InRegion b2 n2 a
    · have h3Rn := Heap.eq_none_of_disjoint_regionHeap hd2 ha2
      refine Or.inr (Or.inl ?_)
      by_cases ha3 : InRegion b3 n3 a <;>
        (simp [Heap.union, h3', regionHeap, ha3] at h3Rn ⊢; try exact h3Rn)
    · exact Or.inl (by simp [h2', regionHeap, ha2])
  have hd1' : h1'.Disjoint (h2'.union (h3'.union hR)) := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h1', regionHeap])
      (hf := by simp [h1', regionHeap]) (hm := by simp [h1', regionHeap]) fun a => ?_
    by_cases ha1 : InRegion b1 n1 a
    · have h23Rn := Heap.eq_none_of_disjoint_regionHeap hd1 ha1
      refine Or.inr (Or.inl ?_)
      by_cases ha2 : InRegion b2 n2 a <;>
        by_cases ha3 : InRegion b3 n3 a <;>
        (simp [Heap.union, h2', h3', regionHeap, ha2, ha3] at h23Rn ⊢; try exact h23Rn)
    · exact Or.inl (by simp [h1', regionHeap, ha1])
  have hmR' : hR.Matches mf := by
    unfold Heap.Matches at hmR ⊢
    refine ⟨fun a c hc => ?_, hmR.2.1, fun a hmap => hf.2.1.2.1 a (hmR.2.2 a hmap)⟩
    have hn3 : ¬ InRegion b3 n3 a := by
      intro ha3
      have hRn := Heap.eq_none_of_disjoint_regionHeap hd3 ha3
      rw [hc] at hRn; cases hRn
    have hn2 : ¬ InRegion b2 n2 a := by
      intro ha2
      have h3Rn := Heap.eq_none_of_disjoint_regionHeap hd2 ha2
      simp [Heap.union, regionHeap, hn3, hc] at h3Rn
    have hn1 : ¬ InRegion b1 n1 a := by
      intro ha1
      have h23Rn := Heap.eq_none_of_disjoint_regionHeap hd1 ha1
      simp [Heap.union, regionHeap, hn2, hn3, hc] at h23Rn
    have ha_out : ∀ r ∈ [(b1, n1), (b2, n2), (b3, n3)], OutsideRegion r.1 r.2 a := by
      intro r hr_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
      rcases hr_mem with rfl | rfl | rfl
      · exact (outsideRegion_iff_not_inRegion b1 n1 a).mpr hn1
      · exact (outsideRegion_iff_not_inRegion b2 n2 a).mpr hn2
      · exact (outsideRegion_iff_not_inRegion b3 n3 a).mpr hn3
    cases c with
    | rw v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.rw v) hc
      have hr_true : (m0.perm a).r = true := by rw [hperm]; rfl
      have hnl : m0.permNoLazy a = some Perm.rw := Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm, hlf⟩
      obtain ⟨hperm', hlf'⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hf.2.1.1.1 a hnl)
      exact ⟨(hf.1 a hr_true hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | ro v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.ro v) hc
      obtain ⟨hperm', hlf'⟩ := hf.2.2 a hperm hlf
      exact ⟨(hf.1 a hperm hlf ha_out).trans hr_eq, hperm', hlf'⟩
    | protNone v =>
      obtain ⟨hr_eq, hperm, hlf⟩ := hmR.1 a (.protNone v) hc
      obtain ⟨hperm_m', hlf_imp⟩ := hf.2.1.2.2 a hperm ha_out
      obtain ⟨hr_m', hlf_m'⟩ := hlf_imp hlf
      exact ⟨hr_m'.trans hr_eq, hperm_m', hlf_m'⟩
    | lazy =>
      exact hf.2.1.1.2 a (hmR.1 a .lazy hc)
    | protNoneLazy =>
      exact (hf.2.1.2.2 a (hmR.1 a .protNoneLazy hc) ha_out).1
  exact Satisfies.sepConj_intro hd1' hp1'
    (SepProp.holds_sepConj_intro hd2' hp2' (SepProp.holds_sepConj_intro hd3' hp3' hpR))
    (Heap.Matches.union hm1' (Heap.Matches.union hm2' (Heap.Matches.union hm3' hmR')))

theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

theorem S2Frame.trans_agreesOutside {m₁ m₂ m₃ : Memory} {regs : List (BitVec 64 × ℕ)}
    {base : BitVec 64} {len : ℕ}
    (hf : S2Frame m₁ m₂ regs) (hmem : (base, len) ∈ regs)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2Frame m₁ m₃ regs :=
  hf.trans (S2Frame.of_frame (Frame.trans_agreesOutside (Frame.refl m₂ regs) hmem hag))

theorem S2Frame.trans_agreesOutside_sub {m₁ m₂ m₃ : Memory} {regs : List (BitVec 64 × ℕ)}
    {rbase base : BitVec 64} {rlen len : ℕ}
    (hf : S2Frame m₁ m₂ regs) (hmem : (rbase, rlen) ∈ regs)
    (hsub : (base - rbase).toNat + len ≤ rlen)
    (hag : AgreesOutside m₂ m₃ base len) :
    S2Frame m₁ m₃ regs :=
  hf.trans (S2Frame.of_frame (Frame.trans_agreesOutside_sub (Frame.refl m₂ regs) hmem hsub hag))

theorem S2Frame.readable_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hr : m₁.Readable a n) :
    m₂.Readable a n :=
  fun x hx => hf.2.2 x (hr x hx).1 (hr x hx).2

/-! ## Cut-Point Predicates and Segments 1a–2b -/

namespace FinX

open FinalizeFixedProof

structure FinCommonX (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 0x40#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : S2Frame s0.mem s.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)]

@[expose] def FinPostX (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  S2Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)]

theorem s2Frame_of_frame_fsp {s0 : State} {m m' : Memory}
    (hframe : S2Frame s0.mem m
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)])
    (hf_sub : Frame m m'
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]) :
    S2Frame s0.mem m'
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
  refine hframe.trans ((S2Frame.of_frame hf_sub).mono fun a ha => ?_)
  intro r hr_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl | rfl
  · exact ha (s0.readReg64 .x0, 32) (by simp)
  · exact ha (s0.readReg64 .x1, 0x90) (by simp)
  · have ha_stk := ha (s0.sp - 16528#64, 16528) (by simp)
    unfold OutsideRegion at ha_stk ⊢; bv_omega

end FinX

end CryptoVerification.LibsignalTripleRatchet.HkdfExt
