/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow

/-! # `generate_keypair_compressed` (`B05`) — Segment 5 Nine `serialize_12` Loops (`Seg5Loops`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  ser12Prefix step_ldp_polyChunk step_ser12_simd18 step_ser12_tail14 step_ser12_tail15_off384)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [25192 → 25340, 25520 → 25668, 25812 → 25960, 26340 → 26492,
   26680 → 26828, 27016 → 27164, 27424 → 27572, 27756 → 27904, 28088 → 28236]
end

attribute [local irreducible] blkPC05 blkLib05 dup8x16 polyVecNat ser12Prefix

private theorem idx32_add32_eq {base k : Nat} (hk16 : k < 16) (_hbase : base ≤ 1024)
    (h : BitVec.ofNat 64 (base + 32 * k) + 32#64 = BitVec.ofNat 64 (base + 512)) : k = 15 := by
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega

private theorem idx24_add24_eq_384 {k : Nat} (hk16 : k < 16)
    (h : BitVec.ofNat 64 (24 * k) + 24#64 = 384#64) : k = 15 := by
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega

private theorem idx24_sub384_add24_eq_0 {k : Nat} (hk16 : k < 16)
    (h : BitVec.ofNat 64 (24 * k) - 384#64 + 24#64 = 0#64) : k = 15 := by
  have h1 : BitVec.ofNat 64 (24 * k) + 24#64 = 384#64 := by bv_omega
  exact idx24_add24_eq_384 hk16 h1

private theorem condNE_subsPState64_true {x y : BitVec 64} (hne : x ≠ y) :
    ConditionHolds .NE (subsPState64 x y) = true := by
  simp [ConditionHolds, subsPState64, AddWithCarry64, wp_norm, arm64_norm]
  bv_omega

private theorem condNE_addsPState64_false {x y : BitVec 64} (hz : x + y = 0#64) :
    ConditionHolds .NE (addsPState64 x y) = false := by
  simp [ConditionHolds, addsPState64, AddWithCarry64, wp_norm, arm64_norm]
  bv_omega

private theorem condNE_addsPState64_true {x y : BitVec 64} (hnz : x + y ≠ 0#64) :
    ConditionHolds .NE (addsPState64 x y) = true := by
  simp [ConditionHolds, addsPState64, AddWithCarry64, wp_norm, arm64_norm]
  bv_omega

@[expose] def LoopPres (s sf : State) : Prop :=
  sf.sp = s.sp ∧
  sf.spAligned = s.spAligned ∧
  sf.readReg64 .fp = s.readReg64 .fp ∧
  sf.readReg64 .x19 = s.readReg64 .x19 ∧
  sf.readReg64 .x20 = s.readReg64 .x20 ∧
  sf.readReg64 .x21 = s.readReg64 .x21 ∧
  sf.readReg64 .x22 = s.readReg64 .x22

theorem LoopPres.trans {s1 s2 s3 : State} (h12 : LoopPres s1 s2) (h23 : LoopPres s2 s3) :
    LoopPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

private theorem run_loop16 {P : Program} {entry exit : BitVec 64}
    {Inv : Nat → State → Prop} {Pre : Nat → SepProp} {Post : SepProp}
    (hiter : ∀ k, k < 16 → ∀ s, s.pc = entry → s.status = .Running → Inv k s →
      SepWP P (if k < 15 then entry else exit) s (Pre k)
        (fun s' P' => LoopPres s s' ∧
          ((k < 15 → Inv (k + 1) s' ∧ (P' ⊢ Pre (k + 1))) ∧
           (k = 15 → (P' ⊢ Post))))) :
    ∀ rem k, k + 1 + rem = 16 → ∀ s, s.pc = entry → s.status = .Running → Inv k s →
      SepWP P exit s (Pre k) (fun sf Pf => LoopPres s sf ∧ (Pf ⊢ Post)) := by
  intro rem; induction rem with
  | zero =>
    intro k hk s hpc hrun hinv
    have hk15 : k = 15 := by omega
    subst hk15
    have h := hiter 15 (by decide) s hpc hrun hinv
    simp only [Nat.lt_irrefl, ↓reduceIte] at h
    exact SepWP.mono h (fun _ _ _ _ ⟨hp, _, hpost⟩ => ⟨hp, hpost trivial⟩)
  | succ rem' ih =>
    intro k hk s hpc hrun hinv
    have hk15 : k < 15 := by omega
    have h := hiter k (by omega) s hpc hrun hinv
    simp only [hk15, ↓reduceIte] at h
    refine SepWP.seq h (fun sm Pm hpcm hrunm ⟨hp1, hlt, _⟩ => ?_)
    obtain ⟨hinvm, hPm⟩ := hlt trivial
    exact SepWP.weaken_pre hPm (SepWP.mono (ih (k + 1) (by omega) sm hpcm hrunm hinvm)
      (fun _ _ _ _ ⟨hp2, hPf⟩ => ⟨hp1.trans hp2, hPf⟩))

theorem seg5_loop1 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 25192)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = dst + 12#64)
    (hx20 : s.readReg64 .x20 = src)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25344) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (32 * k) ∧
      st.readReg64 .x9 = dst + BitVec.ofNat 64 (24 * k) + 12#64 ∧
      st.readReg64 .x20 = src ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx20k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx20, hv0⟩
  wp_steps 2
  refine step_ldp_polyChunk b 25200 25204 k _ hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode]) rfl ?_
  wp_step
  refine step_ser12_simd18 b 25208 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 25280 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx9k]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  wp_step
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx32_add32_eq (base := 0) hk16 (by decide) (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25340) (dst := b + BitVec.ofNat 64 25192)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      (by simp only [arm64_norm]; rfl)
      (by simpa [wp_norm, arm64_norm] using hcond)
      (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx9k]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx20k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25340) (dst := b + BitVec.ofNat 64 25344)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1])
      (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop2 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 25520)
    (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = 512#64)
    (hx8 : s.readReg64 .x8 = dst + 12#64)
    (hx10 : s.readReg64 .x10 = src - 512#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25672) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x9 = BitVec.ofNat 64 (512 + 32 * k) ∧
      st.readReg64 .x8 = dst + BitVec.ofNat 64 (24 * k) + 12#64 ∧
      st.readReg64 .x10 = src - 512#64 ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx9k, hx8k, hx10k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨by simpa using hx9, by simpa using hx8, hx10, hv0⟩
  wp_steps 2
  refine step_ldp_polyChunk b 25528 25532 k _ hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode]; clear * -; bv_omega) rfl ?_
  wp_step
  refine step_ser12_simd18 b 25536 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 25608 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  wp_step
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx32_add32_eq (base := 512) hk16 (by decide) (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25668) (dst := b + BitVec.ofNat 64 25520)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2]) (by simp only [arm64_norm]; rfl)
      (by simpa [wp_norm, arm64_norm] using hcond) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx8k]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx10k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25668) (dst := b + BitVec.ofNat 64 25672)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop3 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 25812)
    (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = 1024#64)
    (hx8 : s.readReg64 .x8 = dst + 12#64)
    (hx10 : s.readReg64 .x10 = src - 1024#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25964) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x9 = BitVec.ofNat 64 (1024 + 32 * k) ∧
      st.readReg64 .x8 = dst + BitVec.ofNat 64 (24 * k) + 12#64 ∧
      st.readReg64 .x10 = src - 1024#64 ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx9k, hx8k, hx10k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨by simpa using hx9, by simpa using hx8, hx10, hv0⟩
  wp_steps 2
  refine step_ldp_polyChunk b 25820 25824 k _ hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode]; clear * -; bv_omega) rfl ?_
  wp_step
  refine step_ser12_simd18 b 25828 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 25900 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1, hx8k]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  wp_step
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx32_add32_eq (base := 1024) hk16 (by decide) (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25960) (dst := b + BitVec.ofNat 64 25812)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2]) (by simp only [arm64_norm]; rfl)
      (by simpa [wp_norm, arm64_norm] using hcond) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx8k]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx10k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 25960) (dst := b + BitVec.ofNat 64 25964)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun2]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop4 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 26340)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = src + 16#64)
    (hx9 : s.readReg64 .x9 = 0#64 - 384#64)
    (hx20 : s.readReg64 .x20 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26496) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x9 = BitVec.ofNat 64 (24 * k) - 384#64 ∧
      st.readReg64 .x20 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx20k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨by simpa using hx8, hx9, hx20, hv0⟩
  refine step_ldp_polyChunk b 26340 26344 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx8k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 26360 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail15_off384 b 26432 k hk16 hpc1 hrun1
    (by simp [hregs1]; clear * -; bv_omega)
    (by simp [hregs1]; clear * -; bv_omega)
    hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (fun svc st' => by simp [execInstWithSvc, execAddSubImm, arm64_norm, wp_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s2 hpc2 hrun2 hsp2 _ hregs2 hpstate2 hv0_2
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_addsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_sub384_add24_eq_0 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 26492) (dst := b + BitVec.ofNat 64 26340)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2 .fp (by decide), hregs1],
        by simp [hregs2 .x19 (by decide), hregs1],
        by simp [hregs2 .x20 (by decide), hregs1],
        by simp [hregs2 .x21 (by decide), hregs1],
        by simp [hregs2 .x22 (by decide), hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2 .x8 (by decide), hregs1]; clear * -; bv_omega,
        by simp [hregs2 .x9 (by decide), hregs1]; clear * -; bv_omega,
        by simp [hregs2 .x20 (by decide), hregs1, hx20k],
        by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = false := by
      rw [hpstate2, hpstate1]
      exact condNE_addsPState64_false (by clear * -; bv_omega)
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 26492) (dst := b + BitVec.ofNat 64 26496)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2 .fp (by decide), hregs1],
        by simp [hregs2 .x19 (by decide), hregs1],
        by simp [hregs2 .x20 (by decide), hregs1],
        by simp [hregs2 .x21 (by decide), hregs1],
        by simp [hregs2 .x22 (by decide), hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop5 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 26680)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = src + 16#64)
    (hx19 : s.readReg64 .x19 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26832) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (24 * k) ∧
      st.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x19 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx19k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx19, hv0⟩
  refine step_ldp_polyChunk b 26680 26684 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx9k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 26700 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 26772 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_add24_eq_384 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 26828) (dst := b + BitVec.ofNat 64 26680)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx19k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 26828) (dst := b + BitVec.ofNat 64 26832)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop6 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 27016)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = src + 16#64)
    (hx19 : s.readReg64 .x19 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27168) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (24 * k) ∧
      st.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x19 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx19k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx19, hv0⟩
  refine step_ldp_polyChunk b 27016 27020 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx9k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 27036 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 27108 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_add24_eq_384 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27164) (dst := b + BitVec.ofNat 64 27016)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx19k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27164) (dst := b + BitVec.ofNat 64 27168)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop7 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 27424)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = src + 16#64)
    (hx10 : s.readReg64 .x10 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27576) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (24 * k) ∧
      st.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x10 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx10k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx10, hv0⟩
  refine step_ldp_polyChunk b 27424 27428 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx9k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 27444 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 27516 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_add24_eq_384 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27572) (dst := b + BitVec.ofNat 64 27424)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx10k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27572) (dst := b + BitVec.ofNat 64 27576)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop8 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 27756)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = src + 16#64)
    (hx20 : s.readReg64 .x20 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27908) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (24 * k) ∧
      st.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x20 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx20k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx20, hv0⟩
  refine step_ldp_polyChunk b 27756 27760 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx9k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 27776 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 27848 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_add24_eq_384 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27904) (dst := b + BitVec.ofNat 64 27756)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx20k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 27904) (dst := b + BitVec.ofNat 64 27908)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

theorem seg5_loop9 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (src dst : BitVec 64) (p : Poly16) (hbnd : PolyBounded16 3328 p) (F : SepProp)
    (s : State)
    (hpc : s.pc = b + BitVec.ofNat 64 28088)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = src + 16#64)
    (hx20 : s.readReg64 .x20 = dst)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 28240) s
      (PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F)
      (fun sf Pf => LoopPres s sf ∧
        (Pf ⊢ PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 16) ∗ F)) := by
  have _ : b = blkPl05.base := hb
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ memRegion dst 384 ∗ F ⊢
      PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p 0) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * 0)) (384 - 24 * 0) ∗ F by
    simp [Seg5Ser.ser12Prefix_zero, pointsToBytes_nil]; sep_frame) ?_
  refine run_loop16
    (Inv := fun k st => st.readReg64 .x8 = BitVec.ofNat 64 (24 * k) ∧
      st.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 ∧
      st.readReg64 .x20 = dst ∧ st.readVReg128 0#5 = dup8x16 3329#16)
    (Pre := fun k => PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
    (fun k hk16 st hpct hrunt ⟨hx8k, hx9k, hx20k, hv0k⟩ => ?_)
    15 0 rfl s hpc hrun ⟨hx8, by simpa using hx9, hx20, hv0⟩
  refine step_ldp_polyChunk b 28088 28092 k _ hk16
    hpct hrunt (by simp only [arm64_norm]; rfl) rfl
    (by simp [evalAddrMode, arm64_norm, hx9k]) rfl ?_
  wp_steps 4
  refine step_ser12_simd18 b 28108 k p hbnd hk16
    (by simp [wp_norm, arm64_norm]) (by simp [hrunt]) (by simp [hv0k]) (by simp) (by simp)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
  intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 hv0_1 hv1_1 hv3_1 _
  refine SepWP.weaken_pre (show PolyMem src (polyVecNat p) ∗ (dst ↦ₛ ser12Prefix p k) ∗
      memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
    (dst ↦ₛ ser12Prefix p k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
      (PolyMem src (polyVecNat p) ∗ F) by sep_frame) ?_
  refine step_ser12_tail14 b 28180 k _ _ _ _ _ _ _ _ hk16 hpc1 hrun1 hv1_1 hv3_1
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1])
    (fun st' hr => by simp [evalAddrMode, hr, hregs1]) ?_
  intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 hv0_2 _
  simp only [Nat.reduceAdd] at hpc2
  by_cases hk15 : k < 15
  · simp only [hk15, ↓reduceIte]
    have hcond : ConditionHolds .NE s2.pstate = true := by
      rw [hpstate2, hpstate1]
      refine condNE_subsPState64_true (fun heq => ?_)
      have hk_eq : k = 15 := idx24_add24_eq_384 hk16 (by simpa using heq)
      omega
    refine step_bCond_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 28236) (dst := b + BitVec.ofNat 64 28088)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl) hcond (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun _ => ⟨⟨by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1]; clear * -; bv_omega,
        by simp [hregs2, hregs1, hx20k], by simp [hv0_2, hv0_1, hv0k]⟩, by sep_frame⟩,
      fun h15 => by omega⟩
  · have hkeq : k = 15 := by omega
    subst hkeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (P := blkPC05.rebase b (fun _ => none))
      (pc := b + BitVec.ofNat 64 28236) (dst := b + BitVec.ofNat 64 28240)
      hpc2 hrun2 (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpstate2, hpstate1]) (by clear * -; bv_omega) ?_
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
      ⟨⟨by simp [hsp2, hsp1], by simp [State.spAligned, hsp2, hsp1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
        by simp [hregs2, hregs1], by simp [hregs2, hregs1]⟩,
      fun hlt => False.elim hlt,
      fun _ => by
        simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl, memRegion_zero]
        sep_frame⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops
