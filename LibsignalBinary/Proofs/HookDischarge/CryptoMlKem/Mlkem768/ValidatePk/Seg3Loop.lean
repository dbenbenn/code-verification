/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Step

/-! # `validate_pk_bytes` (`B21`) — Three 16-Iteration `serialize_12` Loops (`Role::Proof`). -/

set_option autoImplicit false
public section
namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Loop

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (neonSerialize12Mix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq blk21_tree_size blkLib21 blkPC21 blkPl21 blkPlaceable21 blkTree21 reencodePoly384)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (UnspilledSaved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  deserVec8h reducedPolyBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd (
  reencodePolyPrefix reencodePolyPrefix_16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Step (
  step_ldp_deserChunk step_ser12_simd18 step_ser12_tail14)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21
  [0x04c8 → 0x055c, 0x0604 → 0x0698, 0x0740 → 0x07d4]
end

attribute [local irreducible] blkPC21 deserVec8h neonSerialize12Mix

private theorem idx24_add24_eq_384 {k : Nat} (hk16 : k < 16)
    (h : BitVec.ofNat 64 (24 * k) + 24#64 = 384#64) : k = 15 := by
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega

theorem seg3_loop1 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x04c8#64 →
        s.status = .Running →
        s.readReg64 .x8 = BitVec.ofNat 64 (24 * k) →
        s.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 →
        s.readReg64 .x10 = dst →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0560#64) s
          ((src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePoly384 bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx10, hus => by
    have hk16 : k < 16 := by omega
    refine step_ldp_deserChunk b 0x04c8 0x04cc k _ hk16
      hpc hrun (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx9]) rfl ?_
    wp_steps 4
    refine step_ser12_simd18 b 0x04dc k bs
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp) (by simp)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 _ hv1_1 hv3_1 hvcs1
    refine SepWP.weaken_pre (show (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
      (dst ↦ₛ reencodePolyPrefix bs k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
        ((src ↦ₛ reducedPolyBytes bs) ∗ F) by sep_frame) ?_
    refine step_ser12_tail14 b 0x0524 k .x11 hk16 (by decide) hpc1 hrun1
      (by rw [hregs1]; simp) hv1_1 hv3_1
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 _ hvcs2
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.weaken_pre (by sep_frame)
          (SepWP.mono
            (seg3_loop1 s0 src dst bs F rem' (k + 1) (by omega) _
              (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1, hx10])
              ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
               by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
               by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩) ?_)
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hus_f, hPf⟩
        exact ⟨by simpa [hsp2, hsp1] using hsp_f,
          by simpa [hregs2, hregs1] using hx19_f,
          by simpa [hregs2, hregs1] using hx20_f,
          by simpa [hregs2, hregs1] using hx21_f, hus_f, hPf⟩
    · have hk15 : k = 15 := idx24_add24_eq_384 hk16 (by simpa using hne)
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
        ⟨by simp [hsp2, hsp1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
         by simp [hregs2, hregs1],
         ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
          by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
          by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl,
        memRegion_zero, reencodePolyPrefix_16]
      sep_frame

theorem seg3_loop2 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x0604#64 →
        s.status = .Running →
        s.readReg64 .x8 = BitVec.ofNat 64 (24 * k) →
        s.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 →
        s.readReg64 .x21 = dst →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x069c#64) s
          ((src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePoly384 bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx21, hus => by
    have hk16 : k < 16 := by omega
    refine step_ldp_deserChunk b 0x0604 0x0608 k _ hk16
      hpc hrun (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx9]) rfl ?_
    wp_steps 4
    refine step_ser12_simd18 b 0x0618 k bs
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp) (by simp)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 _ hv1_1 hv3_1 hvcs1
    refine SepWP.weaken_pre (show (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
      (dst ↦ₛ reencodePolyPrefix bs k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
        ((src ↦ₛ reducedPolyBytes bs) ∗ F) by sep_frame) ?_
    refine step_ser12_tail14 b 0x0660 k .x10 hk16 (by decide) hpc1 hrun1
      (by rw [hregs1]; simp) hv1_1 hv3_1
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 _ hvcs2
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.weaken_pre (by sep_frame)
          (SepWP.mono
            (seg3_loop2 s0 src dst bs F rem' (k + 1) (by omega) _
              (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1, hx21])
              ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
               by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
               by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩) ?_)
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hus_f, hPf⟩
        exact ⟨by simpa [hsp2, hsp1] using hsp_f,
          by simpa [hregs2, hregs1] using hx19_f,
          by simpa [hregs2, hregs1] using hx20_f,
          by simpa [hregs2, hregs1] using hx21_f, hus_f, hPf⟩
    · have hk15 : k = 15 := idx24_add24_eq_384 hk16 (by simpa using hne)
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
        ⟨by simp [hsp2, hsp1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
         by simp [hregs2, hregs1],
         ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
          by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
          by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl,
        memRegion_zero, reencodePolyPrefix_16]
      sep_frame

theorem seg3_loop3 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x0740#64 →
        s.status = .Running →
        s.readReg64 .x8 = BitVec.ofNat 64 (24 * k) →
        s.readReg64 .x9 = src + BitVec.ofNat 64 (32 * k) + 16#64 →
        s.readReg64 .x21 = dst →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x07d8#64) s
          ((src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePoly384 bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx21, hus => by
    have hk16 : k < 16 := by omega
    refine step_ldp_deserChunk b 0x0740 0x0744 k _ hk16
      hpc hrun (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx9]) rfl ?_
    wp_steps 4
    refine step_ser12_simd18 b 0x0754 k bs
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by simp) (by simp)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s1 hpc1 hrun1 hsp1 hregs1 hpstate1 _ hv1_1 hv3_1 hvcs1
    refine SepWP.weaken_pre (show (src ↦ₛ reducedPolyBytes bs) ∗ (dst ↦ₛ reencodePolyPrefix bs k) ∗
        memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗ F ⊢
      (dst ↦ₛ reencodePolyPrefix bs k) ∗ memRegion (dst + BitVec.ofNat 64 (24 * k)) (384 - 24 * k) ∗
        ((src ↦ₛ reducedPolyBytes bs) ∗ F) by sep_frame) ?_
    refine step_ser12_tail14 b 0x079c k .x10 hk16 (by decide) hpc1 hrun1
      (by rw [hregs1]; simp) hv1_1 hv3_1
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    intro s2 hpc2 hrun2 hsp2 hregs2 hpstate2 _ hvcs2
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.weaken_pre (by sep_frame)
          (SepWP.mono
            (seg3_loop3 s0 src dst bs F rem' (k + 1) (by omega) _
              (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1]; clear * -; bv_omega)
              (by simp [hregs2, hregs1, hx21])
              ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
               by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
               by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩) ?_)
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hus_f, hPf⟩
        exact ⟨by simpa [hsp2, hsp1] using hsp_f,
          by simpa [hregs2, hregs1] using hx19_f,
          by simpa [hregs2, hregs1] using hx20_f,
          by simpa [hregs2, hregs1] using hx21_f, hus_f, hPf⟩
    · have hk15 : k = 15 := idx24_add24_eq_384 hk16 (by simpa using hne)
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun2])
        ⟨by simp [hsp2, hsp1], by simp [hregs2, hregs1], by simp [hregs2, hregs1],
         by simp [hregs2, hregs1],
         ⟨by simp [hregs2, hregs1, hus.1], by simp [hregs2, hregs1, hus.2.1],
          by simp [hregs2, hregs1, hus.2.2.1], by simp [hregs2, hregs1, hus.2.2.2.1],
          by simp [hvcs2, hvcs1, isCalleeSavedVReg, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 384 - 24 * 16 = 0 from rfl,
        memRegion_zero, reencodePolyPrefix_16]
      sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Loop
