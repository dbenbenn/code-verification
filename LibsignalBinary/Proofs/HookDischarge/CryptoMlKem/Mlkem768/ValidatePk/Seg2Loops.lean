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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop

/-!
# `validate_pk_bytes` (`B21`) — Three 16-Iteration `deserialize_12` Loops

Proves the three 16-iteration AdvSIMD 12-bit polynomial deserialization + Barrett-check loops
in `validate_pk_bytes`:
- `seg2_loop1` (`+0x01d8 .. +0x0238`)
- `seg2_loop2` (`+0x02f0 .. +0x0350`)
- `seg2_loop3` (`+0x03c4 .. +0x0424`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loops

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq blk21_tree_size blkLib21 blkPC21 blkPl21 blkPlaceable21 blkTree21
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (UnspilledSaved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  deserVec8h neonDeser12 reducedPolyBytes reducedPolyPrefix
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  deserTmp4 neonDeser12_raw rawHi32 rawLo64 step_deser12_simd12 step_ld1S2_raw step_ldrD64_raw
  step_stp_deserChunk
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21
  [0x01d8 → 0x0234, 0x02f0 → 0x034c, 0x03c4 → 0x0420]
end

attribute [local irreducible] blkPC21 neonDeser12 deserVec8h

theorem seg2_loop1 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x01d8#64 →
        s.status = .Running →
        s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
        s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) →
        s.readReg64 .x22 = dst →
        s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
        s.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 →
        s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0238#64) s
          ((src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            sf.readReg64 .x22 = dst ∧
            sf.readReg64 .x23 = s.readReg64 .x23 ∧
            sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ (src ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyBytes bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx22, hv0, hv1, hv6, hus => by
    have hk16 : k < 16 := by omega
    refine step_ldrD64_raw b 0x01d8 0x01dc 2#5 _ (24 * k)
      hpc hrun (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx9]) (by omega) rfl ?_
    refine step_ldrD64_raw b 0x01dc 0x01e0 3#5 _ (24 * k + 12)
      rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx9]; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 3
    refine step_ld1S2_raw b 0x01ec 0x01f0 .x10 2#5 (24 * k)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ld1S2_raw b 0x01f0 0x01f4 .x11 3#5 (24 * k + 12)
      rfl (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 3
    refine step_deser12_simd12 b 0x0200
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    refine step_stp_deserChunk b 0x0230 0x0234 k _ hk16
      rfl (by simp [hrun])
      (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode])
      (by simpa using neonDeser12_raw bs (24 * k))
      (by simpa using neonDeser12_raw bs (24 * k + 12))
      rfl ?_
    intro m'
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.mono
          (seg2_loop1 s0 src dst bs F hbs rem' (k + 1) (by omega) _
            (by simp [wp_norm, arm64_norm]) (by simp [hrun])
            (by simp; clear * -; bv_omega)
            (by simp; clear * -; bv_omega)
            (by simp [hx22]) (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
            ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
              by simp [calleeSavedVRegs, hus.2.2.2.2]⟩) ?_
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hv6_f, hus_f, hPf⟩
        exact ⟨by simpa using hsp_f, by simpa using hx19_f, by simpa using hx20_f,
          by simpa using hx21_f, hx22_f, by simpa using hx23_f, hv6_f, hus_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa using hne
        have hnat := congrArg BitVec.toNat hbv
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun])
        ⟨by simp, by simp, by simp, by simp, by simp [hx22], by simp, by simp [hv6],
          ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
            by simp [calleeSavedVRegs, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 512 - 32 * 16 = 0 from rfl,
        memRegion_zero, reducedPolyBytes]
      sep_frame

private theorem idx24_sub360_eq_zero {k : Nat} (hk16 : k < 16)
    (h : BitVec.ofNat 64 (24 * k) - 360#64 = 0#64) : k = 15 := by
  bv_omega

theorem seg2_loop2 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (pkBase dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x02f0#64 →
        s.status = .Running →
        s.readReg64 .x8 = dst + BitVec.ofNat 64 (32 * k) + 16#64 →
        s.readReg64 .x9 = BitVec.ofNat 64 (24 * k) - 384#64 →
        s.readReg64 .x10 = pkBase →
        s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
        s.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 →
        s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0350#64) s
          (((pkBase + 384#64) ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            sf.readReg64 .x23 = s.readReg64 .x23 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ ((pkBase + 384#64) ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyBytes bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx10, hv0, hv1, hv6, hus => by
    have hk16 : k < 16 := by omega
    wp_steps 3
    refine step_ldrD64_raw b 0x02fc 0x0300 2#5 _ (24 * k)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode]; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ldrD64_raw b 0x0300 0x0304 3#5 _ (24 * k + 12)
      rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode]; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 2
    refine step_ld1S2_raw b 0x030c 0x0310 .x12 2#5 (24 * k)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ld1S2_raw b 0x0310 0x0314 .x11 3#5 (24 * k + 12)
      rfl (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    refine step_deser12_simd12 b 0x0314
      rfl (by simp [hrun])
      (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    refine step_stp_deserChunk b 0x0344 0x0348 k _ hk16
      rfl (by simp [hrun])
      (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx8])
      (by simpa using neonDeser12_raw bs (24 * k))
      (by simpa using neonDeser12_raw bs (24 * k + 12))
      rfl ?_
    intro m'
    wp_steps 2
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.mono
          (seg2_loop2 s0 pkBase dst bs F hbs rem' (k + 1) (by omega) _
            (by simp [wp_norm, arm64_norm]) (by simp [hrun])
            (by simp; clear * -; bv_omega)
            (by simp; clear * -; bv_omega)
            (by simp [hx10]) (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
            ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
              by simp [calleeSavedVRegs, hus.2.2.2.2]⟩) ?_
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hx23_f, hus_f, hPf⟩
        exact ⟨by simpa using hsp_f, by simpa using hx19_f, by simpa using hx20_f,
          by simpa using hx21_f, by simpa using hx23_f, hus_f, hPf⟩
    · have hk15 : k = 15 :=
        idx24_sub360_eq_zero hk16 (by simpa using hne)
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun])
        ⟨by simp, by simp, by simp, by simp, by simp,
          ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
            by simp [calleeSavedVRegs, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 512 - 32 * 16 = 0 from rfl,
        memRegion_zero, reducedPolyBytes]
      sep_frame

theorem seg2_loop3 [MlKemPlacement] {b : BitVec 64}
    (s0 : State) (pkBase dst : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 →
      ∀ s : State,
        s.pc = b + 0x03c4#64 →
        s.status = .Running →
        s.readReg64 .x8 = dst + BitVec.ofNat 64 (32 * k) + 16#64 →
        s.readReg64 .x9 = BitVec.ofNat 64 (24 * k) - 384#64 →
        s.readReg64 .x10 = pkBase →
        s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
        s.readVReg128 1#5 = 0x0d010d010d010d010d010d010d010d01#128 →
        s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
        UnspilledSaved s0 s →
        SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0424#64) s
          (((pkBase + 768#64) ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyPrefix bs k) ∗
            memRegion (dst + BitVec.ofNat 64 (32 * k)) (512 - 32 * k) ∗ F)
          (fun sf Pf =>
            sf.sp = s.sp ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = s.readReg64 .x20 ∧
            sf.readReg64 .x21 = s.readReg64 .x21 ∧
            sf.readReg64 .x23 = s.readReg64 .x23 ∧
            UnspilledSaved s0 sf ∧
            (Pf ⊢ ((pkBase + 768#64) ↦ₛ bs) ∗ (dst ↦ₛ reducedPolyBytes bs) ∗ F))
  | rem, k, hkrem, s, hpc, hrun, hx8, hx9, hx10, hv0, hv1, hv6, hus => by
    have hk16 : k < 16 := by omega
    wp_steps 3
    refine step_ldrD64_raw b 0x03d0 0x03d4 2#5 _ (24 * k)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode]; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ldrD64_raw b 0x03d4 0x03d8 3#5 _ (24 * k + 12)
      rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode]; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 2
    refine step_ld1S2_raw b 0x03e0 0x03e4 .x12 2#5 (24 * k)
      (by simp [wp_norm, arm64_norm]) (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ld1S2_raw b 0x03e4 0x03e8 .x11 3#5 (24 * k + 12)
      rfl (by simp [hrun])
      (by simp only [arm64_norm]) rfl
      (by simp; clear * -; bv_omega) (by omega) rfl ?_
    refine step_deser12_simd12 b 0x03e8
      rfl (by simp [hrun])
      (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) ?_
    refine step_stp_deserChunk b 0x0418 0x041c k _ hk16
      rfl (by simp [hrun])
      (by simp only [arm64_norm]; rfl) rfl
      (by simp [evalAddrMode, hx8])
      (by simpa using neonDeser12_raw bs (24 * k))
      (by simpa using neonDeser12_raw bs (24 * k + 12))
      rfl ?_
    intro m'
    wp_steps 2
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp at hne
      · refine SepWP.mono
          (seg2_loop3 s0 pkBase dst bs F hbs rem' (k + 1) (by omega) _
            (by simp [wp_norm, arm64_norm]) (by simp [hrun])
            (by simp; clear * -; bv_omega)
            (by simp; clear * -; bv_omega)
            (by simp [hx10]) (by simp [hv0]) (by simp [hv1]) (by simp [hv6])
            ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
              by simp [calleeSavedVRegs, hus.2.2.2.2]⟩) ?_
        rintro sf Pf _ _ ⟨hsp_f, hx19_f, hx20_f, hx21_f, hx23_f, hus_f, hPf⟩
        exact ⟨by simpa using hsp_f, by simpa using hx19_f, by simpa using hx20_f,
          by simpa using hx21_f, by simpa using hx23_f, hus_f, hPf⟩
    · have hk15 : k = 15 :=
        idx24_sub360_eq_zero hk16 (by simpa using hne)
      subst hk15
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [hrun])
        ⟨by simp, by simp, by simp, by simp, by simp,
          ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2.1],
            by simp [calleeSavedVRegs, hus.2.2.2.2]⟩, ?_⟩
      simp only [show 15 + 1 = 16 from rfl, show 512 - 32 * 16 = 0 from rfl,
        memRegion_zero, reducedPolyBytes]
      sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loops
