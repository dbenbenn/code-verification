/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Curve-Model Doubling and Niels Addition/Subtraction Proofs

Machine-code proofs in `dalekCliMultiLib` for `ProjectivePoint::double` (`B13`),
`EdwardsPoint` addition/subtraction with `ProjectiveNielsPoint` (`B28`, `B29`), and
`AffineNielsPoint` (`B31`, `B32`, mutable and read-only right-hand side).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels2

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul fpNeg fpSq fpPow)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  ProjectivePointDoubleOk EdwardsPointAddProjNielsOk EdwardsPointSubProjNielsOk
  EdwardsPointAddAffineNielsOk EdwardsPointAddAffineNielsRoOk
  EdwardsPointSubAffineNielsOk EdwardsPointSubAffineNielsRoOk
  fe51LimbsBoundedAt fe51ValAt edExtOfBytes
  edProjDouble edAddProjNiels edSubProjNiels edAddAffineNiels edSubAffineNiels
  fpPow_two_eq_fpSq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add pointsToBytesRO_take_drop
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_focus_bytes sepWP_unfocus_bytes
  sepWP_have_bytes sepWP_abstract_bytes
  fe51LimbsBounded_slice_of_at
  readLE_write64_self' readLE_write64_ne write64_length_eq
  fe51Add_bounded fe51Add_val_mod fe51Shl1_bounded fe51Shl1_val_mod
  fe51Reduce_bounded fe51Reduce_val_mod
  bv64_add_bias0_sub bv64_bias0_add_sub fe51Sub_val_mod
  fold_fe51ValOfBytes fold_fe51ValAt fe51ValOfBytes_slice mul_mod_eq_fpMul
  fe51_write5_add_post fe51_write5_sub_reduce_post
  edAddNiels_epilogue_post edSubNiels_epilogue_post)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51 (
  fe51_pow2k_ok fe51_mul_ok fe51_mul_ro_right_ok)

arm64_proof_prelude

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 13 dalekCliMultiLib DalekCliPlacement 144 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl13_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl13.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 28 dalekCliMultiLib DalekCliPlacement 156 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl28_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl28.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 29 dalekCliMultiLib DalekCliPlacement 156 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl29_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl29.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 31 dalekCliMultiLib DalekCliPlacement 152 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl31_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl31.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 32 dalekCliMultiLib DalekCliPlacement 152 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl32_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl32.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

/-! ## Read-Only Byte-Window Focus/Unfocus Helpers (`B31` & `B32` RO) -/

private def pointsToBytesRORest (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat) : SepProp :=
  (base ↦ᵣ buf.take off) ∗ ((base + BitVec.ofNat 64 (off + n)) ↦ᵣ buf.drop (off + n))

private theorem pointsToBytesRO_focus (base : BitVec 64) (buf : List (BitVec 8)) (off n : Nat)
    (hlen : off + n ≤ buf.length) :
    (base ↦ᵣ buf) =
      ((base + BitVec.ofNat 64 off) ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗
      pointsToBytesRORest base buf off n := by
  unfold pointsToBytesRORest ProofLib.ByteSlice.slice
  rw [pointsToBytesRO_take_drop base off buf (by omega),
      pointsToBytesRO_take_drop (base + BitVec.ofNat 64 off) n (buf.drop off)
        (by simp [List.length_drop]; omega),
      List.drop_drop, BitVec.add_assoc, ← BitVec.ofNat_add]
  sep_ac_rfl

private theorem sepWP_focus_ro_bytes (base ptr : BitVec 64) (off n : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (base ↦ᵣ buf) ∗ P := by sep_frame)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : (ProofLib.ByteSlice.slice buf off n).length = n →
      SepWP prog target_pc s
        (((ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗
          pointsToBytesRORest base buf off n) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  have hfocus : (base ↦ᵣ buf) =
      (ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRORest base buf off n := by
    subst hptr
    exact pointsToBytesRO_focus base buf off n hlen
  rw [hfocus]
  exact hnext (ByteSlice.slice_length buf off n hlen)

private theorem sepWP_unfocus_ro_bytes (base ptr : BitVec 64) (off n : Nat)
    {buf : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full =
      ((ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗
       pointsToBytesRORest base buf off n) ∗ P := by sep_frame)
    (hlen : off + n ≤ buf.length := by exact le_length_of_hasLenGe)
    (hptr : ptr = base + BitVec.ofNat 64 off := by
      simp (disch := decide) only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, sub_ofNat64_add, Nat.reduceSub])
    (hnext : SepWP prog target_pc s ((base ↦ᵣ buf) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf]
  have hunfocus :
      ((ptr ↦ᵣ ProofLib.ByteSlice.slice buf off n) ∗ pointsToBytesRORest base buf off n) =
      (base ↦ᵣ buf) := by
    subst hptr
    exact (pointsToBytesRO_focus base buf off n hlen).symm
  rw [hunfocus]
  exact hnext

public section

/-! ## 1. `ProjectivePoint::double` (`B13`, 144w) -/

set_option maxHeartbeats 800000 in
theorem projective_point_double_ok : ProjectivePointDoubleOk := by
  intro _
  apply dalekCaller_ok dalekCliPC13 dalekCliPl13
  intro b hb hbase
  wp_init
  have hout_len : a_2.length = 160 := by assumption
  have hself_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  haveI : HasLenGe a_2 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 96 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  haveI : HasLenGe s_120 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: pow2k(self + 0, 1) -> sp + 0
  apply sepWP_focus_bytes a a 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself0
  wp_dalek_call fe51_pow2k_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a a 0 40
  norm_sf 96
  -- Call 2: pow2k(self + 40, 1) -> sp + 40
  wp_steps
  apply sepWP_focus_bytes a (a + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself40
  wp_dalek_call fe51_pow2k_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a (a + 40#64) 40 40
  norm_sf 96
  -- Call 3: pow2k(self + 80, 1) -> sp + 80
  wp_steps
  apply sepWP_focus_bytes a (a + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself80
  wp_dalek_call fe51_pow2k_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a (a + 80#64) 80 40
  norm_sf 96
  -- Step to Call 4: pow2k(sp + 120, 1) -> sp + 160
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_have_bytes (s0.sp - 184#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_rest 40 % p25519) (fe51ValAt a_rest 0 % p25519))
  · unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hs_120, Nat.min_eq_left]
    exact ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hself40 hself0⟩,
      fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hself40 hself0⟩
  intro ⟨⟨hs120_len, _, _, _, _, _⟩, hbuf120_v⟩
  wp_dalek_call fe51_pow2k_ok
  have hw3_b : fe51LimbsBounded w_3 (2 ^ 52) := by assumption
  have hw3_len : w_3.length = 40 := hw3_b.1
  clean_prev_sf
  norm_sf 96
  -- Epilogue: step from +0x0b4 to ret (+0x23c)
  wp_steps
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 96 304
  apply sepWP_have_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
      edExtOfBytes res_bs =
        edProjDouble (fe51ValAt a_rest 0) (fe51ValAt a_rest 40) (fe51ValAt a_rest 80))
  · have hadd_b :
        (ByteSlice.readLE w 0 8 + ByteSlice.readLE w_1 0 8).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w 8 8 + ByteSlice.readLE w_1 8 8).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w 16 8 + ByteSlice.readLE w_1 16 8).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w 24 8 + ByteSlice.readLE w_1 24 8).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w 32 8 + ByteSlice.readLE w_1 32 8).toNat < 2 ^ 53 :=
      fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 53) hw_b.2 hw1_b.2
    have hadd_v :
        fe51Val
          (ByteSlice.readLE w 0 8 + ByteSlice.readLE w_1 0 8)
          (ByteSlice.readLE w 8 8 + ByteSlice.readLE w_1 8 8)
          (ByteSlice.readLE w 16 8 + ByteSlice.readLE w_1 16 8)
          (ByteSlice.readLE w 24 8 + ByteSlice.readLE w_1 24 8)
          (ByteSlice.readLE w 32 8 + ByteSlice.readLE w_1 32 8) % p25519 =
        fpAdd (fe51ValOfBytes w % p25519) (fe51ValOfBytes w_1 % p25519) :=
      fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hw_b.2 hw1_b.2
    have hshl_b :
        (ByteSlice.readLE w_2 0 8 <<< 1).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w_2 8 8 <<< 1).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w_2 16 8 <<< 1).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w_2 24 8 <<< 1).toNat < 2 ^ 53 ∧
        (ByteSlice.readLE w_2 32 8 <<< 1).toNat < 2 ^ 53 :=
      fe51Shl1_bounded _ _ _ _ _ (2 ^ 53) hw2_b.2
    have hshl_v :
        fe51Val
          (ByteSlice.readLE w_2 0 8 <<< 1)
          (ByteSlice.readLE w_2 8 8 <<< 1)
          (ByteSlice.readLE w_2 16 8 <<< 1)
          (ByteSlice.readLE w_2 24 8 <<< 1)
          (ByteSlice.readLE w_2 32 8 <<< 1) % p25519 =
        fpAdd (fe51ValOfBytes w_2 % p25519) (fe51ValOfBytes w_2 % p25519) :=
      fe51Shl1_val_mod _ _ _ _ _ hw2_b.2
    unfold fe51LimbsBoundedAt edExtOfBytes
    simp (disch := decide) only [fe51ValAt, readLE_write64_self', readLE_write64_ne,
      write64_length_eq, hout_len, Nat.min_eq_left]
    refine ⟨trivial, fe51Reduce_bounded _ _ _ _ _, hadd_b, fe51Reduce_bounded _ _ _ _ _,
      fe51Reduce_bounded _ _ _ _ _, ?_⟩
    dsimp only [edProjDouble]
    rw [fe51Reduce_val_mod, fe51Reduce_val_mod, fe51Reduce_val_mod,
        bv64_add_bias0_sub, bv64_bias0_add_sub,
        fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw3_b.2 hadd_b,
        fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hshl_b (fe51Reduce_bounded _ _ _ _ _),
        fe51Reduce_val_mod,
        fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hw1_b.2 hw_b.2]
    rw [hadd_v, hshl_v, fold_fe51ValOfBytes w, fold_fe51ValOfBytes w_1,
        fold_fe51ValOfBytes w_3,
        fold_fe51ValAt a_rest 0, fold_fe51ValAt a_rest 40, fold_fe51ValAt a_rest 80,
        hpost_3, hbuf120_v, hpost, hpost_1, hpost_2]
    simp only [fe51ValOfBytes_slice, fpPow_two_eq_fpSq]
    unfold VerifiedLibraries.Common.fpAdd
    rw [Nat.add_comm (fe51ValAt a_rest 40 % p25519) (fe51ValAt a_rest 0 % p25519)]
  intro ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  wp_done

/-! ## 2. `<&EdwardsPoint as Add<&ProjectiveNielsPoint>>::add` (`B28`, 156w) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_add_proj_niels_ok : EdwardsPointAddProjNielsOk := by
  intro _
  apply dalekCaller_ok dalekCliPC28 dalekCliPl28
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 160 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 54) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  have hother120 : fe51LimbsBoundedAt a_rest 120 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 160 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 352
  apply sepWP_peel_stack_bytes s0.sp 352 8 344; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 344 40 304; intro s_8 hs_8
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_48 hs_48
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_88 hs_88
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_128 hs_128
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_168 hs_168
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_208 hs_208
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul(sp + 8, other + 0) -> sp + 88 (s0.sp - 264)
  apply sepWP_abstract_bytes (s0.sp - 344#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_8 a_4 hs_8 hself0 hself40)
  intro s8' ⟨⟨hs8_len, _, _, _, _, _⟩, hbuf8_v⟩
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_48 a_4 hs_48 hself0 hself40)
  intro s48' ⟨⟨hs48_len, _, _, _, _, _⟩, hbuf48_v⟩
  apply sepWP_focus_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 2: mul(sp + 48, other + 40) -> sp + 128 (s0.sp - 224)
  wp_steps
  apply sepWP_focus_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 3: mul(self + 120, other + 120) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_bytes a_2 (a_2 + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother120
  wp_dalek_call fe51_mul_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 120#64) 120 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Call 4: mul(self + 80, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself80
  apply sepWP_focus_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ok
  have hw3_b : fe51LimbsBounded w_3 (2 ^ 52) := by assumption
  have hw3_len : w_3.length = 40 := hw3_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 80#64) 80 40
  norm_sf 224
  -- Epilogue: step from +0x114 to ret (+0x26c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf8_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf48_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2 hpost_3
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
      edExtOfBytes res_bs =
        edAddProjNiels (edExtOfBytes a_4) (edExtOfBytes a_rest))
    (hQ := edAddNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hw3_b.2
      hpost hpost_1 hpost_2 hpost_3)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_unpeel_stack_bytes s0.sp 344 40 304
  apply sepWP_unpeel_stack_bytes s0.sp 352 8 344
  apply sepWP_merge_stack_callee 224 352
  wp_done

/-! ## 3. `<&EdwardsPoint as Sub<&ProjectiveNielsPoint>>::sub` (`B29`, 156w) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_sub_proj_niels_ok : EdwardsPointSubProjNielsOk := by
  intro _
  apply dalekCaller_ok dalekCliPC29 dalekCliPl29
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 160 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 54) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  have hother120 : fe51LimbsBoundedAt a_rest 120 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 160 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 352
  apply sepWP_peel_stack_bytes s0.sp 352 8 344; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 344 40 304; intro s_8 hs_8
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_48 hs_48
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_88 hs_88
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_128 hs_128
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_168 hs_168
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_208 hs_208
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul(sp + 8, other + 40) -> sp + 88 (s0.sp - 264)
  apply sepWP_abstract_bytes (s0.sp - 344#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_8 a_4 hs_8 hself0 hself40)
  intro s8' ⟨⟨hs8_len, _, _, _, _, _⟩, hbuf8_v⟩
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_48 a_4 hs_48 hself0 hself40)
  intro s48' ⟨⟨hs48_len, _, _, _, _, _⟩, hbuf48_v⟩
  apply sepWP_focus_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 2: mul(sp + 48, other + 0) -> sp + 128 (s0.sp - 224)
  wp_steps
  apply sepWP_focus_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 3: mul(self + 120, other + 120) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_bytes a_2 (a_2 + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother120
  wp_dalek_call fe51_mul_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 120#64) 120 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Call 4: mul(self + 80, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself80
  apply sepWP_focus_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ok
  have hw3_b : fe51LimbsBounded w_3 (2 ^ 52) := by assumption
  have hw3_len : w_3.length = 40 := hw3_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 80#64) 80 40
  norm_sf 224
  -- Epilogue: step from +0x114 to ret (+0x26c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf8_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf48_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2 hpost_3
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
      edExtOfBytes res_bs =
        edSubProjNiels (edExtOfBytes a_4) (edExtOfBytes a_rest))
    (hQ := edSubNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hw3_b.2
      hpost hpost_1 hpost_2 hpost_3)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_unpeel_stack_bytes s0.sp 344 40 304
  apply sepWP_unpeel_stack_bytes s0.sp 352 8 344
  apply sepWP_merge_stack_callee 224 352
  wp_done

/-! ## 4. `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`B31`, 152w, RW & RO) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_add_affine_niels_ok : EdwardsPointAddAffineNielsOk := by
  intro _
  apply dalekCaller_ok dalekCliPC31 dalekCliPl31
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 52) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul(sp + 0, other + 0) -> sp + 80 (s0.sp - 224)
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_0 a_4 hs_0 hself0 hself40)
  intro s0' ⟨⟨hs0_len, _, _, _, _, _⟩, hbuf0_v⟩
  apply sepWP_abstract_bytes (s0.sp - 264#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_40 a_4 hs_40 hself0 hself40)
  intro s40' ⟨⟨hs40_len, _, _, _, _, _⟩, hbuf40_v⟩
  apply sepWP_focus_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 2: mul(sp + 40, other + 40) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 3: mul(self + 120, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Epilogue: step from +0x104 to ret (+0x25c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf0_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf40_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
      edExtOfBytes res_bs =
        edAddAffineNiels (edExtOfBytes a_4)
          (fe51ValAt a_rest 0 % p25519)
          (fe51ValAt a_rest 40 % p25519)
          (fe51ValAt a_rest 80 % p25519))
    (hQ := edAddNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hself80
      hpost hpost_1 hpost_2 rfl)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 224 304
  wp_done

set_option maxHeartbeats 800000 in
theorem edwards_point_add_affine_niels_ro_ok : EdwardsPointAddAffineNielsRoOk := by
  intro _
  apply dalekCaller_ok dalekCliPC31 dalekCliPl31
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 52) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul_ro_right(sp + 0, other + 0) -> sp + 80 (s0.sp - 224)
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_0 a_4 hs_0 hself0 hself40)
  intro s0' ⟨⟨hs0_len, _, _, _, _, _⟩, hbuf0_v⟩
  apply sepWP_abstract_bytes (s0.sp - 264#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_40 a_4 hs_40 hself0 hself40)
  intro s40' ⟨⟨hs40_len, _, _, _, _, _⟩, hbuf40_v⟩
  apply sepWP_focus_ro_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ro_right_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_ro_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 2: mul_ro_right(sp + 40, other + 40) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_ro_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ro_right_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_ro_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 3: mul_ro_right(self + 120, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_ro_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ro_right_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_ro_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Epilogue: step from +0x104 to ret (+0x25c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf0_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf40_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
      edExtOfBytes res_bs =
        edAddAffineNiels (edExtOfBytes a_4)
          (fe51ValAt a_rest 0 % p25519)
          (fe51ValAt a_rest 40 % p25519)
          (fe51ValAt a_rest 80 % p25519))
    (hQ := edAddNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hself80
      hpost hpost_1 hpost_2 rfl)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 224 304
  wp_done

/-! ## 5. `<&EdwardsPoint as Sub<&AffineNielsPoint>>::sub` (`B32`, 152w, RW & RO) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_sub_affine_niels_ok : EdwardsPointSubAffineNielsOk := by
  intro _
  apply dalekCaller_ok dalekCliPC32 dalekCliPl32
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 52) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul(sp + 0, other + 40) -> sp + 80 (s0.sp - 224)
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_0 a_4 hs_0 hself0 hself40)
  intro s0' ⟨⟨hs0_len, _, _, _, _, _⟩, hbuf0_v⟩
  apply sepWP_abstract_bytes (s0.sp - 264#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_40 a_4 hs_40 hself0 hself40)
  intro s40' ⟨⟨hs40_len, _, _, _, _, _⟩, hbuf40_v⟩
  apply sepWP_focus_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 2: mul(sp + 40, other + 0) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 3: mul(self + 120, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Epilogue: step from +0x104 to ret (+0x25c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf0_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf40_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
      edExtOfBytes res_bs =
        edSubAffineNiels (edExtOfBytes a_4)
          (fe51ValAt a_rest 0 % p25519)
          (fe51ValAt a_rest 40 % p25519)
          (fe51ValAt a_rest 80 % p25519))
    (hQ := edSubNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hself80
      hpost hpost_1 hpost_2 rfl)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 224 304
  wp_done

set_option maxHeartbeats 800000 in
theorem edwards_point_sub_affine_niels_ro_ok : EdwardsPointSubAffineNielsRoOk := by
  intro _
  apply dalekCaller_ok dalekCliPC32 dalekCliPl32
  intro b hb hbase
  wp_init
  have hout_len : a_3.length = 160 := by assumption
  have hself_len : a_4.length = 160 := by assumption
  have hother_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_4 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_4 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_4 80 (2 ^ 52) := by assumption
  have hself120 : fe51LimbsBoundedAt a_4 120 (2 ^ 54) := by assumption
  have hother0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 54) := by assumption
  have hother40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 54) := by assumption
  have hother80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  haveI : HasLenGe a_3 160 := ⟨by omega⟩
  haveI : HasLenGe a_4 160 := ⟨by omega⟩
  haveI : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 224 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: mul_ro_right(sp + 0, other + 40) -> sp + 80 (s0.sp - 224)
  apply sepWP_abstract_bytes (s0.sp - 304#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_4 0 % p25519) (fe51ValAt a_4 40 % p25519))
    (hQ := fe51_write5_add_post s_0 a_4 hs_0 hself0 hself40)
  intro s0' ⟨⟨hs0_len, _, _, _, _, _⟩, hbuf0_v⟩
  apply sepWP_abstract_bytes (s0.sp - 264#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpSub (fe51ValAt a_4 40 % p25519) (fe51ValAt a_4 0 % p25519))
    (hQ := fe51_write5_sub_reduce_post s_40 a_4 hs_40 hself0 hself40)
  intro s40' ⟨⟨hs40_len, _, _, _, _, _⟩, hbuf40_v⟩
  apply sepWP_focus_ro_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_dalek_call fe51_mul_ro_right_ok
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_ro_bytes a_2 (a_2 + 40#64) 40 40
  norm_sf 224
  -- Call 2: mul_ro_right(sp + 40, other + 0) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_ro_bytes a_2 a_2 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother0
  wp_dalek_call fe51_mul_ro_right_ok
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_ro_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 3: mul_ro_right(self + 120, other + 80) -> x29 - 0x30 (s0.sp - 144)
  wp_steps
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself120
  apply sepWP_focus_ro_bytes a_2 (a_2 + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother80
  wp_dalek_call fe51_mul_ro_right_ok
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_ro_bytes a_2 (a_2 + 80#64) 80 40
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  norm_sf 224
  -- Epilogue: step from +0x104 to ret (+0x25c)
  wp_steps
  rw [mul_mod_eq_fpMul, hbuf0_v, fe51ValOfBytes_slice] at hpost
  rw [mul_mod_eq_fpMul, hbuf40_v, fe51ValOfBytes_slice] at hpost_1
  rw [mul_mod_eq_fpMul, fe51ValOfBytes_slice, fe51ValOfBytes_slice] at hpost_2
  apply sepWP_abstract_bytes a_1
    (fun res_bs =>
      res_bs.length = 160 ∧
      fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
      fe51LimbsBoundedAt res_bs 120 (2 ^ 54) ∧
      edExtOfBytes res_bs =
        edSubAffineNiels (edExtOfBytes a_4)
          (fe51ValAt a_rest 0 % p25519)
          (fe51ValAt a_rest 40 % p25519)
          (fe51ValAt a_rest 80 % p25519))
    (hQ := edSubNiels_epilogue_post a_3 w w_1 w_2 _ _ _ _ _ _ _ _ _ hout_len hw_b hw1_b hw2_b hself80
      hpost hpost_1 hpost_2 rfl)
  intro out' ⟨hres_len,
    ⟨hb0_0, hb0_1, hb0_2, hb0_3, hb0_4⟩,
    ⟨hb40_0, hb40_1, hb40_2, hb40_3, hb40_4⟩,
    ⟨hb80_0, hb80_1, hb80_2, hb80_3, hb80_4⟩,
    ⟨hb120_0, hb120_1, hb120_2, hb120_3, hb120_4⟩,
    hres_val⟩
  close_cells (s0.sp - 104#64) 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 224 304
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels2
