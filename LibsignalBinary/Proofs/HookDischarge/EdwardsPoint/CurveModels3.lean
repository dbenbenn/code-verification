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
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels2
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `EdwardsPoint::mul_by_pow_2` Machine-Code Proofs

Machine-code proofs in `dalekCliMultiLib` for `<EdwardsPoint>::mul_by_pow_2` (`B18`)
specialized to `k = 3` and `k = 4`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels3

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpMul)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  EdwardsPointMulByPow2Ok EdwardsPointMulByPow2_4Ok
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edProjDouble edAsProjective edDouble3 edDouble4)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe
  sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_abstract_bytes
  proj_copy15_prologue_post proj_copy15_loop_post fe51_mul_post_props
  sepWP_split4_160 sepWP_merge4_160
  sepWP_merge4_stack_bytes sepWP_merge4_stack_512
  sepWP_split4_completed_224 sepWP_split4_completed_512
  sepWP_callee_224_to_400 sepWP_callee_400_to_224
  edAsExtended_of_append4)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51 (fe51_mul_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels2 (projective_point_double_ok)

arm64_proof_prelude

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 18 dalekCliMultiLib DalekCliPlacement 79 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl18_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl18.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

public section

/-! ## 1. `<EdwardsPoint>::mul_by_pow_2` (`B18`, `k = 3`) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_mul_by_pow_2_ok : EdwardsPointMulByPow2Ok := by
  intro _
  apply dalekCaller_ok dalekCliPC18 dalekCliPl18
  intro b hb hbase
  wp_init
  have hself_pt : fe51Point4Bounded a_rest_1 (2 ^ 53) := by assumption
  have hk_eq : a_2 = 3#32 := by assumption
  obtain ⟨hself_len, hself0, hself40, hself80, hself120⟩ := hself_pt
  subst hk_eq
  haveI : HasLenGe a_rest_1 160 := ⟨by omega⟩
  have hself80_54 : fe51LimbsBoundedAt a_rest_1 80 (2 ^ 54) := by
    obtain ⟨h0, h1, h2, h3, h4⟩ := hself80
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  let P0 := edExtOfBytes a_rest_1
  let C1 := edProjDouble P0.X P0.Y P0.Z
  let P1 := edAsProjective C1
  let C2 := edProjDouble P1.X P1.Y P1.Z
  let P2 := edAsProjective C2
  let C3 := edProjDouble P2.X P2.Y P2.Z
  apply sepWP_split_stack_callee 400 512
  apply sepWP_peel_stack_bytes s0.sp 512 160 352; intro sp_512 h_512
  apply sepWP_peel_stack_bytes s0.sp 352 120 232; intro sp_352 h_352
  apply sepWP_peel_stack_bytes s0.sp 232 8 224; intro sp_232 h_232
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro sp_224 h_224
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro sp_184 h_184
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro sp_144 h_144
  apply sepWP_peel_stack_bytes s0.sp 104 40 64; intro sp_104 h_104
  open_cells (s0.sp - 64#64) 64 8
  -- Iteration 1: double + 3 muls
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧
      fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C1)
    (hQ := proj_copy15_prologue_post sp_352 a_rest_1 h_352 hself0 hself40 hself80_54)
  intro proj1 ⟨hp1_len, hp1_0, hp1_40, hp1_80, hp1_val⟩
  unpack_fe51_at hp1_0; unpack_fe51_at hp1_40; unpack_fe51_at hp1_80
  wp_dalek_call projective_point_double_ok
  norm_sf 400
  rw [hp1_val] at hpost
  apply sepWP_split4_completed_512 s0.sp C1
  intro c1_0 c1_1 c1_2 c1_3 hc1_0_l hc1_1_l hc1_2_l hc1_3_l
        hc1_0_b hc1_1_b hc1_2_b hc1_3_b hc1_0_v hc1_1_v hc1_2_v hc1_3_v
  unpack_fe51 hc1_0_b; unpack_fe51 hc1_1_b; unpack_fe51 hc1_2_b; unpack_fe51 hc1_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw1_X_l, hw1_X_b, hw1_X_v⟩ := fe51_mul_post_props w_1 P1.X
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw1_Y_l, hw1_Y_b, hw1_Y_v⟩ := fe51_mul_post_props w_2 P1.Y
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw1_Z_l, hw1_Z_b, hw1_Z_v⟩ := fe51_mul_post_props w_3 P1.Z
  apply sepWP_callee_224_to_400 s0.sp
  apply sepWP_merge4_stack_512 s0.sp
  intro sp_512_2 h_512_2
  clear_dead_vars [sp_512, sp_352, sp_224, sp_184, sp_144, w, c1_0, c1_1, c1_2, c1_3]
  -- Iteration 2: copy + b.ne + double + 3 muls
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧
      fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C2)
    (hQ := proj_copy15_loop_post proj1 w_1 w_2 w_3 P1.X P1.Y P1.Z
      hp1_len hw1_X_b hw1_Y_b hw1_Z_b hw1_X_v hw1_Y_v hw1_Z_v)
  intro proj2 ⟨hp2_len, hp2_0, hp2_40, hp2_80, hp2_val⟩
  unpack_fe51_at hp2_0; unpack_fe51_at hp2_40; unpack_fe51_at hp2_80
  wp_dalek_call projective_point_double_ok
  clean_prev_sf; norm_sf 400
  have hc2_val : edExtOfBytes w_4 = C2 := by rw [← hp2_val]; assumption
  apply sepWP_split4_completed_512 s0.sp C2
  intro c2_0 c2_1 c2_2 c2_3 hc2_0_l hc2_1_l hc2_2_l hc2_3_l
        hc2_0_b hc2_1_b hc2_2_b hc2_3_b hc2_0_v hc2_1_v hc2_2_v hc2_3_v
  unpack_fe51 hc2_0_b; unpack_fe51 hc2_1_b; unpack_fe51 hc2_2_b; unpack_fe51 hc2_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw2_X_l, hw2_X_b, hw2_X_v⟩ := fe51_mul_post_props w_5 P2.X
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw2_Y_l, hw2_Y_b, hw2_Y_v⟩ := fe51_mul_post_props w_6 P2.Y
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hw2_Z_l, hw2_Z_b, hw2_Z_v⟩ := fe51_mul_post_props w_7 P2.Z
  apply sepWP_callee_224_to_400 s0.sp
  apply sepWP_merge4_stack_512 s0.sp
  intro sp_512_3 h_512_3
  clear_dead_vars [proj1, w_1, w_2, w_3, sp_512_2, w_4, c2_0, c2_1, c2_2, c2_3]
  -- Iteration 3: copy + fallthrough b.ne + double + 4 muls into out
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧
      fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C3)
    (hQ := proj_copy15_loop_post proj2 w_5 w_6 w_7 P2.X P2.Y P2.Z
      hp2_len hw2_X_b hw2_Y_b hw2_Z_b hw2_X_v hw2_Y_v hw2_Z_v)
  intro proj3 ⟨hp3_len, hp3_0, hp3_40, hp3_80, hp3_val⟩
  unpack_fe51_at hp3_0; unpack_fe51_at hp3_40; unpack_fe51_at hp3_80
  apply sepWP_merge4_stack_bytes s0.sp
  intro sp_224_160 h_224_160
  clear_dead_vars [proj2, w_5, w_6, w_7, sp_104]
  wp_dalek_call projective_point_double_ok
  clean_prev_sf; norm_sf 400
  have hc3_val : edExtOfBytes w_8 = C3 := by rw [← hp3_val]; assumption
  apply sepWP_split4_completed_224 s0.sp C3
  intro c3_0 c3_1 c3_2 c3_3 hc3_0_l hc3_1_l hc3_2_l hc3_3_l
        hc3_0_b hc3_1_b hc3_2_b hc3_3_b hc3_0_v hc3_1_v hc3_2_v hc3_3_v
  unpack_fe51 hc3_0_b; unpack_fe51 hc3_1_b; unpack_fe51 hc3_2_b; unpack_fe51 hc3_3_b
  apply sepWP_split4_160 a_1
  intro out0 out1 out2 out3 hout0 hout1 hout2 hout3
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_9 (fpMul C3.X C3.T)
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_10 (fpMul C3.Y C3.Z)
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_11 (fpMul C3.Z C3.T)
  wp_steps
  wp_dalek_call fe51_mul_ok
  clean_prev_sf; norm_sf 224
  obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_12 (fpMul C3.X C3.Y)
  apply sepWP_callee_224_to_400 s0.sp
  apply sepWP_merge4_stack_bytes s0.sp
  intro sp_224_end h_224_end
  apply sepWP_merge4_160 a_1
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edDouble3 (edExtOfBytes a_rest_1))
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w_9 w_10 w_11 w_12 C3 hr0_b hr1_b hr2_b hr3_b
        hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv⟩
  intro res_bs ⟨⟨hres_l, hres_0, hres_40, hres_80, hres_120⟩, hres_v⟩
  clear_dead_vars [sp_224_160, w_8, c3_0, c3_1, c3_2, c3_3, out0, out1, out2, out3, w_9, w_10, w_11, w_12]
  have hres_pt : fe51Point4Bounded res_bs (2 ^ 52) := ⟨hres_l, hres_0, hres_40, hres_80, hres_120⟩
  unpack_fe51_at hres_0; unpack_fe51_at hres_40; unpack_fe51_at hres_80; unpack_fe51_at hres_120
  wp_steps
  close_cells (s0.sp - 64#64) 64 8
  apply sepWP_unpeel_stack_bytes s0.sp 224 160 64
  apply sepWP_unpeel_stack_bytes s0.sp 232 8 224
  apply sepWP_unpeel_stack_bytes s0.sp 352 120 232
  apply sepWP_unpeel_stack_bytes s0.sp 512 160 352
  apply sepWP_merge_stack_callee 400 512
  wp_done

/-! ## 2. `<EdwardsPoint>::mul_by_pow_2` (`B18`, `k = 4`) -/

set_option maxHeartbeats 800000 in
theorem edwards_point_mul_by_pow_2_4_ok : EdwardsPointMulByPow2_4Ok := by
  intro _
  apply dalekCaller_ok dalekCliPC18 dalekCliPl18
  intro b hb hbase
  wp_init
  have hself_pt : fe51Point4Bounded a_rest_1 (2 ^ 53) := by assumption
  have hk_eq : a_2 = 4#32 := by assumption
  obtain ⟨hself_len, hself0, hself40, hself80, hself120⟩ := hself_pt
  subst hk_eq
  haveI : HasLenGe a_rest_1 160 := ⟨by omega⟩
  have hself80_54 : fe51LimbsBoundedAt a_rest_1 80 (2 ^ 54) := by
    obtain ⟨h0, h1, h2, h3, h4⟩ := hself80
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  let P0 := edExtOfBytes a_rest_1
  let C1 := edProjDouble P0.X P0.Y P0.Z; let P1 := edAsProjective C1
  let C2 := edProjDouble P1.X P1.Y P1.Z; let P2 := edAsProjective C2
  let C3 := edProjDouble P2.X P2.Y P2.Z; let P3 := edAsProjective C3
  let C4 := edProjDouble P3.X P3.Y P3.Z
  apply sepWP_split_stack_callee 400 512
  apply sepWP_peel_stack_bytes s0.sp 512 160 352; intro sp_512 h_512
  apply sepWP_peel_stack_bytes s0.sp 352 120 232; intro sp_352 h_352
  apply sepWP_peel_stack_bytes s0.sp 232 8 224; intro sp_232 h_232
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro sp_224 h_224
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro sp_184 h_184
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro sp_144 h_144
  apply sepWP_peel_stack_bytes s0.sp 104 40 64; intro sp_104 h_104
  open_cells (s0.sp - 64#64) 64 8
  -- Iteration 1: double + 3 muls
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧ fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧ fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C1)
    (hQ := proj_copy15_prologue_post sp_352 a_rest_1 h_352 hself0 hself40 hself80_54)
  intro proj1 ⟨hp1_len, hp1_0, hp1_40, hp1_80, hp1_val⟩
  unpack_fe51_at hp1_0; unpack_fe51_at hp1_40; unpack_fe51_at hp1_80
  wp_dalek_call projective_point_double_ok; norm_sf 400; rw [hp1_val] at hpost
  apply sepWP_split4_completed_512 s0.sp C1
  intro c1_0 c1_1 c1_2 c1_3 hc1_0_l hc1_1_l hc1_2_l hc1_3_l hc1_0_b hc1_1_b hc1_2_b hc1_3_b hc1_0_v hc1_1_v hc1_2_v hc1_3_v
  unpack_fe51 hc1_0_b; unpack_fe51 hc1_1_b; unpack_fe51 hc1_2_b; unpack_fe51 hc1_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw1_X_l, hw1_X_b, hw1_X_v⟩ := fe51_mul_post_props w_1 P1.X
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw1_Y_l, hw1_Y_b, hw1_Y_v⟩ := fe51_mul_post_props w_2 P1.Y
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw1_Z_l, hw1_Z_b, hw1_Z_v⟩ := fe51_mul_post_props w_3 P1.Z
  apply sepWP_callee_224_to_400 s0.sp; apply sepWP_merge4_stack_512 s0.sp; intro sp_512_2 h_512_2
  clear_dead_vars [sp_512, sp_352, sp_224, sp_184, sp_144, w, c1_0, c1_1, c1_2, c1_3]
  -- Iteration 2: copy + b.ne + double + 3 muls
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧ fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧ fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C2)
    (hQ := proj_copy15_loop_post proj1 w_1 w_2 w_3 P1.X P1.Y P1.Z hp1_len hw1_X_b hw1_Y_b hw1_Z_b hw1_X_v hw1_Y_v hw1_Z_v)
  intro proj2 ⟨hp2_len, hp2_0, hp2_40, hp2_80, hp2_val⟩
  unpack_fe51_at hp2_0; unpack_fe51_at hp2_40; unpack_fe51_at hp2_80
  wp_dalek_call projective_point_double_ok; clean_prev_sf; norm_sf 400
  have hc2_val : edExtOfBytes w_4 = C2 := by rw [← hp2_val]; assumption
  apply sepWP_split4_completed_512 s0.sp C2
  intro c2_0 c2_1 c2_2 c2_3 hc2_0_l hc2_1_l hc2_2_l hc2_3_l hc2_0_b hc2_1_b hc2_2_b hc2_3_b hc2_0_v hc2_1_v hc2_2_v hc2_3_v
  unpack_fe51 hc2_0_b; unpack_fe51 hc2_1_b; unpack_fe51 hc2_2_b; unpack_fe51 hc2_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw2_X_l, hw2_X_b, hw2_X_v⟩ := fe51_mul_post_props w_5 P2.X
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw2_Y_l, hw2_Y_b, hw2_Y_v⟩ := fe51_mul_post_props w_6 P2.Y
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw2_Z_l, hw2_Z_b, hw2_Z_v⟩ := fe51_mul_post_props w_7 P2.Z
  apply sepWP_callee_224_to_400 s0.sp; apply sepWP_merge4_stack_512 s0.sp; intro sp_512_3 h_512_3
  clear_dead_vars [proj1, w_1, w_2, w_3, sp_512_2, w_4, c2_0, c2_1, c2_2, c2_3]
  -- Iteration 3: copy + b.ne + double + 3 muls
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧ fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧ fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C3)
    (hQ := proj_copy15_loop_post proj2 w_5 w_6 w_7 P2.X P2.Y P2.Z hp2_len hw2_X_b hw2_Y_b hw2_Z_b hw2_X_v hw2_Y_v hw2_Z_v)
  intro proj3 ⟨hp3_len, hp3_0, hp3_40, hp3_80, hp3_val⟩
  unpack_fe51_at hp3_0; unpack_fe51_at hp3_40; unpack_fe51_at hp3_80
  wp_dalek_call projective_point_double_ok; clean_prev_sf; norm_sf 400
  have hc3_val : edExtOfBytes w_8 = C3 := by rw [← hp3_val]; assumption
  apply sepWP_split4_completed_512 s0.sp C3
  intro c3_0 c3_1 c3_2 c3_3 hc3_0_l hc3_1_l hc3_2_l hc3_3_l hc3_0_b hc3_1_b hc3_2_b hc3_3_b hc3_0_v hc3_1_v hc3_2_v hc3_3_v
  unpack_fe51 hc3_0_b; unpack_fe51 hc3_1_b; unpack_fe51 hc3_2_b; unpack_fe51 hc3_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw3_X_l, hw3_X_b, hw3_X_v⟩ := fe51_mul_post_props w_9 P3.X
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw3_Y_l, hw3_Y_b, hw3_Y_v⟩ := fe51_mul_post_props w_10 P3.Y
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hw3_Z_l, hw3_Z_b, hw3_Z_v⟩ := fe51_mul_post_props w_11 P3.Z
  apply sepWP_callee_224_to_400 s0.sp; apply sepWP_merge4_stack_512 s0.sp; intro sp_512_4 h_512_4
  clear_dead_vars [proj2, w_5, w_6, w_7, sp_512_3, w_8, c3_0, c3_1, c3_2, c3_3]
  -- Iteration 4: copy + fallthrough b.ne + double + 4 muls into out
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 352#64)
    (fun buf => buf.length = 120 ∧ fe51LimbsBoundedAt buf 0 (2 ^ 53) ∧
      fe51LimbsBoundedAt buf 40 (2 ^ 53) ∧ fe51LimbsBoundedAt buf 80 (2 ^ 54) ∧
      edProjDouble (fe51ValAt buf 0) (fe51ValAt buf 40) (fe51ValAt buf 80) = C4)
    (hQ := proj_copy15_loop_post proj3 w_9 w_10 w_11 P3.X P3.Y P3.Z hp3_len hw3_X_b hw3_Y_b hw3_Z_b hw3_X_v hw3_Y_v hw3_Z_v)
  intro proj4 ⟨hp4_len, hp4_0, hp4_40, hp4_80, hp4_val⟩
  unpack_fe51_at hp4_0; unpack_fe51_at hp4_40; unpack_fe51_at hp4_80
  apply sepWP_merge4_stack_bytes s0.sp; intro sp_224_160 h_224_160
  clear_dead_vars [proj3, w_9, w_10, w_11, sp_104]
  wp_dalek_call projective_point_double_ok; clean_prev_sf; norm_sf 400
  have hc4_val : edExtOfBytes w_12 = C4 := by rw [← hp4_val]; assumption
  apply sepWP_split4_completed_224 s0.sp C4
  intro c4_0 c4_1 c4_2 c4_3 hc4_0_l hc4_1_l hc4_2_l hc4_3_l hc4_0_b hc4_1_b hc4_2_b hc4_3_b hc4_0_v hc4_1_v hc4_2_v hc4_3_v
  unpack_fe51 hc4_0_b; unpack_fe51 hc4_1_b; unpack_fe51 hc4_2_b; unpack_fe51 hc4_3_b
  apply sepWP_split4_160 a_1; intro out0 out1 out2 out3 hout0 hout1 hout2 hout3
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_13 (fpMul C4.X C4.T)
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_14 (fpMul C4.Y C4.Z)
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_15 (fpMul C4.Z C4.T)
  wp_steps; wp_dalek_call fe51_mul_ok; clean_prev_sf; norm_sf 224; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_16 (fpMul C4.X C4.Y)
  apply sepWP_callee_224_to_400 s0.sp; apply sepWP_merge4_stack_bytes s0.sp; intro sp_224_end h_224_end
  apply sepWP_merge4_160 a_1
    (fun res => fe51Point4Bounded res (2 ^ 52) ∧ edExtOfBytes res = edDouble4 (edExtOfBytes a_rest_1))
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w_13 w_14 w_15 w_16 C4 hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv⟩
  intro res_bs ⟨⟨hres_l, hres_0, hres_40, hres_80, hres_120⟩, hres_v⟩
  clear_dead_vars [sp_224_160, w_12, c4_0, c4_1, c4_2, c4_3, out0, out1, out2, out3, w_13, w_14, w_15, w_16]
  have hres_pt : fe51Point4Bounded res_bs (2 ^ 52) := ⟨hres_l, hres_0, hres_40, hres_80, hres_120⟩
  unpack_fe51_at hres_0; unpack_fe51_at hres_40; unpack_fe51_at hres_80; unpack_fe51_at hres_120
  wp_steps; close_cells (s0.sp - 64#64) 64 8
  apply sepWP_unpeel_stack_bytes s0.sp 224 160 64; apply sepWP_unpeel_stack_bytes s0.sp 232 8 224
  apply sepWP_unpeel_stack_bytes s0.sp 352 120 232; apply sepWP_unpeel_stack_bytes s0.sp 512 160 352
  apply sepWP_merge_stack_callee 400 512; wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveModels3
