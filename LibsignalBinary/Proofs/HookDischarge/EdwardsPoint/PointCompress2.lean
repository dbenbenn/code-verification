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
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `EdwardsPoint::ct_eq` and `EdwardsPoint::compress` Proofs

Machine-code proofs in `dalekCliMultiLib` for `EdwardsPoint::ct_eq`
(`edwards_point_ct_eq_ok_of`) and `EdwardsPoint::compress` (`edwards_point_compress_ok_of`).
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress2

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51Pow2kOk Fe51Pow22501Ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  EdwardsPointCtEqOk EdwardsPointCompressOk)
open VerifiedLibraries.Common (p25519 fpPow natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (
  black_box_u8_ok slice32_ct_eq_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  sepWP_norm_stackFrame sepWP_split_stack_callee sepWP_merge_stack_callee
  sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_callee_shrink sepWP_callee_grow sepWP_abstract_bytes
  pointsToBytes40_eq_cells)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  pointsToBytes160_split4 fe51LimbsBounded_take40 fe51LimbsBounded_drop40_take40
  fe51LimbsBounded_drop80_take40 pointsToBytes32_eq_cells8 bv64_sub_add
  pointsToBytes_packCanonical51Bytes fe51_to_bytes_of_bytes
  sepWP_merge_stack_32_8 sepWP_fold_point160 merge_stack_16_496
  zeroExtend8_and32 edPointEq_of_muls
  sepWP_peel_stack_region sepWP_unpeel_stack_region sepWP_split_bytes_append
  fe51LimbsBounded_of_52 write64_copy5_eq
  sepWP_split32_sub sepWP_combine32_sub pointsToBytes40_sub_eq_cells
  fe51_sign_of_bytes encodeEd_of_muls compress_byte31_eq
  pointsToBytes_setByte31Or_packCanonical51Bytes)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 14 dalekCliMultiLib DalekCliPlacement 204 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl14_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl14.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 30 dalekCliMultiLib DalekCliPlacement 408 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl30_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl30.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

public section

set_option maxHeartbeats 800000 in
set_option maxRecDepth 16384 in
theorem edwards_point_ct_eq_ok_of (hMul : Fe51MulOk) : EdwardsPointCtEqOk := by
  intro _
  apply dalekCaller_ok dalekCliPC30 dalekCliPl30
  intro b hb hbase
  wp_init
  apply sepWP_split_stack_callee 224 288
  apply sepWP_peel_stack_bytes s0.sp 288 40 248; intro w_init hw_init
  apply sepWP_peel_stack_bytes s0.sp 248 40 208; intro w1_init hw1_init
  apply sepWP_peel_stack_bytes s0.sp 208 32 176; intro buf1_init hbuf1_init
  apply sepWP_peel_stack_bytes s0.sp 176 8 168; intro gap1_init hgap1_init
  apply sepWP_peel_stack_bytes s0.sp 168 32 136; intro buf2_init hbuf2_init
  apply sepWP_peel_stack_bytes s0.sp 136 8 128; intro gap2_init hgap2_init
  apply sepWP_peel_stack_bytes s0.sp 128 32 96; intro buf3_init hbuf3_init
  apply sepWP_peel_stack_bytes s0.sp 96 32 64; intro buf4_init hbuf4_init
  open_cells (s0.sp - 64#64) 64 8
  wp_conv_pre =>
    rw [pointsToBytes160_split4 a_1 a_2 h_4.1, pointsToBytes160_split4 a a_rest h_1.1]
  -- Call 1: mul(sp, self.X, other.Z) -> s0.sp - 288#64
  obtain ⟨hx1_l, hx1_0, hx1_1, hx1_2, hx1_3, hx1_4⟩ := fe51LimbsBounded_take40 a_2 h_4.1 h_4.2.1
  obtain ⟨hz2_l, hz2_0, hz2_1, hz2_2, hz2_3, hz2_4⟩ := fe51LimbsBounded_drop80_take40 a_rest h_1.1 h_1.2.2.2.1
  wp_cut_codeLoaded
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hx1_l hx1_0 hx1_1 hx1_2 hx1_3 hx1_4 w_init hw_init
  obtain ⟨hw_len, hwl0, hwl1, hwl2, hwl3, hwl4⟩ := ‹fe51LimbsBounded w (2 ^ 52)›
  -- Call 2: mul(sp + 0x28, other.X, self.Z) -> s0.sp - 248#64
  obtain ⟨hx2_l, hx2_0, hx2_1, hx2_2, hx2_3, hx2_4⟩ := fe51LimbsBounded_take40 a_rest h_1.1 h_1.2.1
  obtain ⟨hz1_l, hz1_0, hz1_1, hz1_2, hz1_3, hz1_4⟩ := fe51LimbsBounded_drop80_take40 a_2 h_4.1 h_4.2.2.2.1
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hx2_l hx2_0 hx2_1 hx2_2 hx2_3 hx2_4 w1_init hw1_init
  obtain ⟨hw1_len, hm0, hm1, hm2, hm3, hm4⟩ := ‹fe51LimbsBounded w_1 (2 ^ 52)›
  -- Block 1: interleaved to_bytes of w and w_1
  have h_w := pointsToBytes40_eq_cells (s0.sp - 288#64) w hw_len
  have h_w1 := pointsToBytes40_eq_cells (s0.sp - 248#64) w_1 hw1_len
  have h_open1 := pointsToBytes32_eq_cells8 (s0.sp - 208#64) buf1_init hbuf1_init
  have h_open2 := pointsToBytes32_eq_cells8 (s0.sp - 168#64) buf2_init hbuf2_init
  simp only [bv64_sub_add, BitVec.reduceSub] at h_w h_w1 h_open1 h_open2
  wp_conv_pre => rw [h_w, h_w1, h_open1, h_open2]
  clear h_open1 h_open2
  generalize hwl0_eq : ByteSlice.readLE w 0 8 = l0 at *
  generalize hwl1_eq : ByteSlice.readLE w 8 8 = l1 at *
  generalize hwl2_eq : ByteSlice.readLE w 16 8 = l2 at *
  generalize hwl3_eq : ByteSlice.readLE w 24 8 = l3 at *
  generalize hwl4_eq : ByteSlice.readLE w 32 8 = l4 at *
  generalize hm0_eq : ByteSlice.readLE w_1 0 8 = m0 at *
  generalize hm1_eq : ByteSlice.readLE w_1 8 8 = m1 at *
  generalize hm2_eq : ByteSlice.readLE w_1 16 8 = m2 at *
  generalize hm3_eq : ByteSlice.readLE w_1 24 8 = m3 at *
  generalize hm4_eq : ByteSlice.readLE w_1 32 8 = m4 at *
  wp_cut_codeLoaded
  wp_sym_steps 23
  generalize hh0 : (l0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l4 >>> 51)) * 19#64 = h0
  generalize hh1 : (l1 &&& 2251799813685247#64) + l0 >>> 51 = h1
  generalize hh2 : (l2 &&& 2251799813685247#64) + l1 >>> 51 = h2
  generalize hh3 : (l3 &&& 2251799813685247#64) + l2 >>> 51 = h3
  generalize hh4 : (l4 &&& 2251799813685247#64) + l3 >>> 51 = h4
  generalize hq : (h4 + (h3 + (h2 + (h1 + (h0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q
  generalize hu0 : h0 + BitVec.setWidth 64 (BitVec.setWidth 32 q) * 19#64 = u0
  wp_sym_steps 86
  generalize hu1 : h1 + u0 >>> 51 = u1
  generalize hu2 : h2 + u1 >>> 51 = u2
  generalize hu3 : h3 + u2 >>> 51 = u3
  generalize hu4 : h4 + u3 >>> 51 = u4
  generalize hmh0 : (m0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (m4 >>> 51)) * 19#64 = mh0
  generalize hmh1 : (m1 &&& 2251799813685247#64) + m0 >>> 51 = mh1
  generalize hmh2 : (m2 &&& 2251799813685247#64) + m1 >>> 51 = mh2
  generalize hmh3 : (m3 &&& 2251799813685247#64) + m2 >>> 51 = mh3
  generalize hmh4 : (m4 &&& 2251799813685247#64) + m3 >>> 51 = mh4
  generalize hmq : (mh4 + (mh3 + (mh2 + (mh1 + (mh0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = mq
  generalize hmu0 : mh0 + BitVec.setWidth 64 (BitVec.setWidth 32 mq) * 19#64 = mu0
  wp_sym_steps 79
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_b1
  dsimp only [State.setMem, State.mem] at hcl_b1
  generalize hmu1 : mh1 + mu0 >>> 51 = mu1
  generalize hmu2 : mh2 + mu1 >>> 51 = mu3_dummy_1
  generalize hmu3 : mh3 + mu3_dummy_1 >>> 51 = mu3
  generalize hmu4 : mh4 + mu3 >>> 51 = mu4
  have h_pack1 := pointsToBytes_packCanonical51Bytes (s0.sp - 208#64) u0 u1 u2 u3 u4
  have h_pack2 := pointsToBytes_packCanonical51Bytes (s0.sp - 168#64) mu0 mu1 mu3_dummy_1 mu3 mu4
  simp only [bv64_sub_add, BitVec.reduceSub] at h_pack1 h_pack2
  have h_bytes1 := fe51_to_bytes_of_bytes w l0 l1 l2 l3 l4 hwl0_eq hwl1_eq hwl2_eq hwl3_eq hwl4_eq
    hwl0 hwl1 hwl2 hwl3 hwl4 h0 h1 h2 h3 h4 q u0 u1 u2 u3 u4
    hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4
  have h_bytes2 := fe51_to_bytes_of_bytes w_1 m0 m1 m2 m3 m4 hm0_eq hm1_eq hm2_eq hm3_eq hm4_eq
    hm0 hm1 hm2 hm3 hm4 mh0 mh1 mh2 mh3 mh4 mq mu0 mu1 mu3_dummy_1 mu3 mu4
    hmh0 hmh1 hmh2 hmh3 hmh4 hmq hmu0 hmu1 hmu2 hmu3 hmu4
  have hlen_nb1 : (natToLeBytes 32 (fe51ValOfBytes w % p25519)).length = 32 := by simp [natToLeBytes]
  have hlen_nb2 : (natToLeBytes 32 (fe51ValOfBytes w_1 % p25519)).length = 32 := by simp [natToLeBytes]
  generalize hnb1_eq : natToLeBytes 32 (fe51ValOfBytes w % p25519) = nb1 at hlen_nb1 h_bytes1
  generalize hnb2_eq : natToLeBytes 32 (fe51ValOfBytes w_1 % p25519) = nb2 at hlen_nb2 h_bytes2
  wp_conv_pre =>
    rw [← h_w, ← h_w1, h_pack1, h_pack2, h_bytes1, h_bytes2]
  clear h_w h_w1 h_pack1 h_pack2 h_bytes1 h_bytes2 buf1_init hbuf1_init buf2_init hbuf2_init
    hh0 hh1 hh2 hh3 hh4 hq hu0 hu1 hu2 hu3 hu4 h0 h1 h2 h3 h4 q u0 u1 u2
    hmh0 hmh1 hmh2 hmh3 hmh4 hmq hmu0 hmu1 hmu2 hmu3 hmu4 mh0 mh1 mh2 mh3 mh4 mq
    hwl0 hwl1 hwl2 hwl3 hwl4 hm0 hm1 hm2 hm3 hm4
    hwl0_eq hwl1_eq hwl2_eq hwl3_eq hwl4_eq l0 l1 l2 l3 l4
    hm0_eq hm1_eq hm2_eq hm3_eq hm4_eq m0 m1 m2 m3 m4
  -- Call 3: slice32_ct_eq(sp + 0x50, x29 - 0x68)
  apply sepWP_callee_shrink (s0.sp - 288#64) 224 64 160
  wp_steps; wp_dalek_call slice32_ct_eq_ok; clean_prev_sf; norm_sf 64
  clear u3 u4 mu0 mu1 mu3_dummy_1 mu3 mu4
  rw [← hnb1_eq, ← hnb2_eq] at hpost_2
  generalize hr_c3 : sf.readReg64 (Reg.gpr 0#5) = r_c3 at hpost_2
  have hr_c3_32 : sf.readReg32 (Reg.gpr 0#5) = BitVec.truncate 32 r_c3 :=
    congrArg (BitVec.truncate 32) hr_c3
  apply sepWP_callee_grow (s0.sp - 288#64) 224 64 160
  -- Merge 32-byte buffers with 8-byte gaps for Calls 4 and 5
  apply sepWP_merge_stack_32_8 s0.sp 208#64 176#64 (hxs := hlen_nb1)
  apply sepWP_merge_stack_32_8 s0.sp 168#64 136#64 (hxs := hlen_nb2)
  apply sepWP_abstract_bytes (s0.sp - 208#64) (fun bs => bs.length = 40)
    (hQ := by rw [List.length_append, hlen_nb1, hgap1_init]); intro out4_init hout4_init
  apply sepWP_abstract_bytes (s0.sp - 168#64) (fun bs => bs.length = 40)
    (hQ := by rw [List.length_append, hlen_nb2, hgap2_init]); intro out5_init hout5_init
  clear gap1_init hgap1_init gap2_init hgap2_init hlen_nb1 hlen_nb2 hnb1_eq hnb2_eq nb1 nb2
  -- Call 4: mul(sp + 0x50, self.Y, other.Z) -> s0.sp - 208#64
  obtain ⟨hy1_l, hy1_0, hy1_1, hy1_2, hy1_3, hy1_4⟩ := fe51LimbsBounded_drop40_take40 a_2 h_4.1 h_4.2.2.1
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hy1_l hy1_0 hy1_1 hy1_2 hy1_3 hy1_4 hz2_l hz2_0 hz2_1 hz2_2 hz2_3 hz2_4 out4_init hout4_init
  obtain ⟨hw2_len, h2l0, h2l1, h2l2, h2l3, h2l4⟩ := ‹fe51LimbsBounded w_2 (2 ^ 52)›
  -- Call 5: mul(x29 - 0x68, other.Y, self.Z) -> s0.sp - 168#64
  obtain ⟨hy2_l, hy2_0, hy2_1, hy2_2, hy2_3, hy2_4⟩ := fe51LimbsBounded_drop40_take40 a_rest h_1.1 h_1.2.2.1
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hy2_l hy2_0 hy2_1 hy2_2 hy2_3 hy2_4 hz1_l hz1_0 hz1_1 hz1_2 hz1_3 hz1_4 out5_init hout5_init
  obtain ⟨hw3_len, h3m0, h3m1, h3m2, h3m3, h3m4⟩ := ‹fe51LimbsBounded w_3 (2 ^ 52)›
  -- Block 2: interleaved to_bytes of w_2 and w_3
  have h_w2 := pointsToBytes40_eq_cells (s0.sp - 208#64) w_2 hw2_len
  have h_w3 := pointsToBytes40_eq_cells (s0.sp - 168#64) w_3 hw3_len
  have h_open3 := pointsToBytes32_eq_cells8 (s0.sp - 128#64) buf3_init hbuf3_init
  have h_open4 := pointsToBytes32_eq_cells8 (s0.sp - 96#64) buf4_init hbuf4_init
  simp only [bv64_sub_add, BitVec.reduceSub] at h_w2 h_w3 h_open3 h_open4
  wp_conv_pre => rw [h_w2, h_w3, h_open3, h_open4]
  clear h_open3 h_open4
  generalize h2l0_eq : ByteSlice.readLE w_2 0 8 = l2_0 at *
  generalize h2l1_eq : ByteSlice.readLE w_2 8 8 = l2_1 at *
  generalize h2l2_eq : ByteSlice.readLE w_2 16 8 = l2_2 at *
  generalize h2l3_eq : ByteSlice.readLE w_2 24 8 = l2_3 at *
  generalize h2l4_eq : ByteSlice.readLE w_2 32 8 = l2_4 at *
  generalize h3m0_eq : ByteSlice.readLE w_3 0 8 = m3_0 at *
  generalize h3m1_eq : ByteSlice.readLE w_3 8 8 = m3_1 at *
  generalize h3m2_eq : ByteSlice.readLE w_3 16 8 = m3_2 at *
  generalize h3m3_eq : ByteSlice.readLE w_3 24 8 = m3_3 at *
  generalize h3m4_eq : ByteSlice.readLE w_3 32 8 = m3_4 at *
  wp_cut_codeLoaded
  wp_sym_steps 22
  generalize h2h0 : (l2_0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (l2_4 >>> 51)) * 19#64 = h2_0
  generalize h2h1 : (l2_1 &&& 2251799813685247#64) + l2_0 >>> 51 = h2_1
  generalize h2h2 : (l2_2 &&& 2251799813685247#64) + l2_1 >>> 51 = h2_2
  generalize h2h3 : (l2_3 &&& 2251799813685247#64) + l2_2 >>> 51 = h2_3
  generalize h2h4 : (l2_4 &&& 2251799813685247#64) + l2_3 >>> 51 = h2_4
  generalize h2q : (h2_4 + (h2_3 + (h2_2 + (h2_1 + (h2_0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = q2
  generalize h2u0 : h2_0 + BitVec.setWidth 64 (BitVec.setWidth 32 q2) * 19#64 = u2_0
  wp_sym_steps 86
  generalize h2u1 : h2_1 + u2_0 >>> 51 = u2_1
  generalize h2u2 : h2_2 + u2_1 >>> 51 = u2_2
  generalize h2u3 : h2_3 + u2_2 >>> 51 = u2_3
  generalize h2u4 : h2_4 + u2_3 >>> 51 = u2_4
  generalize h3mh0 : (m3_0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (m3_4 >>> 51)) * 19#64 = mh3_0
  generalize h3mh1 : (m3_1 &&& 2251799813685247#64) + m3_0 >>> 51 = mh3_1
  generalize h3mh2 : (m3_2 &&& 2251799813685247#64) + m3_1 >>> 51 = mh3_2
  generalize h3mh3 : (m3_3 &&& 2251799813685247#64) + m3_2 >>> 51 = mh3_3
  generalize h3mh4 : (m3_4 &&& 2251799813685247#64) + m3_3 >>> 51 = mh3_4
  generalize h3mq : (mh3_4 + (mh3_3 + (mh3_2 + (mh3_1 + (mh3_0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = mq3
  generalize h3mu0 : mh3_0 + BitVec.setWidth 64 (BitVec.setWidth 32 mq3) * 19#64 = mu3_0
  wp_sym_steps 79
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_b2
  dsimp only [State.setMem, State.mem] at hcl_b2
  generalize h3mu1 : mh3_1 + mu3_0 >>> 51 = mu3_1
  generalize h3mu2 : mh3_2 + mu3_1 >>> 51 = mu3_2
  generalize h3mu3 : mh3_3 + mu3_2 >>> 51 = mu3_3
  generalize h3mu4 : mh3_4 + mu3_3 >>> 51 = mu3_4
  have h_pack3 := pointsToBytes_packCanonical51Bytes (s0.sp - 128#64) u2_0 u2_1 u2_2 u2_3 u2_4
  have h_pack4 := pointsToBytes_packCanonical51Bytes (s0.sp - 96#64) mu3_0 mu3_1 mu3_2 mu3_3 mu3_4
  simp only [bv64_sub_add, BitVec.reduceSub] at h_pack3 h_pack4
  have h_bytes3 := fe51_to_bytes_of_bytes w_2 l2_0 l2_1 l2_2 l2_3 l2_4 h2l0_eq h2l1_eq h2l2_eq h2l3_eq h2l4_eq
    h2l0 h2l1 h2l2 h2l3 h2l4 h2_0 h2_1 h2_2 h2_3 h2_4 q2 u2_0 u2_1 u2_2 u2_3 u2_4
    h2h0 h2h1 h2h2 h2h3 h2h4 h2q h2u0 h2u1 h2u2 h2u3 h2u4
  have h_bytes4 := fe51_to_bytes_of_bytes w_3 m3_0 m3_1 m3_2 m3_3 m3_4 h3m0_eq h3m1_eq h3m2_eq h3m3_eq h3m4_eq
    h3m0 h3m1 h3m2 h3m3 h3m4 mh3_0 mh3_1 mh3_2 mh3_3 mh3_4 mq3 mu3_0 mu3_1 mu3_2 mu3_3 mu3_4
    h3mh0 h3mh1 h3mh2 h3mh3 h3mh4 h3mq h3mu0 h3mu1 h3mu2 h3mu3 h3mu4
  have hlen_nb3 : (natToLeBytes 32 (fe51ValOfBytes w_2 % p25519)).length = 32 := by simp [natToLeBytes]
  have hlen_nb4 : (natToLeBytes 32 (fe51ValOfBytes w_3 % p25519)).length = 32 := by simp [natToLeBytes]
  generalize hnb3_eq : natToLeBytes 32 (fe51ValOfBytes w_2 % p25519) = nb3 at hlen_nb3 h_bytes3
  generalize hnb4_eq : natToLeBytes 32 (fe51ValOfBytes w_3 % p25519) = nb4 at hlen_nb4 h_bytes4
  wp_conv_pre =>
    rw [← h_w2, ← h_w3, h_pack3, h_pack4, h_bytes3, h_bytes4]
  clear h_w2 h_w3 h_pack3 h_pack4 h_bytes3 h_bytes4 buf3_init hbuf3_init buf4_init hbuf4_init
    h2h0 h2h1 h2h2 h2h3 h2h4 h2q h2u0 h2u1 h2u2 h2u3 h2u4 h2_0 h2_1 h2_2 h2_3 h2_4 q2 u2_0 u2_1 u2_2
    h3mh0 h3mh1 h3mh2 h3mh3 h3mh4 h3mq h3mu0 h3mu1 h3mu2 h3mu3 h3mu4 mh3_0 mh3_1 mh3_2 mh3_3 mh3_4 mq3
    h2l0 h2l1 h2l2 h2l3 h2l4 h3m0 h3m1 h3m2 h3m3 h3m4
    h2l0_eq h2l1_eq h2l2_eq h2l3_eq h2l4_eq l2_0 l2_1 l2_2 l2_3 l2_4
    h3m0_eq h3m1_eq h3m2_eq h3m3_eq h3m4_eq m3_0 m3_1 m3_2 m3_3 m3_4
  -- Call 6: slice32_ct_eq(x29 - 0x40, x29 - 0x20)
  apply sepWP_callee_shrink (s0.sp - 288#64) 224 64 160
  wp_steps; wp_dalek_call slice32_ct_eq_ok; clean_prev_sf; norm_sf 64
  clear u2_3 u2_4 mu3_0 mu3_1 mu3_2 mu3_3 mu3_4
  rw [← hnb3_eq, ← hnb4_eq] at hpost_5
  generalize hr_c6 : sf_1.readReg64 (Reg.gpr 0#5) = r_c6 at hpost_5
  have hr_c6_32 : sf_1.readReg32 (Reg.gpr 0#5) = BitVec.truncate 32 r_c6 :=
    congrArg (BitVec.truncate 32) hr_c6
  apply sepWP_callee_grow (s0.sp - 288#64) 224 64 160
  wp_steps
  close_cells (s0.sp - 64#64) 64 8
  apply sepWP_unpeel_stack_bytes s0.sp 96 32 64 (hbs := hlen_nb4)
  apply sepWP_unpeel_stack_bytes s0.sp 128 32 96 (hbs := hlen_nb3)
  apply sepWP_unpeel_stack_bytes s0.sp 168 40 128 (hbs := hw3_len)
  apply sepWP_unpeel_stack_bytes s0.sp 208 40 168 (hbs := hw2_len)
  apply sepWP_unpeel_stack_bytes s0.sp 248 40 208 (hbs := hw1_len)
  apply sepWP_unpeel_stack_bytes s0.sp 288 40 248 (hbs := hw_len)
  apply sepWP_merge_stack_callee 224 288
  apply sepWP_fold_point160 a_1 a_2 (h := h_4.1)
  apply sepWP_fold_point160 a a_rest (h := h_1.1)
  apply sepWP_callee_shrink s0.sp 512 16 496
  wp_dalek_tailcall black_box_u8_ok
  clean_prev_sf
  rw [merge_stack_16_496 s0 sf (by assumption)]
  change _ = BitVec.zeroExtend 8 _ at hpost_6
  rw [zeroExtend8_and32 r_c6 r_c3 _ _ hpost_2 hpost_5,
      edPointEq_of_muls a_2 a_rest w w_1 w_2 w_3 hpost hpost_1 hpost_3 hpost_4] at hpost_6
  wp_done

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
theorem edwards_point_compress_ok_of
    (hMul : Fe51MulOk) (hPow2k : Fe51Pow2kOk) (hPow22501 : Fe51Pow22501Ok) :
    EdwardsPointCompressOk := by
  intro _
  apply dalekCaller_ok dalekCliPC14 dalekCliPl14
  intro b hb hbase
  wp_init
  apply sepWP_split_stack_callee 1040 512
  apply sepWP_peel_stack_region s0.sp 512 184 328
  apply sepWP_peel_stack_bytes s0.sp 328 40 288; intro recip_init hrecip_init
  apply sepWP_peel_stack_bytes s0.sp 288 40 248; intro c19_init hc19_init
  apply sepWP_peel_stack_bytes s0.sp 248 8 240; intro gap1_init hgap1_init
  apply sepWP_peel_stack_bytes s0.sp 240 40 200; intro c3_init hc3_init
  apply sepWP_peel_stack_bytes s0.sp 200 8 192; intro gap2_init hgap2_init
  apply sepWP_peel_stack_bytes s0.sp 192 80 112; intro pow_init hpow_init
  apply sepWP_peel_stack_bytes s0.sp 112 16 96; intro gap3_init hgap3_init
  open_cells (s0.sp - 96#64) 96 12
  wp_conv_pre =>
    rw [pointsToBytes160_split4 a a_rest h_1.1]
  -- Call 1: pow22501(x29 - 0x60, self.Z) -> s0.sp - 192#64
  obtain ⟨hz_l, hz_0, hz_1, hz_2, hz_3, hz_4⟩ := fe51LimbsBounded_drop80_take40 a_rest h_1.1 h_1.2.2.2.1
  wp_cut_codeLoaded
  wp_steps; wp_dalek_call hPow22501; clean_prev_sf; norm_sf 1040
  clear hz_l hz_0 hz_1 hz_2 hz_3 hz_4 pow_init hpow_init
  have h_w_b : fe51LimbsBounded w (2 ^ 52) := ‹_›
  have h_w1_b : fe51LimbsBounded w_1 (2 ^ 52) := ‹_›
  have h_pow19 : fe51ValOfBytes w % p25519 =
      fpPow (fe51ValOfBytes ((a_rest.drop 80).take 40) % p25519) (2 ^ 250 - 1) := ‹_›
  have h_pow11 : fe51ValOfBytes w_1 % p25519 =
      fpPow (fe51ValOfBytes ((a_rest.drop 80).take 40) % p25519) 11 := ‹_›
  apply sepWP_split_bytes_append s0.sp 192 40 152 (hbs1 := h_w_b.1)
  obtain ⟨hw_l, hw_0, hw_1, hw_2, hw_3, hw_4⟩ := fe51LimbsBounded_of_52 w h_w_b
  obtain ⟨hw1_l, hw1_0, hw1_1, hw1_2, hw1_3, hw1_4⟩ := fe51LimbsBounded_of_52 w_1 h_w1_b
  wp_cut_codeLoaded
  wp_steps
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_copy5
  dsimp only [State.setMem, State.mem] at hcl_copy5
  wp_conv_pre =>
    rw [write64_copy5_eq c19_init w hc19_init hw_l,
        write64_copy5_eq c3_init w_1 hc3_init hw1_l]
  -- Call 2: pow2k(x29 - 0x60, sp + 0xe0, 5) -> s0.sp - 192#64
  apply sepWP_callee_shrink (s0.sp - 512#64) 1040 96 944
  wp_dalek_call hPow2k; clean_prev_sf; norm_sf 96
  apply sepWP_callee_grow (s0.sp - 512#64) 1040 96 944
  clear hw_0 hw_1 hw_2 hw_3 hw_4 c19_init hc19_init c3_init hc3_init
  obtain ⟨hw2_l, hw2_0, hw2_1, hw2_2, hw2_3, hw2_4⟩ := fe51LimbsBounded_of_52 w_2 ‹fe51LimbsBounded w_2 _›
  -- Call 3: mul(sp + 0xb8, x29 - 0x60, sp + 0x110) -> s0.sp - 328#64 (recip)
  apply sepWP_callee_shrink (s0.sp - 512#64) 1040 224 816
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hw1_0 hw1_1 hw1_2 hw1_3 hw1_4 hw2_0 hw2_1 hw2_2 hw2_3 hw2_4 recip_init hrecip_init
  obtain ⟨hw3_l, hw3_0, hw3_1, hw3_2, hw3_3, hw3_4⟩ := fe51LimbsBounded_of_52 w_3 ‹fe51LimbsBounded w_3 _›
  obtain ⟨hx_l, hx_0, hx_1, hx_2, hx_3, hx_4⟩ := fe51LimbsBounded_take40 a_rest h_1.1 h_1.2.1
  -- Call 4: mul(x21, self.X, sp + 0xb8) -> s0.sp - 192#64 (x)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  clear hx_l hx_0 hx_1 hx_2 hx_3 hx_4
  obtain ⟨hy_l, hy_0, hy_1, hy_2, hy_3, hy_4⟩ := fe51LimbsBounded_drop40_take40 a_rest h_1.1 h_1.2.2.1
  -- Call 5: mul(x29 - 0x38, self.Y, sp + 0xb8) -> s0.sp - 152#64 (y)
  wp_steps; wp_dalek_call hMul; clean_prev_sf; norm_sf 224
  apply sepWP_callee_grow (s0.sp - 512#64) 1040 224 816
  clear hy_l hy_0 hy_1 hy_2 hy_3 hy_4 hw3_0 hw3_1 hw3_2 hw3_3 hw3_4
  -- Open spill slots (184 bytes = 23 u64 cells), x_bs (w_4), y_bs (w_5), and out (a_1)
  open_cells (s0.sp - 512#64) 184 23
  apply sepWP_split32_sub s0.sp 488#64 484#64
  apply sepWP_split32_sub s0.sp 432#64 428#64
  apply sepWP_split32_sub s0.sp 376#64 372#64
  have h_w4 := pointsToBytes40_sub_eq_cells s0.sp 192#64 184#64 176#64 168#64 160#64 w_4 ‹fe51LimbsBounded w_4 _›.1
  have h_w5 := pointsToBytes40_sub_eq_cells s0.sp 152#64 144#64 136#64 128#64 120#64 w_5 ‹fe51LimbsBounded w_5 _›.1
  wp_conv_pre =>
    rw [h_w4, h_w5]
  obtain ⟨hw4_len, hxl0, hxl1, hxl2, hxl3, hxl4⟩ := ‹fe51LimbsBounded w_4 (2 ^ 52)›
  obtain ⟨hw5_len, hyl0, hyl1, hyl2, hyl3, hyl4⟩ := ‹fe51LimbsBounded w_5 (2 ^ 52)›
  generalize hxl0_eq : ByteSlice.readLE w_4 0 8 = lx0 at *
  generalize hxl1_eq : ByteSlice.readLE w_4 8 8 = lx1 at *
  generalize hxl2_eq : ByteSlice.readLE w_4 16 8 = lx2 at *
  generalize hxl3_eq : ByteSlice.readLE w_4 24 8 = lx3 at *
  generalize hxl4_eq : ByteSlice.readLE w_4 32 8 = lx4 at *
  generalize hyl0_eq : ByteSlice.readLE w_5 0 8 = ly0 at *
  generalize hyl1_eq : ByteSlice.readLE w_5 8 8 = ly1 at *
  generalize hyl2_eq : ByteSlice.readLE w_5 16 8 = ly2 at *
  generalize hyl3_eq : ByteSlice.readLE w_5 24 8 = ly3 at *
  generalize hyl4_eq : ByteSlice.readLE w_5 32 8 = ly4 at *
  -- Step +0x09c .. +0x0fc (25 instructions)
  wp_cut_codeLoaded
  wp_sym_steps 25
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_c1
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl_c1
  generalize hhx0 : (lx0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (lx4 >>> 51)) * 19#64 = hx0
  generalize hhx1 : (lx1 &&& 2251799813685247#64) + lx0 >>> 51 = hx1
  generalize hhy0 : (ly0 &&& 2251799813685247#64) + BitVec.setWidth 64 (BitVec.setWidth 32 (ly4 >>> 51)) * 19#64 = hy0
  generalize hhy1 : (ly1 &&& 2251799813685247#64) + ly0 >>> 51 = hy1
  generalize hhy2 : (ly2 &&& 2251799813685247#64) + ly1 >>> 51 = hy2
  generalize hhy3 : (ly3 &&& 2251799813685247#64) + ly2 >>> 51 = hy3
  wp_conv_pre => rw [← h_w4, ← h_w5]
  -- Step +0x100 .. +0x124 (10 instructions)
  wp_cut_codeLoaded
  wp_sym_steps 10
  generalize hhy4 : (ly4 &&& 2251799813685247#64) + ly3 >>> 51 = hy4
  generalize hhx2 : (lx2 &&& 2251799813685247#64) + lx1 >>> 51 = hx2
  generalize hhx3 : (lx3 &&& 2251799813685247#64) + lx2 >>> 51 = hx3
  generalize hhx4 : (lx4 &&& 2251799813685247#64) + lx3 >>> 51 = hx4
  -- Step +0x128 .. +0x138 (5 instructions) -> qy
  wp_sym_steps 5
  generalize hqy : (hy4 + (hy3 + (hy2 + (hy1 + (hy0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = qy
  -- Step +0x13c .. +0x140 (2 instructions) -> uy0, qx
  wp_sym_steps 2
  generalize hqx : (hx4 + (hx3 + (hx2 + (hx1 + (hx0 + 19#64) >>> 51) >>> 51) >>> 51) >>> 51) >>> 51 = qx
  generalize huy0 : hy0 + BitVec.setWidth 64 (BitVec.setWidth 32 qy) * 19#64 = uy0
  -- Step +0x144 (1 instruction) -> uy1
  wp_sym_steps 1
  generalize huy1 : hy1 + uy0 >>> 51 = uy1
  -- Step +0x148 .. +0x160 (7 instructions) -> uy2
  wp_sym_steps 7
  generalize huy2 : hy2 + uy1 >>> 51 = uy2
  -- Step +0x164 .. +0x190 (12 instructions) -> uy3
  wp_sym_steps 12
  generalize huy3 : hy3 + uy2 >>> 51 = uy3
  -- Step +0x194 .. +0x1a4 (5 instructions) -> uy4
  wp_sym_steps 5
  generalize huy4 : hy4 + uy3 >>> 51 = uy4
  -- Step +0x1a8 .. +0x22c (34 instructions) to bl black_box (+0x230)
  wp_sym_steps 34
  apply SepWP.done
  · rfl
  · assumption
  intro hcl_c2
  try dsimp only [State.setMem, State.setPC, State.writeReg64, State.advancePC, State.mem] at hcl_c2
  -- Call 6: black_box::<u8> at +0x230 (stack 16)
  apply sepWP_callee_shrink (s0.sp - 512#64) 1040 16 1024
  wp_steps; wp_dalek_call black_box_u8_ok; clean_prev_sf; norm_sf 16
  apply sepWP_callee_grow (s0.sp - 512#64) 1040 16 1024
  have hsub1552 : (s0.sp - 512#64) - 1040#64 = s0.sp - 1552#64 := by bv_bits
  wp_conv_pre => rw [hsub1552, pointsToBytes32_eq_cells8 a_1 a_2 h_4]
  -- Step +0x234 .. +0x30c (55 instructions)
  wp_sym_steps 55
  apply sepWP_combine32_sub s0.sp 488#64 484#64
  apply sepWP_combine32_sub s0.sp 432#64 428#64
  apply sepWP_combine32_sub s0.sp 376#64 372#64
  close_cells (s0.sp - 512#64) 184 23
  have h_bytes_y := fe51_to_bytes_of_bytes w_5 ly0 ly1 ly2 ly3 ly4 hyl0_eq hyl1_eq hyl2_eq hyl3_eq hyl4_eq
    hyl0 hyl1 hyl2 hyl3 hyl4 hy0 hy1 hy2 hy3 hy4 qy uy0 uy1 uy2 uy3 uy4
    hhy0 hhy1 hhy2 hhy3 hhy4 hqy huy0 huy1 huy2 huy3 huy4
  have h_sign_x := fe51_sign_of_bytes w_4 lx0 lx1 lx2 lx3 lx4 hxl0_eq hxl1_eq hxl2_eq hxl3_eq hxl4_eq
    hxl0 hxl1 hxl2 hxl3 hxl4 hx0 hx1 hx2 hx3 hx4 qx
    hhx0 hhx1 hhx2 hhx3 hhx4 hqx
  have h_enc := encodeEd_of_muls a_rest w w_1 w_2 w_3 w_4 w_5 h_pow19 h_pow11 hpost_1 hpost_2 hpost_3 hpost_4
  wp_conv_pre =>
    rw [compress_byte31_eq,
        pointsToBytes_setByte31Or_packCanonical51Bytes,
        hpost_5, h_bytes_y, h_sign_x, h_enc]
  -- Epilogue (+0x310 .. +0x32c)
  wp_steps
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_bytes s0.sp 112 16 96 (hbs := hgap3_init)
  apply sepWP_unpeel_stack_bytes s0.sp 152 40 112 (hbs := hw5_len)
  apply sepWP_unpeel_stack_bytes s0.sp 192 40 152 (hbs := hw4_len)
  apply sepWP_unpeel_stack_bytes s0.sp 200 8 192 (hbs := hgap2_init)
  apply sepWP_unpeel_stack_bytes s0.sp 240 40 200 (hbs := hw1_l)
  apply sepWP_unpeel_stack_bytes s0.sp 248 8 240 (hbs := hgap1_init)
  apply sepWP_unpeel_stack_bytes s0.sp 288 40 248 (hbs := hw_l)
  apply sepWP_unpeel_stack_bytes s0.sp 328 40 288 (hbs := hw3_l)
  apply sepWP_unpeel_stack_region s0.sp 512 184 328
  apply sepWP_merge_stack_callee 1040 512
  apply sepWP_fold_point160 a a_rest (h := h_1.1)
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PointCompress2
