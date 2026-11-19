/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `EdwardsPoint::is_torsion_free` Machine-Code Proof

Machine-code verification of `<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free`
(`B19`, 32 insns, stack 4848) in `dalekCliMultiLib`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  edExtZero edZero edOrderL edOnCurve edSmul edExtToAffine leBytesToNat)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBlockOk dalekCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51_one fe51OneBytes fe51_edwards_d2 fe51EdwardsD2Bytes
  basepoint_order basepointOrderBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edVarBaseMul edPointEq
  EdwardsPointCtEqOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.MulSpecs (
  EdwardsPointMulScalarRoOk EdwardsPointIsTorsionFreeOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add write64_length_eq
  readLE_write64_self' readLE_write64_ne
  sepWP_abstract_bytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  sepWP_split_stack_callee sepWP_merge_stack_callee)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (fe51LimbsBoundedAt_mono)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (
  fe51OneBytes_length fe51One_readLE_0 fe51One_readLE_8 fe51One_readLE_16 fe51One_readLE_24
  basepointOrderBytes_length basepointOrderBytes_val basepointOrderBytes_getD31)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (
  EdExtValid edExtValid_edExtZero edExtToAffine_edExtZero)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.ScalarMul1 (
  edPointEq_eq_beq_toAffine)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 19 dalekCliMultiLib DalekCliPlacement 32 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl19_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl19.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

/-! ## 1. Stack Resize, Identity Initialization, & `cset` Helpers -/

private theorem sepWP_callee_4496_to_512 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = memRegion (sp - 4848#64) 4496 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s
      ((memRegion (sp - 4848#64) 3984 ∗ memRegion (sp - 864#64) 512) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hsplit : memRegion (sp - 4848#64) 4496 =
      memRegion (sp - 4848#64) 3984 ∗ memRegion (sp - 864#64) 512 := by
    have h1 := memRegion_split (sp - 4848#64) 3984 512 (by decide)
    have haddr : sp - 4848#64 + BitVec.ofNat 64 3984 = sp - 864#64 :=
      sub_ofNat64_add sp 4848 3984 (by decide)
    rw [haddr] at h1; exact h1
  rw [hf, hsplit]; exact hnext

private theorem sepWP_callee_512_to_4496 (sp : BitVec 64)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (memRegion (sp - 4848#64) 3984 ∗ memRegion (sp - 864#64) 512) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp - 4848#64) 4496 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have hsplit : memRegion (sp - 4848#64) 4496 =
      memRegion (sp - 4848#64) 3984 ∗ memRegion (sp - 864#64) 512 := by
    have h1 := memRegion_split (sp - 4848#64) 3984 512 (by decide)
    have haddr : sp - 4848#64 + BitVec.ofNat 64 3984 = sp - 864#64 :=
      sub_ofNat64_add sp 4848 3984 (by decide)
    rw [haddr] at h1; exact h1
  rw [hf, ← hsplit]; exact hnext

private theorem torsion_init_id_post (dst : List (BitVec 8)) (hdst : dst.length = 160) :
    let buf := ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
      (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        dst 32 0#64) 72 0#64)
        40 (ByteSlice.readLE fe51OneBytes 0 8)) 48 (ByteSlice.readLE fe51OneBytes 8 8))
        0 0#64) 8 0#64) 16 0#64) 24 0#64)
        56 (ByteSlice.readLE fe51OneBytes 16 8)) 64 (ByteSlice.readLE fe51OneBytes 24 8))
        80 (ByteSlice.readLE fe51OneBytes 0 8)) 88 (ByteSlice.readLE fe51OneBytes 8 8))
        96 (ByteSlice.readLE fe51OneBytes 16 8)) 104 (ByteSlice.readLE fe51OneBytes 24 8))
        120 0#64) 128 0#64) 136 0#64) 144 0#64) 112 0#64) 152 0#64
    fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = edExtZero := by
  haveI : HasLenGe dst 160 := ⟨by omega⟩
  unfold fe51Point4Bounded fe51LimbsBoundedAt edExtOfBytes edExtZero
  simp (disch := decide) only [fe51ValAt, ↓readLE_write64_self', ↓readLE_write64_ne,
    write64_length_eq, hdst, fe51One_readLE_0, fe51One_readLE_8, fe51One_readLE_16, fe51One_readLE_24]
  decide +kernel

private theorem tst_w_ff_cset_ne (r : BitVec 64) (c : Bool)
    (h : BitVec.setWidth 8 r = if c then 1#8 else 0#8) :
    (if (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r) &&& 1095216660735#64) == 0#32) = true
     then (0#8 : BitVec 8) else 1#8) =
    if c then 1#8 else 0#8 := by
  have hm : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r) &&& 1095216660735#64) =
      BitVec.setWidth 32 (BitVec.setWidth 8 r) := by
    ext i hi
    have h255 := (by decide : ∀ k (hk : k < 32), (255#32)[k] = decide (k < 8)) i hi
    by_cases h8 : i < 8 <;> simp [h255, h8]
  rw [hm, h]; cases c <;> rfl

private theorem tst_w_ff_cset_ne_u32 (r : BitVec 64) (c : Bool)
    (h : BitVec.setWidth 8 r = if c then 1#8 else 0#8) :
    (if (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r) &&& 1095216660735#64) == 0#32) = true
     then (0#32 : BitVec 32) else 1#32) =
    if c then 1#32 else 0#32 := by
  have hm : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r) &&& 1095216660735#64) =
      BitVec.setWidth 32 (BitVec.setWidth 8 r) := by
    ext i hi
    have h255 := (by decide : ∀ k (hk : k < 32), (255#32)[k] = decide (k < 8)) i hi
    by_cases h8 : i < 8 <;> simp [h255, h8]
  rw [hm, h]; cases c <;> rfl

/-! ## 2. Machine-Code Verification of `<EdwardsPoint>::is_torsion_free` (`B19`) -/

public section

/-- 32-bit `w0` (`: (ret : u32)`) contract for `<EdwardsPoint>::is_torsion_free` (`B19`, 32 insns,
    stack 4848), matching `CliExternsFixed.torsionFreeSpec`'s `(sf.readReg64 .x0).setWidth 32`
    return convention directly (`cset w0, ne` zeroes bits `1..63` of `x0`). -/
abbrev rust_spec edwardsPointIsTorsionFreeU32Spec
    (ctx mpl : Obj.MultiPlacement)
    (self : ptr)
    (ghost self_bs : List (BitVec 8)) : (ret : u32)
  requires_cond fe51Point4Bounded self_bs (2 ^ 53)
  preserves     (self ↦ₛ self_bs) ∗
                (basepoint_order mpl ↦ᵣ basepointOrderBytes) ∗
                (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
                (fe51_edwards_d2 mpl ↦ᵣ fe51EdwardsD2Bytes)
  stack         4848
  ensures       ⌜ret = (if edPointEq (edVarBaseMul self_bs basepointOrderBytes) edExtZero
                        then 1#32 else 0#32) ∧
                  (EdExtValid (edExtOfBytes self_bs) →
                    ret = if edSmul edOrderL (edExtToAffine (edExtOfBytes self_bs)) == edZero
                          then 1#32 else 0#32)⌝

abbrev EdwardsPointIsTorsionFreeU32Ok : Prop :=
  DalekBlockOk 19 edwardsPointIsTorsionFreeU32Spec

set_option maxHeartbeats 800000 in
attribute [local irreducible] edVarBaseMul edSmul in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem edwards_point_is_torsion_free_ok_of
    (hMulRo : EdwardsPointMulScalarRoOk)
    (hCtEq : EdwardsPointCtEqOk) :
    EdwardsPointIsTorsionFreeOk := by
  intro _
  apply dalekCaller_ok dalekCliPC19 dalekCliPl19
  intro b _hb hbase
  wp_init
  have hself_b : fe51Point4Bounded a_rest (2 ^ 53) := by assumption
  obtain ⟨hp_l, hp0, hp40, hp80, hp120⟩ := hself_b
  unpack_fe51_at hp0; unpack_fe51_at hp40; unpack_fe51_at hp80; unpack_fe51_at hp120
  have hs_len : basepointOrderBytes.length = 32 := basepointOrderBytes_length
  have hs_31 : (basepointOrderBytes.getD 31 0#8).toNat ≤ 127 := by
    rw [basepointOrderBytes_getD31]; decide
  have h1_len : fe51OneBytes.length = 40 := fe51OneBytes_length
  haveI : HasLenGe fe51OneBytes 40 := ⟨by omega⟩
  apply sepWP_split_stack_callee 4496 352
  apply sepWP_peel_stack_bytes s0.sp 352 160 192; intro mul_init hmul_init
  apply sepWP_peel_stack_bytes s0.sp 192 160 32; intro id_init hid_init
  open_cells (s0.sp - 32#64) 32 4
  haveI : HasLenGe id_init 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  wp_dalek_call hMulRo; clean_prev_sf; norm_sf 4496
  obtain ⟨hw_b, hw_v, hw_spec⟩ :
      fe51Point4Bounded w (2 ^ 52) ∧
      edExtOfBytes w = edVarBaseMul a_rest basepointOrderBytes ∧
      (EdExtValid (edExtOfBytes a_rest) →
        EdExtValid (edExtOfBytes w) ∧
        edOnCurve (edExtToAffine (edExtOfBytes w)) = true ∧
        edExtToAffine (edExtOfBytes w) =
          edSmul (leBytesToNat basepointOrderBytes) (edExtToAffine (edExtOfBytes a_rest))) :=
    ⟨by assumption, by assumption, by assumption⟩
  wp_cut_codeLoaded
  wp_sym_steps 16
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro _hcl_id; simp only [arm64_norm] at _hcl_id
  apply sepWP_abstract_bytes (s0.sp - 192#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = edExtZero)
    (hQ := torsion_init_id_post id_init hid_init)
  intro id0 ⟨hid0_b, hid0_v⟩
  obtain ⟨hw_l, hw0, hw40, hw80, hw120⟩ := hw_b
  replace hw0 := fe51LimbsBoundedAt_mono hw0 (b2 := 2 ^ 54); unpack_fe51_at hw0
  replace hw40 := fe51LimbsBoundedAt_mono hw40 (b2 := 2 ^ 54); unpack_fe51_at hw40
  replace hw80 := fe51LimbsBoundedAt_mono hw80 (b2 := 2 ^ 54); unpack_fe51_at hw80
  replace hw120 := fe51LimbsBoundedAt_mono hw120 (b2 := 2 ^ 54); unpack_fe51_at hw120
  obtain ⟨hid0_l, hi0, hi40, hi80, hi120⟩ := hid0_b
  unpack_fe51_at hi0; unpack_fe51_at hi40; unpack_fe51_at hi80; unpack_fe51_at hi120
  apply sepWP_callee_4496_to_512 s0.sp
  wp_steps; wp_dalek_call hCtEq; clean_prev_sf; norm_sf 512
  apply sepWP_callee_512_to_4496 s0.sp
  have hce_post : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) =
      if edPointEq (edVarBaseMul a_rest basepointOrderBytes) edExtZero then 1#8 else 0#8 := by
    rw [← hw_v, ← hid0_v]; assumption
  wp_sym_steps 6
  close_cells (s0.sp - 32#64) 32 4
  apply sepWP_unpeel_stack_bytes s0.sp 192 160 32
  apply sepWP_unpeel_stack_bytes s0.sp 352 160 192
  apply sepWP_merge_stack_callee 4496 352
  have hret1 := tst_w_ff_cset_ne (sf_1.readReg64 (Reg.gpr 0#5)) _ hce_post
  by_cases hV : EdExtValid (edExtOfBytes a_rest)
  · have hmath_eq : edPointEq (edVarBaseMul a_rest basepointOrderBytes) edExtZero =
        (edSmul edOrderL (edExtToAffine (edExtOfBytes a_rest)) == edZero) := by
      obtain ⟨hW_v, _, hW_aff⟩ := hw_spec hV
      rw [hw_v] at hW_v hW_aff
      rw [edPointEq_eq_beq_toAffine hW_v edExtValid_edExtZero,
          hW_aff, basepointOrderBytes_val, edExtToAffine_edExtZero]
    wp_done
  · wp_done

set_option maxHeartbeats 800000 in
attribute [local irreducible] edVarBaseMul edSmul in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem edwards_point_is_torsion_free_u32_ok_of
    (hMulRo : EdwardsPointMulScalarRoOk)
    (hCtEq : EdwardsPointCtEqOk) :
    EdwardsPointIsTorsionFreeU32Ok := by
  intro _
  apply dalekCaller_ok dalekCliPC19 dalekCliPl19
  intro b _hb hbase
  wp_init
  have hself_b : fe51Point4Bounded a_rest (2 ^ 53) := by assumption
  obtain ⟨hp_l, hp0, hp40, hp80, hp120⟩ := hself_b
  unpack_fe51_at hp0; unpack_fe51_at hp40; unpack_fe51_at hp80; unpack_fe51_at hp120
  have hs_len : basepointOrderBytes.length = 32 := basepointOrderBytes_length
  have hs_31 : (basepointOrderBytes.getD 31 0#8).toNat ≤ 127 := by
    rw [basepointOrderBytes_getD31]; decide
  have h1_len : fe51OneBytes.length = 40 := fe51OneBytes_length
  haveI : HasLenGe fe51OneBytes 40 := ⟨by omega⟩
  apply sepWP_split_stack_callee 4496 352
  apply sepWP_peel_stack_bytes s0.sp 352 160 192; intro mul_init hmul_init
  apply sepWP_peel_stack_bytes s0.sp 192 160 32; intro id_init hid_init
  open_cells (s0.sp - 32#64) 32 4
  haveI : HasLenGe id_init 160 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  wp_dalek_call hMulRo; clean_prev_sf; norm_sf 4496
  obtain ⟨hw_b, hw_v, hw_spec⟩ :
      fe51Point4Bounded w (2 ^ 52) ∧
      edExtOfBytes w = edVarBaseMul a_rest basepointOrderBytes ∧
      (EdExtValid (edExtOfBytes a_rest) →
        EdExtValid (edExtOfBytes w) ∧
        edOnCurve (edExtToAffine (edExtOfBytes w)) = true ∧
        edExtToAffine (edExtOfBytes w) =
          edSmul (leBytesToNat basepointOrderBytes) (edExtToAffine (edExtOfBytes a_rest))) :=
    ⟨by assumption, by assumption, by assumption⟩
  wp_cut_codeLoaded
  wp_sym_steps 16
  apply SepWP.done
  · rfl
  · wp_norm_lhs
  intro _hcl_id; simp only [arm64_norm] at _hcl_id
  apply sepWP_abstract_bytes (s0.sp - 192#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = edExtZero)
    (hQ := torsion_init_id_post id_init hid_init)
  intro id0 ⟨hid0_b, hid0_v⟩
  obtain ⟨hw_l, hw0, hw40, hw80, hw120⟩ := hw_b
  replace hw0 := fe51LimbsBoundedAt_mono hw0 (b2 := 2 ^ 54); unpack_fe51_at hw0
  replace hw40 := fe51LimbsBoundedAt_mono hw40 (b2 := 2 ^ 54); unpack_fe51_at hw40
  replace hw80 := fe51LimbsBoundedAt_mono hw80 (b2 := 2 ^ 54); unpack_fe51_at hw80
  replace hw120 := fe51LimbsBoundedAt_mono hw120 (b2 := 2 ^ 54); unpack_fe51_at hw120
  obtain ⟨hid0_l, hi0, hi40, hi80, hi120⟩ := hid0_b
  unpack_fe51_at hi0; unpack_fe51_at hi40; unpack_fe51_at hi80; unpack_fe51_at hi120
  apply sepWP_callee_4496_to_512 s0.sp
  wp_steps; wp_dalek_call hCtEq; clean_prev_sf; norm_sf 512
  apply sepWP_callee_512_to_4496 s0.sp
  have hce_post : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) =
      if edPointEq (edVarBaseMul a_rest basepointOrderBytes) edExtZero then 1#8 else 0#8 := by
    rw [← hw_v, ← hid0_v]; assumption
  wp_sym_steps 6
  close_cells (s0.sp - 32#64) 32 4
  apply sepWP_unpeel_stack_bytes s0.sp 192 160 32
  apply sepWP_unpeel_stack_bytes s0.sp 352 160 192
  apply sepWP_merge_stack_callee 4496 352
  have hret1 := tst_w_ff_cset_ne_u32 (sf_1.readReg64 (Reg.gpr 0#5)) _ hce_post
  by_cases hV : EdExtValid (edExtOfBytes a_rest)
  · have hmath_eq : edPointEq (edVarBaseMul a_rest basepointOrderBytes) edExtZero =
        (edSmul edOrderL (edExtToAffine (edExtOfBytes a_rest)) == edZero) := by
      obtain ⟨hW_v, _, hW_aff⟩ := hw_spec hV
      rw [hw_v] at hW_v hW_aff
      rw [edPointEq_eq_beq_toAffine hW_v edExtValid_edExtZero,
          hW_aff, basepointOrderBytes_val, edExtToAffine_edExtZero]
    wp_done
  · wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.IsTorsionFree
