/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51Base
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Edwards curve point arithmetic machine-code proofs

Verifies `x25519CliMultiLib` blocks `07` (`ProjectivePoint::double`), `08`
(`&EdwardsPoint + &AffineNielsPoint`), and `09` (`EdwardsPoint::mul_by_pow_2`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CurveModels

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul fpNeg fpSq fpPow)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs (x25519CliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (
  X25519CliPlacement x25519CliMpl x25519Caller_ok
  resolve_blk01 resolve_blk02 resolve_blk07)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.InternalSpecs (
  fe51LimbsBounded fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edProjDouble edAsProjective edAddAffineNiels edDouble4 fpPow_two_eq_fpSq
  Fe51MulOk Fe51Pow2kOk
  ProjectivePointDoubleOk EdwardsPointAddAffineNielsOk EdwardsPointMulByPow2_4Ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add
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
  edAddNiels_epilogue_post
  proj_copy15_prologue_post proj_copy15_loop_post fe51_mul_post_props
  sepWP_split4_160 sepWP_merge4_160
  sepWP_merge4_stack_bytes sepWP_merge4_stack_512
  sepWP_split4_completed_224 sepWP_split4_completed_512
  sepWP_callee_224_to_400 sepWP_callee_400_to_224
  edAsExtended_of_append4)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.Field51 (
  fe51_pow2k_ok fe51_mul_ok)

arm64_proof_prelude

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 07 x25519CliMultiLib X25519CliPlacement 144 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl07_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl07.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 08 x25519CliMultiLib X25519CliPlacement 152 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl08_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl08.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedCodeBase (x25519CliMpl) in
gen_block_fetches x25519Cli 09 x25519CliMultiLib X25519CliPlacement 79 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem x25519CliPl09_rho_norm [X25519CliPlacement] (sym : String) :
    x25519CliPl09.ρ sym = x25519CliMultiLib.resolve x25519CliMpl sym := rfl

private theorem sepWP_head_region_sub (sp : BitVec 64) (off off' n m : Nat) {v : BitVec 64}
    {prog : Program} {tpc : BitVec 64} {s : State} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = (((sp - BitVec.ofNat 64 off) ↦₆₄ v) ∗ memRegion (sp - BitVec.ofNat 64 off') m) ∗ F := by sep_focus)
    (hoff : off = off' + 8 := by decide) (hnm : n = 8 + m := by decide) (hb : n ≤ 2 ^ 64 := by decide)
    (h : SepWP prog tpc s (memRegion (sp - BitVec.ofNat 64 off) n ∗ F) post oom) :
    SepWP prog tpc s P post oom := by
  have ha : sp - BitVec.ofNat 64 off + 8#64 = sp - BitVec.ofNat 64 off' := by
    rw [sub_ofNat64_add sp off 8 (by omega), show off - 8 = off' by omega]
  rw [← ha] at hP; exact SepWP.head_region (sp - BitVec.ofNat 64 off) n m hnm hb hP h

local syntax "close_cells_sub " term:max num num num : tactic
macro_rules
  | `(tactic| close_cells_sub $sp $off $n $k) => do
    let (off, n, k) := (off.getNat, n.getNat, k.getNat)
    if k == 0 then `(tactic| skip) else
    if n == 8 then
      let offLit := Lean.Syntax.mkNumLit (toString off)
      `(tactic| apply SepWP.last_region ($sp - BitVec.ofNat 64 $offLit))
    else
      let offLit := Lean.Syntax.mkNumLit (toString off)
      let off'Lit := Lean.Syntax.mkNumLit (toString (off - 8))
      let nLit := Lean.Syntax.mkNumLit (toString n)
      let n'Lit := Lean.Syntax.mkNumLit (toString (n - 8))
      let k'Lit := Lean.Syntax.mkNumLit (toString (k - 1))
      `(tactic| (close_cells_sub $sp $off'Lit $n'Lit $k'Lit; apply sepWP_head_region_sub $sp $offLit $off'Lit $nLit $n'Lit))

public section

set_option maxHeartbeats 800000 in
/-- Conditional `<ProjectivePoint>::double` (`Blk07`, 144 insns) contract. -/
theorem projective_point_double_ok_of (hPow2k : Fe51Pow2kOk) : ProjectivePointDoubleOk := by
  intro _
  apply x25519Caller_ok x25519CliPC07 x25519CliPl07
  intro b hb hbase
  wp_init
  have hout_len : a_2.length = 160 := by assumption
  have hself_len : a_rest.length = 120 := by assumption
  have hself0 : fe51LimbsBoundedAt a_rest 0 (2 ^ 53) := by assumption
  have hself40 : fe51LimbsBoundedAt a_rest 40 (2 ^ 53) := by assumption
  have hself80 : fe51LimbsBoundedAt a_rest 80 (2 ^ 54) := by assumption
  have : HasLenGe a_2 160 := ⟨by omega⟩
  have : HasLenGe a_rest 120 := ⟨by omega⟩
  apply sepWP_split_stack_callee 96 304
  apply sepWP_peel_stack_bytes s0.sp 304 40 264; intro s_0 hs_0
  apply sepWP_peel_stack_bytes s0.sp 264 40 224; intro s_40 hs_40
  apply sepWP_peel_stack_bytes s0.sp 224 40 184; intro s_80 hs_80
  apply sepWP_peel_stack_bytes s0.sp 184 40 144; intro s_120 hs_120
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro s_160 hs_160
  open_cells (s0.sp - 104#64) 104 13
  have : HasLenGe s_120 40 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_steps
  -- Call 1: pow2k(self + 0, 1) -> sp + 0
  apply sepWP_focus_bytes a a 0 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself0
  wp_x25519_call hPow2k
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a a 0 40
  norm_sf 96
  -- Call 2: pow2k(self + 40, 1) -> sp + 40
  wp_steps
  apply sepWP_focus_bytes a (a + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself40
  wp_x25519_call hPow2k
  have hw1_b : fe51LimbsBounded w_1 (2 ^ 52) := by assumption
  have hw1_len : w_1.length = 40 := hw1_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a (a + 40#64) 40 40
  norm_sf 96
  -- Call 3: pow2k(self + 80, 1) -> sp + 80
  wp_steps
  apply sepWP_focus_bytes a (a + 80#64) 80 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hself80
  wp_x25519_call hPow2k
  have hw2_b : fe51LimbsBounded w_2 (2 ^ 52) := by assumption
  have hw2_len : w_2.length = 40 := hw2_b.1
  clean_prev_sf
  apply sepWP_unfocus_bytes a (a + 80#64) 80 40
  norm_sf 96
  -- Step to Call 4: pow2k(sp + 120, 1) -> sp + 160
  wp_cut_codeLoaded
  wp_steps
  apply sepWP_abstract_bytes (s0.sp - 184#64)
    (fun buf => fe51LimbsBounded buf (2 ^ 54) ∧
      fe51ValOfBytes buf % p25519 = fpAdd (fe51ValAt a_rest 40 % p25519) (fe51ValAt a_rest 0 % p25519))
  · unfold fe51LimbsBounded fe51ValOfBytes fe51ValAt
    simp (disch := decide) only [readLE_write64_self', readLE_write64_ne, write64_length_eq, hs_120, Nat.min_eq_left]
    exact ⟨⟨trivial, fe51Add_bounded _ _ _ _ _ _ _ _ _ _ (2 ^ 54) hself40 hself0⟩,
      fe51Add_val_mod _ _ _ _ _ _ _ _ _ _ hself40 hself0⟩
  intro buf120 ⟨hs120_b, hbuf120_v⟩
  have hs120_len : buf120.length = 40 := hs120_b.1
  unpack_fe51 hs120_b
  wp_x25519_call hPow2k
  have hw3_b : fe51LimbsBounded w_3 (2 ^ 52) := by assumption
  have hw3_len : w_3.length = 40 := hw3_b.1
  clean_prev_sf
  norm_sf 96
  -- Epilogue: step from +0x0b4 to ret (+0x23c)
  wp_steps
  close_cells_sub s0.sp 104 104 13
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


/-- `<ProjectivePoint>::double` (`Blk07`, 144 insns). -/
theorem projective_point_double_ok : ProjectivePointDoubleOk :=
  projective_point_double_ok_of fe51_pow2k_ok

set_option maxHeartbeats 800000 in
/-- Conditional `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`Blk08`, 152 insns) contract. -/
theorem edwards_point_add_affine_niels_ok_of (hMul : Fe51MulOk) : EdwardsPointAddAffineNielsOk := by
  intro _
  apply x25519Caller_ok x25519CliPC08 x25519CliPl08
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
  have : HasLenGe a_3 160 := ⟨by omega⟩
  have : HasLenGe a_4 160 := ⟨by omega⟩
  have : HasLenGe a_rest 120 := ⟨by omega⟩
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
  wp_x25519_call hMul
  have hw_b : fe51LimbsBounded w (2 ^ 52) := by assumption
  have hw_len : w.length = 40 := hw_b.1
  apply sepWP_unfocus_bytes a_2 a_2 0 40
  norm_sf 224
  -- Call 2: mul(sp + 40, other + 40) -> x29 - 0x58 (s0.sp - 184)
  wp_steps
  apply sepWP_focus_bytes a_2 (a_2 + 40#64) 40 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hother40
  wp_x25519_call hMul
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
  wp_x25519_call hMul
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
  close_cells_sub s0.sp 104 104 13
  apply sepWP_unpeel_stack_bytes s0.sp 144 40 104
  apply sepWP_unpeel_stack_bytes s0.sp 184 40 144
  apply sepWP_unpeel_stack_bytes s0.sp 224 40 184
  apply sepWP_unpeel_stack_bytes s0.sp 264 40 224
  apply sepWP_unpeel_stack_bytes s0.sp 304 40 264
  apply sepWP_merge_stack_callee 224 304
  wp_done


/-- `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`Blk08`, 152 insns). -/
theorem edwards_point_add_affine_niels_ok : EdwardsPointAddAffineNielsOk :=
  edwards_point_add_affine_niels_ok_of fe51_mul_ok

set_option maxHeartbeats 1200000 in
/-- Conditional `<EdwardsPoint>::mul_by_pow_2` (`Blk09`, 79 insns, `k = 4#32`) contract. -/
theorem edwards_point_mul_by_pow_2_4_ok_of
    (hDouble : ProjectivePointDoubleOk) (hMul : Fe51MulOk) :
    EdwardsPointMulByPow2_4Ok := by
  intro _
  apply x25519Caller_ok x25519CliPC09 x25519CliPl09
  intro b hb hbase
  wp_init
  have hself_pt : fe51Point4Bounded a_rest_1 (2 ^ 53) := by assumption
  have hk_eq : a_2 = 4#32 := by assumption
  obtain ⟨hself_len, hself0, hself40, hself80, hself120⟩ := hself_pt
  subst hk_eq
  have : HasLenGe a_rest_1 160 := ⟨by omega⟩
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
  wp_x25519_call hDouble; norm_sf 400; rw [hp1_val] at hpost
  apply sepWP_split4_completed_512 s0.sp C1
  intro c1_0 c1_1 c1_2 c1_3 hc1_0_l hc1_1_l hc1_2_l hc1_3_l hc1_0_b hc1_1_b hc1_2_b hc1_3_b hc1_0_v hc1_1_v hc1_2_v hc1_3_v
  unpack_fe51 hc1_0_b; unpack_fe51 hc1_1_b; unpack_fe51 hc1_2_b; unpack_fe51 hc1_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw1_X_l, hw1_X_b, hw1_X_v⟩ := fe51_mul_post_props w_1 P1.X
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw1_Y_l, hw1_Y_b, hw1_Y_v⟩ := fe51_mul_post_props w_2 P1.Y
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw1_Z_l, hw1_Z_b, hw1_Z_v⟩ := fe51_mul_post_props w_3 P1.Z
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
  wp_x25519_call hDouble; clean_prev_sf; norm_sf 400
  have hc2_val : edExtOfBytes w_4 = C2 := by rw [← hp2_val]; assumption
  apply sepWP_split4_completed_512 s0.sp C2
  intro c2_0 c2_1 c2_2 c2_3 hc2_0_l hc2_1_l hc2_2_l hc2_3_l hc2_0_b hc2_1_b hc2_2_b hc2_3_b hc2_0_v hc2_1_v hc2_2_v hc2_3_v
  unpack_fe51 hc2_0_b; unpack_fe51 hc2_1_b; unpack_fe51 hc2_2_b; unpack_fe51 hc2_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw2_X_l, hw2_X_b, hw2_X_v⟩ := fe51_mul_post_props w_5 P2.X
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw2_Y_l, hw2_Y_b, hw2_Y_v⟩ := fe51_mul_post_props w_6 P2.Y
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw2_Z_l, hw2_Z_b, hw2_Z_v⟩ := fe51_mul_post_props w_7 P2.Z
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
  wp_x25519_call hDouble; clean_prev_sf; norm_sf 400
  have hc3_val : edExtOfBytes w_8 = C3 := by rw [← hp3_val]; assumption
  apply sepWP_split4_completed_512 s0.sp C3
  intro c3_0 c3_1 c3_2 c3_3 hc3_0_l hc3_1_l hc3_2_l hc3_3_l hc3_0_b hc3_1_b hc3_2_b hc3_3_b hc3_0_v hc3_1_v hc3_2_v hc3_3_v
  unpack_fe51 hc3_0_b; unpack_fe51 hc3_1_b; unpack_fe51 hc3_2_b; unpack_fe51 hc3_3_b
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw3_X_l, hw3_X_b, hw3_X_v⟩ := fe51_mul_post_props w_9 P3.X
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw3_Y_l, hw3_Y_b, hw3_Y_v⟩ := fe51_mul_post_props w_10 P3.Y
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hw3_Z_l, hw3_Z_b, hw3_Z_v⟩ := fe51_mul_post_props w_11 P3.Z
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
  wp_x25519_call hDouble; clean_prev_sf; norm_sf 400
  have hc4_val : edExtOfBytes w_12 = C4 := by rw [← hp4_val]; assumption
  apply sepWP_split4_completed_224 s0.sp C4
  intro c4_0 c4_1 c4_2 c4_3 hc4_0_l hc4_1_l hc4_2_l hc4_3_l hc4_0_b hc4_1_b hc4_2_b hc4_3_b hc4_0_v hc4_1_v hc4_2_v hc4_3_v
  unpack_fe51 hc4_0_b; unpack_fe51 hc4_1_b; unpack_fe51 hc4_2_b; unpack_fe51 hc4_3_b
  apply sepWP_split4_160 a_1; intro out0 out1 out2 out3 hout0 hout1 hout2 hout3
  apply sepWP_callee_400_to_224 s0.sp
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_13 (fpMul C4.X C4.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_14 (fpMul C4.Y C4.Z)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_15 (fpMul C4.Z C4.T)
  wp_steps; wp_x25519_call hMul; clean_prev_sf; norm_sf 224; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_16 (fpMul C4.X C4.Y)
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
  wp_steps; close_cells_sub s0.sp 64 64 8
  apply sepWP_unpeel_stack_bytes s0.sp 224 160 64; apply sepWP_unpeel_stack_bytes s0.sp 232 8 224
  apply sepWP_unpeel_stack_bytes s0.sp 352 120 232; apply sepWP_unpeel_stack_bytes s0.sp 512 160 352
  apply sepWP_merge_stack_callee 400 512; wp_done


/-- `<EdwardsPoint>::mul_by_pow_2` (`Blk09`, 79 insns, `k = 4#32`). -/
theorem edwards_point_mul_by_pow_2_4_ok : EdwardsPointMulByPow2_4Ok :=
  edwards_point_mul_by_pow_2_4_ok_of projective_point_double_ok fe51_mul_ok

end

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CurveModels
