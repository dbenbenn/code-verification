/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
meta import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `NafLookupTable5::from` Loop-Iteration Helpers

Stack/buffer splitting helpers and single loop-iteration verification (`naf_table_iter`) for
`<NafLookupTable5<ProjectiveNielsPoint> as From<&EdwardsPoint>>::from` (`B20`) in `dalekCliMultiLib`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul edD2 EdExtPoint)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51_edwards_d2 fe51EdwardsD2Bytes fe51Val fe51ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (fe51EdwardsD2_val)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51MulRoRightOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes edProjDouble
  edAddProjNiels edAsExtended edAsProjNiels nafTable5Step nafTable5Points
  EdwardsPointAddProjNielsOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add readLE_write64_self' readLE_write64_ne
  fe51Add_bounded fe51Add_val_mod fe51Reduce_bounded fe51Reduce_val_mod
  bv64_add_bias0_sub fe51Sub_val_mod fe51LimbsBounded_slice_of_at
  fe51ValOfBytes_slice fold_fe51ValOfBytes sepWP_focus_bytes sepWP_unfocus_bytes
  sepWP_abstract_bytes edAsExtended_of_append4 fe51_mul_post_props
  completed_split4_props_54)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  fe51LimbsBoundedAt_mono sepWP_split4_stack sepWP_merge4_stack
  write64_5_len write64_1_len sepWP_merge2_stack sepWP_split2_stack
  fe51_mro_post_props fe51EdwardsD2Bytes_bounded54)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base

public section

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 20 dalekCliMultiLib DalekCliPlacement 317

theorem dalekCliPl20_eq [DalekCliPlacement] :
    dalekCliPl20 = dalekCliMultiLib.blockPlacement dalekCliMpl 20 := by
  unfold dalekCliPl20; rfl

theorem dalekCliPC20_eq [DalekCliPlacement] :
    dalekCliPC20 = dalekCliLib20.program dalekCliPl20 := by
  unfold dalekCliPC20; rfl

theorem dalekCliPC20_block_eq [DalekCliPlacement] :
    dalekCliPC20 = (dalekCliMultiLib.blockLib 20).program dalekCliPl20 := by
  unfold dalekCliPC20 dalekCliLib20; rfl

@[simp, arm64_norm, wp_norm]
theorem dalekCliPl20_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl20.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := by
  unfold dalekCliPl20; rfl

local macro "clean_sf " prev:ident : tactic =>
  `(tactic| (clean_prev_sf; clear_dead_vars [$prev:ident]; try clear $prev:ident))

/-! ## 1. Stack & Buffer Splitting Helpers (`stack 2640`) -/

theorem sepWP_resize_callee_576_2640 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 576 := by decide) (hok : 2064 + k = off_k := by decide)
    (hf : Full = memRegion (sp0 - 2640#64) 576 ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s ((memRegion (sp0 - 2064#64 - BitVec.ofNat 64 k) k ∗
      stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 2640#64 = sp0 - 2064#64 - 576#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - 2064#64 - BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 off_k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha0]; change SepWP prog target_pc s (stackAt (sp0 - 2064#64) 576 ∗ P) post oom
  rw [← hsum, stackAt_region (sp0 - 2064#64) low k (by omega), sepConj_comm (stackAt _ _) (memRegion _ _)]
  conv => arg 4; arg 1; arg 2; rw [ha]
  exact hnext

theorem sepWP_unresize_callee_576_2640 (sp0 : BitVec 64) (low k off_k : Nat)
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsum : low + k = 576 := by decide) (hok : 2064 + k = off_k := by decide)
    (hf : Full = (memRegion (sp0 - 2064#64 - BitVec.ofNat 64 k) k ∗
      stackAt (sp0 - BitVec.ofNat 64 off_k) low) ∗ P := by sep_frame)
    (hnext : SepWP prog target_pc s (memRegion (sp0 - 2640#64) 576 ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha0 : sp0 - 2064#64 - 576#64 = sp0 - 2640#64 := by rw [BitVec.sub_sub]; rfl
  have ha : sp0 - BitVec.ofNat 64 off_k = sp0 - 2064#64 - BitVec.ofNat 64 k := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, hok]
  rw [hf, ha, sepConj_comm (memRegion _ _) (stackAt _ _), ← stackAt_region (sp0 - 2064#64) low k (by omega), hsum]
  change SepWP prog target_pc s (memRegion (sp0 - 2064#64 - 576#64) 576 ∗ P) post oom
  rw [ha0]; exact hnext

theorem sepWP_split4_completed_272 (sp : BitVec 64) (C : EdExtPoint) {bs : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = ((sp - 272#64) ↦ₛ bs) ∗ P := by sep_frame) (hbs : bs.length = 160 := by assumption)
    (h0 : fe51LimbsBoundedAt bs 0 (2 ^ 54) := by assumption) (h40 : fe51LimbsBoundedAt bs 40 (2 ^ 54) := by assumption)
    (h80 : fe51LimbsBoundedAt bs 80 (2 ^ 54) := by assumption) (h120 : fe51LimbsBoundedAt bs 120 (2 ^ 54) := by assumption)
    (hval : edExtOfBytes bs = C := by assumption)
    (hnext : ∀ b0 b1 b2 b3 : List (BitVec 8),
      b0.length = 40 → b1.length = 40 → b2.length = 40 → b3.length = 40 →
      fe51LimbsBounded b0 (2 ^ 54) → fe51LimbsBounded b1 (2 ^ 54) →
      fe51LimbsBounded b2 (2 ^ 54) → fe51LimbsBounded b3 (2 ^ 54) →
      fe51ValOfBytes b0 % p25519 = C.X → fe51ValOfBytes b1 % p25519 = C.Y →
      fe51ValOfBytes b2 % p25519 = C.Z → fe51ValOfBytes b3 % p25519 = C.T →
      SepWP prog target_pc s ((((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗
        ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3)) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  let d1 := bs.drop 40; have hd1 : d1.length = 120 := by simp [d1, hbs]
  let d2 := d1.drop 40; have hd2 : d2.length = 80 := by simp [d2, hd1]
  have hs0 : ((sp - 272#64) ↦ₛ bs) = ((sp - 272#64) ↦ₛ bs.take 40) ∗ ((sp - 232#64) ↦ₛ d1) := by
    conv => lhs; rw [← List.take_append_drop 40 bs]
    rw [pointsToBytes_append, List.length_take, hbs, Nat.min_eq_left (by decide), sub_ofNat64_add sp 272 40]
  have hs1 : ((sp - 232#64) ↦ₛ d1) = ((sp - 232#64) ↦ₛ d1.take 40) ∗ ((sp - 192#64) ↦ₛ d2) := by
    conv => lhs; rw [← List.take_append_drop 40 d1]
    rw [pointsToBytes_append, List.length_take, hd1, Nat.min_eq_left (by decide), sub_ofNat64_add sp 232 40]
  have hs2 : ((sp - 192#64) ↦ₛ d2) = ((sp - 192#64) ↦ₛ d2.take 40) ∗ ((sp - 152#64) ↦ₛ d2.drop 40) := by
    conv => lhs; rw [← List.take_append_drop 40 d2]
    rw [pointsToBytes_append, List.length_take, hd2, Nat.min_eq_left (by decide), sub_ofNat64_add sp 192 40]
  obtain ⟨hb0, hb1, hb2, hb3, hv0, hv1, hv2, hv3⟩ :=
    completed_split4_props_54 bs C ⟨hbs, h0, h40, h80, h120⟩ hval
  rw [hf, hs0, hs1, hs2]
  exact hnext (bs.take 40) (d1.take 40) (d2.take 40) (d2.drop 40)
    hb0.1 hb1.1 hb2.1 hb3.1 hb0 hb1 hb2 hb3 hv0 hv1 hv2 hv3

theorem sepWP_merge4_stack_272 (sp : BitVec 64) {b0 b1 b2 b3 : List (BitVec 8)}
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗
                  ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3)) ∗ P := by sep_frame)
    (h0 : b0.length = 40 := by assumption) (h1 : b1.length = 40 := by assumption)
    (h2 : b2.length = 40 := by assumption) (h3 : b3.length = 40 := by assumption)
    (hnext : ∀ b160 : List (BitVec 8), b160.length = 160 →
      SepWP prog target_pc s (((sp - 272#64) ↦ₛ b160) ∗ P) post oom) :
    SepWP prog target_pc s Full post oom := by
  have ha2 : sp - 192#64 + BitVec.ofNat 64 b2.length = sp - 152#64 := by rw [h2]; exact sub_ofNat64_add sp 192 40
  have ha1 : sp - 232#64 + BitVec.ofNat 64 b1.length = sp - 192#64 := by rw [h1]; exact sub_ofNat64_add sp 232 40
  have ha0 : sp - 272#64 + BitVec.ofNat 64 b0.length = sp - 232#64 := by rw [h0]; exact sub_ofNat64_add sp 272 40
  have hm : ((sp - 272#64) ↦ₛ (b0 ++ (b1 ++ (b2 ++ b3)))) =
      ((sp - 272#64) ↦ₛ b0) ∗ ((sp - 232#64) ↦ₛ b1) ∗ ((sp - 192#64) ↦ₛ b2) ∗ ((sp - 152#64) ↦ₛ b3) := by
    rw [pointsToBytes_append, ha0, pointsToBytes_append, ha1, pointsToBytes_append, ha2]
  rw [hf, ← hm]; exact hnext (b0 ++ (b1 ++ (b2 ++ b3))) (by simp [List.length_append, h0, h1, h2, h3])

theorem asProjNiels_post_core (src t2d_bs dst : List (BitVec 8))
    (hsrc : fe51Point4Bounded src (2 ^ 52)) (ht2d_b : fe51LimbsBounded t2d_bs (2 ^ 52))
    (ht2d_v : fe51ValOfBytes t2d_bs % p25519 =
      (fe51ValOfBytes (ProofLib.ByteSlice.slice src 120 40) * fe51ValOfBytes fe51EdwardsD2Bytes) % p25519)
    (hdst_len : dst.length = 160)
    (hw :
      ByteSlice.readLE dst 0 8 = ByteSlice.readLE src 0 8 + ByteSlice.readLE src 40 8 ∧
      ByteSlice.readLE dst 8 8 = ByteSlice.readLE src 8 8 + ByteSlice.readLE src 48 8 ∧
      ByteSlice.readLE dst 16 8 = ByteSlice.readLE src 16 8 + ByteSlice.readLE src 56 8 ∧
      ByteSlice.readLE dst 24 8 = ByteSlice.readLE src 24 8 + ByteSlice.readLE src 64 8 ∧
      ByteSlice.readLE dst 32 8 = ByteSlice.readLE src 32 8 + ByteSlice.readLE src 72 8 ∧
      ByteSlice.readLE dst 40 8 =
        (((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32
            (((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) >>> 51)) * 19#64 ∧
      ByteSlice.readLE dst 48 8 =
        (((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) >>> 51) ∧
      ByteSlice.readLE dst 56 8 =
        (((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) >>> 51) ∧
      ByteSlice.readLE dst 64 8 =
        (((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) >>> 51) ∧
      ByteSlice.readLE dst 72 8 =
        (((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) >>> 51) ∧
      ByteSlice.readLE dst 80 8 = ByteSlice.readLE src 80 8 ∧
      ByteSlice.readLE dst 88 8 = ByteSlice.readLE src 88 8 ∧
      ByteSlice.readLE dst 96 8 = ByteSlice.readLE src 96 8 ∧
      ByteSlice.readLE dst 104 8 = ByteSlice.readLE src 104 8 ∧
      ByteSlice.readLE dst 112 8 = ByteSlice.readLE src 112 8 ∧
      ByteSlice.readLE dst 120 8 = ByteSlice.readLE t2d_bs 0 8 ∧
      ByteSlice.readLE dst 128 8 = ByteSlice.readLE t2d_bs 8 8 ∧
      ByteSlice.readLE dst 136 8 = ByteSlice.readLE t2d_bs 16 8 ∧
      ByteSlice.readLE dst 144 8 = ByteSlice.readLE t2d_bs 24 8 ∧
      ByteSlice.readLE dst 152 8 = ByteSlice.readLE t2d_bs 32 8) :
    fe51Point4Bounded dst (2 ^ 53) ∧
    edExtOfBytes dst = edAsProjNiels (edExtOfBytes src) := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9,
          hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19⟩ := hw
  obtain ⟨_, hs0, hs40, hs80, _⟩ := hsrc
  have hs0_53 := fe51LimbsBoundedAt_mono hs0 (b2 := 2 ^ 53)
  have hs40_53 := fe51LimbsBoundedAt_mono hs40 (b2 := 2 ^ 53)
  have hs80_53 := fe51LimbsBoundedAt_mono hs80 (b2 := 2 ^ 53)
  have ht2d_53 :
      (ByteSlice.readLE t2d_bs 0 8).toNat < 2 ^ 53 ∧ (ByteSlice.readLE t2d_bs 8 8).toNat < 2 ^ 53 ∧
      (ByteSlice.readLE t2d_bs 16 8).toNat < 2 ^ 53 ∧ (ByteSlice.readLE t2d_bs 24 8).toNat < 2 ^ 53 ∧
      (ByteSlice.readLE t2d_bs 32 8).toNat < 2 ^ 53 := by
    obtain ⟨_, h0, h1, h2, h3, h4⟩ := ht2d_b; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hadd_b := fe51Add_bounded
    (ByteSlice.readLE src 0 8) (ByteSlice.readLE src 8 8) (ByteSlice.readLE src 16 8)
    (ByteSlice.readLE src 24 8) (ByteSlice.readLE src 32 8)
    (ByteSlice.readLE src 40 8) (ByteSlice.readLE src 48 8) (ByteSlice.readLE src 56 8)
    (ByteSlice.readLE src 64 8) (ByteSlice.readLE src 72 8) (2 ^ 53) hs0 hs40
  have hadd_v := fe51Add_val_mod
    (ByteSlice.readLE src 0 8) (ByteSlice.readLE src 8 8) (ByteSlice.readLE src 16 8)
    (ByteSlice.readLE src 24 8) (ByteSlice.readLE src 32 8)
    (ByteSlice.readLE src 40 8) (ByteSlice.readLE src 48 8) (ByteSlice.readLE src 56 8)
    (ByteSlice.readLE src 64 8) (ByteSlice.readLE src 72 8) hs0_53 hs40_53
  obtain ⟨hr0, hr1, hr2, hr3, hr4⟩ := fe51Reduce_bounded
    ((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8)
    ((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64)
  have hred_b53 :
      ((((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) >>> 51)) * 19#64).toNat < 2 ^ 53 ∧
      ((((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) >>> 51)).toNat < 2 ^ 53 ∧
      ((((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 53 ∧
      ((((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 53 ∧
      ((((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 53 :=
    ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hsub_v :
      fe51Val
        ((((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 (((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) >>> 51)) * 19#64)
        ((((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) >>> 51))
        ((((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) >>> 51))
        ((((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) >>> 51))
        ((((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) &&& 2251799813685247#64) +
          (((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) >>> 51)) % p25519 =
      fpSub (fe51ValAt src 40 % p25519) (fe51ValAt src 0 % p25519) := by
    rw [fe51Reduce_val_mod, bv64_add_bias0_sub,
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hs40_53 hs0_53]; rfl
  have ht2d_v' : fe51ValOfBytes t2d_bs % p25519 = fpMul (fe51ValAt src 120 % p25519) edD2 := by
    unfold fpMul
    rw [ht2d_v, fe51ValOfBytes_slice src 120, fe51EdwardsD2_val, Nat.mod_mod, ← Nat.mul_mod]
  have hx_eq : fe51ValAt dst 0 % p25519 = fpAdd (fe51ValAt src 0 % p25519) (fe51ValAt src 40 % p25519) := by
    unfold fe51ValAt; simp only [Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]; exact hadd_v
  have hy_eq : fe51ValAt dst 40 % p25519 = fpSub (fe51ValAt src 40 % p25519) (fe51ValAt src 0 % p25519) := by
    unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]; exact hsub_v
  have hz_eq : fe51ValAt dst 80 % p25519 = fe51ValAt src 80 % p25519 % p25519 := by
    unfold fe51ValAt; simp only [Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14, Nat.mod_mod]
  have ht_eq : fe51ValAt dst 120 % p25519 = fpMul (fe51ValAt src 120 % p25519) edD2 := by
    change fe51Val (ByteSlice.readLE dst 120 8) (ByteSlice.readLE dst 128 8)
      (ByteSlice.readLE dst 136 8) (ByteSlice.readLE dst 144 8)
      (ByteSlice.readLE dst 152 8) % p25519 = _
    rw [hw15, hw16, hw17, hw18, hw19, fold_fe51ValOfBytes t2d_bs, ht2d_v']
  refine ⟨⟨hdst_len, ?_, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [fe51LimbsBoundedAt, Nat.zero_add]; rw [hw0, hw1, hw2, hw3, hw4]; exact hadd_b
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]; exact hred_b53
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]; exact hs80_53
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw15, hw16, hw17, hw18, hw19]; exact ht2d_53
  · unfold edExtOfBytes edAsProjNiels; rw [hx_eq, hy_eq, hz_eq, ht_eq]

private theorem iter_addr_i (sp0 : BitVec 64) (k_i off_i : Nat)
    (ho0 : off_i + k_i = 2032 := by decide) :
    sp0 - BitVec.ofNat 64 off_i = sp0 - 2032#64 + BitVec.ofNat 64 k_i := by
  have h1 := sub_ofNat64_add sp0 2032 k_i (by omega)
  rw [show 2032 - k_i = off_i by omega] at h1; exact h1.symm

private theorem iter_addr_i1 (sp0 : BitVec 64) (k_i off_i1 : Nat)
    (ho1 : off_i1 + k_i + 160 = 2032 := by decide) :
    sp0 - BitVec.ofNat 64 off_i1 = sp0 - 2032#64 + BitVec.ofNat 64 k_i + 160#64 := by
  have h1 := sub_ofNat64_add sp0 2032 k_i (by omega)
  have h2 := sub_ofNat64_add sp0 (2032 - k_i) 160 (by omega)
  rw [show 2032 - k_i - 160 = off_i1 by omega] at h2
  rw [← h2, ← h1]

structure NafLoopRegs [DalekCliPlacement] (s0 s : State) (pc_val x26_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 2064#64
  hx26 : s.readReg64 (Reg.gpr 26#5) = x26_val
  hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0
  hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem

set_option maxRecDepth 4096 in
private theorem ofNat_160i_add_160 {i : Nat} (hi : i < 7) :
    BitVec.ofNat 64 (160 * i) + 160#64 = BitVec.ofNat 64 (160 * (i + 1)) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 4096 in
private theorem bne_160i_1120 {i : Nat} (hi : i < 7) :
    (BitVec.ofNat 64 (160 * i) + 160#64 != 1120#64) = !(i == 6) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 4096 in
private theorem pc_iter_end (b : BitVec 64) {i : Nat} (hi : i < 7) :
    (if (BitVec.ofNat 64 (160 * i) + 160#64 != 1120#64) = true then b + 792#64 else b + 1220#64) =
      if i == 6 then b + 1220#64 else b + 792#64 := by
  rw [bne_160i_1120 hi]
  cases (i == 6) <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> rfl

/-! ## 2. Single Loop Iteration (`+0x318..+0x4c0`) -/

set_option maxHeartbeats 400000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem naf_table_iter_add [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (hbase : dalekCliPl20.base = b)
    (hAdd : EdwardsPointAddProjNielsOk)
    (hMul : Fe51MulOk)
    (s0 s : State) (A : EdExtPoint) (i : Nat)
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (ai_i a2_bs tmp660_bs comp_bs : List (BitVec 8))
    (Full P : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2640#64) 576 ∗
       ((s0.sp - 2032#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗
       ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
       ((s0.sp - 432#64) ↦ₛ tmp660_bs) ∗
       ((s0.sp - 272#64) ↦ₛ comp_bs)) ∗ P := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hregs : NafLoopRegs s0 s (b + 792#64) (BitVec.ofNat 64 (160 * i)))
    (hai_i : fe51Point4Bounded ai_i (2 ^ 53) ∧ edExtOfBytes ai_i = nafTable5Points A i)
    (ha2_b : fe51Point4Bounded a2_bs (2 ^ 52))
    (_ht660 : tmp660_bs.length = 160)
    (_hcomp : comp_bs.length = 160)
    (hnext : ∀ (s_mid : State) (ext_bs comp_bs' : List (BitVec 8)),
      s_mid.pc = b + 888#64 →
      s_mid.status = .Running →
      s_mid.sp = s0.sp - 2064#64 →
      s_mid.readReg64 (Reg.gpr 19#5) = s0.sp - 2032#64 + BitVec.ofNat 64 (160 * i) →
      s_mid.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 (160 * i) →
      s_mid.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s_mid = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s_mid.mem →
      fe51Point4Bounded ext_bs (2 ^ 52) →
      edExtOfBytes ext_bs = edAsExtended (edAddProjNiels (edExtOfBytes a2_bs) (edExtOfBytes ai_i)) →
      comp_bs'.length = 160 →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s_mid
        (((s0.sp - 432#64) ↦ₛ ext_bs) ∗
         ((s0.sp - 272#64) ↦ₛ comp_bs') ∗
         memRegion (s0.sp - 2288#64) 224 ∗
         stackAt (s0.sp - 2288#64) 352 ∗
         ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
         ((s0.sp - 2032#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗ P) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  rcases hregs with ⟨hpc, hrun, hsp, hx26, hx29, hvregs, hcl⟩
  rw [hf]
  wp_sym_steps 6
  have ha2_len : a2_bs.length = 160 := ha2_b.1
  have ha2_0 := fe51LimbsBoundedAt_mono ha2_b.2.1 (b2 := 2 ^ 53); unpack_fe51_at ha2_0
  have ha2_40 := fe51LimbsBoundedAt_mono ha2_b.2.2.1 (b2 := 2 ^ 53); unpack_fe51_at ha2_40
  have ha2_80 := fe51LimbsBoundedAt_mono ha2_b.2.2.2.1 (b2 := 2 ^ 54); unpack_fe51_at ha2_80
  have ha2_120 := fe51LimbsBoundedAt_mono ha2_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at ha2_120
  have hai_len : ai_i.length = 160 := hai_i.1.1
  have hai_0 := fe51LimbsBoundedAt_mono hai_i.1.2.1 (b2 := 2 ^ 54); unpack_fe51_at hai_0
  have hai_40 := fe51LimbsBoundedAt_mono hai_i.1.2.2.1 (b2 := 2 ^ 54); unpack_fe51_at hai_40
  have hai_80 := fe51LimbsBoundedAt_mono hai_i.1.2.2.2.1 (b2 := 2 ^ 54); unpack_fe51_at hai_80
  have hai_120 := fe51LimbsBoundedAt_mono hai_i.1.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at hai_120
  wp_dalek_call hAdd; clean_sf s
  let C := edAddProjNiels (edExtOfBytes a2_bs) (edExtOfBytes ai_i)
  have hc_val : edExtOfBytes w = C := ‹edExtOfBytes w = _›
  apply sepWP_split4_completed_272 s0.sp C
    (h0 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 0 _›)
    (h40 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 40 _›)
    (h80 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 80 _›)
    (h120 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 120 _›)
    (hval := hc_val)
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack s0.sp 432 392 352 312
  intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee_576_2640 s0.sp 352 224 2288
  wp_sym_steps 5; wp_dalek_call hMul; clean_sf sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_1 (fpMul C.X C.T)
  wp_sym_steps 5; wp_dalek_call hMul; clean_sf sf_1; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_2 (fpMul C.Y C.Z)
  wp_sym_steps 4; wp_dalek_call hMul; clean_sf sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_3 (fpMul C.Z C.T)
  wp_sym_steps 4; wp_dalek_call hMul; clean_sf sf_1; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_4 (fpMul C.X C.Y)
  norm_sf 224
  apply sepWP_merge4_stack_272 s0.sp
  intro comp_bs' hcomp'
  apply sepWP_merge4_stack s0.sp 432 392 352 312
    (fun ext_bs => fe51Point4Bounded ext_bs (2 ^ 52) ∧
      edExtOfBytes ext_bs = edAsExtended C)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w_1 w_2 w_3 w_4 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv⟩
  intro ext_bs ⟨hext_b, hext_v⟩
  have h2288 : s0.sp - 2064#64 - 224#64 = s0.sp - 2288#64 := by bv_lin
  wp_conv_pre => rw [h2288]
  exact hnext _ ext_bs comp_bs'
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    ‹_› hext_b hext_v hcomp'

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem naf_table_iter [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl20 b) (hbase : dalekCliPl20.base = b)
    (hAdd : EdwardsPointAddProjNielsOk)
    (hMul : Fe51MulOk)
    (hMRo : Fe51MulRoRightOk)
    (s0 s : State) (A : EdExtPoint) (i off_i off_i1 : Nat) (hi : i < 7)
    (target_pc : BitVec 64) (post : State → SepProp → Prop)
    (w_s10 w_s18 : BitVec 64)
    (ai_i ai_i1 a2_bs tmp5c0_120 tmp638_40 tmp660_bs comp_bs : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2640#64) 576 ∗
       ((s0.sp - 2048#64) ↦₆₄ w_s10) ∗
       ((s0.sp - 2040#64) ↦₆₄ w_s18) ∗
       ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
       ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1) ∗
       ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
       ((s0.sp - 592#64) ↦ₛ tmp5c0_120) ∗
       ((s0.sp - 472#64) ↦ₛ tmp638_40) ∗
       ((s0.sp - 432#64) ↦ₛ tmp660_bs) ∗
       ((s0.sp - 272#64) ↦ₛ comp_bs) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F := by sep_frame)
    (ho0 : off_i + 160 * i = 2032 := by decide)
    (ho1 : off_i1 + 160 * i + 160 = 2032 := by decide)
    (hsp0_align : s0.spAligned = true)
    (hregs : NafLoopRegs s0 s (b + 792#64) (BitVec.ofNat 64 (160 * i)))
    (hai_i : fe51Point4Bounded ai_i (2 ^ 53) ∧ edExtOfBytes ai_i = nafTable5Points A i)
    (hai_i1 : ai_i1.length = 160)
    (ha2_b : fe51Point4Bounded a2_bs (2 ^ 52))
    (ha2_v : edExtOfBytes a2_bs = edAsExtended (edProjDouble A.X A.Y A.Z))
    (ht5c0 : tmp5c0_120.length = 120)
    (ht638 : tmp638_40.length = 40)
    (ht660 : tmp660_bs.length = 160)
    (hcomp : comp_bs.length = 160)
    (hnext : ∀ (s' : State) (w_s10' w_s18' : BitVec 64)
      (ai_i1' tmp5c0_120' tmp638_40' tmp660_bs' comp_bs' : List (BitVec 8)),
      NafLoopRegs s0 s' (if i == 6 then b + 1220#64 else b + 792#64) (BitVec.ofNat 64 (160 * (i + 1))) →
      (fe51Point4Bounded ai_i1' (2 ^ 53) ∧ edExtOfBytes ai_i1' = nafTable5Points A (i + 1)) →
      tmp5c0_120'.length = 120 →
      tmp638_40'.length = 40 →
      tmp660_bs'.length = 160 →
      comp_bs'.length = 160 →
      SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s'
        ((memRegion (s0.sp - 2640#64) 576 ∗
          ((s0.sp - 2048#64) ↦₆₄ w_s10') ∗
          ((s0.sp - 2040#64) ↦₆₄ w_s18') ∗
          ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
          ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
          ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
          ((s0.sp - 592#64) ↦ₛ tmp5c0_120') ∗
          ((s0.sp - 472#64) ↦ₛ tmp638_40') ∗
          ((s0.sp - 432#64) ↦ₛ tmp660_bs') ∗
          ((s0.sp - 272#64) ↦ₛ comp_bs') ∗
          (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) post) :
    SepWP (dalekCliPC20.rebase b (fun _ => none)) target_pc s Full post := by
  rw [hf, iter_addr_i s0.sp (160 * i) off_i ho0, iter_addr_i1 s0.sp (160 * i) off_i1 ho1]
  apply naf_table_iter_add b _hb hbase hAdd hMul s0 s A i target_pc post
    ai_i a2_bs tmp660_bs comp_bs _ _ (by sep_frame)
    hsp0_align hregs hai_i ha2_b ht660 hcomp
  clear hregs s
  intro s_mid ext_bs comp_bs' hpc hrun hsp hx19 hx26 hx29 hvregs hcl_mid hext_b hext_v hcomp'
  have hext_len : ext_bs.length = 160 := hext_b.1
  haveI : HasLenGe ext_bs 160 := ⟨by omega⟩
  wp_cut_codeLoaded hcl_mid
  wp_sym_steps 54
  apply sepWP_focus_bytes (s0.sp - 432#64) (s0.sp - 312#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) hext_b.2.2.2.2
  obtain ⟨_, _, _, _, _, _⟩ := fe51EdwardsD2Bytes_bounded54
  wp_dalek_call hMRo; clean_sf s_mid; norm_sf 224
  obtain ⟨hw5_len, hw5_b, hw5_v⟩ := fe51_mro_post_props w ext_bs
  apply sepWP_unfocus_bytes (s0.sp - 432#64) (s0.sp - 312#64) 120 40
  apply sepWP_unresize_callee_576_2640 s0.sp 352 224 2288
  haveI : HasLenGe tmp5c0_120 120 := ⟨by omega⟩
  haveI : HasLenGe ai_i1 160 := ⟨by omega⟩
  apply sepWP_merge2_stack s0.sp 592 472 40
  intro m_bs hm_len hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136 hm144 hm152
  haveI : HasLenGe m_bs 160 := ⟨by omega⟩
  apply MultiPlacedLib.seq_codeLoaded (mid := if i == 6 then b + 1220#64 else b + 792#64) ‹_›
  wp_sym_steps 29
  have hstep_eq : edAsProjNiels (edExtOfBytes ext_bs) = nafTable5Points A (i + 1) := by
    rw [hext_v]
    show edAsProjNiels (edAsExtended (edAddProjNiels (edExtOfBytes a2_bs) (edExtOfBytes ai_i))) =
      nafTable5Step (edAsExtended (edProjDouble A.X A.Y A.Z)) (nafTable5Points A i)
    rw [ha2_v, hai_i.2]; rfl
  apply sepWP_abstract_bytes (s0.sp - 2032#64 + BitVec.ofNat 64 (160 * i) + 160#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 53) ∧ edExtOfBytes buf = nafTable5Points A (i + 1))
  · rw [← hstep_eq]
    refine asProjNiels_post_core ext_bs w _ hext_b hw5_b hw5_v (by prove_write64_len) ?_
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
      hm80, hm88, hm144, hm152, and_self]
  intro ai_i1' hai_i1'
  apply sepWP_split2_stack s0.sp 592 120 472 40
  intro tmp5c0_120' tmp638_40' ht5c0_l ht638_l
  rw [← iter_addr_i1 s0.sp (160 * i) off_i1 ho1, ← iter_addr_i s0.sp (160 * i) off_i ho0]
  have hperm :
      ((((s0.sp - 592#64) ↦ₛ tmp5c0_120') ∗ ((s0.sp - 472#64) ↦ₛ tmp638_40')) ∗
       ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
       memRegion (s0.sp - 2640#64) 576 ∗
       ((s0.sp - 432#64) ↦ₛ ext_bs) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
       ((s0.sp - 272#64) ↦ₛ comp_bs') ∗
       ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
       ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
       ((s0.sp - 2048#64) ↦₆₄ (ByteSlice.readLE ext_bs 8 8 + ByteSlice.readLE ext_bs 48 8)) ∗
       ((s0.sp - 2040#64) ↦₆₄ (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)) ∗ F) =
      ((memRegion (s0.sp - 2640#64) 576 ∗
        ((s0.sp - 2048#64) ↦₆₄ (ByteSlice.readLE ext_bs 8 8 + ByteSlice.readLE ext_bs 48 8)) ∗
        ((s0.sp - 2040#64) ↦₆₄ (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)) ∗
        ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
        ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
        ((s0.sp - 752#64) ↦ₛ a2_bs) ∗
        ((s0.sp - 592#64) ↦ₛ tmp5c0_120') ∗
        ((s0.sp - 472#64) ↦ₛ tmp638_40') ∗
        ((s0.sp - 432#64) ↦ₛ ext_bs) ∗
        ((s0.sp - 272#64) ↦ₛ comp_bs') ∗
        (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  apply SepWP.done
  · simp only [State.pc_setMem, State.pc_setPC, pc_iter_end b hi]
  · wp_norm_lhs
  intro hcl_end
  refine hnext _ (ByteSlice.readLE ext_bs 8 8 + ByteSlice.readLE ext_bs 48 8)
    (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)
    ai_i1' tmp5c0_120' tmp638_40' ext_bs comp_bs'
    ⟨?_, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, hcl_end⟩
    hai_i1' ht5c0_l ht638_l hext_len hcomp'
  · simp only [State.pc_setMem, State.pc_setPC, pc_iter_end b hi]
  · simp only [arm64_norm, ofNat_160i_add_160 hi]

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.NafLookupTable1
