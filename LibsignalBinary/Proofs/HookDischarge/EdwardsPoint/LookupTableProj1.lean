/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `LookupTable<ProjectiveNielsPoint>::from` Machine-Code Proof

Machine-code proof in `dalekCliMultiLib` for
`<LookupTable<ProjectiveNielsPoint> as From<&EdwardsPoint>>::from` (`B25`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.LookupTableProj1

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 fpAdd fpSub fpMul edD2)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase
  dalekCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51Val fe51ValOfBytes fe51_edwards_d2 fe51EdwardsD2Bytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables (fe51EdwardsD2_val)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  fe51LimbsBounded Fe51MulOk Fe51MulRoRightOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (
  fe51LimbsBoundedAt fe51ValAt fe51Point4Bounded edExtOfBytes
  edAddProjNiels edAsExtended edExtToProjNiels projNielsTableStep
  projNielsTablePoints fe51ProjNielsTable8Bounded
  EdwardsPointAddProjNielsOk LookupTableProjNielsFromOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  HasLenGe le_length_of_hasLenGe sub_ofNat64_add readLE_write64_self' readLE_write64_ne
  fe51Reduce_bounded fe51Reduce_val_mod bv64_add_bias0_sub fe51Sub_val_mod
  fe51Add_bounded fe51Add_val_mod sepWP_focus_bytes sepWP_unfocus_bytes
  sepWP_abstract_bytes fe51LimbsBounded_slice_of_at fe51ValOfBytes_slice
  fold_fe51ValOfBytes sepWP_peel_stack_bytes sepWP_unpeel_stack_bytes
  fe51_mul_post_props edAsExtended_of_append4)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base (
  fe51LimbsBoundedAt_mono sepWP_peel_stack_region sepWP_unpeel_stack_region
  sepWP_resize_callee_576 sepWP_unresize_callee_576
  sepWP_split4_completed_264 sepWP_merge4_stack_264
  sepWP_split4_stack sepWP_merge4_stack
  sepWP_merge2_stack sepWP_split2_stack
  fe51_mro_post_props fe51EdwardsD2Bytes_bounded54
  sepWP_split7_table sepWP_merge8_table)
open scoped LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (memcpy_ok)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 25 dalekCliMultiLib DalekCliPlacement 323 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl25_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl25.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

private theorem asProjNiels_post_core54 (src t2d_bs dst : List (BitVec 8))
    (hsrc : fe51Point4Bounded src (2 ^ 53)) (ht2d_b : fe51LimbsBounded t2d_bs (2 ^ 52))
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
    fe51Point4Bounded dst (2 ^ 54) ∧
    edExtOfBytes dst = edExtToProjNiels (edExtOfBytes src) := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9,
          hw10, hw11, hw12, hw13, hw14, hw15, hw16, hw17, hw18, hw19⟩ := hw
  obtain ⟨_, hs0, hs40, hs80, _⟩ := hsrc
  have hs80_54 := fe51LimbsBoundedAt_mono hs80 (b2 := 2 ^ 54)
  have ht2d_54 :
      (ByteSlice.readLE t2d_bs 0 8).toNat < 2 ^ 54 ∧ (ByteSlice.readLE t2d_bs 8 8).toNat < 2 ^ 54 ∧
      (ByteSlice.readLE t2d_bs 16 8).toNat < 2 ^ 54 ∧ (ByteSlice.readLE t2d_bs 24 8).toNat < 2 ^ 54 ∧
      (ByteSlice.readLE t2d_bs 32 8).toNat < 2 ^ 54 := by
    obtain ⟨_, h0, h1, h2, h3, h4⟩ := ht2d_b; exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hadd_b := fe51Add_bounded
    (ByteSlice.readLE src 0 8) (ByteSlice.readLE src 8 8) (ByteSlice.readLE src 16 8)
    (ByteSlice.readLE src 24 8) (ByteSlice.readLE src 32 8)
    (ByteSlice.readLE src 40 8) (ByteSlice.readLE src 48 8) (ByteSlice.readLE src 56 8)
    (ByteSlice.readLE src 64 8) (ByteSlice.readLE src 72 8) (2 ^ 54) hs0 hs40
  have hadd_v := fe51Add_val_mod
    (ByteSlice.readLE src 0 8) (ByteSlice.readLE src 8 8) (ByteSlice.readLE src 16 8)
    (ByteSlice.readLE src 24 8) (ByteSlice.readLE src 32 8)
    (ByteSlice.readLE src 40 8) (ByteSlice.readLE src 48 8) (ByteSlice.readLE src 56 8)
    (ByteSlice.readLE src 64 8) (ByteSlice.readLE src 72 8) hs0 hs40
  obtain ⟨hr0, hr1, hr2, hr3, hr4⟩ := fe51Reduce_bounded
    ((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8)
    ((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64)
    ((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64)
  have hred_b54 :
      ((((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) >>> 51)) * 19#64).toNat < 2 ^ 54 ∧
      ((((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 40 8 + 36028797018963664#64) - ByteSlice.readLE src 0 8) >>> 51)).toNat < 2 ^ 54 ∧
      ((((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 48 8 - ByteSlice.readLE src 8 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 54 ∧
      ((((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 56 8 - ByteSlice.readLE src 16 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 54 ∧
      ((((ByteSlice.readLE src 72 8 - ByteSlice.readLE src 32 8) + 36028797018963952#64) &&& 2251799813685247#64) +
        (((ByteSlice.readLE src 64 8 - ByteSlice.readLE src 24 8) + 36028797018963952#64) >>> 51)).toNat < 2 ^ 54 :=
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
      fe51Sub_val_mod _ _ _ _ _ _ _ _ _ _ hs40 hs0]; rfl
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
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw5, hw6, hw7, hw8, hw9]; exact hred_b54
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw10, hw11, hw12, hw13, hw14]; exact hs80_54
  · dsimp only [fe51LimbsBoundedAt, Nat.reduceAdd]; rw [hw15, hw16, hw17, hw18, hw19]; exact ht2d_54
  · unfold edExtOfBytes edExtToProjNiels; rw [hx_eq, hy_eq, hz_eq, ht_eq]

private theorem iter_addr_i (sp0 : BitVec 64) (k_i off_i : Nat)
    (ho0 : off_i + k_i = 1872 := by decide) :
    sp0 - BitVec.ofNat 64 off_i = sp0 - 1872#64 + BitVec.ofNat 64 k_i := by
  have h1 := sub_ofNat64_add sp0 1872 k_i (by omega)
  rw [show 1872 - k_i = off_i by omega] at h1; exact h1.symm

private theorem iter_addr_i1 (sp0 : BitVec 64) (k_i off_i1 : Nat)
    (ho1 : off_i1 + k_i + 160 = 1872 := by decide) :
    sp0 - BitVec.ofNat 64 off_i1 = sp0 - 1872#64 + BitVec.ofNat 64 k_i + 160#64 := by
  have h1 := sub_ofNat64_add sp0 1872 k_i (by omega)
  have h2 := sub_ofNat64_add sp0 (1872 - k_i) 160 (by omega)
  rw [show 1872 - k_i - 160 = off_i1 by omega] at h2
  rw [← h2, ← h1]

private structure ProjTableLoopRegs [DalekCliPlacement] (s0 s : State) (pc_val x8_val : BitVec 64) : Prop where
  hpc : s.pc = pc_val
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 1904#64
  hx8 : s.readReg64 (Reg.gpr 8#5) = x8_val
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

private theorem pc_iter_end (b : BitVec 64) {i : Nat} (hi : i < 7) :
    (if (BitVec.ofNat 64 (160 * i) + 160#64 != 1120#64) = true then b + 772#64 else b + 1244#64) =
      if i == 6 then b + 0x4dc#64 else b + 0x304#64 := by
  rw [bne_160i_1120 hi]
  cases (i == 6) <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓ite_false, ↓ite_true] <;> rfl

set_option maxHeartbeats 400000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem proj_table_iter_add [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl25 b) (_hbase : dalekCliPl25.base = b)
    (hAdd : EdwardsPointAddProjNielsOk)
    (hMul : Fe51MulOk)
    (s0 s : State) (a : BitVec 64) (a_bs : List (BitVec 8)) (i : Nat)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) {oom : State → SepProp}
    (w_s18 : BitVec 64)
    (ai_i tmp424_bs comp_bs : List (BitVec 8))
    (Full P : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2480#64) 576 ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗
       ((s0.sp - 1880#64) ↦₆₄ w_s18) ∗
       ((s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗
       (a ↦ₛ a_bs) ∗
       ((s0.sp - 424#64) ↦ₛ tmp424_bs) ∗
       ((s0.sp - 264#64) ↦ₛ comp_bs)) ∗ P := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hregs : ProjTableLoopRegs s0 s (b + 0x304#64) (BitVec.ofNat 64 (160 * i)))
    (hai_i : fe51Point4Bounded ai_i (2 ^ 54) ∧ edExtOfBytes ai_i = projNielsTablePoints (edExtOfBytes a_bs) i)
    (ha_b : fe51Point4Bounded a_bs (2 ^ 53))
    (_ht424 : tmp424_bs.length = 160)
    (_hcomp : comp_bs.length = 160)
    (hnext : ∀ (s_mid : State) (ext_bs comp_bs' : List (BitVec 8)),
      s_mid.pc = b + 0x36c#64 →
      s_mid.status = .Running →
      s_mid.sp = s0.sp - 1904#64 →
      s_mid.readReg64 (Reg.gpr 22#5) = s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i) →
      s_mid.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s_mid = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s_mid.mem →
      fe51Point4Bounded ext_bs (2 ^ 52) →
      edExtOfBytes ext_bs = edAsExtended (edAddProjNiels (edExtOfBytes a_bs) (edExtOfBytes ai_i)) →
      comp_bs'.length = 160 →
      SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s_mid
        (((s0.sp - 424#64) ↦ₛ ext_bs) ∗
         ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
         memRegion (s0.sp - 2128#64) 224 ∗
         stackAt (s0.sp - 2128#64) 352 ∗
         ((s0.sp - 1896#64) ↦₆₄ a) ∗
         ((s0.sp - 1880#64) ↦₆₄ BitVec.ofNat 64 (160 * i)) ∗
         (a ↦ₛ a_bs) ∗
         ((s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗ P) post oom) :
    SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s Full post oom := by
  rcases hregs with ⟨hpc, hrun, hsp, hx8, hx29, hvregs, hcl⟩
  rw [hf]
  wp_cut_codeLoaded
  wp_sym_steps 8
  have ha_len : a_bs.length = 160 := ha_b.1
  have ha_0 := ha_b.2.1; unpack_fe51_at ha_0
  have ha_40 := ha_b.2.2.1; unpack_fe51_at ha_40
  have ha_80 := fe51LimbsBoundedAt_mono ha_b.2.2.2.1 (b2 := 2 ^ 54); unpack_fe51_at ha_80
  have ha_120 := fe51LimbsBoundedAt_mono ha_b.2.2.2.2 (b2 := 2 ^ 54); unpack_fe51_at ha_120
  have hai_len : ai_i.length = 160 := hai_i.1.1
  have hai_0 := hai_i.1.2.1; unpack_fe51_at hai_0
  have hai_40 := hai_i.1.2.2.1; unpack_fe51_at hai_40
  have hai_80 := hai_i.1.2.2.2.1; unpack_fe51_at hai_80
  have hai_120 := hai_i.1.2.2.2.2; unpack_fe51_at hai_120
  wp_dalek_call hAdd; clean_sf s
  let C := edAddProjNiels (edExtOfBytes a_bs) (edExtOfBytes ai_i)
  have hc_val : edExtOfBytes w = C := by assumption
  apply sepWP_split4_completed_264 s0.sp C
    (h0 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 0 _›)
    (h40 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 40 _›)
    (h80 := ‹fe51LimbsBoundedAt w 80 _›)
    (h120 := fe51LimbsBoundedAt_mono ‹fe51LimbsBoundedAt w 120 _›)
    (hval := hc_val)
  intro c0 c1 c2 c3 hc0_l hc1_l hc2_l hc3_l hc0_b hc1_b hc2_b hc3_b hc0_v hc1_v hc2_v hc3_v
  unpack_fe51 hc0_b; unpack_fe51 hc1_b; unpack_fe51 hc2_b; unpack_fe51 hc3_b
  apply sepWP_split4_stack s0.sp 424 384 344 304
  intro e0 e1 e2 e3 he0_l he1_l he2_l he3_l
  apply sepWP_resize_callee_576 s0.sp 352 224 2128
  wp_sym_steps 5; wp_dalek_call hMul; clean_sf sf; obtain ⟨hr0_l, hr0_b, hr0_v⟩ := fe51_mul_post_props w_1 (fpMul C.X C.T)
  wp_sym_steps 5; wp_dalek_call hMul; clean_sf sf_1; obtain ⟨hr1_l, hr1_b, hr1_v⟩ := fe51_mul_post_props w_2 (fpMul C.Y C.Z)
  wp_sym_steps 4; wp_dalek_call hMul; clean_sf sf; obtain ⟨hr2_l, hr2_b, hr2_v⟩ := fe51_mul_post_props w_3 (fpMul C.Z C.T)
  wp_sym_steps 4; wp_dalek_call hMul; clean_sf sf_1; obtain ⟨hr3_l, hr3_b, hr3_v⟩ := fe51_mul_post_props w_4 (fpMul C.X C.Y)
  norm_sf 224
  apply sepWP_merge4_stack_264 s0.sp
  intro comp_bs' hcomp'
  apply sepWP_merge4_stack s0.sp 424 384 344 304
    (fun ext_bs => fe51Point4Bounded ext_bs (2 ^ 52) ∧
      edExtOfBytes ext_bs = edAsExtended C)
  · obtain ⟨hl, hb0, hb1, hb2, hb3, hv⟩ :=
      edAsExtended_of_append4 w_1 w_2 w_3 w_4 C hr0_b hr1_b hr2_b hr3_b hr0_v hr1_v hr2_v hr3_v
    exact ⟨⟨hl, hb0, hb1, hb2, hb3⟩, hv⟩
  intro ext_bs ⟨hext_b, hext_v⟩
  have hperm :
      (((s0.sp - 424#64) ↦ₛ ext_bs) ∗
       ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
       memRegion (s0.sp - 2128#64) 224 ∗
       stackAt (s0.sp - 2128#64) 352 ∗
       (a ↦ₛ a_bs) ∗
       ((s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗
       ((s0.sp - 1880#64) ↦₆₄ BitVec.ofNat 64 (160 * i)) ∗ P) =
      (((s0.sp - 424#64) ↦ₛ ext_bs) ∗
       ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
       memRegion (s0.sp - 2128#64) 224 ∗
       stackAt (s0.sp - 2128#64) 352 ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗
       ((s0.sp - 1880#64) ↦₆₄ BitVec.ofNat 64 (160 * i)) ∗
       (a ↦ₛ a_bs) ∗
       ((s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i)) ↦ₛ ai_i) ∗ P) := by sep_ac_rfl
  have h2128 : s0.sp - 1904#64 - 224#64 = s0.sp - 2128#64 := by rw [BitVec.sub_sub]; rfl
  wp_conv_pre => rw [h2128, hperm]
  exact hnext _ ext_bs comp_bs'
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ‹_›
    hext_b hext_v hcomp'

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem proj_table_iter [DalekCliPlacement] (b : BitVec 64)
    (hb : DalekBase dalekCliPl25 b) (hbase : dalekCliPl25.base = b)
    (hAdd : EdwardsPointAddProjNielsOk)
    (hMul : Fe51MulOk)
    (hMRo : Fe51MulRoRightOk)
    (s0 s : State) (a : BitVec 64) (a_bs : List (BitVec 8)) (i off_i off_i1 : Nat) (hi : i < 7)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) {oom : State → SepProp}
    (w_s10 w_s18 : BitVec 64)
    (ai_i ai_i1 tmp584_120 tmp464_40 tmp424_bs comp_bs : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2480#64) 576 ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗
       ((s0.sp - 1888#64) ↦₆₄ w_s10) ∗
       ((s0.sp - 1880#64) ↦₆₄ w_s18) ∗
       ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
       ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1) ∗
       (a ↦ₛ a_bs) ∗
       ((s0.sp - 584#64) ↦ₛ tmp584_120) ∗
       ((s0.sp - 464#64) ↦ₛ tmp464_40) ∗
       ((s0.sp - 424#64) ↦ₛ tmp424_bs) ∗
       ((s0.sp - 264#64) ↦ₛ comp_bs) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F := by sep_frame)
    (ho0 : off_i + 160 * i = 1872 := by decide)
    (ho1 : off_i1 + 160 * i + 160 = 1872 := by decide)
    (hsp0_align : s0.spAligned = true)
    (hregs : ProjTableLoopRegs s0 s (b + 0x304#64) (BitVec.ofNat 64 (160 * i)))
    (hai_i : fe51Point4Bounded ai_i (2 ^ 54) ∧ edExtOfBytes ai_i = projNielsTablePoints (edExtOfBytes a_bs) i)
    (hai_i1 : ai_i1.length = 160)
    (ha_b : fe51Point4Bounded a_bs (2 ^ 53))
    (ht584 : tmp584_120.length = 120)
    (ht464 : tmp464_40.length = 40)
    (ht424 : tmp424_bs.length = 160)
    (hcomp : comp_bs.length = 160)
    (hnext : ∀ (s' : State) (w_s10' w_s18' : BitVec 64)
      (ai_i1' tmp584_120' tmp464_40' tmp424_bs' comp_bs' : List (BitVec 8)),
      ProjTableLoopRegs s0 s' (if i == 6 then b + 0x4dc#64 else b + 0x304#64) (BitVec.ofNat 64 (160 * (i + 1))) →
      (fe51Point4Bounded ai_i1' (2 ^ 54) ∧ edExtOfBytes ai_i1' = projNielsTablePoints (edExtOfBytes a_bs) (i + 1)) →
      tmp584_120'.length = 120 →
      tmp464_40'.length = 40 →
      tmp424_bs'.length = 160 →
      comp_bs'.length = 160 →
      SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s'
        ((memRegion (s0.sp - 2480#64) 576 ∗
          ((s0.sp - 1896#64) ↦₆₄ a) ∗
          ((s0.sp - 1888#64) ↦₆₄ w_s10') ∗
          ((s0.sp - 1880#64) ↦₆₄ w_s18') ∗
          ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
          ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
          (a ↦ₛ a_bs) ∗
          ((s0.sp - 584#64) ↦ₛ tmp584_120') ∗
          ((s0.sp - 464#64) ↦ₛ tmp464_40') ∗
          ((s0.sp - 424#64) ↦ₛ tmp424_bs') ∗
          ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
          (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) post oom) :
    SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s Full post oom := by
  rw [hf, iter_addr_i s0.sp (160 * i) off_i ho0, iter_addr_i1 s0.sp (160 * i) off_i1 ho1]
  apply proj_table_iter_add b hb hbase hAdd hMul s0 s a a_bs i target_pc post
    w_s18 ai_i tmp424_bs comp_bs _ _ (by sep_frame)
    hsp0_align hregs hai_i ha_b ht424 hcomp
  clear hregs s
  intro s_mid ext_bs comp_bs' hpc hrun hsp hx22 hx29 hvregs hcl_mid hext_b hext_v hcomp'
  have hext_len : ext_bs.length = 160 := hext_b.1
  haveI : HasLenGe ext_bs 160 := ⟨by omega⟩
  haveI : HasLenGe tmp584_120 120 := ⟨by omega⟩
  wp_cut_codeLoaded
  wp_sym_steps 53
  apply sepWP_focus_bytes (s0.sp - 424#64) (s0.sp - 304#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ := fe51LimbsBounded_slice_of_at (2 ^ 54) (fe51LimbsBoundedAt_mono hext_b.2.2.2.2 (b2 := 2 ^ 54))
  obtain ⟨_, _, _, _, _, _⟩ := fe51EdwardsD2Bytes_bounded54
  wp_dalek_call hMRo; clean_sf s_mid; norm_sf 224
  obtain ⟨hw5_len, hw5_b, hw5_v⟩ := fe51_mro_post_props w ext_bs
  apply sepWP_unfocus_bytes (s0.sp - 424#64) (s0.sp - 304#64) 120 40
  apply sepWP_unresize_callee_576 s0.sp 352 224 2128
  haveI : HasLenGe ai_i1 160 := ⟨by omega⟩
  apply sepWP_merge2_stack s0.sp 584 464 40
  intro m_bs hm_len hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136 hm144 hm152
  simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne] at hm80 hm88 hm96 hm104 hm112
  haveI : HasLenGe m_bs 160 := ⟨by omega⟩
  apply MultiPlacedLib.seq_codeLoaded (mid := if i == 6 then b + 0x4dc#64 else b + 0x304#64) ‹_›
  wp_sym_steps 39
  have hstep_eq : edExtToProjNiels (edExtOfBytes ext_bs) = projNielsTablePoints (edExtOfBytes a_bs) (i + 1) := by
    rw [hext_v]
    show edExtToProjNiels (edAsExtended (edAddProjNiels (edExtOfBytes a_bs) (edExtOfBytes ai_i))) =
      projNielsTableStep (edExtOfBytes a_bs) (projNielsTablePoints (edExtOfBytes a_bs) i)
    rw [hai_i.2]; rfl
  have hext_b53 : fe51Point4Bounded ext_bs (2 ^ 53) :=
    ⟨hext_b.1, fe51LimbsBoundedAt_mono hext_b.2.1, fe51LimbsBoundedAt_mono hext_b.2.2.1,
     fe51LimbsBoundedAt_mono hext_b.2.2.2.1, fe51LimbsBoundedAt_mono hext_b.2.2.2.2⟩
  apply sepWP_abstract_bytes (s0.sp - 1872#64 + BitVec.ofNat 64 (160 * i) + 160#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = projNielsTablePoints (edExtOfBytes a_bs) (i + 1))
  · rw [← hstep_eq]
    refine asProjNiels_post_core54 ext_bs w _ hext_b53 hw5_b hw5_v (by prove_write64_len) ?_
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
      hm80, hm88, hm96, hm104, hm112, hm120, hm128, hm136, hm144, hm152, and_self]
  intro ai_i1' hai_i1'
  apply sepWP_split2_stack s0.sp 584 120 464 40
  intro tmp584_120' tmp464_40' ht584_l ht464_l
  rw [← iter_addr_i1 s0.sp (160 * i) off_i1 ho1, ← iter_addr_i s0.sp (160 * i) off_i ho0]
  have hperm :
      ((((s0.sp - 584#64) ↦ₛ tmp584_120') ∗ ((s0.sp - 464#64) ↦ₛ tmp464_40')) ∗
       ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
       memRegion (s0.sp - 2480#64) 576 ∗
       ((s0.sp - 424#64) ↦ₛ ext_bs) ∗
       (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
       ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗
       ((s0.sp - 1880#64) ↦₆₄ BitVec.ofNat 64 (160 * i)) ∗
       (a ↦ₛ a_bs) ∗
       ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
       ((s0.sp - 1888#64) ↦₆₄ (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)) ∗ F) =
      ((memRegion (s0.sp - 2480#64) 576 ∗
        ((s0.sp - 1896#64) ↦₆₄ a) ∗
        ((s0.sp - 1888#64) ↦₆₄ (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)) ∗
        ((s0.sp - 1880#64) ↦₆₄ BitVec.ofNat 64 (160 * i)) ∗
        ((s0.sp - BitVec.ofNat 64 off_i) ↦ₛ ai_i) ∗
        ((s0.sp - BitVec.ofNat 64 off_i1) ↦ₛ ai_i1') ∗
        (a ↦ₛ a_bs) ∗
        ((s0.sp - 584#64) ↦ₛ tmp584_120') ∗
        ((s0.sp - 464#64) ↦ₛ tmp464_40') ∗
        ((s0.sp - 424#64) ↦ₛ ext_bs) ∗
        ((s0.sp - 264#64) ↦ₛ comp_bs') ∗
        (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  apply SepWP.done
  · simp only [State.pc_setMem, State.pc_setPC, pc_iter_end b hi]
  · wp_norm_lhs
  intro hcl_end
  refine hnext _ (ByteSlice.readLE ext_bs 0 8 + ByteSlice.readLE ext_bs 40 8)
    (BitVec.ofNat 64 (160 * i))
    ai_i1' tmp584_120' tmp464_40' ext_bs comp_bs'
    ⟨?_, by wp_norm_lhs, by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, hcl_end⟩
    hai_i1' ht584_l ht464_l hext_len hcomp'
  · simp only [State.pc_setMem, State.pc_setPC, pc_iter_end b hi]
  · simp only [arm64_norm, ofNat_160i_add_160 hi]

set_option maxHeartbeats 600000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem proj_table_init_b0 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl25 b) (_hbase : dalekCliPl25.base = b)
    (hMRo : Fe51MulRoRightOk)
    (s0 s : State) (a : BitVec 64) (a_bs : List (BitVec 8))
    (target_pc : BitVec 64) (post : State → SepProp → Prop) {oom : State → SepProp}
    (w_s8 : BitVec 64)
    (b0_i r1120_i n120_i n40_i : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full =
      (memRegion (s0.sp - 2480#64) 576 ∗
       ((s0.sp - 1896#64) ↦₆₄ w_s8) ∗
       ((s0.sp - 1872#64) ↦ₛ b0_i) ∗ ((s0.sp - 1712#64) ↦ₛ r1120_i) ∗
       ((s0.sp - 264#64) ↦ₛ n120_i) ∗ ((s0.sp - 144#64) ↦ₛ n40_i) ∗
       (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 0x30#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1904#64)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = a)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 19#64)
    (hx18 : s.readReg64 (Reg.gpr 18#5) = 18446744073709551312#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (ha_b : fe51Point4Bounded a_bs (2 ^ 53))
    (hb0_i : b0_i.length = 160) (hr1120_i : r1120_i.length = 1120)
    (hn120_i : n120_i.length = 120) (hn40_i : n40_i.length = 40)
    (hnext : ∀ (s1 : State) (b0 r1120_1 niels0 : List (BitVec 8)),
      s1.pc = b + 0x168#64 → s1.status = .Running → s1.sp = s0.sp - 1904#64 →
      s1.readReg64 (Reg.gpr 8#5) = 0#64 →
      s1.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s1.mem →
      (fe51Point4Bounded b0 (2 ^ 54) ∧ edExtOfBytes b0 = projNielsTablePoints (edExtOfBytes a_bs) 0) →
      r1120_1.length = 1120 →
      niels0.length = 160 →
      SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s1
        ((memRegion (s0.sp - 2480#64) 576 ∗
          ((s0.sp - 1896#64) ↦₆₄ a) ∗
          ((s0.sp - 1872#64) ↦ₛ b0) ∗ ((s0.sp - 1712#64) ↦ₛ r1120_1) ∗
          ((s0.sp - 264#64) ↦ₛ niels0) ∗
          (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) post oom) :
    SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s Full post oom := by
  have ha_len : a_bs.length = 160 := ha_b.1
  haveI : HasLenGe a_bs 160 := ⟨by omega⟩
  haveI : HasLenGe n120_i 120 := ⟨by omega⟩
  rw [hf]
  wp_cut_codeLoaded
  wp_sym_steps 46
  apply sepWP_resize_callee_576 s0.sp 352 224 2128
  apply sepWP_focus_bytes a (a + 120#64) 120 40; intro _
  obtain ⟨_, _, _, _, _, _⟩ :=
    fe51LimbsBounded_slice_of_at (2 ^ 54) (fe51LimbsBoundedAt_mono ha_b.2.2.2.2 (b2 := 2 ^ 54))
  obtain ⟨_, _, _, _, _, _⟩ := fe51EdwardsD2Bytes_bounded54
  wp_dalek_call hMRo; clean_sf s; norm_sf 224
  obtain ⟨hw_t2d_len, hw_t2d_b, hw_t2d_v⟩ := fe51_mro_post_props w a_bs
  apply sepWP_unfocus_bytes a (a + 120#64) 120 40
  apply sepWP_unresize_callee_576 s0.sp 352 224 2128
  haveI : HasLenGe b0_i 160 := ⟨by omega⟩
  haveI : HasLenGe r1120_i 1120 := ⟨by omega⟩
  apply sepWP_merge2_stack s0.sp 264 144 40
  intro m0_bs hm0_len hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136 hm144 hm152
  simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne] at hm80 hm88 hm96 hm104 hm112
  haveI : HasLenGe m0_bs 160 := ⟨by omega⟩
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 0x168#64) ‹_›
  wp_sym_steps 32
  have hb0_eq : edExtToProjNiels (edExtOfBytes a_bs) = projNielsTablePoints (edExtOfBytes a_bs) 0 := rfl
  apply sepWP_abstract_bytes (s0.sp - 1872#64)
    (fun buf => fe51Point4Bounded buf (2 ^ 54) ∧ edExtOfBytes buf = projNielsTablePoints (edExtOfBytes a_bs) 0)
  · rw [← hb0_eq]
    refine asProjNiels_post_core54 a_bs w _ ha_b hw_t2d_b hw_t2d_v (by prove_write64_len) ?_
    simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
      hm80, hm88, hm144, hm152, and_self]
  clear hm80 hm88 hm96 hm104 hm112 hm120 hm128 hm136 hm144 hm152
  intro b0 hb0
  apply sepWP_abstract_bytes (s0.sp - 1712#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_1 hr1120_1
  apply sepWP_abstract_bytes (s0.sp - 264#64) (fun buf => buf.length = 160)
  · prove_write64_len
  intro niels0 hniels0
  have hperm :
      (((s0.sp - 264#64) ↦ₛ niels0) ∗ ((s0.sp - 1712#64) ↦ₛ r1120_1) ∗
       ((s0.sp - 1872#64) ↦ₛ b0) ∗
       memRegion (s0.sp - 2480#64) 576 ∗ (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes) ∗
       ((s0.sp - 1896#64) ↦₆₄ a) ∗ F) =
      ((memRegion (s0.sp - 2480#64) 576 ∗
        ((s0.sp - 1896#64) ↦₆₄ a) ∗
        ((s0.sp - 1872#64) ↦ₛ b0) ∗ ((s0.sp - 1712#64) ↦ₛ r1120_1) ∗
        ((s0.sp - 264#64) ↦ₛ niels0) ∗
        (a ↦ₛ a_bs) ∗ (fe51_edwards_d2 dalekCliMpl ↦ᵣ fe51EdwardsD2Bytes)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl1
  exact hnext _ b0 r1120_1 niels0
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hcl1
    hb0 hr1120_1 hniels0

set_option maxHeartbeats 400000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem proj_table_init_r1 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl25 b) (_hbase : dalekCliPl25.base = b)
    (s0 s : State)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) {oom : State → SepProp}
    (r1120_1 niels0 : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full = ((((s0.sp - 1712#64) ↦ₛ r1120_1) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 0x168#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1904#64)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = 0#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hr1120_1 : r1120_1.length = 1120)
    (hniels0 : niels0.length = 160)
    (hnext : ∀ (s2 : State) (r1120_2 : List (BitVec 8)),
      s2.pc = b + 0x238#64 → s2.status = .Running → s2.sp = s0.sp - 1904#64 →
      s2.readReg64 (Reg.gpr 8#5) = 0#64 →
      s2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      dalekCliMultiLib.CodeLoaded dalekCliMpl s2.mem →
      r1120_2.length = 1120 →
      SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s2
        ((((s0.sp - 1712#64) ↦ₛ r1120_2) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) post oom) :
    SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s Full post oom := by
  haveI : HasLenGe r1120_1 1120 := ⟨by omega⟩
  haveI : HasLenGe niels0 160 := ⟨by omega⟩
  rw [hf]
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 0x238#64) hcl
  wp_sym_steps 26
  apply sepWP_abstract_bytes (s0.sp - 1712#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_a hr1120_a; haveI : HasLenGe r1120_a 1120 := ⟨by omega⟩
  wp_sym_steps 26
  apply sepWP_abstract_bytes (s0.sp - 1712#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_2 hr1120_2
  have hperm :
      (((s0.sp - 1712#64) ↦ₛ r1120_2) ∗ ((s0.sp - 264#64) ↦ₛ niels0) ∗ F) =
      ((((s0.sp - 1712#64) ↦ₛ r1120_2) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl2
  exact hnext _ r1120_2
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) hcl2
    hr1120_2

set_option maxHeartbeats 400000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
private theorem proj_table_init_r2 [DalekCliPlacement] (b : BitVec 64)
    (_hb : DalekBase dalekCliPl25 b) (_hbase : dalekCliPl25.base = b)
    (s0 s : State)
    (target_pc : BitVec 64) (post : State → SepProp → Prop) {oom : State → SepProp}
    (r1120_2 niels0 : List (BitVec 8))
    (Full F : SepProp)
    (hf : Full = ((((s0.sp - 1712#64) ↦ₛ r1120_2) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) := by sep_frame)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = b + 0x238#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1904#64)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = 0#64)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcl : dalekCliMultiLib.CodeLoaded dalekCliMpl s.mem)
    (hr1120_2 : r1120_2.length = 1120)
    (hniels0 : niels0.length = 160)
    (hnext : ∀ (s_l0 : State) (b1 b2 b3 b4 b5 b6 b7 : List (BitVec 8)),
      ProjTableLoopRegs s0 s_l0 (b + 0x304#64) (BitVec.ofNat 64 (160 * 0)) →
      b1.length = 160 → b2.length = 160 → b3.length = 160 → b4.length = 160 →
      b5.length = 160 → b6.length = 160 → b7.length = 160 →
      SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s_l0
        ((((s0.sp - 1712#64) ↦ₛ b1) ∗ ((s0.sp - 1552#64) ↦ₛ b2) ∗ ((s0.sp - 1392#64) ↦ₛ b3) ∗
          ((s0.sp - 1232#64) ↦ₛ b4) ∗ ((s0.sp - 1072#64) ↦ₛ b5) ∗ ((s0.sp - 912#64) ↦ₛ b6) ∗
          ((s0.sp - 752#64) ↦ₛ b7) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) post oom) :
    SepWP (dalekCliPC25.rebase b (fun _ => none)) target_pc s Full post oom := by
  haveI : HasLenGe r1120_2 1120 := ⟨by omega⟩
  haveI : HasLenGe niels0 160 := ⟨by omega⟩
  rw [hf]
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 0x304#64) hcl
  wp_sym_steps 25
  apply sepWP_abstract_bytes (s0.sp - 1712#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120_b hr1120_b; haveI : HasLenGe r1120_b 1120 := ⟨by omega⟩
  wp_sym_steps 26
  apply sepWP_abstract_bytes (s0.sp - 1712#64) (fun buf => buf.length = 1120)
  · prove_write64_len
  intro r1120 hr1120
  apply sepWP_split7_table s0.sp
  intro b1 b2 b3 b4 b5 b6 b7 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hperm :
      ((((s0.sp - 1712#64) ↦ₛ b1) ∗ ((s0.sp - 1552#64) ↦ₛ b2) ∗ ((s0.sp - 1392#64) ↦ₛ b3) ∗
        ((s0.sp - 1232#64) ↦ₛ b4) ∗ ((s0.sp - 1072#64) ↦ₛ b5) ∗ ((s0.sp - 912#64) ↦ₛ b6) ∗
        ((s0.sp - 752#64) ↦ₛ b7)) ∗ (((s0.sp - 264#64) ↦ₛ niels0) ∗ F)) =
      ((((s0.sp - 1712#64) ↦ₛ b1) ∗ ((s0.sp - 1552#64) ↦ₛ b2) ∗ ((s0.sp - 1392#64) ↦ₛ b3) ∗
        ((s0.sp - 1232#64) ↦ₛ b4) ∗ ((s0.sp - 1072#64) ↦ₛ b5) ∗ ((s0.sp - 912#64) ↦ₛ b6) ∗
        ((s0.sp - 752#64) ↦ₛ b7) ∗ ((s0.sp - 264#64) ↦ₛ niels0)) ∗ F) := by sep_ac_rfl
  rw [hperm]
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_l0
  exact hnext _ b1 b2 b3 b4 b5 b6 b7
    ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hcl_l0⟩
    hb1 hb2 hb3 hb4 hb5 hb6 hb7

public section

set_option maxHeartbeats 800000 in
attribute [local wp_norm] ByteSlice.pack64_eq_readLE_8 in
theorem lookup_table_proj_niels_from_ok_of
    (hMul : Fe51MulOk) (hMulRo : Fe51MulRoRightOk)
    (hAddPN : EdwardsPointAddProjNielsOk) :
    LookupTableProjNielsFromOk := by
  intro _
  apply dalekCaller_ok dalekCliPC25 dalekCliPl25
  intro b hb hbase
  wp_init
  apply sepWP_peel_stack_region s0.sp 2480 576 1904
  apply sepWP_peel_stack_region s0.sp 1904 32 1872
  open_cells (s0.sp - 1904#64) 32 4
  apply sepWP_peel_stack_bytes s0.sp 1872 160 1712; intro b0_i hb0_i
  apply sepWP_peel_stack_bytes s0.sp 1712 1120 592; intro r1120_i hr1120_i
  apply sepWP_peel_stack_region s0.sp 592 8 584
  apply sepWP_peel_stack_bytes s0.sp 584 120 464; intro t584_i ht584_i
  apply sepWP_peel_stack_bytes s0.sp 464 40 424; intro t464_i ht464_i
  apply sepWP_peel_stack_bytes s0.sp 424 160 264; intro ext_0 hext_0
  apply sepWP_peel_stack_bytes s0.sp 264 120 144; intro n120_i hn120_i
  apply sepWP_peel_stack_bytes s0.sp 144 40 104; intro n40_i hn40_i
  apply sepWP_peel_stack_region s0.sp 104 8 96
  open_cells (s0.sp - 96#64) 96 12
  apply MultiPlacedLib.seq_codeLoaded (mid := b + 0x30#64) ‹_›
  wp_sym_steps 12
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl0
  have ha_b : fe51Point4Bounded a_rest (2 ^ 53) := by assumption
  apply proj_table_init_b0 b hb hbase hMulRo s0 _ a a_rest _ _ _ b0_i r1120_i n120_i n40_i _ _
    (hsp0_align := hsp_align) (hpc := by wp_norm_lhs) (hrun := by wp_norm_lhs) (hsp := by wp_norm_lhs)
    (hx0 := by wp_norm_lhs) (hx1 := by wp_norm_lhs) (hx18 := by wp_norm_lhs) (hx29 := by wp_norm_lhs)
    (hvregs := by wp_norm_lhs) (hcl := hcl0) (ha_b := ha_b) (hb0_i := hb0_i) (hr1120_i := hr1120_i)
    (hn120_i := hn120_i) (hn40_i := hn40_i)
  intro s1 b0 r1120_1 niels0 hpc1 hrun1 hsp1 hx8_1 hx29_1 hvregs1 hcl1 hb0 hr1120_1 hniels0
  apply proj_table_init_r1 b hb hbase s0 s1 _ _ r1120_1 niels0 _ _
    (hsp0_align := hsp_align) (hpc := hpc1) (hrun := hrun1) (hsp := hsp1)
    (hx8 := hx8_1) (hx29 := hx29_1) (hvregs := hvregs1) (hcl := hcl1)
    (hr1120_1 := hr1120_1) (hniels0 := hniels0)
  intro s2 r1120_2 hpc2 hrun2 hsp2 hx8_2 hx29_2 hvregs2 hcl2 hr1120_2
  apply proj_table_init_r2 b hb hbase s0 s2 _ _ r1120_2 niels0 _ _
    (hsp0_align := hsp_align) (hpc := hpc2) (hrun := hrun2) (hsp := hsp2)
    (hx8 := hx8_2) (hx29 := hx29_2) (hvregs := hvregs2) (hcl := hcl2)
    (hr1120_2 := hr1120_2) (hniels0 := hniels0)
  intro s_l0 b1_i b2_i b3_i b4_i b5_i b6_i b7_i hregs0 hb1_i hb2_i hb3_i hb4_i hb5_i hb6_i hb7_i
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l0 a a_rest 0 1872 1712 (by decide) _ _
    _ _ b0 b1_i t584_i t464_i ext_0 niels0 _ _
    (hsp0_align := hsp_align) (hregs := hregs0) (hai_i := hb0) (hai_i1 := hb1_i)
    (ha_b := ha_b) (ht584 := ht584_i) (ht464 := ht464_i) (ht424 := hext_0) (hcomp := hniels0)
  intro s_l1 w10_1 w18_1 b1 t584_1 t464_1 ext_1 comp_1 hregs1 hb1 ht584_1 ht464_1 hext_1 hcomp_1
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l1 a a_rest 1 1712 1552 (by decide) _ _
    w10_1 w18_1 b1 b2_i t584_1 t464_1 ext_1 comp_1 _ _
    (hsp0_align := hsp_align) (hregs := hregs1) (hai_i := hb1) (hai_i1 := hb2_i)
    (ha_b := ha_b) (ht584 := ht584_1) (ht464 := ht464_1) (ht424 := hext_1) (hcomp := hcomp_1)
  intro s_l2 w10_2 w18_2 b2 t584_2 t464_2 ext_2 comp_2 hregs2 hb2 ht584_2 ht464_2 hext_2 hcomp_2
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l2 a a_rest 2 1552 1392 (by decide) _ _
    w10_2 w18_2 b2 b3_i t584_2 t464_2 ext_2 comp_2 _ _
    (hsp0_align := hsp_align) (hregs := hregs2) (hai_i := hb2) (hai_i1 := hb3_i)
    (ha_b := ha_b) (ht584 := ht584_2) (ht464 := ht464_2) (ht424 := hext_2) (hcomp := hcomp_2)
  intro s_l3 w10_3 w18_3 b3 t584_3 t464_3 ext_3 comp_3 hregs3 hb3 ht584_3 ht464_3 hext_3 hcomp_3
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l3 a a_rest 3 1392 1232 (by decide) _ _
    w10_3 w18_3 b3 b4_i t584_3 t464_3 ext_3 comp_3 _ _
    (hsp0_align := hsp_align) (hregs := hregs3) (hai_i := hb3) (hai_i1 := hb4_i)
    (ha_b := ha_b) (ht584 := ht584_3) (ht464 := ht464_3) (ht424 := hext_3) (hcomp := hcomp_3)
  intro s_l4 w10_4 w18_4 b4 t584_4 t464_4 ext_4 comp_4 hregs4 hb4 ht584_4 ht464_4 hext_4 hcomp_4
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l4 a a_rest 4 1232 1072 (by decide) _ _
    w10_4 w18_4 b4 b5_i t584_4 t464_4 ext_4 comp_4 _ _
    (hsp0_align := hsp_align) (hregs := hregs4) (hai_i := hb4) (hai_i1 := hb5_i)
    (ha_b := ha_b) (ht584 := ht584_4) (ht464 := ht464_4) (ht424 := hext_4) (hcomp := hcomp_4)
  intro s_l5 w10_5 w18_5 b5 t584_5 t464_5 ext_5 comp_5 hregs5 hb5 ht584_5 ht464_5 hext_5 hcomp_5
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l5 a a_rest 5 1072 912 (by decide) _ _
    w10_5 w18_5 b5 b6_i t584_5 t464_5 ext_5 comp_5 _ _
    (hsp0_align := hsp_align) (hregs := hregs5) (hai_i := hb5) (hai_i1 := hb6_i)
    (ha_b := ha_b) (ht584 := ht584_5) (ht464 := ht464_5) (ht424 := hext_5) (hcomp := hcomp_5)
  intro s_l6 w10_6 w18_6 b6 t584_6 t464_6 ext_6 comp_6 hregs6 hb6 ht584_6 ht464_6 hext_6 hcomp_6
  apply proj_table_iter b hb hbase hAddPN hMul hMulRo s0 s_l6 a a_rest 6 912 752 (by decide) _ _
    w10_6 w18_6 b6 b7_i t584_6 t464_6 ext_6 comp_6 _ _
    (hsp0_align := hsp_align) (hregs := hregs6) (hai_i := hb6) (hai_i1 := hb7_i)
    (ha_b := ha_b) (ht584 := ht584_6) (ht464 := ht464_6) (ht424 := hext_6) (hcomp := hcomp_6)
  intro s_l7 w10_7 w18_7 b7 t584_7 t464_7 ext_7 comp_7 hregs7 hb7 ht584_7 ht464_7 hext_7 hcomp_7
  rcases hregs7 with ⟨hpc7, hrun7, hsp, hx8_7, hx29_7, hvregs7, hcl7⟩
  apply sepWP_merge8_table s0.sp (edExtOfBytes a_rest)
    (h0 := hb0) (h1 := hb1) (h2 := hb2) (h3 := hb3)
    (h4 := hb4) (h5 := hb5) (h6 := hb6) (h7 := hb7)
  intro table_bs htable_len ⟨htable_b, htable_v⟩
  clear_dead_vars [s1, s2, s_l0, s_l1, s_l2, s_l3, s_l4, s_l5, s_l6]
  clear s1 s2 s_l0 s_l1 s_l2 s_l3 s_l4 s_l5 s_l6 hcl0
  wp_sym_steps 4
  wp_dalek_call memcpy_ok; clean_sf s_l7
  wp_sym_steps 8
  close_cells (s0.sp - 96#64) 96 12
  apply sepWP_unpeel_stack_region s0.sp 104 8 96
  apply sepWP_unpeel_stack_bytes s0.sp 264 160 104
  apply sepWP_unpeel_stack_bytes s0.sp 424 160 264
  apply sepWP_unpeel_stack_bytes s0.sp 464 40 424
  apply sepWP_unpeel_stack_bytes s0.sp 584 120 464
  apply sepWP_unpeel_stack_region s0.sp 592 8 584
  apply sepWP_unpeel_stack_bytes s0.sp 1872 1280 592
  close_cells (s0.sp - 1904#64) 32 4
  apply sepWP_unpeel_stack_region s0.sp 1904 32 1872
  apply sepWP_unpeel_stack_region s0.sp 2480 576 1904
  have htable_pts : ∀ i < 8, fe51Point4Bounded (ProofLib.ByteSlice.slice table_bs (160 * i) 160) 18014398509481984 := htable_b.2
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.LookupTableProj1
