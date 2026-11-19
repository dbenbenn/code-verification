/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue

/-!
# `generate_keypair_compressed` (`B05`) — Segment 1b Zeroing & Pointer Setup (`+0x0040 .. +0x01a8`)

Steps `sub sp, sp, #1248`, stores `(sp + 40#64) ↦₆₄ outPtr`, `(sp + 128#64) ↦₆₄ (sp + 10248#64)`,
and `(sp + 136#64) ↦₆₄ (sp + 8416#64)`, executes the six initial `B29` `memset` / `B28` `memcpy`
calls (`+0x0108`, `+0x012c`, `+0x0154`, `+0x0170`, `+0x0190`, `+0x01a4`), and folds the dead
zero-initialized scratch buffers back into `memRegion`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Zero

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk28
  resolve_blk29
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok
  blk29_memset_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq
  blk05_tree_size
  blkLib05
  blkPC05
  blkPl05
  blkPlaceable05
  blkTree05
  cell_entails_memRegion8
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  SepStore128
  Vec32
  poly32Mem_entails_memRegion
  step_strQ128
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub
  sepWP_elim_bytes
  sepWP_elim_cell8
  sepWP_elim_poly32
  sepWP_elim_vec128
  vec128At_entails_memRegion16
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x0044 → 0x01a4]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local irreducible] blkLib05
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

private theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n 0#8)
  rwa [List.length_replicate] at h

local macro "find_vec32 " k:num : tactic => `(tactic| first
  | exact (SepStore128.vec32 (k := $k) (by decide) (by clear * -; bv_omega) rfl).left
  | (apply SepStore128.right; exact (SepStore128.vec32 (k := $k) (by decide) (by clear * -; bv_omega) rfl).left)
  | (apply SepStore128.right; apply SepStore128.right; exact (SepStore128.vec32 (k := $k) (by decide) (by clear * -; bv_omega) rfl).left)
  | (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; exact (SepStore128.vec32 (k := $k) (by decide) (by clear * -; bv_omega) rfl).left)
  | (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; exact (SepStore128.vec32 (k := $k) (by decide) (by clear * -; bv_omega) rfl).left))

local macro "find_vec128" : tactic => `(tactic| first
  | (apply SepStore128.left; apply SepStore128.vec128At; clear * -; bv_omega)
  | (apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec128At; clear * -; bv_omega)
  | (apply SepStore128.right; apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec128At; clear * -; bv_omega)
  | (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec128At; clear * -; bv_omega)
  | (apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec128At; clear * -; bv_omega))

local macro "step_z26176 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · find_vec32 $k
  · wp_norm_lhs
  intro _))

local macro "step_zvec128" : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · simp [evalAddrMode, *]; exact ⟨rfl, rfl⟩
  · wp_norm_lhs
  · find_vec128
  · wp_norm_lhs
  intro _))

private theorem spAligned_of_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true) :
    s.spAligned = true := by
  simpa [State.spAligned, hsp] using hchk

private theorem seg1_zero_a_split (sp : BitVec 64) :
    memRegion sp 29920 =
      memRegion sp 8 ∗ memRegion (sp + 8#64) 32 ∗ memRegion (sp + 40#64) 8 ∗
      memRegion (sp + 48#64) 80 ∗ memRegion (sp + 128#64) 8 ∗
      memRegion (sp + 136#64) 25016 ∗ memRegion (sp + 25152#64) 1024 ∗
      memRegion (sp + 26176#64) 512 ∗ memRegion (sp + 26688#64) 3232 := by
  rw [memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := (29912 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 8#64) (b' := sp + 40#64) (n := 32) (k := (29880 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 40#64) (b' := sp + 48#64) (n := 8) (k := (29872 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 48#64) (b' := sp + 128#64) (n := 80) (k := (29792 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 128#64) (b' := sp + 136#64) (n := 8) (k := (29784 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 136#64) (b' := sp + 25152#64) (n := 25016) (k := (4768 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 25152#64) (b' := sp + 26176#64) (n := 1024) (k := (3744 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 26176#64) (b' := sp + 26688#64) (n := 512) (k := (3232 : Nat)) rfl (by bv_omega) (by omega)]

private theorem seg1_zero_a_136 (sp : BitVec 64) :
    memRegion (sp + 136#64) 29784 =
      memRegion (sp + 136#64) 25016 ∗ memRegion (sp + 25152#64) 1024 ∗
      memRegion (sp + 26176#64) 512 ∗ memRegion (sp + 26688#64) 3232 := by
  rw [memRegion_split' (b := sp + 136#64) (b' := sp + 25152#64) (n := 25016) (k := (4768 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 25152#64) (b' := sp + 26176#64) (n := 1024) (k := (3744 : Nat)) rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp + 26176#64) (b' := sp + 26688#64) (n := 512) (k := (3232 : Nat)) rfl (by bv_omega) (by omega)]

private theorem seg1_zero_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (s1 : State) (seedA outPtr : BitVec 64) (F : SepProp)
    (hpc : s1.pc = b + 0x0040#64)
    (hrun : s1.status = .Running)
    (hsp : s1.sp = sp + 1248#64)
    (hsp_al : s1.spAligned = true)
    (hx0 : s1.readReg64 .x0 = seedA)
    (hx1 : s1.readReg64 .x1 = outPtr)
    (hfp : s1.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x010c#64) s1
      (memRegion sp 29920 ∗ F)
      (fun s2 P2 =>
        s2.sp = sp ∧
        s2.spAligned = true ∧
        s2.readReg64 .fp = fpVal ∧
        s2.readReg64 .x20 = seedA ∧
        s2.readReg64 .x23 = sp + 27840#64 ∧
        s2.readReg64 .x24 = sp + 9984#64 ∧
        s2.readReg64 .x26 = sp + 27840#64 ∧
        s2.readReg64 .x28 = sp + 28104#64 ∧
        (P2 ⊢ ((sp + 40#64) ↦₆₄ outPtr) ∗ ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
          memRegion sp 40 ∗ memRegion (sp + 48#64) 80 ∗ memRegion (sp + 136#64) 29784 ∗ F)) := by
  subst hbase
  have hsp_sub : s1.sp - 1248#64 = sp := by rw [hsp]; clear * -; bv_omega
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by
    rw [← hsp_sub]
    exact spAligned_sub s1.sp 1248#64 hsp_al (by decide)
  rw [seg1_zero_a_split sp]
  sep_frame_apply (sepWP_elim_cell8 (a := sp)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 40#64)); intro c40
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 128#64)); intro c128
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 26176#64)); intro t0
  wp_cut_codeLoaded
  wp_steps 15
  step_z26176 0; step_z26176 1
  wp_steps 2
  step_z26176 2; step_z26176 3; step_z26176 4; step_z26176 5
  step_z26176 6; step_z26176 7; step_z26176 8; step_z26176 9
  step_z26176 10; step_z26176 11; step_z26176 12; step_z26176 13
  step_z26176 14; step_z26176 15; step_z26176 16; step_z26176 17
  step_z26176 18; step_z26176 19; step_z26176 20; step_z26176 21
  step_z26176 22; step_z26176 23; step_z26176 24; step_z26176 25
  step_z26176 26; step_z26176 27; step_z26176 28; step_z26176 29
  step_z26176 30
  wp_step
  step_z26176 31
  wp_step
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun]
  intro hcl_pre
  refine SepWP.weaken_pre
    (entails_sub (poly32Mem_entails_memRegion (sp + 26176#64) _) (by sep_frame) (by sep_frame)) ?_
  wp_mlkem_call blk29_memset_ok (sp + 25152#64, 0#8, 1024)
  have hsp_sf_al : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf, hsp_sf_al, hcs_sf.trans hfp, h_1, h_4, h_5, h_7, h_9, ?_⟩
  have hfold40 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 32 ⊢ memRegion sp 40 := by
    rw [memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := 32) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  rw [seg1_zero_a_136 sp]
  exact entails_sub hfold40 (by sep_frame)
    (entails_sub (replicate_entails_memRegion (sp + 25152#64) 1024) (by sep_frame) (by sep_frame))


private theorem seg1_zero_b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (s2 : State) (seedA : BitVec 64) (F : SepProp)
    (hpc : s2.pc = b + 0x010c#64)
    (hrun : s2.status = .Running)
    (hsp : s2.sp = sp)
    (hsp_al : s2.spAligned = true)
    (hfp : s2.readReg64 .fp = fpVal)
    (hx20 : s2.readReg64 .x20 = seedA)
    (hx23 : s2.readReg64 .x23 = sp + 27840#64)
    (hx24 : s2.readReg64 .x24 = sp + 9984#64)
    (hx26 : s2.readReg64 .x26 = sp + 27840#64)
    (hx28 : s2.readReg64 .x28 = sp + 28104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x0158#64) s2
      (memRegion (sp + 144#64) 29776 ∗ F)
      (fun s3 P3 =>
        s3.sp = sp ∧
        s3.spAligned = true ∧
        s3.readReg64 .fp = fpVal ∧
        s3.readReg64 .x20 = seedA ∧
        s3.readReg64 .x22 = sp + 2208#64 ∧
        s3.readReg64 .x23 = sp + 27840#64 ∧
        s3.readReg64 .x24 = sp + 9984#64 ∧
        s3.readReg64 .x26 = sp + 27840#64 ∧
        s3.readReg64 .x28 = sp + 28104#64 ∧
        (P3 ⊢ memRegion (sp + 144#64) 29776 ∗ F)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by rw [State.spAligned, hsp] at hsp_al; exact hsp_al
  have hsplit1 : memRegion (sp + 144#64) 29776 =
      memRegion (sp + 9984#64) 1536 ∗ memRegion (sp + 25152#64) 1536 ∗
      memRegion (sp + 23552#64) 16 ∗ memRegion (sp + 23568#64) 16 ∗
      memRegion (sp + 144#64) 9840 ∗ memRegion (sp + 11520#64) 12032 ∗
      memRegion (sp + 23584#64) 1568 ∗ memRegion (sp + 26688#64) 3232 := by
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 9984#64) (n := 9840) (k := (19936 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 9984#64) (b' := sp + 11520#64) (n := 1536) (k := (18400 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 11520#64) (b' := sp + 23552#64) (n := 12032) (k := (6368 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 23552#64) (b' := sp + 23568#64) (n := 16) (k := (6352 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 23568#64) (b' := sp + 23584#64) (n := 16) (k := (6336 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 23584#64) (b' := sp + 25152#64) (n := 1568) (k := (4768 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 25152#64) (b' := sp + 26688#64) (n := 1536) (k := (3232 : Nat)) rfl (by clear * -; bv_omega) (by omega)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  have hsplit2 : memRegion (sp + 144#64) 29776 =
      memRegion (sp + 2208#64) 6144 ∗
      memRegion (sp + 8352#64) 16 ∗ memRegion (sp + 8368#64) 16 ∗
      memRegion (sp + 11520#64) 16 ∗ memRegion (sp + 11536#64) 16 ∗
      memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8384#64) 3136 ∗
      memRegion (sp + 11552#64) 18368 := by
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (27712 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 2208#64) (b' := sp + 8352#64) (n := 6144) (k := (21568 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 8352#64) (b' := sp + 8368#64) (n := 16) (k := (21552 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 8368#64) (b' := sp + 8384#64) (n := 16) (k := (21536 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 8384#64) (b' := sp + 11520#64) (n := 3136) (k := (18400 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 11520#64) (b' := sp + 11536#64) (n := 16) (k := (18384 : Nat)) rfl (by clear * -; bv_omega) (by omega),
      memRegion_split' (b := sp + 11536#64) (b' := sp + 11552#64) (n := 16) (k := (18368 : Nat)) rfl (by clear * -; bv_omega) (by omega)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [hsplit1]
  sep_frame_apply (sepWP_elim_bytes (a := sp + 25152#64) 1536); intro bs1536 hbs1536
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 23552#64)); intro v23552
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 23568#64)); intro v23568
  simp only [sepConj_assoc]
  wp_cut_codeLoaded
  wp_steps 6
  step_zvec128
  step_zvec128
  wp_step
  wp_mlkem_call blk28_memcpy_ok (sp + 9984#64, sp + 25152#64, bs1536)
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hsp_mid_al : sf.spAligned = true := spAligned_of_chk hsp1 hsp_chk
  have hfp_a : sf.readReg64 .fp = fpVal := hcs_sf.trans hfp
  have hx20_a : sf.readReg64 .x20 = seedA := h_1.trans hx20
  have hx23_a : sf.readReg64 .x23 = sp + 27840#64 := h_4.trans hx23
  have hx24_a : sf.readReg64 .x24 = sp + 9984#64 := h_5.trans hx24
  have hx26_a : sf.readReg64 .x26 = sp + 27840#64 := h_7.trans hx26
  have hx28_a : sf.readReg64 .x28 = sp + 28104#64 := h_9.trans hx28
  have hrejoin1 :
      ((sp + 9984#64) ↦ₛ bs1536) ∗ ((sp + 25152#64) ↦ₛ bs1536) ∗
        Encaps2.VecMem.Vec128At (sp + 23552#64) 0#128 ∗
        Encaps2.VecMem.Vec128At (sp + 23568#64) 0#128 ∗
        memRegion (sp + 144#64) 9840 ∗ memRegion (sp + 11520#64) 12032 ∗
        memRegion (sp + 23584#64) 1568 ∗ memRegion (sp + 26688#64) 3232 ⊢
      memRegion (sp + 2208#64) 6144 ∗
        memRegion (sp + 8352#64) 16 ∗ memRegion (sp + 8368#64) 16 ∗
        memRegion (sp + 11520#64) 16 ∗ memRegion (sp + 11536#64) 16 ∗
        memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8384#64) 3136 ∗
        memRegion (sp + 11552#64) 18368 := by
    rw [← hsplit2, hsplit1]
    have hm1 : ((sp + 9984#64) ↦ₛ bs1536) ⊢ memRegion (sp + 9984#64) 1536 := by
      rw [← hbs1536]; exact pointsToBytes_entails_memRegion _ _
    have hm2 : ((sp + 25152#64) ↦ₛ bs1536) ⊢ memRegion (sp + 25152#64) 1536 := by
      rw [← hbs1536]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm1 (by sep_frame)
      (entails_sub hm2 (by sep_frame)
        (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame)
          (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame) (by sep_frame))))
  refine SepWP.weaken_pre (entails_sub hrejoin1 (by sep_frame) (by sep_frame)) ?_
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 8352#64)); intro v8352
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 8368#64)); intro v8368
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 11520#64)); intro v11520
  sep_frame_apply (sepWP_elim_vec128 (a := sp + 11536#64)); intro v11536
  wp_cut_codeLoaded
  wp_steps 5
  step_zvec128; step_zvec128; step_zvec128; step_zvec128
  wp_step
  wp_mlkem_call blk29_memset_ok (sp + 2208#64, 0#8, 6144)
  have hsp_fin : sf_1.sp = sp := hsp_sf_1.trans hsp1
  refine SepWP.done hpc_sf_1 hrun_sf_1
    ⟨hsp_fin, spAligned_of_chk hsp_fin hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hback :
      ((sp + 2208#64) ↦ₛ List.replicate 6144 0#8) ∗
        Encaps2.VecMem.Vec128At (sp + 8352#64) 0#128 ∗
        Encaps2.VecMem.Vec128At (sp + 8368#64) 0#128 ∗
        Encaps2.VecMem.Vec128At (sp + 11520#64) 0#128 ∗
        Encaps2.VecMem.Vec128At (sp + 11536#64) 0#128 ∗
        memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8384#64) 3136 ∗
        memRegion (sp + 11552#64) 18368 ⊢ memRegion (sp + 144#64) 29776 := by
    rw [hsplit2]
    exact entails_sub (replicate_entails_memRegion (sp + 2208#64) 6144) (by sep_frame)
      (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame)
        (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame)
          (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame)
            (entails_sub (vec128At_entails_memRegion16 _ _) (by sep_frame) (by sep_frame)))))
  exact entails_sub hback (by sep_frame) (by sep_frame)

private theorem seg1_zero_c [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (s3 : State) (seedA : BitVec 64) (F : SepProp)
    (hpc : s3.pc = b + 0x0158#64)
    (hrun : s3.status = .Running)
    (hsp : s3.sp = sp)
    (hsp_al : s3.spAligned = true)
    (hfp : s3.readReg64 .fp = fpVal)
    (hx20 : s3.readReg64 .x20 = seedA)
    (hx22 : s3.readReg64 .x22 = sp + 2208#64)
    (hx23 : s3.readReg64 .x23 = sp + 27840#64)
    (hx24 : s3.readReg64 .x24 = sp + 9984#64)
    (hx26 : s3.readReg64 .x26 = sp + 27840#64)
    (hx28 : s3.readReg64 .x28 = sp + 28104#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x01a8#64) s3
      (memRegion (sp + 136#64) 8 ∗ memRegion (sp + 144#64) 29776 ∗ F)
      (fun s4 P4 =>
        s4.sp = sp ∧
        s4.spAligned = true ∧
        s4.readReg64 .fp = fpVal ∧
        s4.readReg64 .x19 = sp + 17376#64 ∧
        s4.readReg64 .x20 = seedA ∧
        s4.readReg64 .x22 = sp + 2208#64 ∧
        s4.readReg64 .x23 = sp + 27840#64 ∧
        s4.readReg64 .x24 = sp + 9984#64 ∧
        s4.readReg64 .x26 = sp + 27840#64 ∧
        s4.readReg64 .x28 = sp + 28104#64 ∧
        (P4 ⊢ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 144#64) 29776 ∗ F)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by rw [State.spAligned, hsp] at hsp_al; exact hsp_al
  have hsub1 : memRegion (sp + 144#64) 29776 =
      memRegion (sp + 2208#64) 6176 ∗ memRegion (sp + 17376#64) 6176 ∗
      memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8384#64) 8992 ∗ memRegion (sp + 23552#64) 6368 := by
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (27712 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 2208#64) (b' := sp + 8384#64) (n := 6176) (k := (21536 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 8384#64) (b' := sp + 17376#64) (n := 8992) (k := (12544 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 17376#64) (b' := sp + 23552#64) (n := 6176) (k := (6368 : Nat)) rfl (by bv_omega) (by omega)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  have hsub2 : memRegion (sp + 144#64) 29776 =
      memRegion (sp + 8416#64) 1568 ∗ memRegion (sp + 9984#64) 1568 ∗
      memRegion (sp + 144#64) 8272 ∗ memRegion (sp + 11552#64) 18368 := by
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 8416#64) (n := 8272) (k := (21504 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 8416#64) (b' := sp + 9984#64) (n := 1568) (k := (19936 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 9984#64) (b' := sp + 11552#64) (n := 1568) (k := (18368 : Nat)) rfl (by bv_omega) (by omega)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  have hsub3 : memRegion (sp + 144#64) 29776 =
      memRegion (sp + 2208#64) 6208 ∗ memRegion (sp + 17376#64) 6208 ∗
      memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8416#64) 8960 ∗ memRegion (sp + 23584#64) 6336 := by
    rw [memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (27712 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 2208#64) (b' := sp + 8416#64) (n := 6208) (k := (21504 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 8416#64) (b' := sp + 17376#64) (n := 8960) (k := (12544 : Nat)) rfl (by bv_omega) (by omega),
      memRegion_split' (b := sp + 17376#64) (b' := sp + 23584#64) (n := 6208) (k := (6336 : Nat)) rfl (by bv_omega) (by omega)]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [hsub1]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 136#64)); intro c136
  sep_frame_apply (sepWP_elim_bytes (a := sp + 2208#64) 6176); intro bs6176 hbs6176
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 17376#64, sp + 2208#64, bs6176)
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hsp_a : sf.spAligned = true := spAligned_of_chk hsp1 hsp_chk
  have hfp1 : sf.readReg64 .fp = fpVal := hcs_sf.trans hfp
  have hx19_1 : sf.readReg64 .x19 = sp + 17376#64 := h
  have hx20_1 : sf.readReg64 .x20 = seedA := h_1.trans hx20
  have hx22_1 : sf.readReg64 .x22 = sp + 2208#64 := h_3.trans hx22
  have hx23_1 : sf.readReg64 .x23 = sp + 27840#64 := h_4.trans hx23
  have hx24_1 : sf.readReg64 .x24 = sp + 9984#64 := h_5.trans hx24
  have hx26_1 : sf.readReg64 .x26 = sp + 27840#64 := h_7.trans hx26
  have hx28_1 : sf.readReg64 .x28 = sp + 28104#64 := h_9.trans hx28
  have hv8416 : sf.readReg64 .x22 + 6208#64 = sp + 8416#64 := by rw [hx22_1]; clear * -; bv_omega
  have hr1 :
      ((sp + 2208#64) ↦ₛ bs6176) ∗ ((sp + 17376#64) ↦ₛ bs6176) ∗
        memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8384#64) 8992 ∗ memRegion (sp + 23552#64) 6368 ⊢
      memRegion (sp + 144#64) 29776 := by
    rw [hsub1]
    have hm1 : ((sp + 2208#64) ↦ₛ bs6176) ⊢ memRegion (sp + 2208#64) 6176 := by
      rw [← hbs6176]; exact pointsToBytes_entails_memRegion _ _
    have hm2 : ((sp + 17376#64) ↦ₛ bs6176) ⊢ memRegion (sp + 17376#64) 6176 := by
      rw [← hbs6176]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm1 (by sep_frame) (entails_sub hm2 (by sep_frame) (by sep_frame))
  refine SepWP.weaken_pre (entails_sub hr1 (by sep_frame) (by sep_frame)) ?_
  rw [hsub2]
  sep_frame_apply (sepWP_elim_bytes (a := sp + 9984#64) 1568); intro bs1568 hbs1568
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 8416#64, sp + 9984#64, bs1568)
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans hsp1
  have hsp_b : sf_1.spAligned = true := spAligned_of_chk hsp2 hsp_chk
  have hfp2 : sf_1.readReg64 .fp = fpVal := by simp [*]
  have hx19_2 : sf_1.readReg64 .x19 = sp + 17376#64 := by simp [*]
  have hx20_2 : sf_1.readReg64 .x20 = seedA := by simp [*]
  have hx22_2 : sf_1.readReg64 .x22 = sp + 2208#64 := by simp [*]
  have hx23_2 : sf_1.readReg64 .x23 = sp + 27840#64 := by simp [*]
  have hx24_2 : sf_1.readReg64 .x24 = sp + 9984#64 := by simp [*]
  have hx26_2 : sf_1.readReg64 .x26 = sp + 27840#64 := by simp [*]
  have hx28_2 : sf_1.readReg64 .x28 = sp + 28104#64 := by simp [*]
  have hr2 :
      ((sp + 8416#64) ↦ₛ bs1568) ∗ ((sp + 9984#64) ↦ₛ bs1568) ∗
        memRegion (sp + 144#64) 8272 ∗ memRegion (sp + 11552#64) 18368 ⊢
      memRegion (sp + 144#64) 29776 := by
    rw [hsub2]
    have hm1 : ((sp + 8416#64) ↦ₛ bs1568) ⊢ memRegion (sp + 8416#64) 1568 := by
      rw [← hbs1568]; exact pointsToBytes_entails_memRegion _ _
    have hm2 : ((sp + 9984#64) ↦ₛ bs1568) ⊢ memRegion (sp + 9984#64) 1568 := by
      rw [← hbs1568]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm1 (by sep_frame) (entails_sub hm2 (by sep_frame) (by sep_frame))
  refine SepWP.weaken_pre (entails_sub hr2 (by sep_frame) (by sep_frame)) ?_
  rw [hsub3]
  sep_frame_apply (sepWP_elim_bytes (a := sp + 17376#64) 6208); intro bs6208 hbs6208
  wp_cut_codeLoaded
  wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 2208#64, sp + 17376#64, bs6208)
  have hr3 :
      ((sp + 2208#64) ↦ₛ bs6208) ∗ ((sp + 17376#64) ↦ₛ bs6208) ∗
        memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 8416#64) 8960 ∗ memRegion (sp + 23584#64) 6336 ⊢
      memRegion (sp + 144#64) 29776 := by
    rw [hsub3]
    have hm1 : ((sp + 2208#64) ↦ₛ bs6208) ⊢ memRegion (sp + 2208#64) 6208 := by
      rw [← hbs6208]; exact pointsToBytes_entails_memRegion _ _
    have hm2 : ((sp + 17376#64) ↦ₛ bs6208) ⊢ memRegion (sp + 17376#64) 6208 := by
      rw [← hbs6208]; exact pointsToBytes_entails_memRegion _ _
    exact entails_sub hm1 (by sep_frame) (entails_sub hm2 (by sep_frame) (by sep_frame))
  have hsp_fin : sf_2.sp = sp := hsp_sf_2.trans hsp2
  refine SepWP.done hpc_sf_2 hrun_sf_2
    ⟨hsp_fin, spAligned_of_chk hsp_fin hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  try simp only [hsp1, hv8416]
  exact entails_sub hr3 (by sep_frame) (by sep_frame)

theorem seg1_zero_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s1 : State) (seedA outPtr : BitVec 64) (F : SepProp)
    (hpc : s1.pc = b + 0x0040#64)
    (hrun : s1.status = .Running)
    (hsp : s1.sp = s0.sp - 28832#64)
    (hsp_al : s1.spAligned = true)
    (hx0 : s1.readReg64 .x0 = seedA)
    (hx1 : s1.readReg64 .x1 = outPtr)
    (hfp : s1.readReg64 .fp = s0.sp - 96#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem)
    (hro : MlKemRoOk mlkemMpl s1.mem) :
    let sp := s0.sp - 30080#64
    SepWP (blkPC05.rebase b (fun _ => none)) (b + 0x01a8#64) s1
      (memRegion sp 29920 ∗ F)
      (fun s4 P4 =>
        s4.sp = sp ∧
        s4.spAligned = true ∧
        s4.readReg64 .fp = s0.sp - 96#64 ∧
        s4.readReg64 .x19 = sp + 17376#64 ∧
        s4.readReg64 .x20 = seedA ∧
        s4.readReg64 .x22 = sp + 2208#64 ∧
        s4.readReg64 .x23 = sp + 27840#64 ∧
        s4.readReg64 .x24 = sp + 9984#64 ∧
        s4.readReg64 .x26 = sp + 27840#64 ∧
        s4.readReg64 .x28 = sp + 28104#64 ∧
        (P4 ⊢ ((sp + 40#64) ↦₆₄ outPtr) ∗
          ((sp + 128#64) ↦₆₄ (sp + 10248#64)) ∗
          ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
          memRegion sp 40 ∗ memRegion (sp + 48#64) 80 ∗
          memRegion (sp + 144#64) 29776 ∗ F)) := by
  intro sp
  have hsp1 : s1.sp = sp + 1248#64 := by dsimp [sp]; rw [hsp]; bv_omega
  refine sepWP_seq_env hcl hro
    (seg1_zero_a hb hbase sp (s0.sp - 96#64) s1 seedA outPtr F hpc hrun hsp1 hsp_al hx0 hx1 hfp hcl) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hal2, hfp2, hx20_2, hx23_2, hx24_2, hx26_2, hx28_2, hP2⟩
  have h136 : memRegion (sp + 136#64) 29784 =
      memRegion (sp + 136#64) 8 ∗ memRegion (sp + 144#64) 29776 :=
    memRegion_split' (b := sp + 136#64) (b' := sp + 144#64) (n := 8) (k := (29776 : Nat)) rfl (by bv_omega) (by omega)
  refine sepWP_seq_env hcl2 hro2
    (SepWP.weaken_pre (Entails.trans hP2 (by rw [h136]; sep_frame))
      (seg1_zero_b hb hbase sp (s0.sp - 96#64) s2 seedA _ hpc2 hrun2 hsp2 hal2 hfp2 hx20_2 hx23_2 hx24_2 hx26_2 hx28_2 hcl2)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hsp3, hal3, hfp3, hx20_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3, hP3⟩
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
      (seg1_zero_c hb hbase sp (s0.sp - 96#64) s3 seedA _ hpc3 hrun3 hsp3 hal3 hfp3 hx20_3 hx22_3 hx23_3 hx24_3 hx26_3 hx28_3 hcl3)) ?_
  rintro s4 P4 _ _ ⟨hsp4, hal4, hfp4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx26_4, hx28_4, hP4⟩
  exact ⟨hsp4, hal4, hfp4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx26_4, hx28_4,
    Entails.trans hP4 (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Zero

