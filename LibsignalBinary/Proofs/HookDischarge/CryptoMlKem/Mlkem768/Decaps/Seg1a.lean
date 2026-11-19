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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 1a (`+0x0000 .. +0x00e8`)

Prologue saving `SavedFrame04 s0.sp s0` (`160` B), 6-page inductive stack probe loop
(`+0x0030 .. +0x0040`, `24576` B), local frame allocation (`sp = s0.sp - 25824#64`),
two `ct = ct1 ++ ct2` (`1088` B) stack copies at `sp + 2256` and `sp + 3344`,
initial pointer spills (`ret`, `sp + 22664`, `dkA + 2336`, `dkA + 2368`), and
`B29` (`memset`) zeroing `[sp + 22912, sp + 23936)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemMemcpySpec mlkemMemsetSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem Poly32Mem PolyMem PolyOctMem SepLoad128 SepStore128 Vec128At Vec32 VecRangeMem
  bytesToVecNat oct8Mem_eq_pointsToBytes oct8Mem_ofFn pointsToBytes_eq_vecRangeMem
  poly32Mem_ofFn step_ldpQ128 step_strQ128 vecRangeBytes_bytesToVecNat
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x0000 → 0x00e4]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

theorem blk28_memcpy_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk28_memcpy_ok

theorem blk29_memset_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC04

/-! ## 1. Tight-Stack Decomposition (`26960 = 1136 + 25664 + 160`) -/

theorem stackAt_26960_eq (sp0 sp : BitVec 64) (hsp : sp = sp0 - 25824#64) :
    stackAt sp0 26960 =
      stackAt sp 1136 ∗ memRegion sp 25664 ∗ memRegion (sp0 - 160#64) 160 := by
  subst hsp
  unfold stackAt
  have h0 : memRegion (sp0 - BitVec.ofNat 64 26960) 26960 =
      memRegion (sp0 - 26960#64) 26960 := rfl
  have hsub : (sp0 - 25824#64) - BitVec.ofNat 64 1136 = sp0 - 26960#64 := by
    bv_omega
  rw [h0, hsub,
    memRegion_split' (b' := sp0 - 25824#64) (n := 1136) (k := (25824 : Nat)) rfl
      (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 25824#64) (b' := sp0 - 160#64) (n := 25664) (k := (160 : Nat)) rfl
      (by bv_omega) (by decide)]

/-! ## 2. Frame Spill (`+0x0000 → +0x0030`) & 6-Page Stack Probe Loop (`+0x0030 → +0x0040`) -/

private theorem memRegion160_prologue_split (sp0 : BitVec 64) :
    memRegion (sp0 - 160#64) 160 =
      memRegion (sp0 - 160#64) 32 ∗
      memRegion (sp0 - 128#64) 32 ∗
      memRegion (sp0 - 96#64) 32 ∗
      memRegion (sp0 - 64#64) 32 ∗
      memRegion (sp0 - 32#64) 32 := by
  rw [memRegion_split' (b' := sp0 - 128#64) (n := 32) (k := (128 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 96#64) (n := 32) (k := (96 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 64#64) (n := 32) (k := (64 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 32#64) (n := 32) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]

private theorem seg1_save_frame [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64) (Rest : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 48#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = s0.sp - 160#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = ret ∧
        s1.readReg64 .x1 = dkA ∧
        s1.readReg64 .x2 = ct1A ∧
        s1.readReg64 .x3 = ct2A ∧
        s1.readReg64 .fp = s0.sp - 96#64 ∧
        s1.readReg64 .x9 = s0.sp - 24736#64 ∧
        (P1 ⊢ SavedFrame04 s0.sp s0 ∗ Rest)) := by
  subst hbase
  rw [memRegion160_prologue_split s0.sp]
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 160#64)); intro f0 f1 f2 f3
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 128#64)); intro f4 f5 f6 f7
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 96#64)); intro f8 f9 f10 f11
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 64#64)); intro f12 f13 f14 f15
  sep_frame_apply (sepWP_elim_region32 (a := s0.sp - 32#64)); intro f16 f17 f18 f19
  have a1 : s0.sp - 160#64 + 8#64 = s0.sp - 152#64 := by bv_omega
  have a2 : s0.sp - 160#64 + 16#64 = s0.sp - 144#64 := by bv_omega
  have a3 : s0.sp - 160#64 + 24#64 = s0.sp - 136#64 := by bv_omega
  have a5 : s0.sp - 128#64 + 8#64 = s0.sp - 120#64 := by bv_omega
  have a6 : s0.sp - 128#64 + 16#64 = s0.sp - 112#64 := by bv_omega
  have a7 : s0.sp - 128#64 + 24#64 = s0.sp - 104#64 := by bv_omega
  have a9 : s0.sp - 96#64 + 8#64 = s0.sp - 88#64 := by bv_omega
  have a10 : s0.sp - 96#64 + 16#64 = s0.sp - 80#64 := by bv_omega
  have a11 : s0.sp - 96#64 + 24#64 = s0.sp - 72#64 := by bv_omega
  have a13 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have a14 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have a15 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_omega
  have a17 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
  have a18 : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_omega
  have a19 : s0.sp - 32#64 + 24#64 = s0.sp - 8#64 := by bv_omega
  rw [a1, a2, a3, a5, a6, a7, a9, a10, a11, a13, a14, a15, a17, a18, a19]
  have hsp160 : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hsp160,
      by simp [hx0], by simp [hx1], by simp [hx2], by simp [hx3],
      by simp, by simp, ?_⟩
  unfold SavedFrame04
  sep_frame

private theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

private theorem seg1_probe_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (spLim cur : BitVec 64) (p0 : BitVec 64) (R_inner : SepProp)
    (s : State) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 48#64) (hrun : s.status = .Running)
    (hsp : s.sp = cur + 4096#64) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = spLim)
    (hcond : ConditionHolds .NE (subsPState64 cur spLim) = true)
    (hnext : ∀ s' : State,
      s'.pc = b + 48#64 →
      s'.status = .Running →
      s'.sp = cur →
      s'.spAligned = true →
      s'.readReg64 .x0 = s.readReg64 .x0 →
      s'.readReg64 .x1 = s.readReg64 .x1 →
      s'.readReg64 .x2 = s.readReg64 .x2 →
      s'.readReg64 .x3 = s.readReg64 .x3 →
      s'.readReg64 .fp = s.readReg64 .fp →
      s'.readReg64 .x9 = spLim →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 64#64) s'
        ((cur ↦₆₄ 0#64) ∗ R_inner) post) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 64#64) s
      ((cur ↦₆₄ p0) ∗ R_inner) post := by
  subst hbase
  have hsp_sub : s.sp - 4096#64 = cur := by rw [hsp]; bv_omega
  have hcur_A : (cur &&& 15#64 == 0#64) = true := by
    rw [← hsp_sub]; exact spAligned_sub s.sp 4096#64 hspA (by decide)
  rw [← hsp_sub]
  wp_steps 3
  rw [hsp_sub]
  refine step_bCond_taken (pc := blkPl04.base + 60#64) (dst := blkPl04.base + 48#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [hcond]) (by bv_omega) ?_
  exact hnext _ (by wp_norm_lhs) (by simp [hrun]) (by simp)
    (spAligned_of_chk (by simp) hcur_A)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [hx9])

private theorem seg1_probe_loop [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b) (spBase : BitVec 64) :
    ∀ (rem : Nat), 1 ≤ rem → rem ≤ 6 →
      ∀ (s : State) (Rest : SepProp),
        s.pc = b + 48#64 →
        s.status = .Running →
        s.sp = spBase + BitVec.ofNat 64 (4096 * rem) →
        s.spAligned = true →
        s.readReg64 .x9 = spBase →
        SepWP (blkPC04.rebase b (fun _ => none)) (b + 64#64) s
          (memRegion spBase (4096 * rem) ∗ Rest)
          (fun sf Pf =>
            sf.sp = spBase ∧
            sf.spAligned = true ∧
            sf.readReg64 .x0 = s.readReg64 .x0 ∧
            sf.readReg64 .x1 = s.readReg64 .x1 ∧
            sf.readReg64 .x2 = s.readReg64 .x2 ∧
            sf.readReg64 .x3 = s.readReg64 .x3 ∧
            sf.readReg64 .fp = s.readReg64 .fp ∧
            (Pf ⊢ memRegion spBase (4096 * rem) ∗ Rest)) := by
  subst hbase
  intro rem
  induction rem with
  | zero => intro h1; omega
  | succ m ih =>
    intro _ hm6 s Rest hpc hrun hsp hspA hx9
    have hsp_nextA : ((s.sp - 4096#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s.sp 4096#64 hspA (by decide)
    rcases m with _ | m'
    · have hsp_sub : s.sp - 4096#64 = spBase := by rw [hsp]; bv_omega
      have hbase_A : (spBase &&& 15#64 == 0#64) = true := by rwa [hsp_sub] at hsp_nextA
      rw [show 4096 * 1 = (4096 : Nat) from rfl,
        memRegion_split' (b := spBase) (b' := spBase + 8#64) (n := 8) (k := (4088 : Nat))
          rfl rfl (by decide)]
      sep_frame_apply (sepWP_elim_cell8 (a := spBase)); intro p0
      rw [← hsp_sub]
      wp_steps 3
      rw [hsp_sub]
      wp_step
      refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
        ⟨by simp, spAligned_of_chk (by simp) hbase_A,
          by simp, by simp, by simp, by simp, by simp, ?_⟩
      exact entails_sub (cell_entails_memRegion8 spBase 0#64) (by sep_frame) (by sep_frame)
    · have hm_lt : m' < 5 := by omega
      let cur := spBase + BitVec.ofNat 64 (4096 * (m' + 1))
      have hsp_cur : s.sp = cur + 4096#64 := by
        rw [hsp]; dsimp [cur]; clear * -; bv_omega
      have hcur_ne : cur ≠ spBase := by
        intro heq; dsimp [cur] at heq
        rcases m' with _ | _ | _ | _ | _ | m5
        · exact absurd heq (by change spBase + 4096#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 8192#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 12288#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 16384#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 20480#64 = spBase → False; bv_omega)
        · omega
      have hcond : ConditionHolds .NE (subsPState64 cur spBase) = true := by
        rw [conditionHolds_ne_subsPState64, bne_iff_ne]
        exact hcur_ne
      have hsplit_pre :
          memRegion spBase (4096 * (m' + 1 + 1)) ∗ Rest =
            (memRegion spBase (4096 * (m' + 1)) ∗ memRegion cur 8 ∗ memRegion (cur + 8#64) 4088) ∗ Rest := by
        rw [memRegion_split' (b := spBase) (b' := cur) (n := 4096 * (m' + 1)) (k := (4096 : Nat))
            (by omega) rfl (by omega),
          memRegion_split' (b := cur) (b' := cur + 8#64) (n := 8) (k := (4088 : Nat))
            rfl rfl (by decide)]
      have hrest4096 : (cur ↦₆₄ 0#64) ∗ memRegion (cur + 8#64) 4088 ⊢ memRegion cur 4096 := by
        rw [memRegion_split' (b := cur) (b' := cur + 8#64) (n := 8) (k := (4088 : Nat))
          rfl rfl (by decide)]
        exact sepConj_mono_left (cell_entails_memRegion8 cur 0#64)
      have hpre_ent :
          memRegion spBase (4096 * (m' + 1 + 1)) ∗ Rest ⊢
            memRegion cur 8 ∗ (memRegion spBase (4096 * (m' + 1)) ∗ memRegion (cur + 8#64) 4088 ∗ Rest) := by
        rw [hsplit_pre]; sep_frame
      refine SepWP.weaken_pre hpre_ent ?_
      refine sepWP_elim_cell8 fun p0 => ?_
      refine seg1_probe_iter _hb rfl spBase cur p0
        (memRegion spBase (4096 * (m' + 1)) ∗ memRegion (cur + 8#64) 4088 ∗ Rest)
        s _ hpc hrun hsp_cur hspA hx9 hcond ?_
      intro s' hpc' hrun' hsp' hspA' hx0' hx1' hx2' hx3' hfp' hx9'
      have hframe_step :
          (cur ↦₆₄ 0#64) ∗ (memRegion spBase (4096 * (m' + 1)) ∗ memRegion (cur + 8#64) 4088 ∗ Rest) ⊢
            memRegion spBase (4096 * (m' + 1)) ∗ (memRegion cur 4096 ∗ Rest) :=
        entails_sub hrest4096 (by sep_frame) (by sep_frame)
      refine SepWP.weaken_pre hframe_step ?_
      refine SepWP.mono
        (ih (by omega) (by omega) s' (memRegion cur 4096 ∗ Rest)
          hpc' hrun' hsp' hspA' hx9') ?_
      rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx0_f, hx1_f, hx2_f, hx3_f, hfp_f, hPf⟩
      refine ⟨hsp_f, hspA_f, hx0_f.trans hx0', hx1_f.trans hx1',
        hx2_f.trans hx2', hx3_f.trans hx3', hfp_f.trans hfp', Entails.trans hPf ?_⟩
      have hmerge :
          memRegion spBase (4096 * (m' + 1 + 1)) =
            memRegion spBase (4096 * (m' + 1)) ∗ memRegion cur 4096 :=
        memRegion_split' (b := spBase) (b' := cur) (n := 4096 * (m' + 1)) (k := (4096 : Nat))
          (by omega) rfl (by omega)
      rw [hmerge]
      sep_frame

/-! ## 3. `ct2` 128-Byte NEON Copy (`+0x0088 → +0x00c8`) & Segment 1a Contract -/

local macro "step_ldpQ_ct2 " ct2A:ident k1:num k2:num : tactic => `(tactic| (
  apply step_ldpQ128 (ea := $ct2A + BitVec.ofNat 64 (16 * $k1))
    (ea16 := $ct2A + BitVec.ofNat 64 (16 * $k2)) (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · rfl
  · simp [evalAddrMode, *]
  · clear * -; bv_omega
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k1) (by decide) rfl rfl))
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k2) (by decide) rfl rfl))
  · wp_norm_lhs))

local macro "step_strQ_ct2 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.oct8 (k := $k); { decide }; { clear * -; bv_omega }; { rfl }
  · wp_norm_lhs
  intro _))

private theorem oct8_copy_all (t0 src : Oct8) :
    ((((((((t0.set 4 (src.get 4)).set 5 (src.get 5)).set 6 (src.get 6)).set 7 (src.get 7)).set 0
      (src.get 0)).set 1 (src.get 1)).set 2 (src.get 2)).set 3 (src.get 3)) = src := by
  cases t0; cases src; rfl

theorem sepWP_elim_vec128At {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 128, SepWP prog target s (Vec128At a v ∗ R0) post) :
    SepWP prog target s (memRegion a 16 ∗ R0) post := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := (8 : Nat)) rfl rfl (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := a)); intro v0
  sep_frame_apply (sepWP_elim_cell8 (a := a + 8#64)); intro v1
  have hv : Vec128At a (v1 ++ v0) = (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
    unfold Vec128At
    have h0 : (v1 ++ v0).extractLsb' 0 64 = v0 := by bv_bits
    have h1 : (v1 ++ v0).extractLsb' 64 64 = v1 := by bv_bits
    rw [h0, h1]
  refine SepWP.weaken_pre ?_ (h (v1 ++ v0))
  rw [hv]; sep_frame

theorem sepWP_elim_vecRange :
    ∀ (n : Nat), n ≤ 40 → ∀ {prog : Program} {target : BitVec 64} {s : State}
      {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop},
      (∀ f : Nat → BitVec 128, SepWP prog target s (VecRangeMem n a f ∗ R0) post) →
      SepWP prog target s (memRegion a (16 * n) ∗ R0) post
  | 0, _, _, _, _, a, _, _, h => by
    simpa [VecRangeMem, memRegion_zero] using h (fun _ => 0#128)
  | n + 1, hn, _, _, _, a, _, _, h => by
    rw [show 16 * (n + 1) = 16 + 16 * n by omega,
      memRegion_split' (b := a) (b' := a + 16#64) (n := 16) (k := (16 * n : Nat)) rfl rfl (by omega)]
    sep_frame_apply (sepWP_elim_vec128At (a := a)); intro v0
    sep_frame_apply (sepWP_elim_vecRange n (by omega) (a := a + 16#64)); intro f'
    let f : Nat → BitVec 128 := fun i => match i with | 0 => v0 | j + 1 => f' j
    have hf : VecRangeMem (n + 1) a f = Vec128At a v0 ∗ VecRangeMem n (a + 16#64) f' := rfl
    refine SepWP.weaken_pre ?_ (h f)
    rw [hf]; sep_frame

theorem sepWP_elim_poly32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Vec32, SepWP prog target s (Poly32Mem a t ∗ R0) post) :
    SepWP prog target s (memRegion a 512 ∗ R0) post := by
  change SepWP prog target s (memRegion a (16 * 32) ∗ R0) post
  refine sepWP_elim_vecRange 32 (by decide) fun f => ?_
  change SepWP prog target s (PolyMem a f ∗ R0) post
  rw [← poly32Mem_ofFn a f]
  exact h (Vec32.ofFn f)

theorem sepWP_elim_oct8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Oct8, SepWP prog target s (Oct8Mem a t ∗ R0) post) :
    SepWP prog target s (memRegion a 128 ∗ R0) post := by
  change SepWP prog target s (memRegion a (16 * 8) ∗ R0) post
  refine sepWP_elim_vecRange 8 (by decide) fun f => ?_
  change SepWP prog target s (PolyOctMem a f ∗ R0) post
  rw [← oct8Mem_ofFn a f]
  exact h (Oct8.ofFn f)

private theorem pointsTo_128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

private theorem seg1_copy_ct2_dup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp ct2A : BitVec 64) (ct1 ct2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 136#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = ct2A)
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 200#64) s
      (memRegion (sp + 3216#64) 128 ∗ (ct2A ↦ₛ ct2) ∗
        ((sp + 2256#64) ↦ₛ ct1) ∗ memRegion (sp + 3344#64) 1088 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ (ct2A ↦ₛ ct2) ∗ ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗
          ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set oct := Oct8.ofFn (bytesToVecNat ct2) with hoct
  have hct2_oct : (ct2A ↦ₛ ct2) = Oct8Mem ct2A oct := pointsTo_128_eq_oct8Mem ct2A hct2
  have hsp_oct : Oct8Mem (sp + 3216#64) oct = ((sp + 3216#64) ↦ₛ ct2) :=
    (pointsTo_128_eq_oct8Mem (sp + 3216#64) hct2).symm
  have happ : ((sp + 2256#64) ↦ₛ ct1) ∗ ((sp + 3216#64) ↦ₛ ct2) =
      ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) := by
    rw [pointsToBytes_append, hct1, show sp + 2256#64 + BitVec.ofNat 64 960 = sp + 3216#64 by bv_omega]
  rw [hct2_oct]
  sep_frame_apply (sepWP_elim_oct8 (a := sp + 3216#64)); intro t0
  wp_cut_codeLoaded
  step_ldpQ_ct2 ct2A 4 5
  wp_steps 3
  step_strQ_ct2 4
  step_ldpQ_ct2 ct2A 6 7
  step_strQ_ct2 5
  step_strQ_ct2 6
  step_ldpQ_ct2 ct2A 0 1
  step_strQ_ct2 7
  step_strQ_ct2 0
  step_ldpQ_ct2 ct2A 2 3
  step_strQ_ct2 1
  step_strQ_ct2 2
  step_strQ_ct2 3
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  rw [oct8_copy_all t0 (Oct8.ofFn (bytesToVecNat ct2)), ← hoct, hsp_oct, ← hct2_oct]
  have hcomb :
      ((sp + 3216#64) ↦ₛ ct2) ∗ ((ct2A ↦ₛ ct2) ∗ ((sp + 2256#64) ↦ₛ ct1) ∗
        memRegion (sp + 3344#64) 1088 ∗ Rest) ⊢
      memRegion (sp + 3344#64) 1088 ∗ ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗
        ((ct2A ↦ₛ ct2) ∗ Rest) := by
    rw [← happ]; sep_frame
  refine SepWP.weaken_pre hcomb ?_
  have hct_len : (ct1 ++ ct2).length = 1088 := by simp [hct1, hct2]
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 3344#64, sp + 2256#64, ct1 ++ ct2)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by sep_frame⟩

@[expose] def Seg1aSpatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  stackAt sp 1136 ∗
  SavedFrame04 s0.sp s0 ∗
  memRegion sp 136 ∗
  ((sp + 136#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 56 ∗
  ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
  memRegion (sp + 208#64) 1632 ∗
  ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
  memRegion (sp + 1848#64) 8 ∗
  ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
  memRegion (sp + 1864#64) 392 ∗
  ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗
  ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
  memRegion (sp + 4432#64) 21232 ∗
  (ct1A ↦ₛ ct1) ∗
  (ct2A ↦ₛ ct2) ∗
  F

private theorem seg1_alloc_copy_ct1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s2 : State) (sp fp0 ret dkA ct1A ct2A : BitVec 64)
    (ct1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s2.pc = b + 64#64) (hrun : s2.status = .Running)
    (hsp2 : s2.sp = sp + 1088#64) (hspA2 : s2.spAligned = true)
    (hx0 : s2.readReg64 .x0 = ret) (hx1 : s2.readReg64 .x1 = dkA)
    (hx2 : s2.readReg64 .x2 = ct1A) (hx3 : s2.readReg64 .x3 = ct2A)
    (hfp : s2.readReg64 .fp = fp0) (hct1 : ct1.length = 960)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 136#64) s2
      (memRegion sp 136 ∗ memRegion (sp + 136#64) 8 ∗ memRegion (sp + 200#64) 8 ∗
        memRegion (sp + 2256#64) 960 ∗ (ct1A ↦ₛ ct1) ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .fp = fp0 ∧
        s3.readReg64 .x20 = dkA + 384#64 ∧
        s3.readReg64 .x21 = ct2A ∧
        s3.readReg64 .x22 = sp + 22400#64 ∧
        s3.readReg64 .x23 = dkA ∧
        s3.readReg64 .x24 = dkA + 384#64 ∧
        s3.readReg64 .x26 = sp + 20704#64 ∧
        s3.readReg64 .x28 = sp + 20968#64 ∧
        (P3 ⊢ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
          ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
          ((sp + 2256#64) ↦ₛ ct1) ∗ (ct1A ↦ₛ ct1) ∗ Rest)) := by
  subst hbase
  have hsp_sub : s2.sp - 1088#64 = sp := by rw [hsp2]; bv_omega
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by
    rw [← hsp_sub]; exact spAligned_sub s2.sp 1088#64 hspA2 (by decide)
  rw [memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := (128 : Nat)) rfl rfl (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := sp)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 136#64)); intro c136
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 200#64)); intro c200
  wp_cut_codeLoaded
  wp_steps 17
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_call1
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 2256#64, ct1A, ct1)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  have h136 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 128 ⊢ memRegion sp 136 := by
    rw [memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := (128 : Nat)) rfl rfl (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 sp 0#64)
  exact entails_sub h136 (by sep_frame) (by sep_frame)

private theorem seg1_spills_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s4 : State) (sp dkA : BitVec 64) (Rest : SepProp)
    (hpc : s4.pc = b + 200#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp) (hspA : s4.spAligned = true)
    (hx22 : s4.readReg64 .x22 = sp + 22400#64)
    (hx23 : s4.readReg64 .x23 = dkA)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s4.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 232#64) s4
      (memRegion (sp + 1840#64) 8 ∗ memRegion (sp + 1856#64) 8 ∗
        memRegion (sp + 4432#64) 18480 ∗ memRegion (sp + 22912#64) 1024 ∗
        memRegion (sp + 23936#64) 1728 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s4.readReg64 .fp ∧
        sf.readReg64 .x20 = s4.readReg64 .x20 ∧
        sf.readReg64 .x23 = dkA ∧
        sf.readReg64 .x24 = s4.readReg64 .x24 ∧
        sf.readReg64 .x26 = s4.readReg64 .x26 ∧
        sf.readReg64 .x28 = s4.readReg64 .x28 ∧
        (Pf ⊢ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
          ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
          memRegion (sp + 4432#64) 21232 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 1840#64)); intro c1840
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 1856#64)); intro c1856
  wp_cut_codeLoaded
  wp_steps 7
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_call3
  have ha22912 : sp + 22400#64 + 512#64 = sp + 22912#64 := by bv_omega
  wp_call (blk29_memset_04 blkPl04.base) (sp + 22912#64, 0#8, 1024)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  have h1024 : ((sp + 22912#64) ↦ₛ List.replicate 1024 0#8) ⊢ memRegion (sp + 22912#64) 1024 := by
    have hpb := pointsToBytes_entails_memRegion (sp + 22912#64) (List.replicate 1024 0#8)
    rwa [List.length_replicate] at hpb
  have h21232 :
      memRegion (sp + 4432#64) 21232 =
        memRegion (sp + 4432#64) 18480 ∗ memRegion (sp + 22912#64) 1024 ∗
          memRegion (sp + 23936#64) 1728 := by
    rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 22912#64) (n := 18480) (k := (2752 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22912#64) (b' := sp + 23936#64) (n := 1024) (k := (1728 : Nat))
        rfl (by bv_omega) (by decide)]
  rw [h21232]
  exact entails_sub h1024 (by sep_frame) (by sep_frame)

private theorem memRegion_25664_seg1a_split (sp : BitVec 64) :
    memRegion sp 25664 =
      memRegion sp 136 ∗
      memRegion (sp + 136#64) 8 ∗
      memRegion (sp + 144#64) 56 ∗
      memRegion (sp + 200#64) 8 ∗
      memRegion (sp + 208#64) 1632 ∗
      memRegion (sp + 1840#64) 8 ∗
      memRegion (sp + 1848#64) 8 ∗
      memRegion (sp + 1856#64) 8 ∗
      memRegion (sp + 1864#64) 392 ∗
      memRegion (sp + 2256#64) 960 ∗
      memRegion (sp + 3216#64) 128 ∗
      memRegion (sp + 3344#64) 1088 ∗
      memRegion (sp + 4432#64) 18480 ∗
      memRegion (sp + 22912#64) 1024 ∗
      memRegion (sp + 23936#64) 1728 := by
  rw [memRegion_split' (b' := sp + 136#64) (n := 136) (k := (25528 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 136#64) (b' := sp + 144#64) (n := 8) (k := (25520 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 144#64) (b' := sp + 200#64) (n := 56) (k := (25464 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 200#64) (b' := sp + 208#64) (n := 8) (k := (25456 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 208#64) (b' := sp + 1840#64) (n := 1632) (k := (23824 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1840#64) (b' := sp + 1848#64) (n := 8) (k := (23816 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1848#64) (b' := sp + 1856#64) (n := 8) (k := (23808 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1856#64) (b' := sp + 1864#64) (n := 8) (k := (23800 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1864#64) (b' := sp + 2256#64) (n := 392) (k := (23408 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2256#64) (b' := sp + 3216#64) (n := 960) (k := (22448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3216#64) (b' := sp + 3344#64) (n := 128) (k := (22320 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 3344#64) (b' := sp + 4432#64) (n := 1088) (k := (21232 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4432#64) (b' := sp + 22912#64) (n := 18480) (k := (2752 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22912#64) (b' := sp + 23936#64) (n := 1024) (k := (1728 : Nat)) rfl (by bv_omega) (by decide)]

theorem seg1a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64) (ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A)
    (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sp := s0.sp - 25824#64
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 232#64) s0
      (stackAt s0.sp 26960 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x20 = dkA + 384#64 ∧
        sf.readReg64 .x23 = dkA ∧
        sf.readReg64 .x24 = dkA + 384#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        (Pf ⊢ Seg1aSpatial s0 ret dkA ct1A ct2A ct1 ct2 F)) := by
  intro sp
  rw [stackAt_26960_eq s0.sp sp rfl]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg1_save_frame hb hbase s0 ret dkA ct1A ct2A
        (stackAt sp 1136 ∗ memRegion sp 25664 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
        hpc hrun hsp0 hx0 hx1 hx2 hx3) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx3_1, hfp_1, hx9_1, hP1⟩
  have hsplit_probe : memRegion sp 25664 =
      memRegion sp 1088 ∗ memRegion (sp + 1088#64) (4096 * 6) := by
    rw [show 4096 * 6 = (24576 : Nat) from rfl,
      memRegion_split' (b := sp) (b' := sp + 1088#64) (n := 1088) (k := (24576 : Nat)) rfl rfl (by decide)]
  have hsp1_eq : s1.sp = (sp + 1088#64) + BitVec.ofNat 64 (4096 * 6) := by
    rw [hsp1]; dsimp [sp]; bv_omega
  have hx9_1_eq : s1.readReg64 .x9 = sp + 1088#64 := by
    rw [hx9_1]; dsimp [sp]; bv_omega
  have hframe1 : P1 ⊢ memRegion (sp + 1088#64) (4096 * 6) ∗
      (SavedFrame04 s0.sp s0 ∗ stackAt sp 1136 ∗ memRegion sp 1088 ∗
        (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F) := by
    refine Entails.trans hP1 ?_
    rw [hsplit_probe]; sep_frame
  refine SepWP.weaken_pre hframe1
    (sepWP_seq_env hcl1 hro1
      (seg1_probe_loop hb hbase (sp + 1088#64) 6 (by decide) (by decide) s1 _
        hpc1 hrun1 hsp1_eq hspA1 hx9_1_eq) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx0_2, hx1_2, hx2_2, hx3_2, hfp_2, hP2⟩
  have hsub : memRegion sp 1088 ∗ memRegion (sp + 1088#64) (4096 * 6) ⊢ memRegion sp 25664 := by
    rw [← hsplit_probe]; exact Entails.refl _
  have hP2' : P2 ⊢
      memRegion sp 136 ∗ memRegion (sp + 136#64) 8 ∗ memRegion (sp + 200#64) 8 ∗
        memRegion (sp + 2256#64) 960 ∗ (ct1A ↦ₛ ct1) ∗
        (memRegion (sp + 144#64) 56 ∗ memRegion (sp + 208#64) 1632 ∗
          memRegion (sp + 1840#64) 8 ∗ memRegion (sp + 1848#64) 8 ∗
          memRegion (sp + 1856#64) 8 ∗ memRegion (sp + 1864#64) 392 ∗
          memRegion (sp + 3216#64) 128 ∗ memRegion (sp + 3344#64) 1088 ∗
          memRegion (sp + 4432#64) 18480 ∗ memRegion (sp + 22912#64) 1024 ∗
          memRegion (sp + 23936#64) 1728 ∗ SavedFrame04 s0.sp s0 ∗ stackAt sp 1136 ∗
          (ct2A ↦ₛ ct2) ∗ F) := by
    refine Entails.trans hP2 (entails_sub hsub (by sep_frame) ?_)
    rw [memRegion_25664_seg1a_split sp]; sep_frame
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg1_alloc_copy_ct1 hb hbase s2 sp (s0.sp - 96#64) ret dkA ct1A ct2A ct1 _
        hpc2 hrun2 hsp2 hspA2 (hx0_2.trans hx0_1) (hx1_2.trans hx1_1)
        (hx2_2.trans hx2_1) (hx3_2.trans hx3_1) (hfp_2.trans hfp_1) hct1 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3, hP3⟩
  have hP3' : P3 ⊢ memRegion (sp + 3216#64) 128 ∗ (ct2A ↦ₛ ct2) ∗
      ((sp + 2256#64) ↦ₛ ct1) ∗ memRegion (sp + 3344#64) 1088 ∗
      (memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
        (ct1A ↦ₛ ct1) ∗ memRegion (sp + 144#64) 56 ∗
        memRegion (sp + 208#64) 1632 ∗ memRegion (sp + 1840#64) 8 ∗ memRegion (sp + 1848#64) 8 ∗
        memRegion (sp + 1856#64) 8 ∗ memRegion (sp + 1864#64) 392 ∗
        memRegion (sp + 4432#64) 18480 ∗ memRegion (sp + 22912#64) 1024 ∗
        memRegion (sp + 23936#64) 1728 ∗ SavedFrame04 s0.sp s0 ∗ stackAt sp 1136 ∗ F) :=
    Entails.trans hP3 (by sep_frame)
  refine SepWP.weaken_pre hP3'
    (sepWP_seq_env hcl3 hro3
      (seg1_copy_ct2_dup hb hbase s3 sp ct2A ct1 ct2 _
        hpc3 hrun3 hsp3 hspA3 hx21_3 hct1 hct2 hcl3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 _
    ⟨hsp4, hspA4, hfp4, hx20_4, hx22_4, hx23_4, hx24_4, hx26_4, hx28_4, hP4⟩
  have hP4' : P4 ⊢
      memRegion (sp + 1840#64) 8 ∗ memRegion (sp + 1856#64) 8 ∗
        memRegion (sp + 4432#64) 18480 ∗ memRegion (sp + 22912#64) 1024 ∗
        memRegion (sp + 23936#64) 1728 ∗
        (memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 56 ∗
          ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
          memRegion (sp + 1848#64) 8 ∗ memRegion (sp + 1864#64) 392 ∗
          ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
          SavedFrame04 s0.sp s0 ∗ stackAt sp 1136 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F) :=
    Entails.trans hP4 (by sep_frame)
  refine SepWP.weaken_pre hP4'
    (SepWP.mono
      (seg1_spills_memset hb hbase s4 sp dkA _
        hpc4 hrun4 hsp4 hspA4 (hx22_4.trans hx22_3) (hx23_4.trans hx23_3) hcl4) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx20_f, hx23_f, hx24_f, hx26_f, hx28_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    hfp_f.trans (hfp4.trans hfp3), hx20_f.trans (hx20_4.trans hx20_3),
    hx23_f, hx24_f.trans (hx24_4.trans hx24_3),
    hx26_f.trans (hx26_4.trans hx26_3), hx28_f.trans (hx28_4.trans hx28_3), ?_⟩
  dsimp only [Seg1aSpatial]
  exact Entails.trans hPf (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
