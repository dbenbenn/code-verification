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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a

/-!
# `kyber_decapsulate` (`B06`) — Segment 1a (`+0x0000 .. +0x0098`)

Prologue saving `SavedFrame06 s0.sp s0` (`160` B), 8-page inductive stack probe loop
(`+0x0030 .. +0x0040`, `32768` B), local frame allocation (`sp = s0.sp - 34832#64`),
initial stack pointer spills (`ret`, `sp + 30712`, `skA + 3104`, `skA + 3136`), and
`B29` (`memset`) zeroing `[sp + 30960, sp + 32496)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8
  sepWP_seq_env
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub
  sepWP_elim_cell8
  sepWP_elim_region32
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  SavedFrame06
  blk06_code_eq
  blk06_tree_size
  blkLib06
  blkPC06
  blkPl06
  blkPlaceable06
  blkTree06
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x0000 → 0x0094]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC06

/-! ## 1. Tight-Stack Decomposition (`35968 = 1136 + 34672 + 160`) -/

theorem stackAt_35968_eq (sp0 : BitVec 64) :
    let sp := sp0 - 34832#64
    stackAt sp0 35968 =
      stackAt sp 1136 ∗ memRegion sp 34672 ∗ memRegion (sp0 - 160#64) 160 := by
  intro sp
  unfold stackAt
  have h0 : memRegion (sp0 - BitVec.ofNat 64 35968) 35968 =
      memRegion (sp0 - 35968#64) 35968 := rfl
  have hsub : sp - BitVec.ofNat 64 1136 = sp0 - 35968#64 := by
    change (sp0 - 34832#64) - 1136#64 = sp0 - 35968#64
    bv_omega
  rw [h0, hsub,
    memRegion_split' (b' := sp) (n := 1136) (k := (34832 : Nat)) rfl
      (by dsimp [sp]; bv_omega) (by decide),
    memRegion_split' (b := sp) (b' := sp0 - 160#64) (n := 34672) (k := (160 : Nat)) rfl
      (by dsimp [sp]; bv_omega) (by decide)]

/-! ## 2. Frame Spill (`+0x0000 → +0x0030`) & 8-Page Stack Probe Loop (`+0x0030 → +0x0040`) -/

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
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (Rest : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = skA) (hx2 : s0.readReg64 .x2 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0030#64) s0
      (memRegion (s0.sp - 160#64) 160 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = s0.sp - 160#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .fp = s0.sp - 96#64 ∧
        s1.readReg64 .x0 = ret ∧
        s1.readReg64 .x1 = skA ∧
        s1.readReg64 .x2 = ctA ∧
        s1.readReg64 .x9 = s0.sp - 32928#64 ∧
        (P1 ⊢ SavedFrame06 s0.sp s0 ∗ Rest)) := by
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
      by simp,
      by simp [hx0], by simp [hx1], by simp [hx2], by simp, ?_⟩
  unfold SavedFrame06
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
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (base cur : BitVec 64) (p0 : BitVec 64) (R_inner : SepProp)
    (s : State) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 0x0030#64) (hrun : s.status = .Running)
    (hsp : s.sp = cur + 4096#64) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = base)
    (hcond : ConditionHolds .NE (subsPState64 cur base) = true)
    (hnext : ∀ s' : State,
      s'.pc = b + 0x0030#64 →
      s'.status = .Running →
      s'.sp = cur →
      s'.spAligned = true →
      s'.readReg64 .fp = s.readReg64 .fp →
      s'.readReg64 .x0 = s.readReg64 .x0 →
      s'.readReg64 .x1 = s.readReg64 .x1 →
      s'.readReg64 .x2 = s.readReg64 .x2 →
      s'.readReg64 .x9 = base →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0040#64) s'
        ((cur ↦₆₄ 0#64) ∗ R_inner) post) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0040#64) s
      ((cur ↦₆₄ p0) ∗ R_inner) post := by
  subst hbase
  have hsp_sub : s.sp - 4096#64 = cur := by rw [hsp]; bv_omega
  have hcur_A : (cur &&& 15#64 == 0#64) = true := by
    rw [← hsp_sub]; exact spAligned_sub s.sp 4096#64 hspA (by decide)
  rw [← hsp_sub]
  wp_steps 3
  rw [hsp_sub]
  refine step_bCond_taken (pc := blkPl06.base + 60#64) (dst := blkPl06.base + 48#64)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [hcond]) (by bv_omega) ?_
  exact hnext _ (by wp_norm_lhs) (by simp [hrun]) (by simp)
    (spAligned_of_chk (by simp) hcur_A)
    (by simp) (by simp) (by simp) (by simp) (by simp [hx9])

private theorem seg1_probe_loop [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b) (spBase : BitVec 64) :
    ∀ (rem : Nat), 1 ≤ rem → rem ≤ 8 →
      ∀ (s : State) (Rest : SepProp),
        s.pc = b + 0x0030#64 →
        s.status = .Running →
        s.sp = spBase + BitVec.ofNat 64 (4096 * rem) →
        s.spAligned = true →
        s.readReg64 .x9 = spBase →
        SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0040#64) s
          (memRegion spBase (4096 * rem) ∗ Rest)
          (fun sf Pf =>
            sf.sp = spBase ∧
            sf.spAligned = true ∧
            sf.readReg64 .fp = s.readReg64 .fp ∧
            sf.readReg64 .x0 = s.readReg64 .x0 ∧
            sf.readReg64 .x1 = s.readReg64 .x1 ∧
            sf.readReg64 .x2 = s.readReg64 .x2 ∧
            (Pf ⊢ memRegion spBase (4096 * rem) ∗ Rest)) := by
  subst hbase
  intro rem
  induction rem with
  | zero => intro h1; omega
  | succ m ih =>
    intro _ hm8 s Rest hpc hrun hsp hspA hx9
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
          by simp, by simp, by simp, by simp, ?_⟩
      exact entails_sub (cell_entails_memRegion8 spBase 0#64) (by sep_frame) (by sep_frame)
    · have hm_lt : m' < 7 := by omega
      let cur := spBase + BitVec.ofNat 64 (4096 * (m' + 1))
      have hsp_cur : s.sp = cur + 4096#64 := by
        rw [hsp]; dsimp [cur]; clear * -; bv_omega
      have hcur_ne : cur ≠ spBase := by
        intro heq; dsimp [cur] at heq
        rcases m' with _ | _ | _ | _ | _ | _ | _ | m7
        · exact absurd heq (by change spBase + 4096#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 8192#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 12288#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 16384#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 20480#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 24576#64 = spBase → False; bv_omega)
        · exact absurd heq (by change spBase + 28672#64 = spBase → False; bv_omega)
        · omega
      have hcond : ConditionHolds .NE (subsPState64 cur spBase) = true := by
        rw [conditionHolds_ne_subsPState64, bne_iff_ne]
        exact hcur_ne
      have hsplit_pre :
          memRegion spBase (4096 * (m' + 1 + 1)) ∗ Rest =
            (memRegion spBase (4096 * (m' + 1)) ∗ memRegion cur 8 ∗ memRegion (cur + 8#64) 4088) ∗ Rest := by
        rw [memRegion_split' (b := spBase) (b' := cur) (n := 4096 * (m' + 1)) (k := (4096 : Nat))
            (by omega) rfl (by change 4096 * (m' + 1 + 1) ≤ 18446744073709551616; omega),
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
      intro s' hpc' hrun' hsp' hspA' hfp' hx0' hx1' hx2' hx9'
      have hframe_step :
          (cur ↦₆₄ 0#64) ∗ (memRegion spBase (4096 * (m' + 1)) ∗ memRegion (cur + 8#64) 4088 ∗ Rest) ⊢
            memRegion spBase (4096 * (m' + 1)) ∗ (memRegion cur 4096 ∗ Rest) :=
        entails_sub hrest4096 (by sep_frame) (by sep_frame)
      refine SepWP.weaken_pre hframe_step ?_
      refine SepWP.mono
        (ih (by omega) (by omega) s' (memRegion cur 4096 ∗ Rest)
          hpc' hrun' hsp' hspA' hx9') ?_
      rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx0_f, hx1_f, hx2_f, hPf⟩
      refine ⟨hsp_f, hspA_f, hfp_f.trans hfp', hx0_f.trans hx0', hx1_f.trans hx1',
        hx2_f.trans hx2', Entails.trans hPf ?_⟩
      have hmerge :
          memRegion spBase (4096 * (m' + 1 + 1)) =
            memRegion spBase (4096 * (m' + 1)) ∗ memRegion cur 4096 :=
        memRegion_split' (b := spBase) (b' := cur) (n := 4096 * (m' + 1)) (k := (4096 : Nat))
          (by omega) rfl (by change 4096 * (m' + 1 + 1) ≤ 18446744073709551616; omega)
      rw [hmerge]
      sep_frame

/-! ## 3. Segment 1a Postcondition & Proof (`+0x0000 → +0x0098`) -/

@[expose] def Seg1aSpatial (s0 : State) (ret skA : BitVec 64) (F : SepProp) : SepProp :=
  let sp := s0.sp - 34832#64
  stackAt sp 1136 ∗
  SavedFrame06 s0.sp s0 ∗
  memRegion sp 128 ∗
  ((sp + 128#64) ↦₆₄ ret) ∗
  memRegion (sp + 136#64) 80 ∗
  ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
  memRegion (sp + 224#64) 1760 ∗
  ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
  memRegion (sp + 1992#64) 8 ∗
  ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
  memRegion (sp + 2008#64) 28952 ∗
  memRegion (sp + 30960#64) 1536 ∗
  memRegion (sp + 32496#64) 2176 ∗
  F

private theorem memRegion_34672_seg1a_split (sp : BitVec 64) :
    memRegion sp 34672 =
      memRegion sp 8 ∗
      memRegion (sp + 8#64) 120 ∗
      memRegion (sp + 128#64) 8 ∗
      memRegion (sp + 136#64) 80 ∗
      memRegion (sp + 216#64) 8 ∗
      memRegion (sp + 224#64) 1760 ∗
      memRegion (sp + 1984#64) 8 ∗
      memRegion (sp + 1992#64) 8 ∗
      memRegion (sp + 2000#64) 8 ∗
      memRegion (sp + 2008#64) 28952 ∗
      memRegion (sp + 30960#64) 1536 ∗
      memRegion (sp + 32496#64) 2176 := by
  rw [memRegion_split' (b' := sp + 8#64) (n := 8) (k := (34664 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 8#64) (b' := sp + 128#64) (n := 120) (k := (34544 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 128#64) (b' := sp + 136#64) (n := 8) (k := (34536 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 136#64) (b' := sp + 216#64) (n := 80) (k := (34456 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 216#64) (b' := sp + 224#64) (n := 8) (k := (34448 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 224#64) (b' := sp + 1984#64) (n := 1760) (k := (32688 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1984#64) (b' := sp + 1992#64) (n := 8) (k := (32680 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1992#64) (b' := sp + 2000#64) (n := 8) (k := (32672 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2000#64) (b' := sp + 2008#64) (n := 8) (k := (32664 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2008#64) (b' := sp + 30960#64) (n := 28952) (k := (3712 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 30960#64) (b' := sp + 32496#64) (n := 1536) (k := (2176 : Nat)) rfl (by bv_omega) (by decide)]

theorem seg1a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = skA) (hx2 : s0.readReg64 .x2 = ctA) :
    let sp := s0.sp - 34832#64
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0098#64) s0
      (stackAt s0.sp 35968 ∗ F)
      (fun s3 P3 =>
        s3.sp = sp ∧
        s3.spAligned = true ∧
        s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x19 = skA + 384#64 ∧
        s3.readReg64 .x20 = ctA ∧
        s3.readReg64 .x21 = skA ∧
        s3.readReg64 .x22 = skA + 384#64 ∧
        s3.readReg64 .x25 = sp + 28368#64 ∧
        s3.readReg64 .x26 = sp + 28632#64 ∧
        (P3 ⊢ Seg1aSpatial s0 ret skA F)) := by
  intro sp
  rw [stackAt_35968_eq s0.sp]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg1_save_frame hb hbase s0 ret skA ctA
        (stackAt sp 1136 ∗ memRegion sp 34672 ∗ F)
        hpc hrun hsp0 hx0 hx1 hx2) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx9_1, hP1⟩
  have hsplit_probe : memRegion sp 34672 =
      memRegion sp 1904 ∗ memRegion (sp + 1904#64) (4096 * 8) := by
    rw [show 4096 * 8 = (32768 : Nat) from rfl,
      memRegion_split' (b := sp) (b' := sp + 1904#64) (n := 1904) (k := (32768 : Nat)) rfl rfl (by decide)]
  have hsp1_eq : s1.sp = (sp + 1904#64) + BitVec.ofNat 64 (4096 * 8) := by
    rw [hsp1]; dsimp [sp]; bv_omega
  have hx9_1_eq : s1.readReg64 .x9 = sp + 1904#64 := by
    rw [hx9_1]; dsimp [sp]; bv_omega
  have hframe1 : P1 ⊢ memRegion (sp + 1904#64) (4096 * 8) ∗
      (SavedFrame06 s0.sp s0 ∗ stackAt sp 1136 ∗ memRegion sp 1904 ∗ F) := by
    refine Entails.trans hP1 ?_
    rw [hsplit_probe]; sep_frame
  refine SepWP.weaken_pre hframe1
    (sepWP_seq_env hcl1 hro1
      (seg1_probe_loop hb hbase (sp + 1904#64) 8 (by decide) (by decide) s1 _
        hpc1 hrun1 hsp1_eq hspA1 hx9_1_eq) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 _ ⟨hsp2, hspA2, hfp2, hx0_2, hx1_2, hx2_2, hP2⟩
  have hframe2 : P2 ⊢ memRegion sp 34672 ∗ (SavedFrame06 s0.sp s0 ∗ stackAt sp 1136 ∗ F) := by
    refine Entails.trans hP2 ?_
    rw [hsplit_probe]; sep_frame
  refine SepWP.weaken_pre hframe2 ?_
  subst hbase
  rw [memRegion_34672_seg1a_split sp]
  sep_frame_apply (sepWP_elim_cell8 (a := sp)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 128#64)); intro c128
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 216#64)); intro c216
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 1984#64)); intro c1984
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 2000#64)); intro c2000
  have hsp_sub : s2.sp - 1904#64 = sp := by rw [hsp2]; bv_omega
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by
    rw [← hsp_sub]; exact spAligned_sub s2.sp 1904#64 hspA2 (by decide)
  have hfp_s2 : s2.readReg64 .fp = s0.sp - 96#64 := by rw [hfp2, hfp1]
  have hx0_s2 : s2.readReg64 .x0 = ret := by rw [hx0_2, hx0_1]
  have hx1_s2 : s2.readReg64 .x1 = skA := by rw [hx1_2, hx1_1]
  have hx2_s2 : s2.readReg64 .x2 = ctA := by rw [hx2_2, hx2_1]
  wp_cut_codeLoaded
  wp_steps 21
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_call
  wp_call (blk29_memset_06 blkPl06.base) (sp + 30960#64, 0#8, 1536)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  dsimp only [Seg1aSpatial]
  have h128 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ⊢ memRegion sp 128 := by
    rw [memRegion_split' (b := sp) (b' := sp + 8#64) (n := 8) (k := (120 : Nat)) rfl rfl (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 sp 0#64)
  have h1536 : ((sp + 30960#64) ↦ₛ List.replicate 1536 0#8) ⊢ memRegion (sp + 30960#64) 1536 := by
    have hpb := pointsToBytes_entails_memRegion (sp + 30960#64) (List.replicate 1536 0#8)
    rwa [List.length_replicate] at hpb
  exact entails_sub h128 (by sep_frame) (entails_sub h1536 (by sep_frame) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a
