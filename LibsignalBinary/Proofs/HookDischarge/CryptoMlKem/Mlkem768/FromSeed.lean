/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05
meta import ProofLib.GenPlacedFetches

/-!
# `B10` → `B05`: `<KeyPairCompressedBytes>::from_seed` (`Mlkem768.FromSeed`)

Proves `B10` (`24` words, `2,448` B local frame + `B05` `31,216` B = `33,664` B tight stack)
partial (`MlKemBlockSafeOk 10`) and conditional total (`MlKemBlockOk 10`) contracts plus
caller-struct projections at `(stk : Nat)` (`33664 ≤ stk`), `65536`, `extHookStack`, and
`mlkem768Incremental`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement mlkemCall_of_blockOk
  mlkemCaller_ok mlkemMpl mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok
  resolve_blk05 resolve_blk28 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockOk_withNonSyscallPreserved mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768FromSeedTerminates mlkem768Incremental mlkem768KeyPairWith sampleNtt toByteVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame10 blk10_code_eq blk10_tree_size blkLib10 blkPC10 blkPl10 blkPlaceable10 blkTree10
  cell_entails_memRegion8 mlkem768Incremental_fromSeed_dk_toList mlkem768KeyPairWith_length
  mlkemFromSeedCoreSpec mlkemFromSeedCore_simulates_proj mlkemFromSeedProjSpec
  mlkemFromSeedRawSpec mlkemFromSeedTermCoreSpec mlkemFromSeedTermCore_simulates_proj
  mlkemFromSeedTermRawSpec mlkemGenKeypairRawSpec mlkemGenKeypairTermRawSpec
  safe_subroutine_ok_of_simulates savedFrame10_entails_memRegion48 sepWP_seq_env
  toByteVec_64_terminates withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub sepWP_elim_cell8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Core05 (
  blk05_generate_keypair_raw_ok blk05_generate_keypair_raw_safe_ok)

private theorem blk10_hP [MlKemPlacement] :
    blkPC10 = (mlkemMultiLib.blockLib 10).program blkPl10 := rfl

section
set_option linter.literalFetch false
gen_placed_fetches blkPC10 blkLib10 blkTree10 blk10_code_eq blk10_tree_size
  via_placement blkPl10 blkPlaceable10 [0 → 92]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl10_ρ [MlKemPlacement] (sym : String) :
    blkPl10.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib10

/-! ## 1. Stack Layout, Callee-Saved Preservation, & `SafeSepWP` Call Helper -/

private def UnspilledSaved10 (s0 s : State) : Prop :=
  s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem unspilledSaved10_of_cs {s0 s1 s2 : State}
    (h01 : UnspilledSaved10 s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    UnspilledSaved10 s0 s2 := by
  rcases h01 with ⟨h21, h22, h23, h24, h25, h26, h27, hv⟩
  rcases h12 with ⟨_, _, g21, g22, g23, g24, g25, g26, g27, _, _, gv⟩
  exact ⟨g21.trans h21, g22.trans h22, g23.trans h23, g24.trans h24,
    g25.trans h25, g26.trans h26, g27.trans h27, gv.trans hv⟩

private theorem stackAt33664_split (sp0 : BitVec 64) :
    stackAt sp0 33664 =
      stackAt (sp0 - 2448#64) 31216 ∗
      memRegion (sp0 - 2448#64) 2400 ∗
      memRegion (sp0 - 48#64) 48 := by
  dsimp only [stackAt]
  have hsub : sp0 - 2448#64 - 31216#64 = sp0 - 33664#64 := by bv_omega
  change memRegion (sp0 - 33664#64) 33664 =
    memRegion (sp0 - 2448#64 - 31216#64) 31216 ∗
    memRegion (sp0 - 2448#64) 2400 ∗
    memRegion (sp0 - 48#64) 48
  rw [hsub,
    memRegion_split' (b := sp0 - 33664#64) (b' := sp0 - 2448#64) (n := 31216) (k := (2448 : Nat))
      rfl (by bv_omega) (by omega),
    memRegion_split' (b := sp0 - 2448#64) (b' := sp0 - 48#64) (n := 2400) (k := 48)
      rfl (by bv_omega) (by omega)]

private theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n 0#8)
  rwa [List.length_replicate] at h

private theorem safeSepWP_seq_env {prog : Program} {mid : BitVec 64} {s : State}
    {P : SepProp} {post1 Q : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SafeSepWP prog sm Pm Q) :
    SafeSepWP prog s P Q :=
  SafeSepWP.of_sepWP (mid := mid) <|
    sepWP_seq_env hcl hro h1 fun sm Pm hpc hrun hcl' hro' hp => by
      apply SepWP.done
      · exact hpc
      · exact hrun
      · exact h2 sm Pm hpc hrun hcl' hro' hp

private theorem safeSepWP_call_steps {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (hcall : safe_subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp} {Q : State → SepProp → Prop} {ret_pc : BitVec 64}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SafeSepWP prog sf (spec.post x s sf ∗ F) Q)
    (h_panic : ∀ R sf, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ hp; exact False.elim (not_satisfies_false_sepConj hp))
    (h_exit : ∀ R code sf, sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R)) → ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ _ he; exact False.elim (not_satisfies_false_sepConj he))
    (h_oom : ∀ R sf, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R)) →
      ∃ Pf, (sf.mem ⊨ Pf ∗ R) ∧ Q sf Pf := by
      intro _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    SafeSepWP prog s P Q := by
  intro R hm
  refine Arm64.safe_reaches.call hcall x (F ∗ R) ⟨hpc, hrun, hsp_align⟩ (hpre R hm) ?_
  intro sf hsteps hout
  rcases hout with ⟨⟨hpc_sf, hsp, hrun_sf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨hst, hp⟩ | ⟨code, hst, he⟩ |
      ⟨hst, ho⟩
  · rw [← sepConj_assoc] at hpost
    exact hnext sf hsteps (hpc_sf.trans hlr) hrun_sf hsp hcs R hpost
  · exact Arm64.safe_reaches.done (h_panic R sf hst hp)
  · exact Arm64.safe_reaches.done (h_exit R code sf hst he)
  · exact Arm64.safe_reaches.done (h_oom R sf hst ho)

/-! ## 2. `B10` Pre-`B05` & Post-`B05` `SepWP` Segments -/

private theorem memRegion48_save_split (sp0 : BitVec 64) :
    memRegion (sp0 - 48#64) 48 =
      memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
      memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
      memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
  rw [memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]

private theorem blk10_pre_b05_wp [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl10 b) (hbase : blkPl10.base = b)
    (s0 : State) (seedA kpA : BitVec 64) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = seedA) (hx8 : s0.readReg64 .x8 = kpA)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) :
    SepWP (blkPC10.rebase b (fun _ => none)) (mlkemMpl.base 5) s0
      (memRegion (s0.sp - 2448#64) 2400 ∗ memRegion (s0.sp - 48#64) 48 ∗ F)
      (fun s1 P1 =>
        s1.sp = s0.sp - 2448#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .lr = b + 0x003c#64 ∧
        s1.readReg64 .x0 = seedA ∧
        s1.readReg64 .x1 = s0.sp - 2448#64 ∧
        s1.readReg64 .x20 = kpA ∧
        UnspilledSaved10 s0 s1 ∧
        (P1 ⊢ memRegion (s0.sp - 2448#64) 2400 ∗ SavedFrame10 s0.sp s0 ∗ F)) := by
  subst hbase
  have hsp1_chk : ((s0.sp - 2448#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub s0.sp 2448#64 hsp0 (by decide)
  rw [memRegion48_save_split s0.sp,
    memRegion_split' (b := s0.sp - 2448#64) (b' := s0.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 2448#64)); intro c0
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 48#64)); intro cfp
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 40#64)); intro clr
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 32#64)); intro c28
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 16#64)); intro c20
  sep_frame_apply (sepWP_elim_cell8 (a := s0.sp - 8#64)); intro c19
  wp_cut_codeLoaded
  wp_steps 12
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun]
  intro hcl_pre
  have hfold2400 : ((s0.sp - 2448#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 2440#64) 2392 ⊢
      memRegion (s0.sp - 2448#64) 2400 := by
    rw [memRegion_split' (b := s0.sp - 2448#64) (b' := s0.sp - 2440#64) (n := 8) (k := (2392 : Nat))
      rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (cell_entails_memRegion8 _ _)
  refine SepWP.weaken_pre (entails_sub hfold2400 (by sep_frame) (by sep_frame)) ?_
  wp_mlkem_call blk29_memset_ok (s0.sp - 2448#64, 0#8, 2400)
  have hsp_sf_al : sf.spAligned = true := by simpa [State.spAligned, hsp_sf] using hsp1_chk
  refine SepWP.weaken_pre
    (entails_sub (replicate_entails_memRegion (s0.sp - 2448#64) 2400) (by sep_frame) (by sep_frame)) ?_
  wp_steps 3
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun_sf]
  refine ⟨by simpa using hsp_sf, hsp_sf_al, rfl, rfl, rfl, ?_,
    ⟨h_2, h_3, h_4, h_5, h_6, h_7, h_8, hvregs⟩, ?_⟩
  · simpa using h_1
  · dsimp only [SavedFrame10]
    have ha48 : s0.sp + 0xffffffffffffffd0#64 = s0.sp - 48#64 := by bv_omega
    have ha40 : s0.sp + 0xffffffffffffffd0#64 + 8#64 = s0.sp - 40#64 := by bv_omega
    have ha32 : s0.sp + 0xffffffffffffffd0#64 + 16#64 = s0.sp - 32#64 := by bv_omega
    have ha16 : s0.sp + 0xffffffffffffffd0#64 + 32#64 = s0.sp - 16#64 := by bv_omega
    have ha8  : s0.sp + 0xffffffffffffffd0#64 + 40#64 = s0.sp - 8#64 := by bv_omega
    sep_frame

private theorem blk10_ldp_epilogue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl10 b) (hbase : blkPl10.base = b)
    (s0 sm : State) (Rest : SepProp)
    (hpc : sm.pc = b + 0x0050#64) (hrun : sm.status = .Running)
    (hsp : sm.sp = s0.sp - 48#64) (hsp0 : s0.spAligned = true)
    (hus : UnspilledSaved10 s0 sm) :
    SepWP (blkPC10.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
      (SavedFrame10 s0.sp s0 ∗ Rest)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ memRegion (s0.sp - 48#64) 48 ∗ Rest)) := by
  subst hbase
  have hsp_chk : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using spAligned_sub s0.sp 48#64 hsp0 (by decide)
  rcases hus with ⟨h21, h22, h23, h24, h25, h26, h27, hvregs⟩
  dsimp only [SavedFrame10]
  wp_steps 4
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun]
  refine ⟨rfl, ⟨rfl, rfl, by simpa using h21, by simpa using h22, by simpa using h23,
    by simpa using h24, by simpa using h25, by simpa using h26, by simpa using h27,
    rfl, rfl, by simpa using hvregs⟩, ?_⟩
  exact sepConj_mono_left (savedFrame10_entails_memRegion48 s0.sp s0)

private theorem blk10_post_b05_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl10 b) (hbase : blkPl10.base = b)
    (s0 s2 : State) (seedA kpA : BitVec 64) (seed : List (BitVec 8)) (R : SepProp)
    (hseed : seed.length = 64) (hsp0 : s0.spAligned = true)
    (hpc2 : s2.pc = b + 0x003c#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2448#64)
    (hx20 : s2.readReg64 .x20 = kpA) (hus2 : UnspilledSaved10 s0 s2)
    (hcl2 : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem) :
    SepWP (blkPC10.rebase b (fun _ => none)) (s0.readReg64 .lr) s2
      (((seedA ↦ₛ seed) ∗ ((s0.sp - 2448#64) ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗
          stackAt (s0.sp - 2448#64) 31216) ∗
        (memRegion kpA 2400 ∗ SavedFrame10 s0.sp s0))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨ (mlkemFromSeedRawSpec mlkemMpl).post (seedA, seed, kpA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  subst hbase
  have hkp_len : (mlkem768KeyPairWith sampleNtt seed).length = 2400 :=
    mlkem768KeyPairWith_length sampleNtt hseed
  have hsp2_al : s2.spAligned = true := by
    rw [State.spAligned, hsp2]
    simpa [State.spAligned] using spAligned_sub s0.sp 2448#64 hsp0 (by decide)
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done
  · wp_norm_lhs
  · simp [hrun2]
  intro hcl_pre
  wp_mlkem_call blk28_memcpy_ok (kpA, s0.sp - 2448#64, mlkem768KeyPairWith sampleNtt seed)
  have hus_sf : UnspilledSaved10 s0 sf := by
    rcases hus2 with ⟨h21, h22, h23, h24, h25, h26, h27, hv2⟩
    exact ⟨h_2.trans h21, h_3.trans h22, h_4.trans h23, h_5.trans h24,
      h_6.trans h25, h_7.trans h26, h_8.trans h27, hvregs.trans hv2⟩
  refine SepWP.seq (mid := blkPl10.base + 80#64)
    (Mid := fun sm Pm => sm.sp = s0.sp - 48#64 ∧
      UnspilledSaved10 s0 sm ∧ (Pm ⊢ SavedFrame10 s0.sp s0 ∗
      (memRegion (s0.sp - 2448#64) 2400 ∗ stackAt (s0.sp - 2448#64) 31216 ∗
        (seedA ↦ₛ seed) ∗ (kpA ↦ₛ mlkem768KeyPairWith sampleNtt seed))))
    (prog := blkPC10.rebase blkPl10.base (fun _ => none)) (target := s0.readReg64 .lr) ?_ ?_
  · show SepWP _ (blkPl10.base + 80#64) sf _ _
    wp_steps 1
    apply SepWP.done
    · wp_norm_lhs
    · simp [hrun_sf]
    refine ⟨rfl, hus_sf, ?_⟩
    have hmr2400 : ((s0.sp - 2448#64) ↦ₛ mlkem768KeyPairWith sampleNtt seed) ⊢
        memRegion (s0.sp - 2448#64) 2400 := by
      have h := pointsToBytes_entails_memRegion (s0.sp - 2448#64) (mlkem768KeyPairWith sampleNtt seed)
      rwa [hkp_len] at h
    exact entails_sub hmr2400 (by sep_frame) (by sep_frame)
  · intro sm Pm hpcm hrunm ⟨hspm, husm, hPm⟩
    refine SepWP.weaken_pre hPm (SepWP.mono
      (blk10_ldp_epilogue hb rfl s0 sm _ hpcm hrunm hspm hsp0 husm)
      fun sfin Pfin _ _ ⟨hspfin, hcsfin, hPfin⟩ => ⟨fun hm => ?_, hspfin, hcsfin⟩)
    have hm1 := Satisfies.mono (sepConj_mono_left hPfin) hm
    rw [stackAt33664_split s0.sp]
    exact Satisfies.mono (by sep_frame) hm1

/-! ## 3. Block 10 (`from_seed`) Core `SafeOk` & `Ok` Theorems (`33,664` B Stack) -/

/-- `B10` (`from_seed`) unconditional partial-correctness raw contract (`33,664` B stack). -/
theorem blk10_from_seed_raw_safe_ok : MlKemBlockSafeOk 10 mlkemFromSeedRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC10 blkPl10 rfl blk10_hP fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨seedA, seed, kpA⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemFromSeedRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hseed, hro0⟩, hspat⟩ := hpre
  rw [stackAt33664_split s0.sp] at hspat
  set F0 : SepProp :=
    (seedA ↦ₛ seed) ∗ stackAt (s0.sp - 2448#64) 31216 ∗ memRegion kpA 2400
  refine ⟨memRegion (s0.sp - 2448#64) 2400 ∗ memRegion (s0.sp - 48#64) 48 ∗ F0,
    Satisfies.mono (by dsimp only [F0]; sep_frame) hspat, ?_⟩
  refine safeSepWP_seq_env hcl0 hro0
    (blk10_pre_b05_wp hb hbase s0 seedA kpA F0 hpc hrun hsp0 hx0 hx8 hcl0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hx20_1, hus1, hP1⟩
  refine SafeSepWP.weaken_pre
    (safeSepWP_call_steps
      (mlkemSafeCall_of_blockSafeOk (blkPC10.rebase b (fun _ => none))
        blk05_generate_keypair_raw_safe_ok)
      (x := (seedA, seed, s0.sp - 2448#64))
      (F := memRegion kpA 2400 ∗ SavedFrame10 s0.sp s0)
      (ret_pc := b + 0x003c#64) hpc1 hrun1 hspA1 hlr1
      (fun R1 hm1 => ?_)
      (fun s2 hsteps hpc2 hrun2 hsp2 hcs2 => by
        dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemGenKeypairRawSpec]
        rw [hsp1]
        exact SafeSepWP.ret_of_sepWP
          (spec := mlkemMultiLib.withCodeLoaded mlkemMpl (mlkemFromSeedRawSpec mlkemMpl))
          (blk10_post_b05_wp hb hbase s0 s2 seedA kpA seed R hseed hsp0
            hpc2 hrun2 (hsp2.trans hsp1)
            (hcs2.2.1.trans hx20_1)
            (unspilledSaved10_of_cs hus1 hcs2)
            (hcl1.of_keepsFrozen hsteps.keepsFrozen)))) hP1
  dsimp only [MultiPlacedLib.withCodeLoaded, mlkemGenKeypairRawSpec, F0] at hm1 ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
  refine ⟨hcl1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hx0_1, hx1_1, hseed, hro1⟩, ?_⟩
  rw [hsp1]
  exact Satisfies.mono (by sep_frame) hm1

/-- `B10` (`from_seed`) unconditional partial-correctness tight-stack contract (`33,664` B)
    lifted with `NonSyscallPreserved`. -/
theorem blk10_from_seed_safe_ok : MlKemBlockSafeOk 10 mlkemFromSeedCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved (j := 10) (spec := mlkemFromSeedRawSpec)
    blk10_from_seed_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨seedA, seed, kpA⟩ R s0 h => by
      dsimp only [mlkemFromSeedRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨⟨hx0, hx8, hseed, hro⟩, hspat⟩ := h
      refine ⟨⟨by simpa [stripS_readReg64] using hx0,
        by simpa [stripS_readReg64] using hx8, hseed, ?_⟩,
        by simpa [stripS_sp] using hspat⟩
      simpa [stripS_mem] using mlkemRoOk_stripExecOutside (mlkemKeep mpl) hro)
    (h_post := fun _mpl _x _R _s0 _sf _ h => by
      dsimp only [mlkemFromSeedRawSpec] at h ⊢
      simpa [stripS_sp] using h)

/-- `B10` (`from_seed`) conditional total-correctness raw contract (`33,664` B stack). -/
theorem blk10_from_seed_raw_ok : MlKemBlockOk 10 mlkemFromSeedTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC10 blkPl10 rfl blk10_hP fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨seedA, seed, kpA⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemFromSeedTermRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hseed, hTerm, hro0⟩, hspat⟩ := hpre
  have hMat := (toByteVec_64_terminates hseed).mp hTerm
  rw [stackAt33664_split s0.sp] at hspat
  set F0 : SepProp :=
    (seedA ↦ₛ seed) ∗ stackAt (s0.sp - 2448#64) 31216 ∗ memRegion kpA 2400
  refine ⟨memRegion (s0.sp - 2448#64) 2400 ∗ memRegion (s0.sp - 48#64) 48 ∗ F0,
    Satisfies.mono (by dsimp only [F0]; sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (blk10_pre_b05_wp hb hbase s0 seedA kpA F0 hpc hrun hsp0 hx0 hx8 hcl0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hlr1, hx0_1, hx1_1, hx20_1, hus1, hP1⟩
  refine SepWP.weaken_pre hP1 (seq_codeLoaded_lr hcl1 ?_)
  refine SepWP.call_subroutine_frame
    (mlkemCall_of_blockOk (blkPC10.rebase b (fun _ => none)) blk05_generate_keypair_raw_ok)
    (x := (seedA, seed, s0.sp - 2448#64))
    (F := memRegion kpA 2400 ∗ SavedFrame10 s0.sp s0)
    (ret_pc := b + 0x003c#64) hpc1 hrun1 hspA1 hlr1
    (fun R1 hm1 => ?_)
    (fun _ _ _ => not_satisfies_false_sepConj)
    (fun _ _ _ _ => not_satisfies_false_sepConj)
    (fun s2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [MultiPlacedLib.withCodeLoaded, mlkemGenKeypairTermRawSpec, F0] at hm1 ⊢
    rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, hseed, hMat, hro1⟩, ?_⟩
    rw [hsp1]
    exact Satisfies.mono (by sep_frame) hm1
  · apply SepWP.done
    · exact hlr1 ▸ hpc2
    · exact hrun2
    · intro hcl2
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemGenKeypairTermRawSpec]
      rw [hsp1]
      exact blk10_post_b05_wp hb hbase s0 s2 seedA kpA seed R hseed hsp0
        hpc2 hrun2 (hsp2.trans hsp1)
        (hcs2.2.1.trans hx20_1)
        (unspilledSaved10_of_cs hus1 hcs2) hcl2

attribute [local irreducible] toByteVec Mlkem768FromSeedTerminates mlkem768KeyPairWith in
/-- `B10` (`from_seed`) conditional total-correctness tight-stack contract (`33,664` B)
    lifted with `NonSyscallPreserved`. -/
theorem blk10_from_seed_ok : MlKemBlockOk 10 mlkemFromSeedTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved (j := 10) (spec := mlkemFromSeedTermRawSpec)
    blk10_from_seed_raw_ok (by decide)
    (h_pre := fun mpl ⟨seedA, seed, kpA⟩ R s0 h => by
      dsimp only [mlkemFromSeedTermRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨⟨hx0, hx8, hseed, hTerm, hro⟩, hspat⟩ := h
      refine ⟨⟨by simpa [stripS_readReg64] using hx0,
        by simpa [stripS_readReg64] using hx8, hseed, hTerm, ?_⟩,
        by simpa [stripS_sp] using hspat⟩
      simpa [stripS_mem] using mlkemRoOk_stripExecOutside (mlkemKeep mpl) hro)
    (h_post := fun _mpl _x _R _s0 _sf _ h => by
      dsimp only [mlkemFromSeedTermRawSpec] at h ⊢
      simpa [stripS_sp] using h)

/-! ## 4. Caller-Struct Projections (`33,664 ≤ stk`, `65,536`, `extHookStack`, & `mlkem768Incremental`) -/

/-- `B10` unconditional partial-correctness caller-struct projection (`33664 ≤ stk`). -/
theorem blk10_from_seed_proj_safe_ok (stk : Nat) (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec stk K seedA seed kpA))) :=
  fun [MlKemPlacement] =>
    safe_subroutine_ok_of_simulates
      ((mlkemFromSeedCore_simulates_proj hstk hstk_fit K hK seedA seed kpA mlkemMpl).withCodeLoaded
        mlkemMultiLib mlkemMpl)
      blk10_from_seed_safe_ok

/-- `B10` conditional total-correctness caller-struct projection (`33664 ≤ stk`). -/
theorem blk10_from_seed_proj_ok (stk : Nat) (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec stk K seedA seed kpA))) :=
  fun [MlKemPlacement] =>
    ((mlkemFromSeedTermCore_simulates_proj hstk hstk_fit K hK seedA seed kpA hTerm
        mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok
      blk10_from_seed_ok

/-- `B10` partial-correctness caller-struct projection at `stk = 65536`. -/
theorem blk10_from_seed_65536_proj_safe_ok (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec 65536 K seedA seed kpA))) :=
  blk10_from_seed_proj_safe_ok 65536 (by decide) (by decide) K hK seedA seed kpA

/-- `B10` conditional total-correctness caller-struct projection at `stk = 65536`. -/
theorem blk10_from_seed_65536_proj_ok (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec 65536 K seedA seed kpA))) :=
  blk10_from_seed_proj_ok 65536 (by decide) (by decide) K hK seedA seed kpA hTerm

/-- `B10` partial-correctness caller-struct projection at `extHookStack` (`33664 ≤ extHookStack`). -/
theorem blk10_from_seed_extHookStack_proj_safe_ok (hstk : 33664 ≤ extHookStack) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec extHookStack K seedA seed kpA))) :=
  blk10_from_seed_proj_safe_ok extHookStack hstk (by decide) K hK seedA seed kpA

/-- `B10` conditional total-correctness caller-struct projection at `extHookStack`. -/
theorem blk10_from_seed_extHookStack_proj_ok (hstk : 33664 ≤ extHookStack) (K : MlKem)
    (hK : ∀ s, (K.fromSeed s).2.2.toList = mlkem768KeyPairWith sampleNtt s.toList)
    {C : Type} (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64)
    (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemFromSeedProjSpec extHookStack K seedA seed kpA))) :=
  blk10_from_seed_proj_ok extHookStack hstk (by decide) K hK seedA seed kpA hTerm

/-- `B10` concrete `mlkem768Incremental` partial-correctness projection (`33664 ≤ stk`). -/
theorem blk10_from_seed_inc_proj_safe_ok (stk : Nat) (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec stk mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_proj_safe_ok stk hstk hstk_fit mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList seedA seed kpA

/-- `B10` concrete `mlkem768Incremental` conditional total-correctness projection (`33664 ≤ stk`). -/
theorem blk10_from_seed_inc_proj_ok (stk : Nat) (hstk : 33664 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec stk mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_proj_ok stk hstk hstk_fit mlkem768Incremental
    mlkem768Incremental_fromSeed_dk_toList seedA seed kpA hTerm

/-- `B10` concrete `mlkem768Incremental` partial-correctness projection at `stk = 65536`. -/
theorem blk10_from_seed_65536_inc_proj_safe_ok {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec 65536 mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_inc_proj_safe_ok 65536 (by decide) (by decide) seedA seed kpA

/-- `B10` concrete `mlkem768Incremental` conditional total-correctness projection at `stk = 65536`. -/
theorem blk10_from_seed_65536_inc_proj_ok {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec 65536 mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_inc_proj_ok 65536 (by decide) (by decide) seedA seed kpA hTerm

/-- `B10` concrete `mlkem768Incremental` partial-correctness projection at `extHookStack`. -/
theorem blk10_from_seed_extHookStack_inc_proj_safe_ok (hstk : 33664 ≤ extHookStack) {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64) :
    MlKemBlockSafeOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec extHookStack mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_inc_proj_safe_ok extHookStack hstk (by decide) seedA seed kpA

/-- `B10` concrete `mlkem768Incremental` conditional total-correctness projection at `extHookStack`. -/
theorem blk10_from_seed_extHookStack_inc_proj_ok (hstk : 33664 ≤ extHookStack) {C : Type}
    (seedA : C → BitVec 64) (seed : C → List.Vector (BitVec 8) 64) (kpA : C → BitVec 64)
    (hTerm : ∀ x, Mlkem768FromSeedTerminates (seed x)) :
    MlKemBlockOk 10 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemFromSeedProjSpec extHookStack mlkem768Incremental seedA seed kpA))) :=
  blk10_from_seed_inc_proj_ok extHookStack hstk (by decide) seedA seed kpA hTerm

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed
