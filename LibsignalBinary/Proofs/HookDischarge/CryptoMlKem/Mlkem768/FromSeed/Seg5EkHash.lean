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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops

/-!
# `generate_keypair_compressed` (`B05`) — Segment 5b `ek[1..2]`, `SHA3-256(ek)`, & `7776`-B Stage (`+0x6338 .. +0x666c`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemPlacement mlkemCall_of_blockOk mlkemMpl
  resolve_blk02 resolve_blk28 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW keccak2_136_6_RW1Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6 (blk02_keccak2_136_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (memRegion32_cells)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 sha3_256List sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdDup_8h_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem VecRangeMem bytesToVecNat polyVecNat vecRangeBytes vecRangeBytes_length
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (
  entails_sub sepWP_elim_bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (SHatMem cbdNttPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec (
  Seg4Exit THatMem off60fc tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  orr_12_eq_add_12 ser12Prefix ser12Prefix_length step_dead_stpQ_reg)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops (
  seg5_loop2 seg5_loop3)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek (
  aMatrixMem_entails_memRegion call_bytes_memcpy call_dead_memset cells32_entails_memRegion
  eHatMem_entails_memRegion enter_mem_block extractLsb64_hi_append extractLsb64_lo_append off666c
  seg5_dead_shuffle seg5_ek_col0 sepWP_seq_cl spAligned_mod16 spAligned_of_chk
  stackAt_1136_split_1040 tHatPoly16_ser12 truncate64_append vec2_cells_eq_bytes)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [25400 → 25516, 25672 → 25808, 25964 → 26216]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local irreducible] blkLib05 dup8x16 polyVecNat ser12Prefix sha3_256List sha3_512List
  shake256List cbdNttPoly16 tHatPoly16 bytesToVecNat
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 svc_simdDup_8h_gpr

local macro "step_strQ_sp " baseOff:num total:num pcOff:num nextOff:num subOff:num offLit:num vt:term:arg : tactic => `(tactic| (
  refine Seg5Ek.step_dead_strQ_sp $baseOff $total $pcOff $nextOff $subOff $offLit $vt
    ‹_› ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) (by omega) ?_
  intro _))

local macro "step_stpQ_reg " rn:term:arg total:num pcOff:num nextOff:num off:num vt1:term:arg vt2:term:arg : tactic => `(tactic| (
  refine step_dead_stpQ_reg $rn $total $pcOff $nextOff $off $vt1 $vt2
    (by decide) ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) ?_
  intro _))

theorem enter_mem_block_x9 {prog : Program} {target_pc : BitVec 64} (sp p v9 : BitVec 64)
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = p) (hrun : s.status = .Running) (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = v9)
    (hcont : s.status = .Running → s.sp = sp → s.spAligned = true → s.readReg64 .x9 = v9 →
      SepWP prog target_pc ((s.setPC p).setMem s.mem) P post) :
    SepWP prog target_pc s P post := by
  rw [← Seg5Ek.setPC_setMem_self hpc]
  exact hcont hrun hsp hspA hx9

theorem poly3_eq_pointsToBytes (ptr : BitVec 64) (f0 f1 f2 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 =
      (ptr ↦ₛ (vecRangeBytes 32 f0 ++ vecRangeBytes 32 f1 ++ vecRangeBytes 32 f2)) := by
  have h0 := vecRangeMem_eq_pointsToBytes 32 ptr f0
  have h1 := vecRangeMem_eq_pointsToBytes 32 (ptr + 512#64) f1
  have h2 := vecRangeMem_eq_pointsToBytes 32 (ptr + 1024#64) f2
  change VecRangeMem 32 ptr f0 ∗ VecRangeMem 32 (ptr + 512#64) f1 ∗ VecRangeMem 32 (ptr + 1024#64) f2 = _
  rw [h0, h1, h2, List.append_assoc, pointsToBytes_append, vecRangeBytes_length,
      pointsToBytes_append, vecRangeBytes_length,
      show ptr + BitVec.ofNat 64 (16 * 32) = ptr + 512#64 by bv_omega,
      show (ptr + 512#64) + BitVec.ofNat 64 (16 * 32) = ptr + 1024#64 by bv_omega]

theorem seg5_ek_col1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v : BitVec 64) (p1 : Poly16)
    (hbnd1 : PolyBounded16 3328 p1) (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 25400) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = sp + 27840#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 25724) s
      (PolyMem (sp + 2720#64) (polyVecNat p1) ∗
        memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10368#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x20 = sp + 27840#64 ∧
        (Pf ⊢ PolyMem (sp + 2720#64) (polyVecNat p1) ∗
          ((sp + 10368#64) ↦ₛ ser12Prefix p1 16) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
          memRegion (sp + 29024#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hmod : sp.toNat % 16 = 0 := spAligned_mod16 hsp hspA
  have horr : (sp + 27840#64) ||| 12#64 = sp + 27852#64 := orr_12_eq_add_12 hmod 27840 (by decide)
  refine SepWP.weaken_pre (show PolyMem (sp + 2720#64) (polyVecNat p1) ∗
        memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        (PolyMem (sp + 2720#64) (polyVecNat p1) ∗ _) by sep_frame) ?_
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 25520) hcl ?_
  wp_steps 6
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 25424)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk) ?_
  intro hrun0 hsp0 hspA0
  step_strQ_sp 27840 384 25424 25428 368 28208 1#5; step_strQ_sp 27840 384 25428 25432 352 28192 1#5
  step_strQ_sp 27840 384 25432 25436 336 28176 1#5; step_strQ_sp 27840 384 25436 25440 320 28160 1#5
  step_strQ_sp 27840 384 25440 25444 304 28144 1#5; step_strQ_sp 27840 384 25444 25448 288 28128 1#5
  step_strQ_sp 27840 384 25448 25452 272 28112 1#5; step_strQ_sp 27840 384 25452 25456 256 28096 1#5
  step_strQ_sp 27840 384 25456 25460 240 28080 1#5; step_strQ_sp 27840 384 25460 25464 224 28064 1#5
  step_strQ_sp 27840 384 25464 25468 208 28048 1#5; step_strQ_sp 27840 384 25468 25472 192 28032 1#5
  step_strQ_sp 27840 384 25472 25476 176 28016 1#5; step_strQ_sp 27840 384 25476 25480 160 28000 1#5
  step_strQ_sp 27840 384 25480 25484 144 27984 1#5; step_strQ_sp 27840 384 25484 25488 128 27968 1#5
  step_strQ_sp 27840 384 25488 25492 112 27952 1#5; step_strQ_sp 27840 384 25492 25496 96 27936 1#5
  step_strQ_sp 27840 384 25496 25500 80 27920 1#5; step_strQ_sp 27840 384 25500 25504 64 27904 1#5
  step_strQ_sp 27840 384 25504 25508 48 27888 1#5; step_strQ_sp 27840 384 25508 25512 32 27872 1#5
  step_strQ_sp 27840 384 25512 25516 16 27856 1#5; step_strQ_sp 27840 384 25516 25520 0 27840 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        (PolyMem (sp + 2720#64) (polyVecNat p1) ∗
          memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10368#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 2720#64) (polyVecNat p1) ∗ memRegion (sp + 27840#64) 384 ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10368#64) 384 ∗ Rest) by
    sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop2 hb (sp + 2720#64) (sp + 27840#64) p1 hbnd1 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hx19_1 : s1.readReg64 .x19 = x19v := by simpa [hx19] using hlp1.2.2.2.1
  have hx20_1 : s1.readReg64 .x20 = sp + 27840#64 := by simpa [hx20] using hlp1.2.2.2.2.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 2720#64) (polyVecNat p1) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10368#64) 384 ∗ Rest) ⊢
      memRegion (sp + 29024#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 10368#64) 384 ∗ PolyMem (sp + 2720#64) (polyVecNat p1) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 6
  refine call_bytes_memcpy (dst := sp + 29024#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 29024#64) ↦ₛ ser12Prefix p1 16) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 10368#64) 384 ∗ PolyMem (sp + 2720#64) (polyVecNat p1) ∗ Rest) ⊢
      memRegion (sp + 10368#64) 384 ∗ ((sp + 29024#64) ↦ₛ ser12Prefix p1 16) ∗
        (((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗ PolyMem (sp + 2720#64) (polyVecNat p1) ∗ Rest) by
    sep_frame) ?_
  wp_steps 7
  refine call_bytes_memcpy (dst := sp + 10368#64) (src := sp + 29024#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm29 : ((sp + 29024#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + 29024#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 29024#64) (ser12Prefix p1 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + BitVec.ofNat 64 27840) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p1 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf,
    spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfp] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.1, hx19_1] using hlpf.2.2.2.1,
    by simpa [hlp2.2.2.2.2.1, hx20_1] using hlpf.2.2.2.2.1,
    entails_sub hm29 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

theorem seg5_ek_col2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v : BitVec 64) (p2 : Poly16)
    (hbnd2 : PolyBounded16 3328 p2) (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 25724) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = x19v)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26016) s
      (PolyMem (sp + 3232#64) (polyVecNat p2) ∗
        memRegion (sp + 27840#64) 384 ∗
        memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10752#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x20 = sp + 9984#64 ∧
        (Pf ⊢ PolyMem (sp + 3232#64) (polyVecNat p2) ∗
          ((sp + 10752#64) ↦ₛ ser12Prefix p2 16) ∗
          memRegion (sp + 27840#64) 384 ∗
          memRegion (sp + 29024#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hmod : sp.toNat % 16 = 0 := spAligned_mod16 hsp hspA
  have horr : (sp + 27840#64) ||| 12#64 = sp + 27852#64 := orr_12_eq_add_12 hmod 27840 (by decide)
  refine SepWP.weaken_pre (show PolyMem (sp + 3232#64) (polyVecNat p2) ∗
        memRegion (sp + 27840#64) 384 ∗ _ ⊢
      memRegion (sp + 27840#64) 384 ∗
        (PolyMem (sp + 3232#64) (polyVecNat p2) ∗ _) by sep_frame) ?_
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 25808) hcl ?_
  wp_steps 9
  refine enter_mem_block_x9 sp (blkPl05.base + BitVec.ofNat 64 25760) (sp + 27840#64)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk)
    (by simp [wp_norm, arm64_norm]) ?_
  intro hrun0 _ _ _
  step_stpQ_reg .x9 384 25760 25764 0 1#5 1#5; step_stpQ_reg .x9 384 25764 25768 32 1#5 1#5
  step_stpQ_reg .x9 384 25768 25772 64 1#5 1#5; step_stpQ_reg .x9 384 25772 25776 96 1#5 1#5
  step_stpQ_reg .x9 384 25776 25780 128 1#5 1#5; step_stpQ_reg .x9 384 25780 25784 160 1#5 1#5
  step_stpQ_reg .x9 384 25784 25788 192 1#5 1#5; step_stpQ_reg .x9 384 25788 25792 224 1#5 1#5
  step_stpQ_reg .x9 384 25792 25796 256 1#5 1#5; step_stpQ_reg .x9 384 25796 25800 288 1#5 1#5
  step_stpQ_reg .x9 384 25800 25804 320 1#5 1#5; step_stpQ_reg .x9 384 25804 25808 352 1#5 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 25812) hcl0 ?_
  wp_steps 1
  apply SepWP.done; · wp_norm_lhs
  · simp [hrun]
  intro hcl0'
  refine SepWP.weaken_pre (show memRegion (sp + 27840#64) 384 ∗
        (PolyMem (sp + 3232#64) (polyVecNat p2) ∗
          memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10752#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 3232#64) (polyVecNat p2) ∗ memRegion (sp + 27840#64) 384 ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10752#64) 384 ∗ Rest) by
    sep_frame) ?_
  refine sepWP_seq_cl hcl0' (seg5_loop3 hb (sp + 3232#64) (sp + 27840#64) p2 hbnd2 _ _
    (by wp_norm_lhs) (by simp [hrun])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hx19_1 : s1.readReg64 .x19 = x19v := by simpa [hx19] using hlp1.2.2.2.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 3232#64) (polyVecNat p2) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + 29024#64) 384 ∗ memRegion (sp + 10752#64) 384 ∗ Rest) ⊢
      memRegion (sp + 29024#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + 10752#64) 384 ∗ PolyMem (sp + 3232#64) (polyVecNat p2) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 6
  refine call_bytes_memcpy (dst := sp + 29024#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 29024#64) ↦ₛ ser12Prefix p2 16) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + 10752#64) 384 ∗ PolyMem (sp + 3232#64) (polyVecNat p2) ∗ Rest) ⊢
      memRegion (sp + 10752#64) 384 ∗ ((sp + 29024#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗ PolyMem (sp + 3232#64) (polyVecNat p2) ∗ Rest) by
    sep_frame) ?_
  wp_steps 7
  refine call_bytes_memcpy (dst := sp + 10752#64) (src := sp + 29024#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm29 : ((sp + 29024#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + 29024#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 29024#64) (ser12Prefix p2 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + 27840#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p2 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf,
    spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfp] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.1, hx19_1] using hlpf.2.2.2.1,
    by simpa [wp_norm, arm64_norm, hsp2] using hlpf.2.2.2.2.1,
    entails_sub hm29 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

private theorem call_blk02_keccak2 [MlKemPlacement]
    (hkeccak : MlKemBlockOk 2 keccak2_136_6_RW1Spec)
    {b target_pc retPC sp : BitVec 64} {pk : List (BitVec 8)}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mlkemMpl.base 2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hlr : s.readReg64 .lr = retPC)
    (hx0 : s.readReg64 (.gpr 0#5) = sp + 9984#64)
    (hx1 : s.readReg64 (.gpr 1#5) = sp + 29872#64)
    (hx2 : s.readReg64 (.gpr 2#5) = sp + 29024#64)
    (hpk : pk.length < 2 ^ 32)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hcont : ∀ sf : State, sf.pc = retPC → sf.status = .Running →
      sf.sp = sp ∧ sf.readReg64 .fp = s.readReg64 .fp ∧ sf.readReg64 .x20 = s.readReg64 .x20 →
      SepWP (blkPC05.rebase b (fun _ => none)) target_pc sf
        (((sp + 29872#64) ↦ₛ sha3_256List pk) ∗
          Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length ∗
          ((sp + 29024#64) ↦ₛ sha3_256List pk) ∗ ((sp + 27840#64) ↦ₛ pk) ∗
          stackAt sp 1040 ∗ Rest) post) :
    SepWP (blkPC05.rebase b (fun _ => none)) target_pc s
      (Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length ∗
        ((sp + 27840#64) ↦ₛ pk) ∗ memRegion (sp + 29872#64) 32 ∗ memRegion (sp + 29024#64) 32 ∗
        stackAt sp 1040 ∗ Rest) post := by
  rw [← hsp]
  refine SepWP.weaken_pre (by rw [hsp]; exact Entails.refl _) ?_
  wp_mlkem_call hkeccak (sp + 9984#64, sp + 27840#64, sp + 29872#64, sp + 29024#64, pk)
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  rw [hsp]
  exact SepWP.weaken_pre (by sep_frame)
    (hcont sf hpc_sf hrun_sf ⟨hsp_sf2, hcs_sf, h_1⟩)

theorem seg5_ek_hash_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp : BitVec 64) (pk2 rho : List (BitVec 8))
    (hpk2 : pk2.length = 1152) (hrho : rho.length = 32)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 26016) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = sp + 8352#64) (hx20 : s.readReg64 .x20 = sp + 9984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let pk := pk2 ++ rho
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26112) s
      (((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 9984#64) ↦ₛ pk2) ∗ memRegion (sp + 11136#64) 32 ∗
        memRegion (sp + 27840#64) 1184 ∗ memRegion (sp + 29024#64) 32 ∗
        memRegion (sp + 29872#64) 32 ∗ stackAt sp 1040 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x20 = sp + 9984#64 ∧
        (Pf ⊢ ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 9984#64) 1184 ∗
          ((sp + 27840#64) ↦ₛ pk) ∗ ((sp + 29872#64) ↦ₛ sha3_256List pk) ∗
          ((sp + 29024#64) ↦ₛ sha3_256List pk) ∗ stackAt sp 1040 ∗ Rest)) := by
  intro pk; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hpk : pk.length = 1184 := by simp [pk, hpk2, hrho]
  refine sepWP_seq_env (mid := blkPl05.base + BitVec.ofNat 64 26064)
    (post1 := fun s1 P1 => s1.sp = sp ∧ s1.readReg64 .fp = sp + 29984#64 ∧
      s1.readReg64 .x19 = 1184#64 ∧ s1.readReg64 .x20 = sp + 9984#64 ∧
      s1.readReg64 .x21 = sp + 27840#64 ∧
      P1 = (((sp + 27840#64) ↦ₛ pk) ∗ ((sp + 9984#64) ↦ₛ pk) ∗
        (((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 29024#64) 32 ∗
          memRegion (sp + 29872#64) 32 ∗ stackAt sp 1040 ∗ Rest)))
    hcl hro ?_ ?_
  · refine SepWP.weaken_pre (show ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 9984#64) ↦ₛ pk2) ∗
          memRegion (sp + 11136#64) 32 ∗ _ ⊢
        memRegion (sp + 11136#64) 32 ∗ (((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 9984#64) ↦ₛ pk2) ∗ _) by
      sep_frame) ?_
    apply memRegion32_cells (sp + 11136#64); intro c0 c1 c2 c3
    refine SepWP.weaken_pre
      (P' := ((sp + 11136#64) ↦₆₄ c0) ∗ ((sp + 11144#64) ↦₆₄ c1) ∗
        ((sp + 11152#64) ↦₆₄ c2) ∗ ((sp + 11160#64) ↦₆₄ c3) ∗
        ((sp + 8352#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
        ((sp + 8360#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
        ((sp + 8368#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
        ((sp + 8376#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
        ((sp + 9984#64) ↦ₛ pk2) ∗ memRegion (sp + 27840#64) 1184 ∗ memRegion (sp + 29024#64) 32 ∗
        memRegion (sp + 29872#64) 32 ∗ stackAt sp 1040 ∗ Rest)
      (by rw [← vec2_cells_eq_bytes (sp + 8352#64) hrho]; simp only [bitvec64_add_add_fold]; sep_frame) ?_
    wp_cut_codeLoaded
    wp_steps 12
    apply SepWP.done; · wp_norm_lhs
    · simp [hrun]
    intro hcl0
    have hcat : ((sp + 9984#64) ↦ₛ pk2) ∗ ((sp + 11136#64) ↦ₛ rho) = ((sp + 9984#64) ↦ₛ pk) := by
      dsimp only [pk]; rw [pointsToBytes_append, hpk2, show (sp + 9984#64) + BitVec.ofNat 64 1152 = sp + 11136#64 by clear * -; bv_omega]
    refine SepWP.weaken_pre (P' := memRegion (sp + 27840#64) 1184 ∗ ((sp + 9984#64) ↦ₛ pk) ∗
        (((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 29024#64) 32 ∗
          memRegion (sp + 29872#64) 32 ∗ stackAt sp 1040 ∗ Rest))
      (by
        rw [← hcat, ← vec2_cells_eq_bytes (sp + 8352#64) hrho, ← vec2_cells_eq_bytes (sp + 11136#64) hrho]
        simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]; sep_frame) ?_
    refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 9984#64) (n := 1184)
      (by wp_norm_lhs) (by simp [hrun]) (spAligned_of_chk (by simp [hsp]) hchk)
      (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs) hpk (by decide) hcl0
      fun s1 hpc1 hrun1 hlp1 _ => ?_
    exact SepWP.done hpc1 hrun1 ⟨by simpa [hsp] using hlp1.1, by simpa [hfp] using hlp1.2.2.1,
      by simpa [wp_norm, arm64_norm] using hlp1.2.2.2.1,
      by simpa [wp_norm, arm64_norm, hx20] using hlp1.2.2.2.2.1,
      by simpa [wp_norm, arm64_norm, hsp] using hlp1.2.2.2.2.2.1, rfl⟩
  · rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp1, hfp1, hx19_1, hx20_1, hx21_1, rfl⟩
    have hm99 : ((sp + 9984#64) ↦ₛ pk) ⊢ memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 10016#64) 1152 := by
      rw [← memRegion_split' (b := sp + 9984#64) (b' := sp + 10016#64) (n := 32) (k := (1152 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
      simpa [hpk] using pointsToBytes_entails_memRegion (sp + 9984#64) pk
    refine SepWP.weaken_pre (entails_sub hm99 (by sep_frame)
      (show (memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 10016#64) 1152) ∗
            (((sp + 27840#64) ↦ₛ pk) ∗ ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 29024#64) 32 ∗
              memRegion (sp + 29872#64) 32 ∗ stackAt sp 1040 ∗ Rest) ⊢
          memRegion (sp + 9984#64) 32 ∗ (memRegion (sp + 29872#64) 32 ∗
            (memRegion (sp + 10016#64) 1152 ∗ ((sp + 27840#64) ↦ₛ pk) ∗
              ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 29024#64) 32 ∗ stackAt sp 1040 ∗ Rest)) by
        sep_frame)) ?_
    apply memRegion32_cells (sp + 9984#64); intro d0 d1 d2 d3
    refine SepWP.weaken_pre
      (P' := memRegion (sp + 29872#64) 32 ∗
        (((sp + 9984#64) ↦₆₄ d0) ∗ ((sp + 9992#64) ↦₆₄ d1) ∗
          ((sp + 10000#64) ↦₆₄ d2) ∗ ((sp + 10008#64) ↦₆₄ d3) ∗
          memRegion (sp + 10016#64) 1152 ∗ ((sp + 27840#64) ↦ₛ pk) ∗
          ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 29024#64) 32 ∗ stackAt sp 1040 ∗ Rest))
      (by simp only [bitvec64_add_add_fold]; sep_frame) ?_
    apply memRegion32_cells (sp + 29872#64); intro e0 e1 e2 e3
    have hfp_al : ((sp + 29984#64 - 112#64) &&& 15#64 == 0#64) = true := by
      have h0 : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hchk
      have h1 : (sp + 29984#64 - 112#64) &&& 15#64 = 0#64 := by clear * - h0; bv_bits
      exact beq_iff_eq.mpr h1
    refine sepWP_seq_env (mid := mlkemMpl.base 2)
      (post1 := fun s2 P2 => s2.sp = sp ∧ s2.readReg64 .fp = sp + 29984#64 ∧
        s2.readReg64 .x20 = sp + 9984#64 ∧ s2.readReg64 .lr = blkPl05.base + BitVec.ofNat 64 26112 ∧
        s2.readReg64 (.gpr 0#5) = sp + 9984#64 ∧
        s2.readReg64 (.gpr 1#5) = sp + 29872#64 ∧ s2.readReg64 (.gpr 2#5) = sp + 29024#64 ∧
        P2 = (Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length ∗
          ((sp + 27840#64) ↦ₛ pk) ∗ memRegion (sp + 29872#64) 32 ∗ memRegion (sp + 29024#64) 32 ∗
          stackAt sp 1040 ∗ (memRegion (sp + 10016#64) 1152 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ Rest)))
      hcl1 hro1 ?_ ?_
    · wp_steps 12
      have hsl : ((sp + 9984#64) ↦₆₄ (sp + 27840#64)) ∗ ((sp + 9992#64) ↦₆₄ 1184#64) ∗
          ((sp + 10000#64) ↦₆₄ (sp + 27840#64)) ∗ ((sp + 10008#64) ↦₆₄ 1184#64) =
          Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length := by
        unfold Keccak2SlicesRW; rw [hpk]; simp only [bitvec64_add_add_fold]; rfl
      refine SepWP.weaken_pre
        (P' := Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length ∗
          ((sp + 27840#64) ↦ₛ pk) ∗ memRegion (sp + 29872#64) 32 ∗ memRegion (sp + 29024#64) 32 ∗
          stackAt sp 1040 ∗ (memRegion (sp + 10016#64) 1152 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ Rest))
        (by
          rw [← hsl]; simp only [bitvec64_add_add_fold]
          exact entails_sub (cells32_entails_memRegion (sp + 29872#64) _ _ _ _)
            (by sep_frame) (by sep_frame)) ?_
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
        ⟨by simp [wp_norm, arm64_norm, hsp1], by simp [wp_norm, arm64_norm, hfp1],
          by simp [wp_norm, arm64_norm, hx20_1], by wp_norm_lhs,
          by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
          by simp [wp_norm, arm64_norm], rfl⟩
    · rintro s2 _ hpc2 hrun2 hcl2 hro2 ⟨hsp2, hfp2, hx20_2, hlr2, hx0_2, hx1_2, hx2_2, rfl⟩
      refine call_blk02_keccak2 blk02_keccak2_136_6_RW1_ok hpc2 hrun2 hsp2
        (spAligned_of_chk hsp2 hchk) hlr2 hx0_2 hx1_2 hx2_2 (by omega) hcl2 hro2
        fun sf hpcsf hrunsf ⟨hsp_sf, hfp_sf, hx20_sf⟩ => ?_
      have hsl_m : Keccak2SlicesRW (sp + 9984#64) (sp + 27840#64) (sp + 27840#64) pk.length pk.length ∗
          memRegion (sp + 10016#64) 1152 ⊢ memRegion (sp + 9984#64) 1184 := by
        unfold Keccak2SlicesRW
        rw [memRegion_split' (b := sp + 9984#64) (b' := sp + 10016#64) (n := 32) (k := (1152 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
        simp only [bitvec64_add_add_fold]
        exact entails_sub (cells32_entails_memRegion (sp + 9984#64) _ _ _ _) (by sep_frame) (by sep_frame)
      exact SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
        hfp_sf.trans hfp2, hx20_sf.trans hx20_2,
        entails_sub hsl_m (by sep_frame) (by sep_frame)⟩

theorem seg5_ek_hash_b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp seedA : BitVec 64) (seed rho sigma hPk : List (BitVec 8))
    (hseed : seed.length = 64) (hrho : rho.length = 32) (hhPk : hPk.length = 32)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 26112) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx20 : s.readReg64 .x20 = sp + 9984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let z := seed.drop 32
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off666c) s
      (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗
        THatMem sp rho sigma ∗ memRegion (sp + 3744#64) 4608 ∗
        ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 8384#64) 32 ∗
        SHatMem sp sigma ∗ memRegion (sp + 9952#64) 32 ∗
        memRegion (sp + 17376#64) 7776 ∗ memRegion (sp + 27072#64) 768 ∗
        memRegion (sp + 29024#64) 64 ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = sp + 17376#64 ∧ sf.readReg64 .x20 = sp + 9984#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗
          memRegion (sp + 2208#64) 6144 ∗
          ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 8384#64) ↦ₛ hPk) ∗
          SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
          PolyMem (sp + 17376#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗
          PolyMem (sp + 17888#64) (polyVecNat (tHatPoly16 rho sigma 1)) ∗
          PolyMem (sp + 18400#64) (polyVecNat (tHatPoly16 rho sigma 2)) ∗
          memRegion (sp + 18912#64) 6240 ∗ memRegion (sp + 27072#64) 768 ∗
          ((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ∗
          ((sp + 29872#64) ↦ₛ hPk) ∗ Rest)) := by
  intro z; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hz : z.length = 32 := by simp [z, hseed]
  have ht32 : (seed.take 32).length = 32 := by simp [hseed]
  have hseed_sp : (seedA ↦ₛ seed) = ((seedA ↦ₛ seed.take 32) ∗ ((seedA + 32#64) ↦ₛ z)) := by
    conv_lhs => rw [← List.take_append_drop 32 seed]
    rw [pointsToBytes_append, ht32]
  have hfp_al : ((sp + 29984#64 - 112#64) &&& 15#64 == 0#64) = true := by
    have h0 : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hchk
    have h1 : (sp + 29984#64 - 112#64) &&& 15#64 = 0#64 := by clear * - h0; bv_bits
    exact beq_iff_eq.mpr h1
  refine SepWP.weaken_pre (show ((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗
        THatMem sp rho sigma ∗ memRegion (sp + 3744#64) 4608 ∗
        ((sp + 8352#64) ↦ₛ rho) ∗ memRegion (sp + 8384#64) 32 ∗
        SHatMem sp sigma ∗ memRegion (sp + 9952#64) 32 ∗ _ ⊢
      memRegion (sp + 8384#64) 32 ∗ (memRegion (sp + 9952#64) 32 ∗
        (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ THatMem sp rho sigma ∗
          memRegion (sp + 3744#64) 4608 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ SHatMem sp sigma ∗ _)) by
    sep_frame) ?_
  apply memRegion32_cells (sp + 8384#64); intro a0 a1 a2 a3
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 9952#64) 32 ∗
      (((sp + 8384#64) ↦₆₄ a0) ∗ ((sp + 8392#64) ↦₆₄ a1) ∗
        ((sp + 8400#64) ↦₆₄ a2) ∗ ((sp + 8408#64) ↦₆₄ a3) ∗
        ((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ THatMem sp rho sigma ∗
        memRegion (sp + 3744#64) 4608 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ SHatMem sp sigma ∗
        memRegion (sp + 17376#64) 7776 ∗ memRegion (sp + 27072#64) 768 ∗
        memRegion (sp + 29024#64) 64 ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ Rest))
    (by simp only [bitvec64_add_add_fold]; sep_frame) ?_
  apply memRegion32_cells (sp + 9952#64); intro b0 b1 b2 b3
  refine SepWP.weaken_pre
    (P' := ((sp + 32#64) ↦₆₄ seedA) ∗
      ((sp + 29872#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 0 64) ∗
      ((sp + 29880#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 64 64) ∗
      ((sp + 29888#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 0 64) ∗
      ((sp + 29896#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 64 64) ∗
      ((seedA + 32#64) ↦₆₄ (bytesToVecNat z 0).extractLsb' 0 64) ∗
      ((seedA + 40#64) ↦₆₄ (bytesToVecNat z 0).extractLsb' 64 64) ∗
      ((seedA + 48#64) ↦₆₄ (bytesToVecNat z 1).extractLsb' 0 64) ∗
      ((seedA + 56#64) ↦₆₄ (bytesToVecNat z 1).extractLsb' 64 64) ∗
      ((sp + 8384#64) ↦₆₄ a0) ∗ ((sp + 8392#64) ↦₆₄ a1) ∗
      ((sp + 8400#64) ↦₆₄ a2) ∗ ((sp + 8408#64) ↦₆₄ a3) ∗
      ((sp + 9952#64) ↦₆₄ b0) ∗ ((sp + 9960#64) ↦₆₄ b1) ∗
      ((sp + 9968#64) ↦₆₄ b2) ∗ ((sp + 9976#64) ↦₆₄ b3) ∗
      (seedA ↦ₛ seed.take 32) ∗ THatMem sp rho sigma ∗ memRegion (sp + 3744#64) 4608 ∗
      ((sp + 8352#64) ↦ₛ rho) ∗ SHatMem sp sigma ∗ memRegion (sp + 17376#64) 7776 ∗
      memRegion (sp + 27072#64) 768 ∗ memRegion (sp + 29024#64) 64 ∗ Rest)
    (by
      rw [hseed_sp, ← vec2_cells_eq_bytes (sp + 29872#64) hhPk, ← vec2_cells_eq_bytes (seedA + 32#64) hz]
      simp only [bitvec64_add_add_fold]; sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 14
  apply SepWP.done; · wp_norm_lhs
  · simp [hrun]
  intro hcl0
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 3744#64) 4608 ∗
      (memRegion (sp + 17376#64) 7776 ∗ THatMem sp rho sigma ∗ ((sp + 8352#64) ↦ₛ rho) ∗
        ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
        ((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 27072#64) 768 ∗
        memRegion (sp + 29024#64) 64 ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ Rest))
    (by
      rw [hseed_sp, ← vec2_cells_eq_bytes (sp + 29872#64) hhPk, ← vec2_cells_eq_bytes (seedA + 32#64) hz,
          ← vec2_cells_eq_bytes (sp + 8384#64) hhPk, ← vec2_cells_eq_bytes (sp + 9952#64) hz]
      simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]; sep_frame) ?_
  refine sepWP_elim_bytes 4608 (by decide) fun mid4608 hmid => ?_
  let fT0 := polyVecNat (tHatPoly16 rho sigma 0)
  let fT1 := polyVecNat (tHatPoly16 rho sigma 1)
  let fT2 := polyVecNat (tHatPoly16 rho sigma 2)
  let fS0 := polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [0#8])))
  let fS1 := polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [1#8])))
  let fS2 := polyVecNat (cbdNttPoly16 (shake256List 128 (sigma ++ [2#8])))
  let tBytes := vecRangeBytes 32 fT0 ++ vecRangeBytes 32 fT1 ++ vecRangeBytes 32 fT2
  let sBytes := vecRangeBytes 32 fS0 ++ vecRangeBytes 32 fS1 ++ vecRangeBytes 32 fS2
  have htLen : tBytes.length = 1536 := by simp [tBytes, vecRangeBytes_length]
  have hsLen : sBytes.length = 1536 := by simp [sBytes, vecRangeBytes_length]
  have hTHat : THatMem sp rho sigma = ((sp + 2208#64) ↦ₛ tBytes) := by
    unfold THatMem
    have h := poly3_eq_pointsToBytes (sp + 2208#64) fT0 fT1 fT2
    rw [show (sp + 2208#64) + 512#64 = sp + 2720#64 by clear * -; bv_omega,
        show (sp + 2208#64) + 1024#64 = sp + 3232#64 by clear * -; bv_omega] at h
    exact h
  have hSHat : SHatMem sp sigma = ((sp + 8416#64) ↦ₛ sBytes) := by
    unfold SHatMem
    have h := poly3_eq_pointsToBytes (sp + 8416#64) fS0 fS1 fS2
    rw [show (sp + 8416#64) + 512#64 = sp + 8928#64 by clear * -; bv_omega,
        show (sp + 8416#64) + 1024#64 = sp + 9440#64 by clear * -; bv_omega] at h
    exact h
  let tail6240 := mid4608 ++ (rho ++ (hPk ++ (sBytes ++ z)))
  have htailLen : tail6240.length = 6240 := by simp [tail6240, hmid, hrho, hhPk, hsLen, hz]
  let big7776 := tBytes ++ tail6240
  have hbigLen : big7776.length = 7776 := by simp [big7776, htLen, htailLen]
  have hsrcCat : ((sp + 2208#64) ↦ₛ big7776) =
      (THatMem sp rho sigma ∗ ((sp + 3744#64) ↦ₛ mid4608) ∗ ((sp + 8352#64) ↦ₛ rho) ∗
        ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z)) := by
    dsimp only [big7776, tail6240]
    rw [pointsToBytes_append (xs := tBytes), htLen,
        show (sp + 2208#64) + BitVec.ofNat 64 1536 = sp + 3744#64 by clear * -; bv_omega,
        pointsToBytes_append (xs := mid4608), hmid,
        show (sp + 3744#64) + BitVec.ofNat 64 4608 = sp + 8352#64 by clear * -; bv_omega,
        pointsToBytes_append (xs := rho), hrho,
        show (sp + 8352#64) + BitVec.ofNat 64 32 = sp + 8384#64 by clear * -; bv_omega,
        pointsToBytes_append (xs := hPk), hhPk,
        show (sp + 8384#64) + BitVec.ofNat 64 32 = sp + 8416#64 by clear * -; bv_omega,
        pointsToBytes_append (xs := sBytes), hsLen,
        show (sp + 8416#64) + BitVec.ofNat 64 1536 = sp + 9952#64 by clear * -; bv_omega,
        hTHat, hSHat]
  refine SepWP.weaken_pre (P' := memRegion (sp + 17376#64) 7776 ∗ ((sp + 2208#64) ↦ₛ big7776) ∗
      (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 27072#64) 768 ∗
        memRegion (sp + 29024#64) 64 ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ Rest))
    (by rw [hsrcCat]; sep_frame) ?_
  refine call_bytes_memcpy (dst := sp + 17376#64) (src := sp + 2208#64) (n := 7776)
    (by wp_norm_lhs) (by simp [hrun]) (spAligned_of_chk (by simp [hsp]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs) hbigLen (by decide) hcl0
    fun s1 hpc1 hrun1 hlp1 hcl1 => ?_
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hfp1 : s1.readReg64 .fp = sp + 29984#64 := by simpa [hfp] using hlp1.2.2.1
  have hx19_1 : s1.readReg64 .x19 = sp + 17376#64 := by simpa [wp_norm, arm64_norm, hsp] using hlp1.2.2.2.1
  have hx20_1 : s1.readReg64 .x20 = sp + 9984#64 := by simpa [wp_norm, arm64_norm, hx20] using hlp1.2.2.2.2.1
  have hdstSplit : ((sp + 17376#64) ↦ₛ big7776) ⊢
      PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗
      PolyMem (sp + 18400#64) fT2 ∗ memRegion (sp + 18912#64) 6240 := by
    dsimp only [big7776]
    rw [pointsToBytes_append, htLen, show (sp + 17376#64) + BitVec.ofNat 64 1536 = sp + 18912#64 by clear * -; bv_omega]
    have hd3 : ((sp + 17376#64) ↦ₛ tBytes) =
        (PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗ PolyMem (sp + 18400#64) fT2) := by
      have h := poly3_eq_pointsToBytes (sp + 17376#64) fT0 fT1 fT2
      rw [show (sp + 17376#64) + 512#64 = sp + 17888#64 by clear * -; bv_omega,
          show (sp + 17376#64) + 1024#64 = sp + 18400#64 by clear * -; bv_omega] at h
      exact h.symm
    rw [hd3]
    have hm6240 : ((sp + 18912#64) ↦ₛ tail6240) ⊢ memRegion (sp + 18912#64) 6240 := by
      simpa [htailLen] using pointsToBytes_entails_memRegion (sp + 18912#64) tail6240
    exact entails_sub hm6240 (by sep_frame) (by sep_frame)
  have hsrc6144 : THatMem sp rho sigma ∗ ((sp + 3744#64) ↦ₛ mid4608) ⊢ memRegion (sp + 2208#64) 6144 := by
    rw [hTHat, memRegion_split' (b := sp + 2208#64) (b' := sp + 3744#64) (n := 1536) (k := (4608 : Nat))
      rfl (by clear * -; bv_omega) (by decide)]
    have hmT : ((sp + 2208#64) ↦ₛ tBytes) ⊢ memRegion (sp + 2208#64) 1536 := by
      simpa [htLen] using pointsToBytes_entails_memRegion (sp + 2208#64) tBytes
    have hmM : ((sp + 3744#64) ↦ₛ mid4608) ⊢ memRegion (sp + 3744#64) 4608 := by
      simpa [hmid] using pointsToBytes_entails_memRegion (sp + 3744#64) mid4608
    exact entails_sub hmT (by sep_frame) (entails_sub hmM (by sep_frame) (by sep_frame))
  have h29024 : memRegion (sp + 29024#64) 64 = memRegion (sp + 29024#64) 32 ∗ memRegion (sp + 29056#64) 32 :=
    memRegion_split' (b := sp + 29024#64) (b' := sp + 29056#64) (n := 32) (k := (32 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 29024#64) 32 ∗ (memRegion (sp + 29056#64) 32 ∗
      (((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ memRegion (sp + 27072#64) 768 ∗
        (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 2208#64) 6144 ∗
          ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
          PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗
          PolyMem (sp + 18400#64) fT2 ∗ memRegion (sp + 18912#64) 6240 ∗ Rest))))
    (by
      rw [hsrcCat, h29024]
      exact entails_sub hdstSplit (by sep_frame) (entails_sub hsrc6144 (by sep_frame) (by sep_frame))) ?_
  apply memRegion32_cells (sp + 29024#64); intro c0 c1 c2 c3
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 29056#64) 32 ∗
      (((sp + 29024#64) ↦₆₄ c0) ∗ ((sp + 29032#64) ↦₆₄ c1) ∗
        ((sp + 29040#64) ↦₆₄ c2) ∗ ((sp + 29048#64) ↦₆₄ c3) ∗
        ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 29872#64) ↦ₛ hPk) ∗ memRegion (sp + 27072#64) 768 ∗
        (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 2208#64) 6144 ∗
          ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
          PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗
          PolyMem (sp + 18400#64) fT2 ∗ memRegion (sp + 18912#64) 6240 ∗ Rest)))
    (by simp only [bitvec64_add_add_fold]; sep_frame) ?_
  apply memRegion32_cells (sp + 29056#64); intro d0 d1 d2 d3
  refine SepWP.weaken_pre
    (P' := ((sp + 8352#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
      ((sp + 8360#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
      ((sp + 8368#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
      ((sp + 8376#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
      ((sp + 29872#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 0 64) ∗
      ((sp + 29880#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 64 64) ∗
      ((sp + 29888#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 0 64) ∗
      ((sp + 29896#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 64 64) ∗
      ((sp + 29024#64) ↦₆₄ c0) ∗ ((sp + 29032#64) ↦₆₄ c1) ∗
      ((sp + 29040#64) ↦₆₄ c2) ∗ ((sp + 29048#64) ↦₆₄ c3) ∗
      ((sp + 29056#64) ↦₆₄ d0) ∗ ((sp + 29064#64) ↦₆₄ d1) ∗
      ((sp + 29072#64) ↦₆₄ d2) ∗ ((sp + 29080#64) ↦₆₄ d3) ∗
      memRegion (sp + 27072#64) 768 ∗
      (((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 2208#64) 6144 ∗
        ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
        PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗
        PolyMem (sp + 18400#64) fT2 ∗ memRegion (sp + 18912#64) 6240 ∗ Rest))
    (by
      rw [← vec2_cells_eq_bytes (sp + 8352#64) hrho, ← vec2_cells_eq_bytes (sp + 29872#64) hhPk]
      simp only [bitvec64_add_add_fold]; sep_frame) ?_
  wp_cut_codeLoaded
  wp_steps 13
  apply SepWP.done; · wp_norm_lhs
  · simp [hrun1]
  intro hcl2
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 27072#64) 768 ∗
      (((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ∗
        ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 29872#64) ↦ₛ hPk) ∗
        ((sp + 32#64) ↦₆₄ seedA) ∗ (seedA ↦ₛ seed) ∗ memRegion (sp + 2208#64) 6144 ∗
        ((sp + 8384#64) ↦ₛ hPk) ∗ SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
        PolyMem (sp + 17376#64) fT0 ∗ PolyMem (sp + 17888#64) fT1 ∗
        PolyMem (sp + 18400#64) fT2 ∗ memRegion (sp + 18912#64) 6240 ∗ Rest))
    (by
      rw [← vec2_cells_eq_bytes (sp + 8352#64) hrho, ← vec2_cells_eq_bytes (sp + 29872#64) hhPk,
          ← vec2_cells_eq_bytes (sp + 29024#64) hrho, ← vec2_cells_eq_bytes (sp + 29056#64) hhPk]
      simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]; sep_frame) ?_
  refine call_dead_memset (dst := sp + 27072#64) (offD := 0) (n := 768)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by clear * -; bv_omega) (by decide) (by decide) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf hclsf => ?_
  have hsp_sf : sf.sp = sp := by simpa [hsp1] using hlpf.1
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [hfp1] using hlpf.2.2.1,
    by simpa [hx19_1] using hlpf.2.2.2.1,
    by simpa [hx20_1] using hlpf.2.2.2.2.1,
    hclsf, by dsimp only [fT0, fT1, fT2]; sep_frame⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash
