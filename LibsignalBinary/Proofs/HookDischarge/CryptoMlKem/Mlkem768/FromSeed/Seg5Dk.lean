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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash

/-!
# `generate_keypair_compressed` (`B05`) — Segment 5c Second `pk2` Serialization (`+0x666c .. +0x6a5c`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_blk28)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 byteEncode polyAdd polyNtt sampleMatrixWith sampleNtt sampleVecCbd2
  sha3_256 sha3_256List sha3_512 sha3_512List shake256List vecDotNtt zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (keccakSponge)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdDup_8h_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (SHatMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4MatVec (
  Seg4Exit THatMem off60fc tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  ser12Prefix ser12Prefix_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops (
  seg5_loop4 seg5_loop5 seg5_loop6)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek (
  aMatrixMem_entails_memRegion call_bytes_memcpy eHatMem_entails_memRegion enter_mem_block off666c
  polyMem_entails_memRegion512 seg5_dead_shuffle seg5_ek_col0 sepWP_seq_cl spAligned_of_chk
  stackAt_1136_split_1040 tHatPoly16_ser12)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash (
  seg5_ek_col1 seg5_ek_col2 seg5_ek_hash_a seg5_ek_hash_b)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [26220 → 26336, 26496 → 26676, 26832 → 27012, 27168 → 27224]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local irreducible] blkLib05 dup8x16 polyVecNat ser12Prefix sha3_256List sha3_512List
  shake256List tHatPoly16 byteEncode
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 svc_simdDup_8h_gpr

@[simp, arm64_norm, wp_norm] abbrev off6a5c : BitVec 64 := BitVec.ofNat 64 27228

local macro "step_strQ_sp " baseOff:num total:num pcOff:num nextOff:num subOff:num offLit:num vt:term:arg : tactic => `(tactic| (
  refine Seg5Ek.step_dead_strQ_sp $baseOff $total $pcOff $nextOff $subOff $offLit $vt
    ‹_› ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) (by omega) ?_
  intro _))

theorem seg5_dk_col0 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal : BitVec 64) (p0 : Poly16) (hbnd0 : PolyBounded16 3328 p0)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + off666c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 17376#64) (hx20 : s.readReg64 .x20 = sp + 9984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26552) s
      (PolyMem (sp + 17376#64) (polyVecNat p0) ∗
        memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        memRegion (sp + 26688#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 9984#64 ∧
        (Pf ⊢ PolyMem (sp + 17376#64) (polyVecNat p0) ∗
          ((sp + 26688#64) ↦ₛ ser12Prefix p0 16) ∗
          memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine SepWP.weaken_pre (show PolyMem (sp + 17376#64) (polyVecNat p0) ∗
        memRegion (sp + 9984#64) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (PolyMem (sp + 17376#64) (polyVecNat p0) ∗ _) by sep_frame) ?_
  refine sepWP_seq_cl hcl (post1 := fun sm Pm =>
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = fpVal ∧
      sm.readReg64 .x8 = 3329#64 ∧ sm.readReg64 .x9 = 0xfffffffffffffe80#64 ∧
      sm.readReg64 .x19 = sp + 17376#64 ∧ sm.readReg64 .x20 = sp + 9984#64 ∧
      Pm = (memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (PolyMem (sp + 17376#64) (polyVecNat p0) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 26688#64) 384 ∗ Rest)))
    (mid := blkPl05.base + BitVec.ofNat 64 26316) ?_ ?_
  · wp_steps 4
    refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 26236)
      (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk) ?_
    intro hrun0a _ _
    step_strQ_sp 9984 384 26236 26240 368 10352 0#5; step_strQ_sp 9984 384 26240 26244 352 10336 0#5
    step_strQ_sp 9984 384 26244 26248 336 10320 0#5; step_strQ_sp 9984 384 26248 26252 320 10304 0#5
    step_strQ_sp 9984 384 26252 26256 304 10288 0#5; step_strQ_sp 9984 384 26256 26260 288 10272 0#5
    step_strQ_sp 9984 384 26260 26264 272 10256 0#5; step_strQ_sp 9984 384 26264 26268 256 10240 0#5
    step_strQ_sp 9984 384 26268 26272 240 10224 0#5; step_strQ_sp 9984 384 26272 26276 224 10208 0#5
    step_strQ_sp 9984 384 26276 26280 208 10192 0#5; step_strQ_sp 9984 384 26280 26284 192 10176 0#5
    step_strQ_sp 9984 384 26284 26288 176 10160 0#5; step_strQ_sp 9984 384 26288 26292 160 10144 0#5
    step_strQ_sp 9984 384 26292 26296 144 10128 0#5; step_strQ_sp 9984 384 26296 26300 128 10112 0#5
    step_strQ_sp 9984 384 26300 26304 112 10096 0#5; step_strQ_sp 9984 384 26304 26308 96 10080 0#5
    step_strQ_sp 9984 384 26308 26312 80 10064 0#5; step_strQ_sp 9984 384 26312 26316 64 10048 0#5
    refine SepWP.done rfl hrun0a ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [wp_norm, arm64_norm, hfp], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hx19],
      by simp [wp_norm, arm64_norm, hx20], rfl⟩
  rintro sm Pm hpcm hrunm hcl0a ⟨hspm, hspAm, hfpm, hx8m, hx9m, hx19m, hx20m, rfl⟩
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 26340) hcl0a ?_
  wp_steps 2
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 26324)
    (by wp_norm_lhs) (by simp [hrunm]) (by simp [hspm]) (spAligned_of_chk (by simp [hspm]) hchk) ?_
  intro hrun0 _ _
  step_strQ_sp 9984 384 26324 26328 48 10032 1#5; step_strQ_sp 9984 384 26328 26332 32 10016 1#5
  step_strQ_sp 9984 384 26332 26336 16 10000 1#5; step_strQ_sp 9984 384 26336 26340 0 9984 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (PolyMem (sp + 17376#64) (polyVecNat p0) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 26688#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 17376#64) (polyVecNat p0) ∗ memRegion (sp + 9984#64) 384 ∗
        (memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 26688#64) 384 ∗ Rest) by
    sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop4 hb (sp + 17376#64) (sp + 9984#64) p0 hbnd0 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx9m])
    (by simp [wp_norm, arm64_norm, hx20m])
    (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hspm] using hlp1.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 17376#64) (polyVecNat p0) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 26688#64) 384 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 26688#64) 384 ∗ PolyMem (sp + 17376#64) (polyVecNat p0) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 9984#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 26688#64) 384 ∗ PolyMem (sp + 17376#64) (polyVecNat p0) ∗ Rest) ⊢
      memRegion (sp + 26688#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        (((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ∗ PolyMem (sp + 17376#64) (polyVecNat p0) ∗ Rest) by
    sep_frame) ?_
  wp_steps 6
  refine call_bytes_memcpy (dst := sp + 26688#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm99 : ((sp + 9984#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + 9984#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 9984#64) (ser12Prefix p0 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + BitVec.ofNat 64 27840) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p0 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfpm] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.1, wp_norm, arm64_norm, hsp1] using hlpf.2.2.2.1,
    entails_sub hm99 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

theorem seg5_dk_col1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal outPtr : BitVec 64) (p1 : Poly16) (hbnd1 : PolyBounded16 3328 p1)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 26552) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 9984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 26892) s
      (((sp + 40#64) ↦₆₄ outPtr) ∗ PolyMem (sp + 17888#64) (polyVecNat p1) ∗
        memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        memRegion (sp + 27072#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 9984#64 ∧ sf.readReg64 .x21 = outPtr ∧
        (Pf ⊢ ((sp + 40#64) ↦₆₄ outPtr) ∗ PolyMem (sp + 17888#64) (polyVecNat p1) ∗
          ((sp + 27072#64) ↦ₛ ser12Prefix p1 16) ∗
          memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 26680) hcl ?_
  wp_steps 8
  refine SepWP.weaken_pre (show ((sp + 40#64) ↦₆₄ outPtr) ∗ PolyMem (sp + 17888#64) (polyVecNat p1) ∗
        memRegion (sp + 9984#64) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (((sp + 40#64) ↦₆₄ outPtr) ∗ PolyMem (sp + 17888#64) (polyVecNat p1) ∗ _) by sep_frame) ?_
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 26584)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk) ?_
  intro hrun0 hsp0 hspA0
  step_strQ_sp 9984 384 26584 26588 368 10352 1#5; step_strQ_sp 9984 384 26588 26592 352 10336 1#5
  step_strQ_sp 9984 384 26592 26596 336 10320 1#5; step_strQ_sp 9984 384 26596 26600 320 10304 1#5
  step_strQ_sp 9984 384 26600 26604 304 10288 1#5; step_strQ_sp 9984 384 26604 26608 288 10272 1#5
  step_strQ_sp 9984 384 26608 26612 272 10256 1#5; step_strQ_sp 9984 384 26612 26616 256 10240 1#5
  step_strQ_sp 9984 384 26616 26620 240 10224 1#5; step_strQ_sp 9984 384 26620 26624 224 10208 1#5
  step_strQ_sp 9984 384 26624 26628 208 10192 1#5; step_strQ_sp 9984 384 26628 26632 192 10176 1#5
  step_strQ_sp 9984 384 26632 26636 176 10160 1#5; step_strQ_sp 9984 384 26636 26640 160 10144 1#5
  step_strQ_sp 9984 384 26640 26644 144 10128 1#5; step_strQ_sp 9984 384 26644 26648 128 10112 1#5
  step_strQ_sp 9984 384 26648 26652 112 10096 1#5; step_strQ_sp 9984 384 26652 26656 96 10080 1#5
  step_strQ_sp 9984 384 26656 26660 80 10064 1#5; step_strQ_sp 9984 384 26660 26664 64 10048 1#5
  step_strQ_sp 9984 384 26664 26668 48 10032 1#5; step_strQ_sp 9984 384 26668 26672 32 10016 1#5
  step_strQ_sp 9984 384 26672 26676 16 10000 1#5; step_strQ_sp 9984 384 26676 26680 0 9984 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0

  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (((sp + 40#64) ↦₆₄ outPtr) ∗ PolyMem (sp + 17888#64) (polyVecNat p1) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 27072#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 17888#64) (polyVecNat p1) ∗ memRegion (sp + 9984#64) 384 ∗
        (((sp + 40#64) ↦₆₄ outPtr) ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
          memRegion (sp + 27072#64) 384 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop5 hb (sp + 17888#64) (sp + 9984#64) p1 hbnd1 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx19])
    (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hx21_1 : s1.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm] using hlp1.2.2.2.2.2.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 17888#64) (polyVecNat p1) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p1 16) ∗
        (((sp + 40#64) ↦₆₄ outPtr) ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
          memRegion (sp + 27072#64) 384 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 9984#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 27072#64) 384 ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
          PolyMem (sp + 17888#64) (polyVecNat p1) ∗ Rest) by sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 9984#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 27072#64) 384 ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
          PolyMem (sp + 17888#64) (polyVecNat p1) ∗ Rest) ⊢
      memRegion (sp + 27072#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        (((sp + 9984#64) ↦ₛ ser12Prefix p1 16) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
          PolyMem (sp + 17888#64) (polyVecNat p1) ∗ Rest) by sep_frame) ?_
  wp_steps 7
  refine call_bytes_memcpy (dst := sp + 27072#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm99 : ((sp + 9984#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + 9984#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 9984#64) (ser12Prefix p1 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + BitVec.ofNat 64 27840) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p1 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfp] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.1, wp_norm, arm64_norm, hsp1] using hlpf.2.2.2.1,
    by simpa [hlp2.2.2.2.2.2.1, hx21_1, wp_norm, arm64_norm] using hlpf.2.2.2.2.2.1,
    entails_sub hm99 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

theorem seg5_dk_col2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x21v : BitVec 64) (p2 : Poly16) (hbnd2 : PolyBounded16 3328 p2)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 26892) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 9984#64) (hx21 : s.readReg64 .x21 = x21v)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off6a5c) s
      (PolyMem (sp + 18400#64) (polyVecNat p2) ∗
        memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
        memRegion (sp + 27456#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x20 = sp + 9984#64 ∧ sf.readReg64 .x21 = x21v ∧
        (Pf ⊢ PolyMem (sp + 18400#64) (polyVecNat p2) ∗
          ((sp + 27456#64) ↦ₛ ser12Prefix p2 16) ∗
          memRegion (sp + 9984#64) 384 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine SepWP.weaken_pre (show PolyMem (sp + 18400#64) (polyVecNat p2) ∗
        memRegion (sp + 9984#64) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (PolyMem (sp + 18400#64) (polyVecNat p2) ∗ _) by sep_frame) ?_
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 27016) hcl ?_
  wp_steps 7
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 26920)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_chk (by simp [hsp]) hchk) ?_
  intro hrun0 hsp0 hspA0
  step_strQ_sp 9984 384 26920 26924 368 10352 1#5; step_strQ_sp 9984 384 26924 26928 352 10336 1#5
  step_strQ_sp 9984 384 26928 26932 336 10320 1#5; step_strQ_sp 9984 384 26932 26936 320 10304 1#5
  step_strQ_sp 9984 384 26936 26940 304 10288 1#5; step_strQ_sp 9984 384 26940 26944 288 10272 1#5
  step_strQ_sp 9984 384 26944 26948 272 10256 1#5; step_strQ_sp 9984 384 26948 26952 256 10240 1#5
  step_strQ_sp 9984 384 26952 26956 240 10224 1#5; step_strQ_sp 9984 384 26956 26960 224 10208 1#5
  step_strQ_sp 9984 384 26960 26964 208 10192 1#5; step_strQ_sp 9984 384 26964 26968 192 10176 1#5
  step_strQ_sp 9984 384 26968 26972 176 10160 1#5; step_strQ_sp 9984 384 26972 26976 160 10144 1#5
  step_strQ_sp 9984 384 26976 26980 144 10128 1#5; step_strQ_sp 9984 384 26980 26984 128 10112 1#5
  step_strQ_sp 9984 384 26984 26988 112 10096 1#5; step_strQ_sp 9984 384 26988 26992 96 10080 1#5
  step_strQ_sp 9984 384 26992 26996 80 10064 1#5; step_strQ_sp 9984 384 26996 27000 64 10048 1#5
  step_strQ_sp 9984 384 27000 27004 48 10032 1#5; step_strQ_sp 9984 384 27004 27008 32 10016 1#5
  step_strQ_sp 9984 384 27008 27012 16 10000 1#5; step_strQ_sp 9984 384 27012 27016 0 9984 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 9984) 384 ∗
        (PolyMem (sp + 18400#64) (polyVecNat p2) ∗
          memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 27456#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 18400#64) (polyVecNat p2) ∗ memRegion (sp + 9984#64) 384 ∗
        (memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 27456#64) 384 ∗ Rest) by
    sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop6 hb (sp + 18400#64) (sp + 9984#64) p2 hbnd2 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx19])
    (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  have hsp1 : s1.sp = sp := by simpa [hsp] using hlp1.1
  have hx21_1 : s1.readReg64 .x21 = x21v := by simpa [hx21] using hlp1.2.2.2.2.2.1
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 18400#64) (polyVecNat p2) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 27456#64) 384 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 9984#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + 27456#64) 384 ∗ PolyMem (sp + 18400#64) (polyVecNat p2) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 9984#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  have hsp2 : s2.sp = sp := by simpa [hsp1] using hlp2.1
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        ((sp + 9984#64) ↦ₛ ser12Prefix p2 16) ∗
        (memRegion (sp + 27456#64) 384 ∗ PolyMem (sp + 18400#64) (polyVecNat p2) ∗ Rest) ⊢
      memRegion (sp + 27456#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 9984#64) ↦ₛ ser12Prefix p2 16) ∗ PolyMem (sp + 18400#64) (polyVecNat p2) ∗ Rest) by
    sep_frame) ?_
  wp_steps 7
  refine call_bytes_memcpy (dst := sp + 27456#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (by simp [ser12Prefix_length]) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  have hsp_sf : sf.sp = sp := by simpa [hlp2.1, hsp1] using hlpf.1
  have hm99 : ((sp + 9984#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + 9984#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 9984#64) (ser12Prefix p2 16)
  have hm27 : ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + BitVec.ofNat 64 27840) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p2 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [hlp2.2.2.1, hlp1.2.2.1, hfp] using hlpf.2.2.1,
    by simpa [hlp2.2.2.2.2.1, wp_norm, arm64_norm, hsp1] using hlpf.2.2.2.2.1,
    by simpa [hlp2.2.2.2.2.2.1, hx21_1, wp_norm, arm64_norm] using hlpf.2.2.2.2.2.1,
    entails_sub hm99 (by sep_frame) (entails_sub hm27 (by sep_frame) (by sep_frame))⟩

@[expose] noncomputable def pk2OfRhoSigma (rho sigma : List (BitVec 8)) : List (BitVec 8) :=
  let aMat := sampleMatrixWith sampleNtt 3 rho true
  let sHat := (sampleVecCbd2 3 sigma 0).map polyNtt
  let eHat := (sampleVecCbd2 3 sigma 3).map polyNtt
  let tHat : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    polyAdd (vecDotNtt 3 (aMat.getD i #[]) sHat) (eHat.getD i zeroPoly)
  ((List.range 3).map fun i => byteEncode 12 (tHat.getD i zeroPoly)).flatten

@[expose] def Seg5DkExit [MlKemPlacement] (b : BitVec 64) (s0 : State)
    (seedA outPtr : BitVec 64) (seed : List (BitVec 8)) (F : SepProp)
    (sf : State) (Pf : SepProp) : Prop :=
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  let rho := g.take 32
  let sigma := g.drop 32
  let z := seed.drop 32
  let pk2 := pk2OfRhoSigma rho sigma
  let hPk := sha3_256List (pk2 ++ rho)
  sf.pc = b + off6a5c ∧
  sf.status = .Running ∧
  sf.sp = sp ∧
  sf.spAligned = true ∧
  sf.readReg64 .fp = s0.sp - 96#64 ∧
  sf.readReg64 .x20 = sp + 9984#64 ∧
  sf.readReg64 .x21 = outPtr ∧
  mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
  MlKemRoOk mlkemMpl sf.mem ∧
  (Pf ⊢ SavedFrame05 s0.sp s0 ∗
    stackAt sp 1136 ∗
    (seedA ↦ₛ seed) ∗
    memRegion sp 8416 ∗
    SHatMem sp sigma ∗
    ((sp + 9952#64) ↦ₛ z) ∗
    memRegion (sp + 9984#64) 5760 ∗
    memRegion (sp + 15744#64) 64 ∗
    memRegion (sp + 15808#64) 1568 ∗
    memRegion (sp + 17376#64) 384 ∗
    memRegion (sp + 17760#64) 8928 ∗
    ((sp + 26688#64) ↦ₛ pk2) ∗
    memRegion (sp + 27840#64) 384 ∗
    memRegion (sp + 28224#64) 800 ∗
    ((sp + 29024#64) ↦ₛ rho) ∗
    ((sp + 29056#64) ↦ₛ hPk) ∗
    memRegion (sp + 29088#64) 832 ∗
    F)

theorem pk2OfRhoSigma_eq {rho sigma : List (BitVec 8)}
    (hrho : rho.length = 32) (hsig : sigma.length = 32) :
    pk2OfRhoSigma rho sigma =
      ser12Prefix (tHatPoly16 rho sigma 0) 16 ++
      ser12Prefix (tHatPoly16 rho sigma 1) 16 ++
      ser12Prefix (tHatPoly16 rho sigma 2) 16 := by
  have h0 := (tHatPoly16_ser12 hrho hsig (col := 0) (by decide)).2
  have h1 := (tHatPoly16_ser12 hrho hsig (col := 1) (by decide)).2
  have h2 := (tHatPoly16_ser12 hrho hsig (col := 2) (by decide)).2
  unfold pk2OfRhoSigma
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]
  have g0 : (Array.ofFn (n := 3) fun ⟨i, _⟩ =>
      polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD i #[])
        ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD i zeroPoly)).getD 0 zeroPoly =
    polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD 0 #[])
      ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD 0 zeroPoly) := by simp [Array.getD]
  have g1 : (Array.ofFn (n := 3) fun ⟨i, _⟩ =>
      polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD i #[])
        ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD i zeroPoly)).getD 1 zeroPoly =
    polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD 1 #[])
      ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD 1 zeroPoly) := by simp [Array.getD]
  have g2 : (Array.ofFn (n := 3) fun ⟨i, _⟩ =>
      polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD i #[])
        ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD i zeroPoly)).getD 2 zeroPoly =
    polyAdd (vecDotNtt 3 ((sampleMatrixWith sampleNtt 3 rho true).getD 2 #[])
      ((sampleVecCbd2 3 sigma 0).map polyNtt))
      (((sampleVecCbd2 3 sigma 3).map polyNtt).getD 2 zeroPoly) := by simp [Array.getD]
  rw [g0, g1, g2, ← h0, ← h1, ← h2]

theorem pk2OfRhoSigma_length {rho sigma : List (BitVec 8)}
    (hrho : rho.length = 32) (hsig : sigma.length = 32) :
    (pk2OfRhoSigma rho sigma).length = 1152 := by
  rw [pk2OfRhoSigma_eq hrho hsig]; simp [ser12Prefix_length]

private theorem seg5_ek_all [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8))
    (hseed : seed.length = 64) (F : SepProp) {P : SepProp}
    (hexit : Seg4Exit b s0 seedA outPtr seed F s P) :
    let sp := s0.sp - 30080#64
    let g := sha3_512List (seed.take 32 ++ [3#8])
    let rho := g.take 32
    let sigma := g.drop 32
    let z := seed.drop 32
    let pk2 := pk2OfRhoSigma rho sigma
    let hPk := sha3_256List (pk2 ++ rho)
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off666c) s P
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = sp + 17376#64 ∧ sf.readReg64 .x20 = sp + 9984#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ SavedFrame05 s0.sp s0 ∗ stackAt sp 1136 ∗ (seedA ↦ₛ seed) ∗
          (sp ↦ₛ rho) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
          ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 56#64) 80 ∗
          ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 144#64) 2064 ∗
          memRegion (sp + 2208#64) 6144 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 8384#64) ↦ₛ hPk) ∗
          SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
          memRegion (sp + 9984#64) 1184 ∗ memRegion (sp + 11168#64) 6208 ∗
          PolyMem (sp + 17376#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗
          PolyMem (sp + 17888#64) (polyVecNat (tHatPoly16 rho sigma 1)) ∗
          PolyMem (sp + 18400#64) (polyVecNat (tHatPoly16 rho sigma 2)) ∗
          memRegion (sp + 18912#64) 7776 ∗ memRegion (sp + 26688#64) 1152 ∗
          memRegion (sp + 27840#64) 1184 ∗ ((sp + 29024#64) ↦ₛ rho) ∗
          ((sp + 29056#64) ↦ₛ hPk) ∗ memRegion (sp + 29088#64) 832 ∗ F)) := by
  intro sp g rho sigma z pk2 hPk
  rcases hexit with ⟨hpc, hrun, hsp, hspA, hfp0, hcl, hro, hP⟩
  have hfp : s.readReg64 .fp = sp + 29984#64 := by
    rw [hfp0]; dsimp only [sp]; clear * -; bv_omega
  have hg : g.length = 64 := (sha3_512 (seed.take 32 ++ [3#8])).2
  have hrho : rho.length = 32 := by simp [rho, hg]
  have hsig : sigma.length = 32 := by simp [sigma, hg]
  have hpk2 : pk2.length = 1152 := pk2OfRhoSigma_length hrho hsig
  have hhPk : hPk.length = 32 := (sha3_256 (pk2 ++ rho)).2
  have hbnd0 := (tHatPoly16_ser12 hrho hsig (col := 0) (by decide)).1
  have hbnd1 := (tHatPoly16_ser12 hrho hsig (col := 1) (by decide)).1
  have hbnd2 := (tHatPoly16_ser12 hrho hsig (col := 2) (by decide)).1
  have hs8352 : memRegion (sp + 8352#64) 64 =
      memRegion (sp + 8352#64) 32 ∗ memRegion (sp + 8384#64) 32 :=
    memRegion_split' (b' := sp + 8384#64) (n := 32) (k := (32 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hs9952 : memRegion (sp + 9952#64) 7424 =
      memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 9984#64) 1184 ∗
      memRegion (sp + 11168#64) 6208 := by
    rw [memRegion_split' (b' := sp + 9984#64) (n := 32) (k := (7392 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 9984#64) (b' := sp + 11168#64) (n := 1184) (k := (6208 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
  have hs18912 : memRegion (sp + 18912#64) 10496 =
      memRegion (sp + 18912#64) 3072 ∗ memRegion (sp + 21984#64) 3168 ∗
      memRegion (sp + 25152#64) 1536 ∗ memRegion (sp + 26688#64) 384 ∗
      memRegion (sp + 27072#64) 768 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
      memRegion (sp + 28224#64) 800 ∗ memRegion (sp + 29024#64) 384 := by
    rw [memRegion_split' (b' := sp + 21984#64) (n := 3072) (k := (7424 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 21984#64) (b' := sp + 25152#64) (n := 3168) (k := (4256 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 25152#64) (b' := sp + 26688#64) (n := 1536) (k := (2720 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 26688#64) (b' := sp + 27072#64) (n := 384) (k := (2336 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 27072#64) (b' := sp + BitVec.ofNat 64 27840) (n := 768) (k := (1568 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + BitVec.ofNat 64 27840) (b' := sp + 28224#64) (n := 384) (k := (1184 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 28224#64) (b' := sp + 29024#64) (n := 800) (k := (384 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm17376_4608 : memRegion (sp + 17376#64) 1536 ∗ memRegion (sp + 18912#64) 3072 =
      memRegion (sp + 17376#64) 4608 :=
    (memRegion_split' (b := sp + 17376#64) (b' := sp + 18912#64) (n := 1536) (k := (3072 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  have hs29440 : memRegion (sp + 29440#64) 480 =
      memRegion (sp + 29440#64) 432 ∗ memRegion (sp + 29872#64) 32 ∗ memRegion (sp + 29904#64) 16 := by
    rw [memRegion_split' (b' := sp + 29872#64) (n := 432) (k := (48 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29872#64) (b' := sp + 29904#64) (n := 32) (k := (16 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  let Inv :=
    SavedFrame05 s0.sp s0 ∗ memRegion (sp - 1136#64) 96 ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
    memRegion (sp + 56#64) 80 ∗ ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗
    memRegion (sp + 144#64) 2064 ∗ memRegion (sp + 11168#64) 6208 ∗
    memRegion (sp + 25152#64) 1536 ∗ memRegion (sp + 26688#64) 384 ∗
    ((sp + 29408#64) ↦ₛ sigma) ∗ memRegion (sp + 29440#64) 432 ∗ memRegion (sp + 29904#64) 16 ∗ F
  let Rest0 :=
    stackAt sp 1040 ∗ (seedA ↦ₛ seed) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗
    THatMem sp rho sigma ∗ memRegion (sp + 8384#64) 32 ∗ SHatMem sp sigma ∗
    memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 21984#64) 3168 ∗
    memRegion (sp + 27072#64) 768 ∗ memRegion (sp + BitVec.ofNat 64 27840) 384 ∗
    memRegion (sp + 28224#64) 800 ∗ memRegion (sp + 29024#64) 384 ∗
    memRegion (sp + 29872#64) 32 ∗ Inv
  refine SepWP.weaken_pre (Entails.trans hP ?_)
    (sepWP_seq_env hcl hro (seg5_dead_shuffle hb hbase sp (sp + 29984#64) rho hrho s Rest0
      hpc hrun hsp hspA hfp hcl) ?_)
  · rw [stackAt_1136_split_1040, hs8352, hs9952, hs18912, hs29440]
    refine entails_sub (aMatrixMem_entails_memRegion sp rho) (by dsimp only [rho]; sep_frame) ?_
    refine entails_sub (eHatMem_entails_memRegion sp sigma) (by dsimp only [sigma]; sep_frame) ?_
    rw [← hm17376_4608]; dsimp only [Rest0, Inv, rho, sigma]; sep_frame
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hP1⟩
  have hs9984 : memRegion (sp + 9984#64) 1184 =
      memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 10368#64) 384 ∗
      memRegion (sp + 10752#64) 384 ∗ memRegion (sp + 11136#64) 32 := by
    rw [memRegion_split' (b' := sp + 10368#64) (n := 384) (k := (800 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 10368#64) (b' := sp + 10752#64) (n := 384) (k := (416 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 10752#64) (b' := sp + 11136#64) (n := 384) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  refine SepWP.weaken_pre (Entails.trans hP1 (by dsimp only [Rest0]; unfold THatMem; rw [hs9984]; sep_frame))
    (sepWP_seq_env hcl1 hro1 (seg5_ek_col0 hb hbase sp (sp + 29984#64) (sp + 8352#64)
      (tHatPoly16 rho sigma 0) hbnd0 s1 _ hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hx20_1 hcl1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2 (seg5_ek_col1 hb hbase sp (sp + 29984#64) (sp + 8352#64)
      (tHatPoly16 rho sigma 1) hbnd1 s2 _ hpc2 hrun2 hsp2 hspA2 hfp2 hx19_2 hx20_2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hfp3, hx19_3, hx20_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢
      PolyMem (sp + 3232#64) (polyVecNat (tHatPoly16 rho sigma 2)) ∗
        memRegion (sp + 27840#64) 384 ∗ memRegion (sp + 29024#64) 384 ∗
        memRegion (sp + 10752#64) 384 ∗ _ by
    have : sp + BitVec.ofNat 64 27840 = sp + 27840#64 := rfl; rw [this]; sep_frame))
    (sepWP_seq_env hcl3 hro3 (seg5_ek_col2 hb hbase sp (sp + 29984#64) (sp + 8352#64)
      (tHatPoly16 rho sigma 2) hbnd2 s3 _ hpc3 hrun3 hsp3 hspA3 hfp3 hx19_3 hcl3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hfp4, hx19_4, hx20_4, hP4⟩
  have hpk2_cat : ((sp + 9984#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 0) 16) ∗
      ((sp + 10368#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 1) 16) ∗
      ((sp + 10752#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 2) 16) =
      ((sp + 9984#64) ↦ₛ pk2) := by
    dsimp only [pk2]
    rw [pk2OfRhoSigma_eq hrho hsig, List.append_assoc,
        pointsToBytes_append, ser12Prefix_length,
        show (sp + 9984#64) + BitVec.ofNat 64 384 = sp + 10368#64 by clear * -; bv_omega,
        pointsToBytes_append, ser12Prefix_length,
        show (sp + 10368#64) + BitVec.ofNat 64 384 = sp + 10752#64 by clear * -; bv_omega]
  have hm27840 : memRegion (sp + 27840#64) 384 ∗ memRegion (sp + 28224#64) 800 =
      memRegion (sp + 27840#64) 1184 :=
    (memRegion_split' (b := sp + 27840#64) (b' := sp + 28224#64) (n := 384) (k := (800 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  have hs29024 : memRegion (sp + 29024#64) 384 =
      memRegion (sp + 29024#64) 32 ∗ memRegion (sp + 29056#64) 32 ∗ memRegion (sp + 29088#64) 320 := by
    rw [memRegion_split' (b' := sp + 29056#64) (n := 32) (k := (352 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29056#64) (b' := sp + 29088#64) (n := 32) (k := (320 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  refine SepWP.weaken_pre (Entails.trans hP4 (by rw [← hm27840, hs29024, ← hpk2_cat]; sep_frame))
    (sepWP_seq_env hcl4 hro4 (seg5_ek_hash_a hb hbase sp pk2 rho hpk2 hrho s4 _
      hpc4 hrun4 hsp4 hspA4 hfp4 hx19_4 hx20_4 hcl4 hro4) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hfp5, hx20_5, hP5⟩
  have hm_pk : ((sp + 27840#64) ↦ₛ (pk2 ++ rho)) ⊢ memRegion (sp + 27840#64) 1184 := by
    simpa [hpk2, hrho] using pointsToBytes_entails_memRegion (sp + 27840#64) (pk2 ++ rho)
  have hm_hPk : ((sp + 29024#64) ↦ₛ hPk) ⊢ memRegion (sp + 29024#64) 32 := by
    simpa [hhPk] using pointsToBytes_entails_memRegion (sp + 29024#64) hPk
  have hm17376_7776 : memRegion (sp + 17376#64) 4608 ∗ memRegion (sp + 21984#64) 3168 =
      memRegion (sp + 17376#64) 7776 :=
    (memRegion_split' (b := sp + 17376#64) (b' := sp + 21984#64) (n := 4608) (k := (3168 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  have hm29024_64 : memRegion (sp + 29024#64) 32 ∗ memRegion (sp + 29056#64) 32 =
      memRegion (sp + 29024#64) 64 :=
    (memRegion_split' (b := sp + 29024#64) (b' := sp + 29056#64) (n := 32) (k := (32 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  refine SepWP.weaken_pre (Entails.trans hP5 (by
      dsimp only [hPk] at hm_hPk ⊢
      refine entails_sub hm_pk (by sep_frame) (entails_sub hm_hPk (by sep_frame) ?_)
      unfold THatMem; rw [← hm17376_7776, ← hm29024_64]; sep_frame))
    (sepWP_seq_env hcl5 hro5 (seg5_ek_hash_b hb hbase sp seedA seed rho sigma hPk
      hseed hrho hhPk s5 _ hpc5 hrun5 hsp5 hspA5 hfp5 hx20_5 hcl5) ?_)
  rintro sf Pf hpcsf hrunsf _ hrosf ⟨hspsf, hspAsf, hfpsf, hx19sf, hx20sf, hclsf, hPf⟩
  refine SepWP.done hpcsf hrunsf ⟨hspsf, hspAsf, hfpsf, hx19sf, hx20sf, hclsf, hrosf,
    Entails.trans hPf ?_⟩
  have hm_sig : ((sp + 29408#64) ↦ₛ sigma) ⊢ memRegion (sp + 29408#64) 32 := by
    simpa [hsig] using pointsToBytes_entails_memRegion (sp + 29408#64) sigma
  have hm_h298 : ((sp + 29872#64) ↦ₛ hPk) ⊢ memRegion (sp + 29872#64) 32 := by
    simpa [hhPk] using pointsToBytes_entails_memRegion (sp + 29872#64) hPk
  have hm18912 : memRegion (sp + 18912#64) 7776 =
      memRegion (sp + 18912#64) 6240 ∗ memRegion (sp + 25152#64) 1536 :=
    memRegion_split' (b' := sp + 25152#64) (n := 6240) (k := (1536 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm26688 : memRegion (sp + 26688#64) 1152 =
      memRegion (sp + 26688#64) 384 ∗ memRegion (sp + 27072#64) 768 :=
    memRegion_split' (b' := sp + 27072#64) (n := 384) (k := (768 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm29088 : memRegion (sp + 29088#64) 832 =
      memRegion (sp + 29088#64) 320 ∗ memRegion (sp + 29408#64) 32 ∗
      memRegion (sp + 29440#64) 432 ∗ memRegion (sp + 29872#64) 32 ∗ memRegion (sp + 29904#64) 16 := by
    rw [memRegion_split' (b' := sp + 29408#64) (n := 320) (k := (512 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29408#64) (b' := sp + 29440#64) (n := 32) (k := (480 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29440#64) (b' := sp + 29872#64) (n := 432) (k := (48 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29872#64) (b' := sp + 29904#64) (n := 32) (k := (16 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  rw [stackAt_1136_split_1040, hm18912, hm26688, hm29088]
  exact entails_sub hm_sig (by sep_frame) (entails_sub hm_h298 (by sep_frame) (by sep_frame))

private theorem fold_low_8416 (sp seedA outPtr : BitVec 64) (rho hPk : List (BitVec 8))
    (hrho : rho.length = 32) (hhPk : hPk.length = 32) :
    (sp ↦ₛ rho) ∗ ((sp + 32#64) ↦₆₄ seedA) ∗ ((sp + 40#64) ↦₆₄ outPtr) ∗
      ((sp + 48#64) ↦₆₄ (sp + 3744#64)) ∗ memRegion (sp + 56#64) 80 ∗
      ((sp + 136#64) ↦₆₄ (sp + 8416#64)) ∗ memRegion (sp + 144#64) 2064 ∗
      memRegion (sp + 2208#64) 6144 ∗ ((sp + 8352#64) ↦ₛ rho) ∗ ((sp + 8384#64) ↦ₛ hPk) ⊢
      memRegion sp 8416 := by
  have hm0 : (sp ↦ₛ rho) ⊢ memRegion sp 32 := by
    simpa [hrho] using pointsToBytes_entails_memRegion sp rho
  have hm8352 : ((sp + 8352#64) ↦ₛ rho) ⊢ memRegion (sp + 8352#64) 32 := by
    simpa [hrho] using pointsToBytes_entails_memRegion (sp + 8352#64) rho
  have hm8384 : ((sp + 8384#64) ↦ₛ hPk) ⊢ memRegion (sp + 8384#64) 32 := by
    simpa [hhPk] using pointsToBytes_entails_memRegion (sp + 8384#64) hPk
  rw [memRegion_split' (b' := sp + 32#64) (n := 32) (k := (8384 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 32#64) (b' := sp + 40#64) (n := 8) (k := (8376 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 40#64) (b' := sp + 48#64) (n := 8) (k := (8368 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 48#64) (b' := sp + 56#64) (n := 8) (k := (8360 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 56#64) (b' := sp + 136#64) (n := 80) (k := (8280 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 136#64) (b' := sp + 144#64) (n := 8) (k := (8272 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 144#64) (b' := sp + 2208#64) (n := 2064) (k := (6208 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 2208#64) (b' := sp + 8352#64) (n := 6144) (k := (64 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 8352#64) (b' := sp + 8384#64) (n := 32) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  exact entails_sub hm0 (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (sp + 32#64) seedA) (by sep_frame)
      (entails_sub (cell_entails_memRegion8 (sp + 40#64) outPtr) (by sep_frame)
        (entails_sub (cell_entails_memRegion8 (sp + 48#64) (sp + 3744#64)) (by sep_frame)
          (entails_sub (cell_entails_memRegion8 (sp + 136#64) (sp + 8416#64)) (by sep_frame)
            (entails_sub hm8352 (by sep_frame)
              (entails_sub hm8384 (by sep_frame) (by sep_frame)))))))

theorem seg5_ek_dk_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8))
    (hseed : seed.length = 64) (F : SepProp) {P : SepProp}
    (hexit : Seg4Exit b s0 seedA outPtr seed F s P) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off6a5c) s P
      (Seg5DkExit b s0 seedA outPtr seed F) := by
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  let rho := g.take 32
  let sigma := g.drop 32
  let pk2 := pk2OfRhoSigma rho sigma
  let hPk := sha3_256List (pk2 ++ rho)
  have hg : g.length = 64 := (sha3_512 (seed.take 32 ++ [3#8])).2
  have hrho : rho.length = 32 := by simp [rho, hg]
  have hsig : sigma.length = 32 := by simp [sigma, hg]
  have hhPk : hPk.length = 32 := (sha3_256 (pk2 ++ rho)).2
  have hbnd0 := (tHatPoly16_ser12 hrho hsig (col := 0) (by decide)).1
  have hbnd1 := (tHatPoly16_ser12 hrho hsig (col := 1) (by decide)).1
  have hbnd2 := (tHatPoly16_ser12 hrho hsig (col := 2) (by decide)).1
  refine SepWP.seq (seg5_ek_all hb hbase s0 s seedA outPtr seed hseed F hexit) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hcl1, hro1, hP1⟩
  have hs9984 : memRegion (sp + 9984#64) 1184 =
      memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 10368#64) 800 :=
    memRegion_split' (b' := sp + 10368#64) (n := 384) (k := (800 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hs26688 : memRegion (sp + 26688#64) 1152 =
      memRegion (sp + 26688#64) 384 ∗ memRegion (sp + 27072#64) 384 ∗ memRegion (sp + 27456#64) 384 := by
    rw [memRegion_split' (b' := sp + 27072#64) (n := 384) (k := (768 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 27072#64) (b' := sp + 27456#64) (n := 384) (k := (384 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hs27840 : memRegion (sp + 27840#64) 1184 =
      memRegion (sp + BitVec.ofNat 64 27840) 384 ∗ memRegion (sp + 28224#64) 800 :=
    memRegion_split' (b' := sp + 28224#64) (n := 384) (k := (800 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (Entails.trans hP1 (by rw [hs9984, hs26688, hs27840]; sep_frame))
    (sepWP_seq_env hcl1 hro1 (seg5_dk_col0 hb hbase sp (sp + 29984#64)
      (tHatPoly16 rho sigma 0) hbnd0 s1 _ hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1 hx20_1 hcl1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2 (seg5_dk_col1 hb hbase sp (sp + 29984#64) outPtr
      (tHatPoly16 rho sigma 1) hbnd1 s2 _ hpc2 hrun2 hsp2 hspA2 hfp2 hx19_2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hfp3, hx19_3, hx21_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3 (seg5_dk_col2 hb hbase sp (sp + 29984#64) outPtr
      (tHatPoly16 rho sigma 2) hbnd2 s3 _ hpc3 hrun3 hsp3 hspA3 hfp3 hx19_3 hx21_3 hcl3) ?_)
  rintro sf Pf hpcsf hrunsf hclsf hrosf ⟨hspsf, hspAsf, hfpsf, hx20sf, hx21sf, hPf⟩
  have hfp_end : sf.readReg64 .fp = s0.sp - 96#64 := by
    rw [hfpsf]; dsimp only [sp]; clear * -; bv_omega
  refine SepWP.done hpcsf hrunsf ⟨hpcsf, hrunsf, hspsf, hspAsf, hfp_end, hx20sf, hx21sf,
    hclsf, hrosf, Entails.trans hPf ?_⟩
  have hpk2_26688 : ((sp + 26688#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 0) 16) ∗
      ((sp + 27072#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 1) 16) ∗
      ((sp + 27456#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 2) 16) =
      ((sp + 26688#64) ↦ₛ pk2) := by
    dsimp only [pk2]
    rw [pk2OfRhoSigma_eq hrho hsig, List.append_assoc,
        pointsToBytes_append, ser12Prefix_length,
        show (sp + 26688#64) + BitVec.ofNat 64 384 = sp + 27072#64 by clear * -; bv_omega,
        pointsToBytes_append, ser12Prefix_length,
        show (sp + 27072#64) + BitVec.ofNat 64 384 = sp + 27456#64 by clear * -; bv_omega]
  have hm9984_5760 : memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 10368#64) 800 ∗
      memRegion (sp + 11168#64) 6208 =
      memRegion (sp + 9984#64) 5760 ∗ memRegion (sp + 15744#64) 64 ∗ memRegion (sp + 15808#64) 1568 := by
    rw [← sepConj_assoc,
        ← memRegion_split' (b := sp + 9984#64) (b' := sp + 10368#64) (n := 384) (k := (800 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        ← memRegion_split' (b := sp + 9984#64) (b' := sp + 11168#64) (n := 1184) (k := (6208 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 9984#64) (b' := sp + 15744#64) (n := 5760) (k := (1632 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 15744#64) (b' := sp + 15808#64) (n := 64) (k := (1568 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm17376_9312 : PolyMem (sp + 17376#64) (polyVecNat (tHatPoly16 rho sigma 0)) ∗
      PolyMem (sp + 17888#64) (polyVecNat (tHatPoly16 rho sigma 1)) ∗
      PolyMem (sp + 18400#64) (polyVecNat (tHatPoly16 rho sigma 2)) ∗
      memRegion (sp + 18912#64) 7776 ⊢
      memRegion (sp + 17376#64) 384 ∗ memRegion (sp + 17760#64) 8928 := by
    have hsplit : memRegion (sp + 17376#64) 384 ∗ memRegion (sp + 17760#64) 8928 =
        memRegion (sp + 17376#64) 512 ∗ memRegion (sp + 17888#64) 512 ∗
        memRegion (sp + 18400#64) 512 ∗ memRegion (sp + 18912#64) 7776 := by
      rw [← memRegion_split' (b := sp + 17376#64) (b' := sp + 17760#64) (n := 384) (k := (8928 : Nat)) rfl (by clear * -; bv_omega) (by decide),
          memRegion_split' (b := sp + 17376#64) (b' := sp + 17888#64) (n := 512) (k := (8800 : Nat)) rfl (by clear * -; bv_omega) (by decide),
          memRegion_split' (b := sp + 17888#64) (b' := sp + 18400#64) (n := 512) (k := (8288 : Nat)) rfl (by clear * -; bv_omega) (by decide),
          memRegion_split' (b := sp + 18400#64) (b' := sp + 18912#64) (n := 512) (k := (7776 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    rw [hsplit]
    exact entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
      (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame)
        (entails_sub (polyMem_entails_memRegion512 _ _) (by sep_frame) (by sep_frame)))
  have h27840_eq : sp + BitVec.ofNat 64 27840 = sp + 27840#64 := rfl
  rw [h27840_eq]
  refine entails_sub (fold_low_8416 sp seedA outPtr rho hPk hrho hhPk) (by sep_frame) ?_
  refine entails_sub hm17376_9312 (by sep_frame) ?_
  have hm99_ent : memRegion (sp + 9984#64) 384 ∗ (memRegion (sp + 10368#64) 800 ∗
      memRegion (sp + 11168#64) 6208) ⊢
      memRegion (sp + 9984#64) 5760 ∗ memRegion (sp + 15744#64) 64 ∗ memRegion (sp + 15808#64) 1568 := by
    rw [hm9984_5760]; exact Entails.refl _
  refine entails_sub hm99_ent (by sep_frame) ?_
  have hpk2_ent : ((sp + 26688#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 0) 16) ∗
      (((sp + 27072#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 1) 16) ∗
        ((sp + 27456#64) ↦ₛ ser12Prefix (tHatPoly16 rho sigma 2) 16)) ⊢
      ((sp + 26688#64) ↦ₛ pk2) := by
    rw [hpk2_26688]; exact Entails.refl _
  exact entails_sub hpk2_ent (by sep_frame) (by dsimp only [sp, g, rho, sigma, pk2, hPk]; sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk
