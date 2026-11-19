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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5PackA

/-!
# `generate_keypair_compressed` (`B05`): Segment 5d secret-key pack and epilogue (`+0x6d38 .. +0x6eec`)

Proves `seg5_pack_s2` (12-bit serialization of `sHat[2]` and copy of `pk2`), the trailing copies of
`rho`, `hPk`, and `z`, and the function epilogue (`seg5_pack_epi`), composing them with `Seg5PackA`
into `seg5_pack_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 80000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Pack

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_blk28)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (memRegion32_cells)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 byteEncode mlkem768KeyPairWith sampleNtt sha3_256List sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (sha3_256 sha3_512)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdDup_8h_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem bytesToVecNat polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  SavedFrame05 blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05
  savedFrame05_entails_memRegion160 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (cbdNttPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  ser12Prefix ser12Prefix_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops (seg5_loop9)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek (
  call_bytes_memcpy enter_mem_block polyMem_entails_memRegion512 sepWP_seq_cl spAligned_of_chk
  step_dead_strQ_sp vec2_cells_eq_bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk (Seg5DkExit pk2OfRhoSigma)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5PackA (
  cbdNttPoly16_ser12 mlkem768KeyPairWith_eq pk2OfRhoSigma_length
  seg5_pack_prep seg5_pack_s0 seg5_pack_s1)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [27960 → 28084, 28240 → 28396]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

private theorem sha3_512List_len (msg : List (BitVec 8)) : (sha3_512List msg).length = 64 :=
  (sha3_512 msg).2

private theorem sha3_256List_len (msg : List (BitVec 8)) : (sha3_256List msg).length = 32 :=
  (sha3_256 msg).2

attribute [local irreducible] blkPC05 blkLib05 dup8x16 polyVecNat ser12Prefix
  sha3_256List sha3_512List shake256List cbdNttPoly16 pk2OfRhoSigma byteEncode bytesToVecNat
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 svc_simdDup_8h_gpr

local macro "step_strQ_sp " baseOff:num total:num pcOff:num nextOff:num subOff:num offLit:num vt:term:arg : tactic => `(tactic| (
  refine step_dead_strQ_sp $baseOff $total $pcOff $nextOff $subOff $offLit $vt
    ‹_› ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) (by omega) ?_
  intro _))

theorem seg5_pack_s2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v outPtr : BitVec 64) (p2 : Poly16) (hbnd2 : PolyBounded16 3328 p2)
    (pk2 : List (BitVec 8)) (hpk2 : pk2.length = 1152)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 27960) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = outPtr)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 28304) s
      (PolyMem (sp + 16832#64) (polyVecNat p2) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        ((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (sp + 27840#64) 384 ∗
        memRegion (outPtr + 768#64) 384 ∗ memRegion (outPtr + 1152#64) 1152 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x21 = outPtr ∧
        (Pf ⊢ ((outPtr + 768#64) ↦ₛ ser12Prefix p2 16) ∗
          ((outPtr + 1152#64) ↦ₛ pk2) ∗
          memRegion (sp + 16832#64) 512 ∗
          memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
          memRegion (sp + 26688#64) 1152 ∗
          memRegion (sp + 27840#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 28088) hcl ?_
  wp_steps 8
  refine SepWP.weaken_pre (show PolyMem (sp + 16832#64) (polyVecNat p2) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 16832#64) (polyVecNat p2) ∗ _) by sep_frame) ?_
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 27992)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [wp_norm, arm64_norm, hsp])
    (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp]) hchk) ?_
  intro hrun0 _ _
  step_strQ_sp 17376 384 27992 27996 368 17744 1#5; step_strQ_sp 17376 384 27996 28000 352 17728 1#5
  step_strQ_sp 17376 384 28000 28004 336 17712 1#5; step_strQ_sp 17376 384 28004 28008 320 17696 1#5
  step_strQ_sp 17376 384 28008 28012 304 17680 1#5; step_strQ_sp 17376 384 28012 28016 288 17664 1#5
  step_strQ_sp 17376 384 28016 28020 272 17648 1#5; step_strQ_sp 17376 384 28020 28024 256 17632 1#5
  step_strQ_sp 17376 384 28024 28028 240 17616 1#5; step_strQ_sp 17376 384 28028 28032 224 17600 1#5
  step_strQ_sp 17376 384 28032 28036 208 17584 1#5; step_strQ_sp 17376 384 28036 28040 192 17568 1#5
  step_strQ_sp 17376 384 28040 28044 176 17552 1#5; step_strQ_sp 17376 384 28044 28048 160 17536 1#5
  step_strQ_sp 17376 384 28048 28052 144 17520 1#5; step_strQ_sp 17376 384 28052 28056 128 17504 1#5
  step_strQ_sp 17376 384 28056 28060 112 17488 1#5; step_strQ_sp 17376 384 28060 28064 96 17472 1#5
  step_strQ_sp 17376 384 28064 28068 80 17456 1#5; step_strQ_sp 17376 384 28068 28072 64 17440 1#5
  step_strQ_sp 17376 384 28072 28076 48 17424 1#5; step_strQ_sp 17376 384 28076 28080 32 17408 1#5
  step_strQ_sp 17376 384 28080 28084 16 17392 1#5; step_strQ_sp 17376 384 28084 28088 0 17376 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 16832#64) (polyVecNat p2) ∗
          ((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (sp + 27840#64) 384 ∗
          memRegion (outPtr + 768#64) 384 ∗ memRegion (outPtr + 1152#64) 1152 ∗ Rest) ⊢
      PolyMem (sp + 16832#64) (polyVecNat p2) ∗ memRegion (sp + 17376#64) 384 ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (sp + 27840#64) 384 ∗
          memRegion (outPtr + 768#64) 384 ∗ memRegion (outPtr + 1152#64) 1152 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop9 hb (sp + 16832#64) (sp + 17376#64) p2 hbnd2 _ _ rfl hrun0
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hx20])
    (by simp [wp_norm, arm64_norm])) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  rcases hlp1 with ⟨hsp1', _, hfp1', hx19_1', _, hx21_1', _⟩
  have hsp1 : s1.sp = sp := by simpa [wp_norm, arm64_norm, hsp] using hsp1'
  have hfp1 : s1.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfp] using hfp1'
  have hx19_1 : s1.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19] using hx19_1'
  have hx21_1 : s1.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21] using hx21_1'
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 16832#64) (polyVecNat p2) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (sp + 27840#64) 384 ∗
          memRegion (outPtr + 768#64) 384 ∗ memRegion (outPtr + 1152#64) 1152 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (outPtr + 768#64) 384 ∗
          memRegion (outPtr + 1152#64) 1152 ∗ PolyMem (sp + 16832#64) (polyVecNat p2) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 6
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 17376#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p2 16) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  rcases hlp2 with ⟨hsp2', _, hfp2', hx19_2', _, hx21_2', _⟩
  have hsp2 : s2.sp = sp := by simpa [wp_norm, arm64_norm, hsp1] using hsp2'
  have hfp2 : s2.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfp1] using hfp2'
  have hx19_2 : s2.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19_1] using hx19_2'
  have hx21_2 : s2.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21_1] using hx21_2'
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (outPtr + 768#64) 384 ∗
          memRegion (outPtr + 1152#64) 1152 ∗ PolyMem (sp + 16832#64) (polyVecNat p2) ∗ Rest) ⊢
      memRegion (outPtr + 768#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (outPtr + 1152#64) 1152 ∗
          ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
          PolyMem (sp + 16832#64) (polyVecNat p2) ∗ Rest) by sep_frame) ?_
  wp_steps 5
  refine call_bytes_memcpy (dst := outPtr + 768#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p2 16) (by decide) hcl2
    fun s3 hpc3 hrun3 hlp3 hcl3 => ?_
  rcases hlp3 with ⟨hsp3', _, hfp3', hx19_3', _, hx21_3', _⟩
  have hsp3 : s3.sp = sp := by simpa [wp_norm, arm64_norm, hsp2] using hsp3'
  have hfp3 : s3.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfp2] using hfp3'
  have hx19_3 : s3.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19_2] using hx19_3'
  have hx21_3 : s3.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21_2] using hx21_3'
  refine SepWP.weaken_pre (show ((outPtr + 768#64) ↦ₛ ser12Prefix p2 16) ∗
        ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
        (((sp + 26688#64) ↦ₛ pk2) ∗ memRegion (outPtr + 1152#64) 1152 ∗
          ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
          PolyMem (sp + 16832#64) (polyVecNat p2) ∗ Rest) ⊢
      memRegion (outPtr + 1152#64) 1152 ∗ ((sp + 26688#64) ↦ₛ pk2) ∗
        (((outPtr + 768#64) ↦ₛ ser12Prefix p2 16) ∗
          ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ∗
          ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ∗
          PolyMem (sp + 16832#64) (polyVecNat p2) ∗ Rest) by sep_frame) ?_
  wp_steps 5
  refine call_bytes_memcpy (dst := outPtr + 1152#64) (src := sp + 26688#64) (n := 1152)
    (by wp_norm_lhs) (by simp [hrun3]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp3]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    hpk2 (by decide) hcl3
    fun sf hpcsf hrunsf hlpf _ => ?_
  rcases hlpf with ⟨hspsf', _, hfpsf', hx19sf', _, hx21sf', _⟩
  have hsp_sf : sf.sp = sp := by simpa [wp_norm, arm64_norm, hsp3] using hspsf'
  have hm16832 := polyMem_entails_memRegion512 (sp + 16832#64) (polyVecNat p2)
  have hm17376 : ((sp + 17376#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + BitVec.ofNat 64 17376) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 17376#64) (ser12Prefix p2 16)
  have hm26688 : ((sp + 26688#64) ↦ₛ pk2) ⊢ memRegion (sp + 26688#64) 1152 := by
    simpa [hpk2] using pointsToBytes_entails_memRegion (sp + 26688#64) pk2
  have hm27840 : ((sp + 27840#64) ↦ₛ ser12Prefix p2 16) ⊢ memRegion (sp + 27840#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p2 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [wp_norm, arm64_norm, hfp3] using hfpsf',
    by simpa [wp_norm, arm64_norm, hx19_3] using hx19sf',
    by simpa [wp_norm, arm64_norm, hx21_3] using hx21sf',
    entails_sub hm16832 (by sep_frame)
      (entails_sub hm17376 (by sep_frame)
        (entails_sub hm26688 (by sep_frame)
          (entails_sub hm27840 (by sep_frame) (by sep_frame))))⟩

private theorem spAligned_add_29920 {sp : BitVec 64}
    (hchk : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 28672#64 + 1248#64) &&& 15#64 == 0#64) = true := by
  have h1 : (sp + 28672#64 + 1248#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  rwa [h1]

private theorem seg5_pack_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp outPtr : BitVec 64) (rho hPk z : List (BitVec 8))
    (hrho : rho.length = 32) (hhPk : hPk.length = 32) (hz : z.length = 32)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 28304) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 15744#64) (hx21 : s.readReg64 .x21 = outPtr) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 28348) s
      (((sp + 9952#64) ↦ₛ z) ∗ ((sp + 15744#64) ↦ₛ rho) ∗ ((sp + 15776#64) ↦ₛ hPk) ∗
        memRegion (outPtr + 2304#64) 96 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        (Pf ⊢ ((outPtr + 2304#64) ↦ₛ rho) ∗ ((outPtr + 2336#64) ↦ₛ hPk) ∗
          ((outPtr + 2368#64) ↦ₛ z) ∗
          memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 15744#64) 64 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hs96 : memRegion (outPtr + 2304#64) 96 =
      memRegion (outPtr + 2304#64) 32 ∗ memRegion (outPtr + 2336#64) 32 ∗ memRegion (outPtr + 2368#64) 32 := by
    rw [memRegion_split' (b' := outPtr + 2336#64) (n := 32) (k := (64 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := outPtr + 2368#64) (n := 32) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  rw [hs96]
  apply memRegion32_cells (outPtr + 2304#64); intro a0 a1 a2 a3
  apply memRegion32_cells (outPtr + 2336#64); intro b0 b1 b2 b3
  apply memRegion32_cells (outPtr + 2368#64); intro c0 c1 c2 c3
  refine SepWP.weaken_pre
    (P' := ((outPtr + 2304#64) ↦₆₄ a0) ∗ ((outPtr + 2312#64) ↦₆₄ a1) ∗
      ((outPtr + 2320#64) ↦₆₄ a2) ∗ ((outPtr + 2328#64) ↦₆₄ a3) ∗
      ((outPtr + 2336#64) ↦₆₄ b0) ∗ ((outPtr + 2344#64) ↦₆₄ b1) ∗
      ((outPtr + 2352#64) ↦₆₄ b2) ∗ ((outPtr + 2360#64) ↦₆₄ b3) ∗
      ((outPtr + 2368#64) ↦₆₄ c0) ∗ ((outPtr + 2376#64) ↦₆₄ c1) ∗
      ((outPtr + 2384#64) ↦₆₄ c2) ∗ ((outPtr + 2392#64) ↦₆₄ c3) ∗
      ((sp + 9952#64) ↦₆₄ (bytesToVecNat z 0).extractLsb' 0 64) ∗
      ((sp + 9960#64) ↦₆₄ (bytesToVecNat z 0).extractLsb' 64 64) ∗
      ((sp + 9968#64) ↦₆₄ (bytesToVecNat z 1).extractLsb' 0 64) ∗
      ((sp + 9976#64) ↦₆₄ (bytesToVecNat z 1).extractLsb' 64 64) ∗
      ((sp + 15744#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
      ((sp + 15752#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
      ((sp + 15760#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
      ((sp + 15768#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
      ((sp + 15776#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 0 64) ∗
      ((sp + 15784#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 64 64) ∗
      ((sp + 15792#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 0 64) ∗
      ((sp + 15800#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 64 64) ∗ Rest)
    (by
      rw [← vec2_cells_eq_bytes (sp + 9952#64) hz,
          ← vec2_cells_eq_bytes (sp + 15744#64) hrho,
          ← vec2_cells_eq_bytes (sp + 15776#64) hhPk]
      simp only [bitvec64_add_add_fold]; sep_frame) ?_
  wp_steps 11
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  refine ⟨by wp_norm_lhs, by simp [State.spAligned, hsp, hchk], ?_⟩
  have hm9952 : ((sp + 9952#64) ↦ₛ z) ⊢ memRegion (sp + 9952#64) 32 := by
    simpa [hz] using pointsToBytes_entails_memRegion (sp + 9952#64) z
  have hm15744 : ((sp + 15744#64) ↦ₛ rho) ∗ ((sp + 15776#64) ↦ₛ hPk) ⊢
      memRegion (sp + 15744#64) 64 := by
    rw [memRegion_split' (b' := sp + 15776#64) (n := 32) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (by simpa [hrho] using pointsToBytes_entails_memRegion (sp + 15744#64) rho)
      (by simpa [hhPk] using pointsToBytes_entails_memRegion (sp + 15776#64) hPk)
  rw [← vec2_cells_eq_bytes (sp + 9952#64) hz] at hm9952
  rw [← vec2_cells_eq_bytes (sp + 15744#64) hrho, ← vec2_cells_eq_bytes (sp + 15776#64) hhPk] at hm15744
  simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate] at hm9952 hm15744 ⊢
  rw [← vec2_cells_eq_bytes (outPtr + 2304#64) hrho,
      ← vec2_cells_eq_bytes (outPtr + 2336#64) hhPk,
      ← vec2_cells_eq_bytes (outPtr + 2368#64) hz]
  simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]
  exact entails_sub hm9952 (by sep_frame) (entails_sub hm15744 (by sep_frame) (by sep_frame))

private theorem calleeSavedVRegs_eq_of_readVReg128 (s0 sf : State)
    (h : ∀ r : Fin 8, sf.readVReg128 (BitVec.ofNat 5 (8 + r.val)) =
      ((s0.readVReg128 (BitVec.ofNat 5 (8 + r.val))).truncate 64).zeroExtend 128) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  have htr (v : BitVec 128) : ((v.truncate 64).zeroExtend 128).truncate 64 = v.truncate 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
  have hr (i : Fin 8) :
      (sf.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 =
        (s0.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 := by
    rw [h i, htr]
  exact Prod.ext (hr 0) (Prod.ext (hr 1) (Prod.ext (hr 2) (Prod.ext (hr 3)
    (Prod.ext (hr 4) (Prod.ext (hr 5) (Prod.ext (hr 6) (hr 7)))))))

private theorem seg5_pack_ldp [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 28356) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 160#64) (hspA : s.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame05 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  subst hbase
  have hchk : ((s0.sp - 160#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hspA
  dsimp only [SavedFrame05]
  wp_steps 11
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega), ?_⟩,
    sepConj_mono_left (savedFrame05_entails_memRegion160 s0.sp s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

private theorem seg5_pack_epi [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 28348) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 30080#64) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame05 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  have hstep2 : SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 28356) s
      (SavedFrame05 s0.sp s0 ∗ Rest)
      (fun sm Pm => sm.sp = s0.sp - 160#64 ∧ sm.spAligned = true ∧
        Pm = (SavedFrame05 s0.sp s0 ∗ Rest)) := by
    subst hbase
    have hchk : ((s0.sp - 30080#64) &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned, hsp] using hspA
    have hal : (((s0.sp - 30080#64) + 28672#64 + 1248#64) &&& 15#64 == 0#64) = true :=
      spAligned_add_29920 hchk
    wp_steps 2
    apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
    exact ⟨Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega),
      by simpa [State.spAligned, hsp] using hal, rfl⟩
  refine sepWP_seq_cl hcl hstep2 ?_
  rintro sm Pm hpcm hrunm _ ⟨hspm, hspAm, rfl⟩
  exact seg5_pack_ldp hb hbase s0 sm Rest hpcm hrunm hspm hspAm

private theorem outPtr_2400_split (outPtr : BitVec 64) :
    memRegion outPtr 2400 =
      memRegion outPtr 384 ∗ memRegion (outPtr + 384#64) 384 ∗
      memRegion (outPtr + 768#64) 384 ∗ memRegion (outPtr + 1152#64) 1152 ∗
      memRegion (outPtr + 2304#64) 96 := by
  rw [memRegion_split' (b' := outPtr + 384#64) (n := 384) (k := (2016 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := outPtr + 768#64) (n := 384) (k := (1632 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := outPtr + 1152#64) (n := 384) (k := (1248 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := outPtr + 2304#64) (n := 1152) (k := (96 : Nat)) rfl (by bv_omega) (by decide)]

private theorem outPtr_2400_join (outPtr : BitVec 64)
    (b0 b1 b2 pk2 rho hPk z : List (BitVec 8))
    (hb0 : b0.length = 384) (hb1 : b1.length = 384) (hb2 : b2.length = 384)
    (hpk2 : pk2.length = 1152) (hrho : rho.length = 32) (hhPk : hPk.length = 32) :
    (outPtr ↦ₛ b0) ∗ ((outPtr + 384#64) ↦ₛ b1) ∗ ((outPtr + 768#64) ↦ₛ b2) ∗
      ((outPtr + 1152#64) ↦ₛ pk2) ∗ ((outPtr + 2304#64) ↦ₛ rho) ∗
      ((outPtr + 2336#64) ↦ₛ hPk) ∗ ((outPtr + 2368#64) ↦ₛ z) =
      (outPtr ↦ₛ (b0 ++ b1 ++ b2 ++ pk2 ++ rho ++ hPk ++ z)) := by
  simp only [List.append_assoc, pointsToBytes_append, hb0, hb1, hb2, hpk2, hrho, hhPk]
  have a1 : outPtr + BitVec.ofNat 64 384 = outPtr + 384#64 := rfl
  have a2 : outPtr + 384#64 + BitVec.ofNat 64 384 = outPtr + 768#64 := by bv_omega
  have a3 : outPtr + 768#64 + BitVec.ofNat 64 384 = outPtr + 1152#64 := by bv_omega
  have a4 : outPtr + 1152#64 + BitVec.ofNat 64 1152 = outPtr + 2304#64 := by bv_omega
  have a5 : outPtr + 2304#64 + BitVec.ofNat 64 32 = outPtr + 2336#64 := by bv_omega
  have a6 : outPtr + 2336#64 + BitVec.ofNat 64 32 = outPtr + 2368#64 := by bv_omega
  rw [a1, a2, a3, a4, a5, a6]

private theorem stack_31216_join (sp0 : BitVec 64) :
    let sp := sp0 - 30080#64
    stackAt sp 1136 ∗ memRegion sp 8416 ∗ memRegion (sp + 8416#64) 1536 ∗
      memRegion (sp + 9952#64) 32 ∗ memRegion (sp + 9984#64) 5760 ∗
      memRegion (sp + 15744#64) 64 ∗ memRegion (sp + 15808#64) 512 ∗
      memRegion (sp + 16320#64) 512 ∗ memRegion (sp + 16832#64) 512 ∗
      memRegion (sp + 17344#64) 32 ∗ memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
      memRegion (sp + 17760#64) 8928 ∗ memRegion (sp + 26688#64) 1152 ∗
      memRegion (sp + 27840#64) 384 ∗ memRegion (sp + 28224#64) 800 ∗
      memRegion (sp + 29024#64) 64 ∗ memRegion (sp + 29088#64) 832 ∗
      memRegion (sp0 - 160#64) 160 = stackAt sp0 31216 := by
  intro sp
  unfold stackAt
  have hs0 : sp - BitVec.ofNat 64 1136 = sp0 - BitVec.ofNat 64 31216 := by dsimp [sp]; bv_omega
  rw [hs0,
    memRegion_split' (b := sp0 - BitVec.ofNat 64 31216) (b' := sp) (n := 1136) (k := (30080 : Nat)) rfl (by dsimp [sp]; bv_omega) (by decide),
    memRegion_split' (b := sp) (b' := sp + 8416#64) (n := 8416) (k := (21664 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 8416#64) (b' := sp + 9952#64) (n := 1536) (k := (20128 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 9952#64) (b' := sp + 9984#64) (n := 32) (k := (20096 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 9984#64) (b' := sp + 15744#64) (n := 5760) (k := (14336 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 15744#64) (b' := sp + 15808#64) (n := 64) (k := (14272 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 15808#64) (b' := sp + 16320#64) (n := 512) (k := (13760 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16320#64) (b' := sp + 16832#64) (n := 512) (k := (13248 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16832#64) (b' := sp + 17344#64) (n := 512) (k := (12736 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 17344#64) (b' := sp + BitVec.ofNat 64 17376) (n := 32) (k := (12704 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + BitVec.ofNat 64 17376) (b' := sp + 17760#64) (n := 384) (k := (12320 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 17760#64) (b' := sp + 26688#64) (n := 8928) (k := (3392 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 26688#64) (b' := sp + 27840#64) (n := 1152) (k := (2240 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 27840#64) (b' := sp + 28224#64) (n := 384) (k := (1856 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 28224#64) (b' := sp + 29024#64) (n := 800) (k := (1056 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 29024#64) (b' := sp + 29088#64) (n := 64) (k := (992 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 29088#64) (b' := sp0 - 160#64) (n := 832) (k := (160 : Nat)) rfl (by dsimp [sp]; bv_omega) (by decide)]

theorem seg5_pack_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s0 s5 : State) (seedA outPtr : BitVec 64) (seed : List (BitVec 8))
    (hseed : seed.length = 64) {P5 : SepProp}
    (hex5 : Seg5DkExit b s0 seedA outPtr seed (memRegion outPtr 2400) s5 P5) :
    SepWP (blkPC05.rebase b (fun _ => none)) (s0.readReg64 .lr) s5 P5
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((seedA ↦ₛ seed) ∗ (outPtr ↦ₛ mlkem768KeyPairWith sampleNtt seed) ∗ stackAt s0.sp 31216)) := by
  let sp := s0.sp - 30080#64
  let g := sha3_512List (seed.take 32 ++ [3#8])
  let rho := g.take 32
  let sigma := g.drop 32
  let z := seed.drop 32
  let pk2 := pk2OfRhoSigma rho sigma
  let hPk := sha3_256List (pk2 ++ rho)
  let p0 := cbdNttPoly16 (shake256List 128 (sigma ++ [0#8]))
  let p1 := cbdNttPoly16 (shake256List 128 (sigma ++ [1#8]))
  let p2 := cbdNttPoly16 (shake256List 128 (sigma ++ [2#8]))
  have hg : g.length = 64 := sha3_512List_len _
  have hrho : rho.length = 32 := by simp [rho, hg]
  have hsig : sigma.length = 32 := by simp [sigma, hg]
  have hz : z.length = 32 := by simp [z, hseed]
  have hpk2 : pk2.length = 1152 := pk2OfRhoSigma_length hrho hsig
  have hhPk : hPk.length = 32 := sha3_256List_len _
  have hbnd0 : PolyBounded16 3328 p0 := (cbdNttPoly16_ser12 hsig (j := 0) (by decide)).1
  have hbnd1 : PolyBounded16 3328 p1 := (cbdNttPoly16_ser12 hsig (j := 1) (by decide)).1
  have hbnd2 : PolyBounded16 3328 p2 := (cbdNttPoly16_ser12 hsig (j := 2) (by decide)).1
  rcases hex5 with ⟨hpc5, hrun5, hsp5, hspA5, hfp5, hx20_5, hx21_5, hcl5, _, hP5⟩
  refine sepWP_seq_cl hcl5 (SepWP.weaken_pre
    (Entails.trans hP5 (by rw [outPtr_2400_split outPtr]; sep_frame))
    (seg5_pack_prep hb hbase sp (s0.sp - 96#64) outPtr sigma rho hPk z
      hrho hhPk hz s5 _ hpc5 hrun5 hsp5 hspA5 hfp5 hx20_5 hx21_5 hcl5)) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 ⟨hsp6, hspA6, hfp6, hx8_6, hx9_6, hx10_6, hx19_6, hx21_6, hv0_6, _, hP6⟩
  refine sepWP_seq_cl hcl6 (SepWP.weaken_pre (Entails.trans hP6 (by sep_frame))
    (seg5_pack_s0 hb hbase sp (s0.sp - 96#64) (sp + 15744#64) outPtr p0 hbnd0
      s6 _ hpc6 hrun6 hsp6 hspA6 hfp6 hx8_6 hx9_6 hx10_6 hx19_6 hx21_6 hv0_6 hcl6)) ?_
  rintro s7 P7 hpc7 hrun7 hcl7 ⟨hsp7, hspA7, hfp7, hx19_7, hx20_7, hx21_7, hP7⟩
  refine sepWP_seq_cl hcl7 (SepWP.weaken_pre (Entails.trans hP7 (by sep_frame))
    (seg5_pack_s1 hb hbase sp (s0.sp - 96#64) (sp + 15744#64) outPtr p1 hbnd1
      s7 _ hpc7 hrun7 hsp7 hspA7 hfp7 hx19_7 hx20_7 hx21_7 hcl7)) ?_
  rintro s8 P8 hpc8 hrun8 hcl8 ⟨hsp8, hspA8, hfp8, hx19_8, hx20_8, hx21_8, hP8⟩
  refine sepWP_seq_cl hcl8 (SepWP.weaken_pre (Entails.trans hP8 (by sep_frame))
    (seg5_pack_s2 hb hbase sp (s0.sp - 96#64) (sp + 15744#64) outPtr p2 hbnd2
      pk2 hpk2 s8 _ hpc8 hrun8 hsp8 hspA8 hfp8 hx19_8 hx20_8 hx21_8 hcl8)) ?_
  rintro s9 P9 hpc9 hrun9 hcl9 ⟨hsp9, hspA9, _, hx19_9, hx21_9, hP9⟩
  refine sepWP_seq_cl hcl9 (SepWP.weaken_pre (Entails.trans hP9 (by sep_frame))
    (seg5_pack_tail hb hbase sp outPtr rho hPk z hrho hhPk hz s9 _
      hpc9 hrun9 hsp9 hspA9 hx19_9 hx21_9)) ?_
  rintro s10 P10 hpc10 hrun10 hcl10 ⟨hsp10, hspA10, hP10⟩
  refine SepWP.weaken_pre (Entails.trans hP10 (by sep_frame))
    (SepWP.mono (seg5_pack_epi hb hbase s0 s10 _ hpc10 hrun10 hsp10 hspA10 hcl10) ?_)
  intro sf Pf _ _ hpost
  rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have hout := outPtr_2400_join outPtr (ser12Prefix p0 16) (ser12Prefix p1 16) (ser12Prefix p2 16)
    pk2 rho hPk z (ser12Prefix_length p0 16) (ser12Prefix_length p1 16) (ser12Prefix_length p2 16)
    hpk2 hrho hhPk
  rw [← mlkem768KeyPairWith_eq hseed] at hout
  have hstk := stack_31216_join s0.sp
  exact entails_sub (Entails.of_eq hout) (by sep_frame)
    (entails_sub (Entails.of_eq hstk) (by sep_frame) (by sep_frame))
end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Pack
