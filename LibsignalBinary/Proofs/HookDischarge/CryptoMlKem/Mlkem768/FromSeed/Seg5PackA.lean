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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash

/-!
# `generate_keypair_compressed` (`B05`): Segment 5d part A (`+0x6a5c .. +0x6d38`)

Proves `cbdNttPoly16_ser12`, `mlkem768KeyPairWith_eq`, staging setup (`seg5_pack_prep`), and
12-bit serialization of `sHat[0]` and `sHat[1]` (`seg5_pack_s0`, `seg5_pack_s1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 80000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5PackA

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_blk28)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (memRegion32_cells)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 byteEncode mlkem768KeyPairWith polyNtt sampleNtt samplePolyCbd2 sampleVecCbd2
  sha3_256List sha3_512List shake256List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (sha3_256 sha3_512)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdDup_8h_gpr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem bytesToVecNat polyVecNat vecRangeBytes vecRangeBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (shake256List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHat (
  SHatMem cbdNttPoly16 cbdNttPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ser (
  polyBounded16_mono polyNtt_canonical samplePolyCbd2_size ser12Prefix
  ser12Prefix_16_eq_byteEncode ser12Prefix_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Loops (seg5_loop7 seg5_loop8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Ek (
  call_bytes_memcpy enter_mem_block polyMem_entails_memRegion512 sepWP_seq_cl spAligned_of_chk
  step_dead_strQ_sp vec2_cells_eq_bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5EkHash (poly3_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5Dk (off6a5c pk2OfRhoSigma)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05
  [27228 → 27420, 27576 → 27752, 27908 → 27956]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

local macro "step_strQ_sp " baseOff:num total:num pcOff:num nextOff:num subOff:num offLit:num vt:term:arg : tactic => `(tactic| (
  refine step_dead_strQ_sp $baseOff $total $pcOff $nextOff $subOff $offLit $vt
    ‹_› ‹_› ‹_› (by simp only [arm64_norm]) (by omega) (by omega) (by omega) (by omega) ?_
  intro _))

theorem cbdNttPoly16_ser12 {sigma : List (BitVec 8)} (hsig : sigma.length = 32)
    {j : Nat} (hj : j < 3) :
    let prf := shake256List 128 (sigma ++ [BitVec.ofNat 8 j])
    let sHat := (sampleVecCbd2 3 sigma 0).map polyNtt
    PolyBounded16 3328 (cbdNttPoly16 prf) ∧
    ser12Prefix (cbdNttPoly16 prf) 16 = byteEncode 12 (sHat.getD j zeroPoly) := by
  dsimp only
  obtain ⟨_, hbnd1664, hrep⟩ :=
    cbdNttPoly16_spec (shake256List_length 128 (sigma ++ [BitVec.ofNat 8 j]))
  have hbnd3328 : PolyBounded16 3328 (cbdNttPoly16 (shake256List 128 (sigma ++ [BitVec.ofNat 8 j]))) :=
    polyBounded16_mono (by decide : (1664 : Int) ≤ 3328) hbnd1664
  refine ⟨hbnd3328, ?_⟩
  have hget : ((sampleVecCbd2 3 sigma 0).map polyNtt).getD j zeroPoly =
      polyNtt (samplePolyCbd2 (shake256List 128 (sigma ++ [BitVec.ofNat 8 j]))) := by
    simp [sampleVecCbd2, Array.getD_eq_getD_getElem?, hj, List.take_of_length_le hsig.le]
  rw [hget]
  exact ser12Prefix_16_eq_byteEncode hbnd3328 hrep (polyNtt_canonical (samplePolyCbd2_size _))

theorem pk2OfRhoSigma_length {rho sigma : List (BitVec 8)}
    (hrho : rho.length = 32) (hsig : sigma.length = 32) :
    (pk2OfRhoSigma rho sigma).length = 1152 := by
  rw [Seg5Dk.pk2OfRhoSigma_eq hrho hsig]; simp [ser12Prefix_length]

theorem mlkem768KeyPairWith_eq {seed : List (BitVec 8)} (hseed : seed.length = 64) :
    let g := sha3_512List (seed.take 32 ++ [3#8])
    let rho := g.take 32; let sigma := g.drop 32; let z := seed.drop 32
    let pk2 := pk2OfRhoSigma rho sigma; let hPk := sha3_256List (pk2 ++ rho)
    let p0 := cbdNttPoly16 (shake256List 128 (sigma ++ [0#8]))
    let p1 := cbdNttPoly16 (shake256List 128 (sigma ++ [1#8]))
    let p2 := cbdNttPoly16 (shake256List 128 (sigma ++ [2#8]))
    mlkem768KeyPairWith sampleNtt seed =
      ser12Prefix p0 16 ++ ser12Prefix p1 16 ++ ser12Prefix p2 16 ++ pk2 ++ rho ++ hPk ++ z := by
  dsimp only
  have hg : (sha3_512List (seed.take 32 ++ [3#8])).length = 64 := (sha3_512 (seed.take 32 ++ [3#8])).2
  have hsig_len : ((sha3_512List (seed.take 32 ++ [3#8])).drop 32).length = 32 := by simp [hg]
  have hz_len : (seed.drop 32).length = 32 := by simp [hseed]
  have hs0 := (cbdNttPoly16_ser12 hsig_len (j := 0) (by decide)).2
  have hs1 := (cbdNttPoly16_ser12 hsig_len (j := 1) (by decide)).2
  have hs2 := (cbdNttPoly16_ser12 hsig_len (j := 2) (by decide)).2
  unfold mlkem768KeyPairWith pk2OfRhoSigma; dsimp only
  rw [List.take_of_length_le hsig_len.le, List.take_of_length_le hz_len.le]
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]
  rw [hs0, hs1, hs2]

attribute [local irreducible] blkPC05 blkLib05 dup8x16 polyVecNat ser12Prefix
  sha3_256List sha3_512List shake256List cbdNttPoly16 pk2OfRhoSigma byteEncode bytesToVecNat
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 svc_simdDup_8h_gpr

theorem poly3_z_eq_bytes (ptr : BitVec 64)
    (f0 f1 f2 : Nat → BitVec 128) (z : List (BitVec 8)) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 ∗
      ((ptr + 1536#64) ↦ₛ z) =
      (ptr ↦ₛ ((vecRangeBytes 32 f0 ++ vecRangeBytes 32 f1 ++ vecRangeBytes 32 f2) ++ z)) := by
  have h3 := poly3_eq_pointsToBytes ptr f0 f1 f2
  have hlen : ptr + BitVec.ofNat 64
      (vecRangeBytes 32 f0 ++ vecRangeBytes 32 f1 ++ vecRangeBytes 32 f2).length = ptr + 1536#64 := by
    simp [vecRangeBytes_length]
  have hassoc : PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2 ∗
      ((ptr + 1536#64) ↦ₛ z) =
      (PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗ PolyMem (ptr + 1024#64) f2) ∗
        ((ptr + 1536#64) ↦ₛ z) := by simp only [sepConj_assoc]
  rw [hassoc, h3, ← hlen, ← pointsToBytes_append]

theorem seg5_pack_prep [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal outPtr : BitVec 64) (sigma rho hPk z : List (BitVec 8))
    (hrho : rho.length = 32) (hhPk : hPk.length = 32) (hz : z.length = 32)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + off6a5c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx20 : s.readReg64 .x20 = sp + 9984#64) (hx21 : s.readReg64 .x21 = outPtr)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let p0 := cbdNttPoly16 (shake256List 128 (sigma ++ [0#8]))
    let p1 := cbdNttPoly16 (shake256List 128 (sigma ++ [1#8]))
    let p2 := cbdNttPoly16 (shake256List 128 (sigma ++ [2#8]))
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27328) s
      (SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
        memRegion (sp + 15744#64) 64 ∗ memRegion (sp + 15808#64) 1568 ∗
        ((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 15824#64 ∧
        sf.readReg64 .x10 = sp + 17376#64 ∧ sf.readReg64 .x19 = sp + 15744#64 ∧
        sf.readReg64 .x21 = outPtr ∧ sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ memRegion (sp + 8416#64) 1536 ∗ ((sp + 9952#64) ↦ₛ z) ∗
          ((sp + 15744#64) ↦ₛ rho) ∗ ((sp + 15776#64) ↦ₛ hPk) ∗
          PolyMem (sp + 15808#64) (polyVecNat p0) ∗
          PolyMem (sp + 16320#64) (polyVecNat p1) ∗
          PolyMem (sp + 16832#64) (polyVecNat p2) ∗
          memRegion (sp + 17344#64) 32 ∗ memRegion (sp + 29024#64) 64 ∗ Rest)) := by
  intro p0 p1 p2
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set sBytes := vecRangeBytes 32 (polyVecNat p0) ++ vecRangeBytes 32 (polyVecNat p1) ++
    vecRangeBytes 32 (polyVecNat p2)
  have hsLen : (sBytes ++ z).length = 1568 := by simp [sBytes, vecRangeBytes_length, hz]
  have hsrc : SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) = ((sp + 8416#64) ↦ₛ (sBytes ++ z)) := by
    unfold SHatMem
    rw [sepConj_assoc, sepConj_assoc]
    simpa only [sBytes, p0, p1, p2,
      show (sp + 8416#64) + 512#64 = sp + 8928#64 by clear * -; bv_omega,
      show (sp + 8416#64) + 1024#64 = sp + 9440#64 by clear * -; bv_omega,
      show (sp + 8416#64) + 1536#64 = sp + 9952#64 by clear * -; bv_omega] using
      poly3_z_eq_bytes (sp + 8416#64) (polyVecNat p0) (polyVecNat p1) (polyVecNat p2) z
  refine SepWP.weaken_pre (show SHatMem sp sigma ∗ ((sp + 9952#64) ↦ₛ z) ∗
        memRegion (sp + 15744#64) 64 ∗ memRegion (sp + 15808#64) 1568 ∗ _ ⊢
      memRegion (sp + 15808#64) 1568 ∗ ((sp + 8416#64) ↦ₛ (sBytes ++ z)) ∗
        (memRegion (sp + 15744#64) 64 ∗ _) by
    rw [← sepConj_assoc, hsrc]; sep_frame) ?_
  wp_steps 7
  refine call_bytes_memcpy (dst := sp + 15808#64) (src := sp + 8416#64) (n := 1568)
    (by wp_norm_lhs) (by simp [hrun]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp]) hchk)
    (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_lhs) hsLen (by decide) hcl
    fun s1 hpc1 hrun1 hlp1 _ => ?_
  rcases hlp1 with ⟨hsp1', _, hfp1', _, hx20_1', hx21_1', _⟩
  have hsp1 : s1.sp = sp := by simpa [wp_norm, arm64_norm, hsp] using hsp1'
  have hfp1 : s1.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfp] using hfp1'
  have hx20_1 : s1.readReg64 .x20 = sp + 9984#64 := by simpa [wp_norm, arm64_norm, hx20] using hx20_1'
  have hx21_1 : s1.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21] using hx21_1'
  have hdst : ((sp + 15808#64) ↦ₛ (sBytes ++ z)) =
      PolyMem (sp + 15808#64) (polyVecNat p0) ∗ PolyMem (sp + 16320#64) (polyVecNat p1) ∗
      PolyMem (sp + 16832#64) (polyVecNat p2) ∗ ((sp + 17344#64) ↦ₛ z) := by
    simpa only [sBytes,
      show (sp + 15808#64) + 512#64 = sp + 16320#64 by clear * -; bv_omega,
      show (sp + 15808#64) + 1024#64 = sp + 16832#64 by clear * -; bv_omega,
      show (sp + 15808#64) + 1536#64 = sp + 17344#64 by clear * -; bv_omega] using
      (poly3_z_eq_bytes (sp + 15808#64) (polyVecNat p0) (polyVecNat p1) (polyVecNat p2) z).symm
  have hsrc_sp : ((sp + 8416#64) ↦ₛ (sBytes ++ z)) =
      ((sp + 8416#64) ↦ₛ sBytes) ∗ ((sp + 9952#64) ↦ₛ z) := by
    have hs1536 : sBytes.length = 1536 := by simp [sBytes, vecRangeBytes_length]
    rw [pointsToBytes_append, hs1536]
    simp only [show (sp + 8416#64) + BitVec.ofNat 64 1536 = sp + 9952#64 by clear * -; bv_omega]
  have hm8416 : ((sp + 8416#64) ↦ₛ sBytes) ⊢ memRegion (sp + 8416#64) 1536 := by
    simpa [sBytes, vecRangeBytes_length] using pointsToBytes_entails_memRegion (sp + 8416#64) sBytes
  have hm17344 : ((sp + 17344#64) ↦ₛ z) ⊢ memRegion (sp + 17344#64) 32 := by
    simpa [hz] using pointsToBytes_entails_memRegion (sp + 17344#64) z
  have hs15744 : memRegion (sp + 15744#64) 64 =
      memRegion (sp + 15744#64) 32 ∗ memRegion (sp + 15776#64) 32 :=
    memRegion_split' (b' := sp + 15776#64) (n := 32) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (show ((sp + 15808#64) ↦ₛ (sBytes ++ z)) ∗
        ((sp + 8416#64) ↦ₛ (sBytes ++ z)) ∗ (memRegion (sp + 15744#64) 64 ∗
          (((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ∗ Rest)) ⊢
      memRegion (sp + 15744#64) 32 ∗ (memRegion (sp + 15776#64) 32 ∗
        (((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ∗
          memRegion (sp + 8416#64) 1536 ∗ ((sp + 9952#64) ↦ₛ z) ∗
          PolyMem (sp + 15808#64) (polyVecNat p0) ∗ PolyMem (sp + 16320#64) (polyVecNat p1) ∗
          PolyMem (sp + 16832#64) (polyVecNat p2) ∗ memRegion (sp + 17344#64) 32 ∗ Rest)) by
    rw [hdst, hsrc_sp, hs15744]
    exact entails_sub hm8416 (by sep_frame) (entails_sub hm17344 (by sep_frame) (by sep_frame))) ?_
  apply memRegion32_cells (sp + 15744#64); intro c0 c1 c2 c3
  refine SepWP.weaken_pre (show _ ∗ (memRegion (sp + 15776#64) 32 ∗ _) ⊢
      memRegion (sp + 15776#64) 32 ∗ (_ ∗ _) by sep_frame) ?_
  apply memRegion32_cells (sp + 15776#64); intro d0 d1 d2 d3
  refine SepWP.weaken_pre
    (P' := ((sp + 15744#64) ↦₆₄ c0) ∗ ((sp + 15752#64) ↦₆₄ c1) ∗
      ((sp + 15760#64) ↦₆₄ c2) ∗ ((sp + 15768#64) ↦₆₄ c3) ∗
      ((sp + 15776#64) ↦₆₄ d0) ∗ ((sp + 15784#64) ↦₆₄ d1) ∗
      ((sp + 15792#64) ↦₆₄ d2) ∗ ((sp + 15800#64) ↦₆₄ d3) ∗
      ((sp + 29024#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 0 64) ∗
      ((sp + 29032#64) ↦₆₄ (bytesToVecNat rho 0).extractLsb' 64 64) ∗
      ((sp + 29040#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 0 64) ∗
      ((sp + 29048#64) ↦₆₄ (bytesToVecNat rho 1).extractLsb' 64 64) ∗
      ((sp + 29056#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 0 64) ∗
      ((sp + 29064#64) ↦₆₄ (bytesToVecNat hPk 0).extractLsb' 64 64) ∗
      ((sp + 29072#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 0 64) ∗
      ((sp + 29080#64) ↦₆₄ (bytesToVecNat hPk 1).extractLsb' 64 64) ∗
      memRegion (sp + 8416#64) 1536 ∗ ((sp + 9952#64) ↦ₛ z) ∗
      PolyMem (sp + 15808#64) (polyVecNat p0) ∗ PolyMem (sp + 16320#64) (polyVecNat p1) ∗
      PolyMem (sp + 16832#64) (polyVecNat p2) ∗ memRegion (sp + 17344#64) 32 ∗ Rest)
    (by
      rw [← vec2_cells_eq_bytes (sp + 29024#64) hrho, ← vec2_cells_eq_bytes (sp + 29056#64) hhPk]
      simp only [bitvec64_add_add_fold]; sep_frame) ?_
  wp_steps 18
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨by simp [wp_norm, arm64_norm, hsp1], spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp1]) hchk,
      by simp [wp_norm, arm64_norm, hfp1],
      by simp [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm, hx21_1], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], ?_⟩
  have hm29024 : ((sp + 29024#64) ↦ₛ rho) ∗ ((sp + 29056#64) ↦ₛ hPk) ⊢
      memRegion (sp + 29024#64) 64 := by
    rw [memRegion_split' (b' := sp + 29056#64) (n := 32) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono (by simpa [hrho] using pointsToBytes_entails_memRegion (sp + 29024#64) rho)
      (by simpa [hhPk] using pointsToBytes_entails_memRegion (sp + 29056#64) hPk)
  rw [← vec2_cells_eq_bytes (sp + 29024#64) hrho, ← vec2_cells_eq_bytes (sp + 29056#64) hhPk] at hm29024
  simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate] at hm29024 ⊢
  rw [← vec2_cells_eq_bytes (sp + 15744#64) hrho, ← vec2_cells_eq_bytes (sp + 15776#64) hhPk]
  simp only [bitvec64_add_add_fold, BitVec.extractLsb'_0_64_eq_truncate]
  exact entails_sub hm29024 (by sep_frame) (by sep_frame)

theorem seg5_pack_s0 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v outPtr : BitVec 64) (p0 : Poly16) (hbnd0 : PolyBounded16 3328 p0)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 27328) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = sp + 15824#64)
    (hx10 : s.readReg64 .x10 = sp + 17376#64) (hx19 : s.readReg64 .x19 = x19v)
    (hx21 : s.readReg64 .x21 = outPtr)
    (hv0 : s.readVReg128 0#5 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27628) s
      (PolyMem (sp + 15808#64) (polyVecNat p0) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x20 = sp + 17376#64 ∧
        sf.readReg64 .x21 = outPtr ∧
        (Pf ⊢ (outPtr ↦ₛ ser12Prefix p0 16) ∗
          memRegion (sp + 15808#64) 512 ∗
          memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
          memRegion (sp + 27840#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine SepWP.weaken_pre (show PolyMem (sp + 15808#64) (polyVecNat p0) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 15808#64) (polyVecNat p0) ∗ _) by sep_frame) ?_
  refine sepWP_seq_cl hcl (post1 := fun sm Pm =>
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = fpVal ∧
      sm.readReg64 .x8 = 0#64 ∧ sm.readReg64 .x9 = sp + 15824#64 ∧
      sm.readReg64 .x10 = sp + 17376#64 ∧ sm.readReg64 .x19 = x19v ∧
      sm.readReg64 .x21 = outPtr ∧ sm.readVReg128 0#5 = dup8x16 3329#16 ∧
      Pm = (memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 15808#64) (polyVecNat p0) ∗
          memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest)))
    (mid := blkPl05.base + BitVec.ofNat 64 27376) ?_ ?_
  · refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 27328) hpc hrun hsp hspA ?_
    intro hrun0a _ _
    step_strQ_sp 17376 384 27328 27332 368 17744 3#5; step_strQ_sp 17376 384 27332 27336 352 17728 3#5
    step_strQ_sp 17376 384 27336 27340 336 17712 3#5; step_strQ_sp 17376 384 27340 27344 320 17696 3#5
    step_strQ_sp 17376 384 27344 27348 304 17680 3#5; step_strQ_sp 17376 384 27348 27352 288 17664 3#5
    step_strQ_sp 17376 384 27352 27356 272 17648 3#5; step_strQ_sp 17376 384 27356 27360 256 17632 3#5
    step_strQ_sp 17376 384 27360 27364 240 17616 3#5; step_strQ_sp 17376 384 27364 27368 224 17600 3#5
    step_strQ_sp 17376 384 27368 27372 208 17584 3#5; step_strQ_sp 17376 384 27372 27376 192 17568 3#5
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun0a])
      ⟨by simp [wp_norm, arm64_norm, hsp], spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp]) hchk,
        by simp [wp_norm, arm64_norm, hfp], by simp [wp_norm, arm64_norm, hx8],
        by simp [wp_norm, arm64_norm, hx9], by simp [wp_norm, arm64_norm, hx10],
        by simp [wp_norm, arm64_norm, hx19], by simp [wp_norm, arm64_norm, hx21],
        by simp [wp_norm, arm64_norm, hv0], rfl⟩
  rintro sm Pm hpcm hrunm hclm ⟨hspm, hspAm, hfpm, hx8m, hx9m, hx10m, hx19m, hx21m, hv0m, rfl⟩
  refine sepWP_seq_cl hclm (post1 := fun sm2 Pm2 =>
      sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.readReg64 .fp = fpVal ∧
      sm2.readReg64 .x8 = 0#64 ∧ sm2.readReg64 .x9 = sp + 15824#64 ∧
      sm2.readReg64 .x10 = sp + 17376#64 ∧ sm2.readReg64 .x19 = x19v ∧
      sm2.readReg64 .x21 = outPtr ∧ sm2.readVReg128 0#5 = dup8x16 3329#16 ∧
      Pm2 = (memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 15808#64) (polyVecNat p0) ∗
          memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest)))
    (mid := blkPl05.base + BitVec.ofNat 64 27424) ?_ ?_
  · refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 27376) hpcm hrunm hspm hspAm ?_
    intro hrun0b _ _
    step_strQ_sp 17376 384 27376 27380 176 17552 3#5; step_strQ_sp 17376 384 27380 27384 160 17536 3#5
    step_strQ_sp 17376 384 27384 27388 144 17520 3#5; step_strQ_sp 17376 384 27388 27392 128 17504 3#5
    step_strQ_sp 17376 384 27392 27396 112 17488 3#5; step_strQ_sp 17376 384 27396 27400 96 17472 3#5
    step_strQ_sp 17376 384 27400 27404 80 17456 3#5; step_strQ_sp 17376 384 27404 27408 64 17440 3#5
    step_strQ_sp 17376 384 27408 27412 48 17424 3#5; step_strQ_sp 17376 384 27412 27416 32 17408 3#5
    step_strQ_sp 17376 384 27416 27420 16 17392 3#5; step_strQ_sp 17376 384 27420 27424 0 17376 3#5
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun0b])
      ⟨by simp [wp_norm, arm64_norm, hspm], spAligned_of_chk (by simp [wp_norm, arm64_norm, hspm]) hchk,
        by simp [wp_norm, arm64_norm, hfpm], by simp [wp_norm, arm64_norm, hx8m],
        by simp [wp_norm, arm64_norm, hx9m], by simp [wp_norm, arm64_norm, hx10m],
        by simp [wp_norm, arm64_norm, hx19m], by simp [wp_norm, arm64_norm, hx21m],
        by simp [wp_norm, arm64_norm, hv0m], rfl⟩
  rintro sm2 Pm2 hpcm2 hrun0 hcl0 ⟨hspm2, _, hfpm2, hx8m2, hx9m2, hx10m2, hx19m2, hx21m2, hv0m2, rfl⟩
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 15808#64) (polyVecNat p0) ∗
          memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest) ⊢
      PolyMem (sp + 15808#64) (polyVecNat p0) ∗ memRegion (sp + 17376#64) 384 ∗
        (memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop7 hb (sp + 15808#64) (sp + 17376#64) p0 hbnd0 _ _ hpcm2 hrun0
    hx8m2 (by rw [hx9m2]; clear * -; bv_omega) hx10m2 hv0m2) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hlp1, hP1⟩
  rcases hlp1 with ⟨hsp1', _, hfp1', hx19_1', _, hx21_1', _⟩
  have hsp1 : s1.sp = sp := by simpa [wp_norm, arm64_norm, hspm2] using hsp1'
  have hfp1 : s1.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfpm2] using hfp1'
  have hx19_1 : s1.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19m2] using hx19_1'
  have hx21_1 : s1.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21m2] using hx21_1'
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 15808#64) (polyVecNat p0) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion (sp + 27840#64) 384 ∗ memRegion outPtr 384 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 17376#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion outPtr 384 ∗ PolyMem (sp + 15808#64) (polyVecNat p0) ∗ Rest) by sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 17376#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p0 16) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  rcases hlp2 with ⟨hsp2', _, hfp2', hx19_2', hx20_2', hx21_2', _⟩
  have hsp2 : s2.sp = sp := by simpa [wp_norm, arm64_norm, hsp1] using hsp2'
  have hx19_2 : s2.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19_1] using hx19_2'
  have hx20_2 : s2.readReg64 .x20 = sp + 17376#64 := by simpa [wp_norm, arm64_norm, hsp1] using hx20_2'
  have hx21_2 : s2.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21_1] using hx21_2'
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p0 16) ∗
        (memRegion outPtr 384 ∗ PolyMem (sp + 15808#64) (polyVecNat p0) ∗ Rest) ⊢
      memRegion outPtr 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ∗
        (((sp + 17376#64) ↦ₛ ser12Prefix p0 16) ∗
          PolyMem (sp + 15808#64) (polyVecNat p0) ∗ Rest) by sep_frame) ?_
  wp_steps 5
  refine call_bytes_memcpy (dst := outPtr) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p0 16) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  rcases hlpf with ⟨hspsf', _, hfpsf', hx19sf', hx20sf', hx21sf', _⟩
  have hsp_sf : sf.sp = sp := by simpa [wp_norm, arm64_norm, hsp2] using hspsf'
  have hm15808 := polyMem_entails_memRegion512 (sp + 15808#64) (polyVecNat p0)
  have hm17376 : ((sp + 17376#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + BitVec.ofNat 64 17376) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 17376#64) (ser12Prefix p0 16)
  have hm27840 : ((sp + 27840#64) ↦ₛ ser12Prefix p0 16) ⊢ memRegion (sp + 27840#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p0 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [wp_norm, arm64_norm, hfp2', hfp1] using hfpsf',
    by simpa [wp_norm, arm64_norm, hx19_2] using hx19sf',
    by simpa [wp_norm, arm64_norm, hx20_2] using hx20sf',
    by simpa [wp_norm, arm64_norm, hx21_2] using hx21sf',
    entails_sub hm15808 (by sep_frame)
      (entails_sub hm17376 (by sep_frame)
        (entails_sub hm27840 (by sep_frame) (by sep_frame)))⟩

theorem seg5_pack_s1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp fpVal x19v outPtr : BitVec 64) (p1 : Poly16) (hbnd1 : PolyBounded16 3328 p1)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = b + BitVec.ofNat 64 27628) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = outPtr)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + BitVec.ofNat 64 27960) s
      (PolyMem (sp + 16320#64) (polyVecNat p1) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        memRegion (sp + 27840#64) 384 ∗ memRegion (outPtr + 384#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = x19v ∧ sf.readReg64 .x20 = sp + 17376#64 ∧
        sf.readReg64 .x21 = outPtr ∧
        (Pf ⊢ ((outPtr + 384#64) ↦ₛ ser12Prefix p1 16) ∗
          memRegion (sp + 16320#64) 512 ∗
          memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
          memRegion (sp + 27840#64) 384 ∗ Rest)) := by
  subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine mlkemMultiLib.seq_codeLoaded (mid := blkPl05.base + BitVec.ofNat 64 27756) hcl ?_
  wp_steps 8
  refine SepWP.weaken_pre (show PolyMem (sp + 16320#64) (polyVecNat p1) ∗
        memRegion (sp + BitVec.ofNat 64 17376) 384 ∗ _ ⊢
      memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 16320#64) (polyVecNat p1) ∗ _) by sep_frame) ?_
  refine enter_mem_block sp (blkPl05.base + BitVec.ofNat 64 27660)
    (by wp_norm_lhs) (by simp [hrun]) (by simp [wp_norm, arm64_norm, hsp])
    (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp]) hchk) ?_
  intro hrun0 _ _
  step_strQ_sp 17376 384 27660 27664 368 17744 1#5; step_strQ_sp 17376 384 27664 27668 352 17728 1#5
  step_strQ_sp 17376 384 27668 27672 336 17712 1#5; step_strQ_sp 17376 384 27672 27676 320 17696 1#5
  step_strQ_sp 17376 384 27676 27680 304 17680 1#5; step_strQ_sp 17376 384 27680 27684 288 17664 1#5
  step_strQ_sp 17376 384 27684 27688 272 17648 1#5; step_strQ_sp 17376 384 27688 27692 256 17632 1#5
  step_strQ_sp 17376 384 27692 27696 240 17616 1#5; step_strQ_sp 17376 384 27696 27700 224 17600 1#5
  step_strQ_sp 17376 384 27700 27704 208 17584 1#5; step_strQ_sp 17376 384 27704 27708 192 17568 1#5
  step_strQ_sp 17376 384 27708 27712 176 17552 1#5; step_strQ_sp 17376 384 27712 27716 160 17536 1#5
  step_strQ_sp 17376 384 27716 27720 144 17520 1#5; step_strQ_sp 17376 384 27720 27724 128 17504 1#5
  step_strQ_sp 17376 384 27724 27728 112 17488 1#5; step_strQ_sp 17376 384 27728 27732 96 17472 1#5
  step_strQ_sp 17376 384 27732 27736 80 17456 1#5; step_strQ_sp 17376 384 27736 27740 64 17440 1#5
  step_strQ_sp 17376 384 27740 27744 48 17424 1#5; step_strQ_sp 17376 384 27744 27748 32 17408 1#5
  step_strQ_sp 17376 384 27748 27752 16 17392 1#5; step_strQ_sp 17376 384 27752 27756 0 17376 1#5
  apply SepWP.done; · rfl
  · exact hrun0
  intro hcl0
  refine SepWP.weaken_pre (show memRegion (sp + BitVec.ofNat 64 17376) 384 ∗
        (PolyMem (sp + 16320#64) (polyVecNat p1) ∗
          memRegion (sp + 27840#64) 384 ∗ memRegion (outPtr + 384#64) 384 ∗ Rest) ⊢
      PolyMem (sp + 16320#64) (polyVecNat p1) ∗ memRegion (sp + 17376#64) 384 ∗
        (memRegion (sp + 27840#64) 384 ∗ memRegion (outPtr + 384#64) 384 ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_cl hcl0 (seg5_loop8 hb (sp + 16320#64) (sp + 17376#64) p1 hbnd1 _ _ rfl hrun0
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
  refine SepWP.weaken_pre (Entails.trans hP1 (show PolyMem (sp + 16320#64) (polyVecNat p1) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (sp + 27840#64) 384 ∗ memRegion (outPtr + 384#64) 384 ∗ Rest) ⊢
      memRegion (sp + 27840#64) 384 ∗ ((sp + 17376#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (outPtr + 384#64) 384 ∗ PolyMem (sp + 16320#64) (polyVecNat p1) ∗ Rest) by
    sep_frame)) ?_
  wp_steps 8
  refine call_bytes_memcpy (dst := sp + 27840#64) (src := sp + 17376#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun1]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp1]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p1 16) (by decide) hcl1
    fun s2 hpc2 hrun2 hlp2 hcl2 => ?_
  rcases hlp2 with ⟨hsp2', _, hfp2', hx19_2', hx20_2', hx21_2', _⟩
  have hsp2 : s2.sp = sp := by simpa [wp_norm, arm64_norm, hsp1] using hsp2'
  have hfp2 : s2.readReg64 .fp = fpVal := by simpa [wp_norm, arm64_norm, hfp1] using hfp2'
  have hx19_2 : s2.readReg64 .x19 = x19v := by simpa [wp_norm, arm64_norm, hx19_1] using hx19_2'
  have hx20_2 : s2.readReg64 .x20 = sp + 17376#64 := by simpa [wp_norm, arm64_norm, hsp1] using hx20_2'
  have hx21_2 : s2.readReg64 .x21 = outPtr := by simpa [wp_norm, arm64_norm, hx21_1] using hx21_2'
  refine SepWP.weaken_pre (show ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        ((sp + 17376#64) ↦ₛ ser12Prefix p1 16) ∗
        (memRegion (outPtr + 384#64) 384 ∗ PolyMem (sp + 16320#64) (polyVecNat p1) ∗ Rest) ⊢
      memRegion (outPtr + 384#64) 384 ∗ ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ∗
        (((sp + 17376#64) ↦ₛ ser12Prefix p1 16) ∗
          PolyMem (sp + 16320#64) (polyVecNat p1) ∗ Rest) by sep_frame) ?_
  wp_steps 5
  refine call_bytes_memcpy (dst := outPtr + 384#64) (src := sp + 27840#64) (n := 384)
    (by wp_norm_lhs) (by simp [hrun2]) (spAligned_of_chk (by simp [wp_norm, arm64_norm, hsp2]) hchk)
    (by wp_norm_lhs) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by wp_norm_lhs)
    (ser12Prefix_length p1 16) (by decide) hcl2
    fun sf hpcsf hrunsf hlpf _ => ?_
  rcases hlpf with ⟨hspsf', _, hfpsf', hx19sf', hx20sf', hx21sf', _⟩
  have hsp_sf : sf.sp = sp := by simpa [wp_norm, arm64_norm, hsp2] using hspsf'
  have hm16320 := polyMem_entails_memRegion512 (sp + 16320#64) (polyVecNat p1)
  have hm17376 : ((sp + 17376#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + BitVec.ofNat 64 17376) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 17376#64) (ser12Prefix p1 16)
  have hm27840 : ((sp + 27840#64) ↦ₛ ser12Prefix p1 16) ⊢ memRegion (sp + 27840#64) 384 := by
    simpa [ser12Prefix_length] using pointsToBytes_entails_memRegion (sp + 27840#64) (ser12Prefix p1 16)
  refine SepWP.done hpcsf hrunsf ⟨hsp_sf, spAligned_of_chk hsp_sf hchk,
    by simpa [wp_norm, arm64_norm, hfp2] using hfpsf',
    by simpa [wp_norm, arm64_norm, hx19_2] using hx19sf',
    by simpa [wp_norm, arm64_norm, hx20_2] using hx20sf',
    by simpa [wp_norm, arm64_norm, hx21_2] using hx21sf',
    entails_sub hm16320 (by sep_frame)
      (entails_sub hm17376 (by sep_frame)
        (entails_sub hm27840 (by sep_frame) (by sep_frame)))⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg5PackA
