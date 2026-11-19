/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure

/-!
# `kyber::encapsulate` (`B07`) — Segment 3 Entry Ops & `rHat` SWAR `cbd2` (`+0x3d0c .. +0x4264`)

1. `PublicKeyStateAt` (`10272` B: `Âᵀ` + `tHat[0..3]` + 32 zero bytes) byte-list bridge.
2. `seg3_entry_ops` (`+0x3d0c → +0x3d78`): copies `PublicKeyStateAt` from `sp + 12832` to `sp + 2560`,
   zeroes `ct1` (`1568` B) and `rHat` (`2048` B), and stages `coins ++ [0#8]` (`33` B) at `sp + 24672`.
3. `seg3_cbd2_rhat_loop` (`+0x4134 → +0x4264`): zeroes `[sp + 12832, sp + 13344)` and runs 32 SWAR
   `cbd2` iterations into `PolyMem (sp + 12832#64) (polyVecNat (neonCbd2Poly16 prf))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk28 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord cbd2SwarSum neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq
  sepWP_elim_byte setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64
  step_bCond_not_taken step_bCond_taken truncate32_zext64 ubfx2_w32_norm
  vec128At_eq_halfRangeMem8 vec2_bytesToVecNat_eq vecRangeBytes_zero vecRangeMem_focus
  wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 (
  ATransMem aTransPoly16)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x3d0c → 0x3d74, 0x4134 → 0x4260]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

/-! ## 1. `PublicKeyStateAt` (`10272` B: `Âᵀ` + `tHat[0..3]` + 32 Zero Bytes) -/

@[expose] noncomputable def ATransRowAt (ptr : BitVec 64) (rho : List (BitVec 8)) (row : Nat) :
    SepProp :=
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row)) (polyVecNat (aTransPoly16 rho row 0)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 512)) (polyVecNat (aTransPoly16 rho row 1)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 1024)) (polyVecNat (aTransPoly16 rho row 2)) ∗
  PolyMem (ptr + BitVec.ofNat 64 (2048 * row + 1536)) (polyVecNat (aTransPoly16 rho row 3))

@[expose] noncomputable def ATransAt (ptr : BitVec 64) (rho : List (BitVec 8)) : SepProp :=
  ATransRowAt ptr rho 0 ∗ ATransRowAt ptr rho 1 ∗ ATransRowAt ptr rho 2 ∗ ATransRowAt ptr rho 3

@[expose] noncomputable def PublicKeyStateAt (ptr : BitVec 64) (pk : List (BitVec 8)) : SepProp :=
  ATransAt ptr (pkRho pk) ∗
  PolyMem (ptr + 8192#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
  PolyMem (ptr + 8704#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
  PolyMem (ptr + 9216#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
  PolyMem (ptr + 9728#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
  ((ptr + BitVec.ofNat 64 10240) ↦ₛ List.replicate 32 0#8)

theorem aTransAt_12832_eq (sp : BitVec 64) (rho : List (BitVec 8)) :
    ATransAt (sp + 12832#64) rho = ATransMem sp rho := rfl

private noncomputable def aTransRowBytes (rho : List (BitVec 8)) (row : Nat) : List (BitVec 8) :=
  vecRangeBytes 32 (polyVecNat (aTransPoly16 rho row 0)) ++
  (vecRangeBytes 32 (polyVecNat (aTransPoly16 rho row 1)) ++
   (vecRangeBytes 32 (polyVecNat (aTransPoly16 rho row 2)) ++
    vecRangeBytes 32 (polyVecNat (aTransPoly16 rho row 3))))

private theorem aTransRowBytes_length (rho : List (BitVec 8)) (row : Nat) :
    (aTransRowBytes rho row).length = 2048 := by
  simp [aTransRowBytes, vecRangeBytes_length]

private theorem aTransRowAt_eq_pointsToBytes (ptr : BitVec 64) (rho : List (BitVec 8)) (row : Nat)
    (hrow : row < 4) :
    ATransRowAt ptr rho row =
      ((ptr + BitVec.ofNat 64 (2048 * row)) ↦ₛ aTransRowBytes rho row) := by
  unfold ATransRowAt aTransRowBytes PolyMem
  have h123 :
      ptr + BitVec.ofNat 64 (2048 * row) + BitVec.ofNat 64 512 =
        ptr + BitVec.ofNat 64 (2048 * row + 512) ∧
      ptr + BitVec.ofNat 64 (2048 * row + 512) + BitVec.ofNat 64 512 =
        ptr + BitVec.ofNat 64 (2048 * row + 1024) ∧
      ptr + BitVec.ofNat 64 (2048 * row + 1024) + BitVec.ofNat 64 512 =
        ptr + BitVec.ofNat 64 (2048 * row + 1536) := by
    rcases row with _ | _ | _ | _ | row
    · exact ⟨by bv_omega, by bv_omega, by bv_omega⟩
    · exact ⟨by bv_omega, by bv_omega, by bv_omega⟩
    · exact ⟨by bv_omega, by bv_omega, by bv_omega⟩
    · exact ⟨by bv_omega, by bv_omega, by bv_omega⟩
    · omega
  rcases h123 with ⟨h1, h2, h3⟩
  simp only [vecRangeMem_eq_pointsToBytes, pointsToBytes_append, vecRangeBytes_length,
    show BitVec.ofNat 64 (16 * 32) = 512#64 from rfl, h1, h2, h3]

noncomputable def pkStateBytes (pk : List (BitVec 8)) : List (BitVec 8) :=
  let rho := pkRho pk
  aTransRowBytes rho 0 ++
  (aTransRowBytes rho 1 ++
   (aTransRowBytes rho 2 ++
    (aTransRowBytes rho 3 ++
     (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk0 pk))) ++
      (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk1 pk))) ++
       (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk2 pk))) ++
        (vecRangeBytes 32 (polyVecNat (tHatModPoly16 (pkEk3 pk))) ++
         List.replicate 32 0#8)))))))

theorem pkStateBytes_length (pk : List (BitVec 8)) : (pkStateBytes pk).length = 10272 := by
  simp [pkStateBytes, aTransRowBytes_length, vecRangeBytes_length]

theorem publicKeyStateAt_eq_pointsToBytes (ptr : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt ptr pk = (ptr ↦ₛ pkStateBytes pk) := by
  unfold PublicKeyStateAt ATransAt pkStateBytes
  rw [aTransRowAt_eq_pointsToBytes ptr _ 0 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 1 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 2 (by decide),
    aTransRowAt_eq_pointsToBytes ptr _ 3 (by decide)]
  simp only [PolyMem, vecRangeMem_eq_pointsToBytes, pointsToBytes_append,
    aTransRowBytes_length, vecRangeBytes_length, sepConj_assoc,
    show ptr + BitVec.ofNat 64 (2048 * 0) = ptr by bv_omega,
    show ptr + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 1) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 1) + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 2) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 2) + BitVec.ofNat 64 2048 = ptr + BitVec.ofNat 64 (2048 * 3) by bv_omega,
    show ptr + BitVec.ofNat 64 (2048 * 3) + BitVec.ofNat 64 2048 = ptr + 8192#64 by bv_omega,
    show ptr + 8192#64 + BitVec.ofNat 64 (16 * 32) = ptr + 8704#64 by bv_omega,
    show ptr + 8704#64 + BitVec.ofNat 64 (16 * 32) = ptr + 9216#64 by bv_omega,
    show ptr + 9216#64 + BitVec.ofNat 64 (16 * 32) = ptr + 9728#64 by bv_omega,
    show ptr + 9728#64 + BitVec.ofNat 64 (16 * 32) = ptr + BitVec.ofNat 64 10240 by bv_omega]

attribute [local irreducible] PublicKeyStateAt pkStateBytes

/-! ## 2. `seg3_entry_ops` (`+0x3d0c → +0x3d78`) -/

@[simp, arm64_norm, wp_norm] abbrev off3d0c : BitVec 64 := BitVec.ofNat 64 15628
@[simp, arm64_norm, wp_norm] abbrev off3d2c : BitVec 64 := BitVec.ofNat 64 15660
@[simp, arm64_norm, wp_norm] abbrev off3d40 : BitVec 64 := BitVec.ofNat 64 15680
@[simp, arm64_norm, wp_norm] abbrev off3d78 : BitVec 64 := BitVec.ofNat 64 15736

private theorem seg3_entry_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (pk : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off3d0c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off3d40) s
      (memRegion (sp + 2560#64) 10272 ∗
       PublicKeyStateAt (sp + 12832#64) pk ∗
       memRegion (sp + 23104#64) 1568 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 12832#64 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ PublicKeyStateAt (sp + 2560#64) pk ∗
          memRegion (sp + 12832#64) 10272 ∗
          memRegion (sp + 23104#64) 1568 ∗
          stackAt sp 1136 ∗ Rest)) := by
  have _ : b = blkPl07.base := hb
  subst hbase
  have hpks_len := pkStateBytes_length pk
  have hstep1 : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + off3d2c) s
      (memRegion (sp + 2560#64) 10272 ∗ PublicKeyStateAt (sp + 12832#64) pk ∗
        memRegion (sp + 23104#64) 1568 ∗ stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        s1.readReg64 .x20 = sp + 12832#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        (P1 ⊢ PublicKeyStateAt (sp + 2560#64) pk ∗
          memRegion (sp + 12832#64) 10272 ∗
          memRegion (sp + 23104#64) 1568 ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [publicKeyStateAt_eq_pointsToBytes (sp + 12832#64) pk, ← hpks_len]
    wp_steps 7
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk28_memcpy_ok (sp + 2560#64, sp + 12832#64, pkStateBytes pk)
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
        Eq.trans ‹_› rfl, Eq.trans ‹_› (by bv_omega), ‹_›, ‹_›, ?_⟩
    rw [← publicKeyStateAt_eq_pointsToBytes (sp + 2560#64) pk]
    have hsrc : ((sp + 12832#64) ↦ₛ pkStateBytes pk) ⊢ memRegion (sp + 12832#64) 10272 := by
      have h := pointsToBytes_entails_memRegion (sp + 12832#64) (pkStateBytes pk)
      rwa [hpks_len] at h
    exact entails_sub hsrc (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ _)
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl hstep1 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hcl1, hsp1, hspA1, hx19_1, hx20_1, hx22_1, hfp1, hP1⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have _ := hpc1
  refine SepWP.weaken_pre hP1 ?_
  wp_steps 4
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 23104#64, 0#8, (1568 : Nat))
  refine SepWP.done hpc_sf hrun_sf
    ⟨‹_›, hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
      Eq.trans ‹_› hx19_1, Eq.trans ‹_› hx20_1, Eq.trans ‹_› hx22_1, Eq.trans ‹_› hfp1, ?_⟩
  have hm1568 : ((sp + 23104#64) ↦ₛ List.replicate 1568 0#8) ⊢ memRegion (sp + 23104#64) 1568 := by
    simpa only [List.length_replicate] using
      pointsToBytes_entails_memRegion (sp + 23104#64) (List.replicate 1568 0#8)
  exact entails_sub hm1568 (by sep_frame) (by sep_frame)

section
attribute [local irreducible] Vec128At

private theorem seg3_entry_step2 [MlKemPlacement]
    (_hb : MlKemBase blkPl07 blkPl07.base)
    (s1 : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (P1 : SepProp) (rx22 rfp : BitVec 64)
    (hh_split : ((sp + 2496#64) ↦ₛ hashed) =
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗ ((sp + 2528#64) ↦ₛ hashed.drop 32))
    (hcoins_len : (hashed.drop 32).length = 32)
    (hpc1 : s1.pc = blkPl07.base + off3d40) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp) (hspA1 : s1.spAligned = true)
    (hx19_1 : s1.readReg64 .x19 = 0x55555555#64)
    (hx20_1 : s1.readReg64 .x20 = sp + 12832#64)
    (hx22_1 : s1.readReg64 .x22 = rx22) (hfp1 : s1.readReg64 .fp = rfp)
    (hP1 : P1 ⊢ PublicKeyStateAt (sp + 2560#64) pk ∗ memRegion (sp + 12832#64) 10272 ∗
      memRegion (sp + 23104#64) 1568 ∗ stackAt sp 1136 ∗
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 24672#64) 33 ∗
        memRegion (sp + 24720#64) 2048 ∗ Rest)) :
    let coins := hashed.drop 32
    SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + BitVec.ofNat 64 15732) s1 P1
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x0 = sp + 24720#64 ∧ s2.readReg64 .x1 = 0#64 ∧ s2.readReg64 .x2 = 2048#64 ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 12832#64 ∧
        s2.readReg64 .x21 = sp + 24720#64 ∧ s2.readReg64 .x22 = rx22 ∧
        s2.readReg64 .fp = rfp ∧
        (P2 ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 2560#64) pk ∗
          memRegion (sp + 12832#64) 10272 ∗ memRegion (sp + 23104#64) 1568 ∗
          ((sp + 24672#64) ↦ₛ coins) ∗ ((sp + 24704#64) ↦₈ 0#8) ∗
          memRegion (sp + 24720#64) 2048 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro coins
  subst hsp1
  refine SepWP.weaken_pre hP1 ?_
  rw [memRegion_split' (b := s1.sp + 24672#64) (b' := s1.sp + 24688#64) (n := 16) (k := (17 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := s1.sp + 24688#64) (b' := s1.sp + 24704#64) (n := 16) (k := (1 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 1 (s1.sp + 24672#64) (by decide) (by sep_focus); intro vc0
  apply SepWP.of_memRegion_vecRangeMem 1 (s1.sp + 24688#64) (by decide) (by sep_focus); intro vc1
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := s1.sp + 24704#64)); intro b0
  rw [hh_split, ← vec2_bytesToVecNat_eq (s1.sp + 2528#64) hcoins_len]
  wp_steps 3
  refine step_ldpQ128 (wb := none) (ea := s1.sp + 2528#64) (ea16 := s1.sp + 2528#64 + 16#64)
    (v1 := bytesToVecNat coins 0) (v2 := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.left (SepLoad128.vec128At rfl)))))))))))
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.right (SepLoad128.vec128At rfl)))))))))))
    (by wp_norm_lhs) ?_
  wp_steps 6
  have hal_sp1 : (s1.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hspA1
  refine step_strQ128 (wb := none) (ea := s1.sp + 24672#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hal_sp1])
    (by simp [evalAddrMode]) rfl
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl))))
    (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := s1.sp + 24688#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hal_sp1])
    (by simp [evalAddrMode]) rfl
    (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
    (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨by simp, spAligned_of_sp_eq hspA1 rfl (by simp),
      by simp, by simp, by simp, by simp [hx19_1], by simp [hx20_1],
      by simp, by simp [hx22_1], by simp [hfp1], ?_⟩
  rw [vec2_bytesToVecNat_eq (s1.sp + 2528#64) hcoins_len, ← hh_split]
  have hc24672 : Vec128At (s1.sp + 24672#64) (bytesToVecNat coins 0) ∗
      Vec128At (s1.sp + 24688#64) (bytesToVecNat coins 1) = ((s1.sp + 24672#64) ↦ₛ coins) := by
    simpa [show s1.sp + 24672#64 + 16#64 = s1.sp + 24688#64 by bv_omega] using
      vec2_bytesToVecNat_eq (s1.sp + 24672#64) hcoins_len
  exact entails_sub (Entails.of_eq hc24672) (by sep_frame) (by sep_frame)

end

theorem seg3_entry_ops [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off3d0c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let coins := hashed.drop 32
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off3d78) s
      (((sp + 2496#64) ↦ₛ hashed) ∗
       memRegion (sp + 2560#64) 10272 ∗
       PublicKeyStateAt (sp + 12832#64) pk ∗
       memRegion (sp + 23104#64) 1568 ∗
       memRegion (sp + 24672#64) 33 ∗
       memRegion (sp + 24720#64) 2048 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 12832#64 ∧
        sm.readReg64 .x21 = sp + 24720#64 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗
          PublicKeyStateAt (sp + 2560#64) pk ∗
          memRegion (sp + 12832#64) 10272 ∗
          memRegion (sp + 23104#64) 1568 ∗
          ((sp + 24672#64) ↦ₛ coins) ∗
          ((sp + 24704#64) ↦₈ 0#8) ∗
          PolyMem (sp + 24720#64) (fun _ => 0#128) ∗
          PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
          PolyMem (sp + 25744#64) (fun _ => 0#128) ∗
          PolyMem (sp + 26256#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins
  have _ : b = blkPl07.base := hb
  subst hbase
  have htake_len : (hashed.take 32).length = 32 := by simp [hh]
  have hcoins_len : coins.length = 32 := by simp [coins, hh]
  have hh_split : ((sp + 2496#64) ↦ₛ hashed) =
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗ ((sp + 2528#64) ↦ₛ coins) := by
    conv_lhs => rw [← List.take_append_drop 32 hashed]
    rw [pointsToBytes_append, htake_len,
      show sp + 2496#64 + BitVec.ofNat 64 32 = sp + 2528#64 by bv_omega]
  refine SepWP.weaken_pre (by sep_frame :
      ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 2560#64) 10272 ∗
        PublicKeyStateAt (sp + 12832#64) pk ∗ memRegion (sp + 23104#64) 1568 ∗
        memRegion (sp + 24672#64) 33 ∗ memRegion (sp + 24720#64) 2048 ∗ stackAt sp 1136 ∗ Rest ⊢
      memRegion (sp + 2560#64) 10272 ∗ PublicKeyStateAt (sp + 12832#64) pk ∗
        memRegion (sp + 23104#64) 1568 ∗ stackAt sp 1136 ∗
        (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 24672#64) 33 ∗
          memRegion (sp + 24720#64) 2048 ∗ Rest)) ?_
  refine SepWP.seq (seg3_entry_a hb rfl s sp pk _ hpc hrun hsp hspA hcl) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hcl1, hsp1, hspA1, hx19_1, hx20_1, hx22_1, hfp1, hP1⟩
  have hstep2 := seg3_entry_step2 hb s1 sp pk hashed Rest P1 (s.readReg64 .x22) (s.readReg64 .fp)
    hh_split hcoins_len hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx22_1 hfp1 hP1
  refine SepWP.seq
    (SepWP.mono_frozen (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ _)
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl1 hstep2 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hcl2, hsp2, hspA2, hx0_2, hx1_2, hx2_2, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hP2⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem := hcl2
  have _ := hpc2
  refine SepWP.weaken_pre hP2 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 24720#64, 0#8, (2048 : Nat))
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp2, spAligned_of_sp_eq hspA2 hsp2 (hsp_sf.trans hsp2),
      Eq.trans ‹_› hx19_2, Eq.trans ‹_› hx20_2, Eq.trans ‹_› hx21_2,
      Eq.trans ‹_› hx22_2, Eq.trans ‹_› hfp2, ?_⟩
  have hz4 : ((sp + 24720#64) ↦ₛ List.replicate 2048 0#8) =
      PolyMem (sp + 24720#64) (fun _ => 0#128) ∗
      PolyMem (sp + 25232#64) (fun _ => 0#128) ∗
      PolyMem (sp + 25744#64) (fun _ => 0#128) ∗
      PolyMem (sp + 26256#64) (fun _ => 0#128) := by
    have hrep : List.replicate 2048 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++
         (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128))) := by
      rw [vecRangeBytes_zero 32, show (2048 : Nat) = 512 + (512 + (512 + 512)) from rfl,
        List.replicate_add, List.replicate_add, List.replicate_add]
    rw [hrep, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp [PolyMem,
      show sp + 24720#64 + BitVec.ofNat 64 (16 * 32) = sp + 25232#64 by bv_omega,
      show sp + 25232#64 + BitVec.ofNat 64 (16 * 32) = sp + 25744#64 by bv_omega,
      show sp + 25744#64 + BitVec.ofNat 64 (16 * 32) = sp + 26256#64 by bv_omega]
  rw [hz4]
  sep_frame

/-! ## 3. `rHat` Scratch Zero & SWAR `cbd2` Loop (`+0x4134 → +0x4264`) -/

attribute [local irreducible] blkPC07

@[simp, arm64_norm, wp_norm] abbrev offRhatCbdStart : BitVec 64 := BitVec.ofNat 64 16692
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdBody  : BitVec 64 := BitVec.ofNat 64 16836
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdBr    : BitVec 64 := BitVec.ofNat 64 16992
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdEnd   : BitVec 64 := BitVec.ofNat 64 16996

local macro "step_strQ12832 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg3_cbd2_rhat_zero [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offRhatCbdBody) s
      (memRegion (sp + 12832#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x6 = 0#64 ∧ s1.readReg64 .x7 = s.readReg64 .x7 ∧
        s1.readReg64 .x8 = s.readReg64 .x7 ∧ s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x10 ∧
        s1.readReg64 .x12 = s.readReg64 .x12 ∧ s1.readReg64 .x13 = s.readReg64 .x13 ∧
        s1.readReg64 .x14 = s.readReg64 .x14 ∧ s1.readReg64 .x15 = s.readReg64 .x15 ∧
        s1.readReg64 .x16 = s.readReg64 .x16 ∧ s1.readReg64 .x17 = s.readReg64 .x17 ∧
        s1.readReg64 .x18 = s.readReg64 .x18 ∧ s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 12832#64) 512 ∗ Rest)) := by
  have _ : b = blkPl07.base := hb
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 12832#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 12832#64) f = PolyMem (sp + 12832#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ12832 31; step_strQ12832 30; step_strQ12832 29; step_strQ12832 28
  step_strQ12832 27; step_strQ12832 26; step_strQ12832 25; step_strQ12832 24
  step_strQ12832 23; step_strQ12832 22; step_strQ12832 21; step_strQ12832 20
  step_strQ12832 19; step_strQ12832 18; step_strQ12832 17; step_strQ12832 16
  step_strQ12832 15; step_strQ12832 14; step_strQ12832 13; step_strQ12832 12
  step_strQ12832 11; step_strQ12832 10; step_strQ12832 9;  step_strQ12832 8
  step_strQ12832 7;  step_strQ12832 6;  step_strQ12832 5;  step_strQ12832 4
  step_strQ12832 3;  step_strQ12832 2;  step_strQ12832 1;  step_strQ12832 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_cbd_strh " cellPtr:ident hx20Id:term:arg hx6Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx20Id:term, $hx6Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg3_cbd2_rhat_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdBody) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if k < 31 then b + offRhatCbdBody else b + offRhatCbdEnd) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x6 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x7 = s.readReg64 .x7 ∧
        s'.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = dstPtr ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest)) := by
  subst hbase
  obtain ⟨Fk, hsplit, hupd⟩ := vecRangeMem_focus hk dstPtr f
  let cellPtr := dstPtr + BitVec.ofNat 64 (16 * k)
  let w := readU32LE prf k
  rw [hsplit, vec128At_eq_halfRangeMem8 cellPtr (f k),
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗
        (HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗ Fk) ∗ Rest =
      HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest by
      simp only [sepConj_assoc]; rw [sepConj_left_comm (WordRangeMem 32 prfPtr (readU32LE prf))]]
  refine SepWP.step_ldur32 (wb := none) (ea := prfPtr + BitVec.ofNat 64 (4 * k)) (v := w)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_cbd_strh cellPtr hx20 hx6 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx6 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx6 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx20 hx6 6 (cbd2CoeffFromWord w 6)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  have hmem_eq : ∀ hFin : Nat → BitVec 16,
      (∀ j (hj : j < 8), hFin j = cbd2CoeffFromWord w ⟨j, hj⟩) →
      HalfRangeMem 8 cellPtr hFin ∗ WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest := by
    intro hFin hhFin
    rw [halfRangeMem8_cbd2_eq cellPtr prf k hk hFin hhFin,
      sepConj_left_comm (Vec128At cellPtr _), ← sepConj_assoc (Vec128At cellPtr _) Fk Rest,
      hupd]
  by_cases hk31 : k < 31
  · simp only [hk31, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl07.base + offRhatCbdBody)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offRhatCbdBr, offRhatCbdBody]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega, by simp,
        by simp; clear * -; bv_omega, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl07.base + offRhatCbdEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offRhatCbdBr, offRhatCbdEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp,
        by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg3_cbd2_rhat_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offRhatCbdBody else b + offRhatCbdEnd) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x6 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + offRhatCbdEnd) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
          s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
          s'.readReg64 .x7 = s.readReg64 .x7 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
          s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
          s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
          s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = dstPtr ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest))
  | 0, k, hsum, s, f, hf, hpc, hrun, hsp, hspA, _, _, hx19, hx20 => by
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hx19, hx20, rfl, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | rem + 1, k, hsum, s, f, hf, hpc, hrun, hsp, hspA, hx6, hx8, hx19, hx20 => by
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + offRhatCbdBody else b + offRhatCbdEnd) =
        (if k + 1 < 32 then b + offRhatCbdBody else b + offRhatCbdEnd) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (seg3_cbd2_rhat_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx6 hx8 hx19 hx20)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hr2, hr3, hr4, hr5, hx6_1, hr7, hx8_1,
        hr9, hr10, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hx20_1, hr21, hfp1, hv3_1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (seg3_cbd2_rhat_steps hb hbase sp prfPtr dstPtr prf Rest rem (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx6_1 hx8_1 hx19_1 hx20_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g2.trans hr2, g3.trans hr3,
        g4.trans hr4, g5.trans hr5, g7.trans hr7, g9.trans hr9, g10.trans hr10,
        g12.trans hr12, g13.trans hr13, g14.trans hr14, g15.trans hr15, g16.trans hr16,
        g17.trans hr17, g18.trans hr18, gx19, gx20, g21.trans hr21, gfp.trans hfp1,
        gv3.trans hv3_1, hP2⟩

theorem seg3_cbd2_rhat_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx7 : s.readReg64 .x7 = prfPtr + 1#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12832#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offRhatCbdEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 12832#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x7 = prfPtr + 1#64 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = sp + 12832#64 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 12832#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 12832#64) 512 ∗ Rest =
      memRegion (sp + 12832#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (seg3_cbd2_rhat_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, hx6_1, r7, hx8_1,
      r9, r10, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, rfp, rv3, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.of_memRegion_vecRangeMem 32 (sp + 12832#64) (by decide) rfl fun f => by
      rw [show VecRangeMem 32 (sp + 12832#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 12832#64) f ∗ Rest by
        rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 12832#64) f), sepConj_assoc]]
      refine SepWP.seq
        (seg3_cbd2_rhat_steps hb hbase sp prfPtr (sp + 12832#64) prf Rest 32 0 rfl s1 f
          (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx6_1
          (by simp [hx8_1, hx7]) (r19.trans hx19) (r20.trans hx20)) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g2.trans r2, g3.trans r3,
        g4.trans r4, g5.trans r5, g7.trans (r7.trans hx7), g9.trans r9, g10.trans r10,
        g12.trans r12, g13.trans r13, g14.trans r14, g15.trans r15, g16.trans r16,
        g17.trans r17, g18.trans r18, gx19, gx20, g21.trans r21, gfp.trans rfp,
        gv3.trans rv3, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3Cbd
