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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 1b (`+0x00e8 .. +0x02d0`)

`.rodata.cst16.3` load, `dkA` spill at `sp + 1872`, AdvSIMD unreduced `deserialize_12`
loops 0–1, and `B28` (`memcpy`) copy producing `sHat[0]` at `[sp + 22400, sp + 22912)`
and `sHat[1]` staged at `[sp + 11856, sp + 12368)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  fetch_rebase_ldst128Lo12_site
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16_3_vec
  mlkemData05Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env
  step_ldrQ128_ro
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  PolyMem
  SepLoad128
  SepStore128
  Vec128At
  Vec32
  poly32Mem_ofFn
  polyVecNat
  step_ldrQ128
  step_stpQ128
  step_strQ128
  vecRangeBytes
  vecRangeBytes_length
  vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_cell8
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  loadVec12
  rawDeser12
  rawDeser12_loadVec12_eq
  tHatPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdDup_8h
  exec_simdTbl_16b_1
  exec_simdUshl_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq
  blk04_tree_size
  blkLib04
  blkPC04
  blkPl04
  blkPlaceable04
  blkTree04
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x00e8 → 0x02cc]
gen_placed_odd_sites blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x00e8 → 0x00f4]

@[simp, arm64_norm]
private theorem blkPC04_rebase_cst16_3_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 244) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 3)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := 244)
    (r := { off := 244, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 244)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 61) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

theorem blk28_memcpy_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC04

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

abbrev cst16_3_val : BitVec 128 := 14673634461853297750225786205640917248#128
abbrev mvni_4s_3_val : BitVec 128 := 340261597812727650982291982701393870848#128
abbrev mask_0fff_val : BitVec 128 := 21262780079976241823186373959458164735#128

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
theorem exec_simdMvni_4s_3 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 26#5 3#5 rd) s =
      (s.writeVReg128 rd mvni_4s_3_val).advancePC := by
  simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_8h_240 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 7#3 22#5 16#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& mask_0fff_val)).advancePC := by
  simp [execInstWithSvc]

attribute [local wp_norm ↓ high]
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdDup_8h
  exec_simdMovi_2d_0 exec_simdMvni_4s_3 exec_simdBic_8h_240

/-! ## 1. `dk` Byte-Slice Split & Shared Step Macros -/

theorem dk_pointsTo_split (dkA : BitVec 64) {dk : List (BitVec 8)} (hdk : dk.length = 2400) :
    (dkA ↦ₛ dk) =
      (dkA ↦ₛ dk.take 384) ∗
      ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗
      ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗
      ((dkA + 1152#64) ↦ₛ dk.drop 1152) := by
  have h0 : dk = dk.take 384 ++ dk.drop 384 := (List.take_append_drop 384 dk).symm
  have h1 : dk.drop 384 = (dk.drop 384).take 384 ++ dk.drop 768 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (dk.drop 384)).symm
  have h2 : dk.drop 768 = (dk.drop 768).take 384 ++ dk.drop 1152 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (dk.drop 768)).symm
  have hl0 : (dk.take 384).length = 384 := by simp [hdk]
  have hl1 : ((dk.drop 384).take 384).length = 384 := by simp [hdk]
  have hl2 : ((dk.drop 768).take 384).length = 384 := by simp [hdk]
  conv_lhs => rw [h0]
  rw [pointsToBytes_append, hl0, show BitVec.ofNat 64 384 = 384#64 from rfl]
  conv_lhs => rhs; rw [h1]
  rw [pointsToBytes_append, hl1, show dkA + 384#64 + BitVec.ofNat 64 384 = dkA + 768#64 by bv_omega]
  conv_lhs => rhs; rhs; rw [h2]
  rw [pointsToBytes_append, hl2, show dkA + 768#64 + BitVec.ofNat 64 384 = dkA + 1152#64 by bv_omega]

private theorem update2_prefix {f g : Nat → BitVec 128} {k : Nat}
    (hf : ∀ j, j < 2 * k → f j = g j) :
    ∀ j, j < 2 * (k + 1) →
      Function.update (Function.update f (2 * k) (g (2 * k))) (2 * k + 1) (g (2 * k + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * k + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * k
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g := vecRangeMem_congr h

local macro "step_strQ_poly0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { bv_omega }; { rfl }
  · wp_norm_lhs
  intro _))

local macro "step_strQ_vec0" : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec128At; bv_omega
  · wp_norm_lhs
  intro _))

local macro "step_ldrQ_vec0" : tactic => `(tactic| (
  apply step_ldrQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · apply SepLoad128.left; apply SepLoad128.vec128At; bv_omega
  · wp_norm_lhs))

local macro "step_zero32_poly0" : tactic => `(tactic| (
  step_strQ_poly0 31; step_strQ_poly0 30; step_strQ_poly0 29; step_strQ_poly0 28;
  step_strQ_poly0 27; step_strQ_poly0 26; step_strQ_poly0 25; step_strQ_poly0 24;
  step_strQ_poly0 23; step_strQ_poly0 22; step_strQ_poly0 21; step_strQ_poly0 20;
  step_strQ_poly0 19; step_strQ_poly0 18; step_strQ_poly0 17; step_strQ_poly0 16;
  step_strQ_poly0 15; step_strQ_poly0 14; step_strQ_poly0 13; step_strQ_poly0 12;
  step_strQ_poly0 11; step_strQ_poly0 10; step_strQ_poly0 9; step_strQ_poly0 8;
  step_strQ_poly0 7; step_strQ_poly0 6; step_strQ_poly0 5; step_strQ_poly0 4;
  step_strQ_poly0 3; step_strQ_poly0 2; step_strQ_poly0 1; step_strQ_poly0 0))

local macro "prove_deser12_loop " src:ident dst:ident bs:ident hbs:ident
    pc0:term:arg pc1:term:arg pc2:term:arg pc3:term:arg pc4:term:arg
    srcReg:term:arg : tactic => `(tactic| (
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih =>
    intro k hkrem s f hpc hrun hspA hx_src hx8 hx_dst hv0 hv3 hf
    have hk16 : k < 16 := by omega
    refine SepWP.step_ldrSimd64 (pc := $pc0) hpc hrun (by wp_norm_lhs) rfl
      (show evalAddrMode s (.Offset $srcReg 0#64) = ($src + BitVec.ofNat 64 (24 * k), none) by
        simp [evalAddrMode, hx_src])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    refine SepWP.step_ldrSimd64 (pc := $pc1) (by simp [wp_norm, arm64_norm]) hrun
      (by wp_norm_lhs) rfl
      (show evalAddrMode _ (.UnscaledOffset $srcReg 12#64) =
          ($src + BitVec.ofNat 64 (24 * k + 12), none) by
        simp [evalAddrMode, hx_src]; clear * -; bv_omega)
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    wp_steps 3
    refine step_simdLd1Single32 (pc := $pc2) (by simp [wp_norm, arm64_norm])
      (by simp [hrun]) (by wp_norm_lhs) rfl
      (show _ = $src + BitVec.ofNat 64 (24 * k + 8) by simp [hx_src]; clear * -; bv_omega)
      (SepLoad32.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    refine step_simdLd1Single32 (pc := $pc3) (by simp [wp_norm, arm64_norm])
      (by simp [hrun]) (by wp_norm_lhs) rfl
      (show _ = $src + BitVec.ofNat 64 (24 * k + 20) by simp [hx_src]; clear * -; bv_omega)
      (SepLoad32.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    wp_steps 9
    have hv1_eq : rawDeser12 (loadVec12 $bs (24 * k)) = polyVecNat (tHatPoly16 $bs) (2 * k) := by
      simpa [show 12 * (2 * k) = 24 * k by omega] using rawDeser12_loadVec12_eq $hbs (2 * k) (by omega)
    have hv2_eq : rawDeser12 (loadVec12 $bs (24 * k + 12)) = polyVecNat (tHatPoly16 $bs) (2 * k + 1) := by
      simpa [show 12 * (2 * k + 1) = 24 * k + 12 by omega] using
        rawDeser12_loadVec12_eq $hbs (2 * k + 1) (by omega)
    refine step_stpQ128 (pc := $pc4) (wb := none) (ea := $dst + BitVec.ofNat 64 (32 * k))
      (ea16 := $dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (tHatPoly16 $bs) (2 * k)) (v2 := polyVecNat (tHatPoly16 $bs) (2 * k + 1))
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_dst, hx8]) rfl
      (by simp [hv0, hv3, ← hv1_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
      (by simp [hv0, hv3, ← hv2_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k) (by omega) (by clear * -; bv_omega))))
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k + 1) (by omega) (by clear * -; bv_omega))))
      (by wp_norm_lhs) ?_
    intro m'
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp [hx8] at hne
      · refine SepWP.mono
          (ih rem' (by omega) (k + 1) (by omega) _ _
            (by wp_norm_lhs) (by first | rfl | simp [hrun])
            (by simpa [State.spAligned] using hspA)
            (by simp [hx_src]; clear * -; bv_omega)
            (by simp [hx8]; clear * -; bv_omega)
            (by simp [hx_dst]) (by simp [hv0]) (by simp [hv3])
            (update2_prefix hf)) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hkr_f, hfp_f, hx24_f, hx26_f, hx28_f, hv3_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hkr_f, by simpa using hfp_f,
          by simpa using hx24_f, by simpa using hx26_f, by simpa using hx28_f, hv3_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa [hx8] using hne
        have hlt1 : 32 * k < 2 ^ 64 := by omega
        have hlt2 : 32 * k + 32 < 2 ^ 64 := by omega
        have hnat := congrArg BitVec.toNat hbv
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
            show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt hlt2,
            show (512#64).toNat = 512 from rfl] at hnat
        omega
      subst hk15
      have hf32 : ∀ j, j < 32 →
          Function.update (Function.update f 30 (polyVecNat (tHatPoly16 $bs) 30))
            31 (polyVecNat (tHatPoly16 $bs) 31) j = polyVecNat (tHatPoly16 $bs) j :=
        update2_prefix (k := 15) hf
      refine SepWP.done (by wp_norm_lhs) (by first | rfl | simp [hrun])
        ⟨by simp, by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp, by simp, by simp, by simp [hv3], ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _))

/-! ## 2. Sub-Segments of `Seg1b` (`+0x00e8 .. +0x02d0`) -/

private theorem seg1b_setup0 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (vInit : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 232#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = dkA) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 396#64) s
      (Poly32Mem (sp + 11856#64) vInit ∗ memRegion (sp + 1872#64) 8 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 11856#64 ∧
        sf.readReg64 .x10 = dkA ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = mvni_4s_3_val ∧
        sf.readVReg128 3#5 = cst16_3_val ∧
        (Pf ⊢ Poly32Mem (sp + 11856#64) Vec32.zero ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 1872#64)); intro c1872
  wp_step; wp_step; wp_step
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_3 mlkemData05Bytes_length cst16_3_vec (by wp_norm_lhs) ?_
  wp_steps 5
  have hreord : ((sp + 1872#64) ↦₆₄ dkA) ∗ Poly32Mem (sp + 11856#64) vInit ∗ Rest ⊢
      Poly32Mem (sp + 11856#64) vInit ∗ (((sp + 1872#64) ↦₆₄ dkA) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg1b_loop0 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 396#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x10 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x9 = dst →
      s.readVReg128 0#5 = mvni_4s_3_val →
      s.readVReg128 3#5 = cst16_3_val →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 468#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          sf.readVReg128 3#5 = cst16_3_val ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 396#64) (b + 400#64) (b + 416#64) (b + 420#64) (b + 460#64) Reg.x10

private theorem seg1b_copy0_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (v1904 : BitVec 128) (dk0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 468#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = cst16_3_val)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 648#64) s
      (Vec128At (sp + 1904#64) v1904 ∗ memRegion (sp + 22400#64) 512 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk0)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = mvni_4s_3_val ∧
        sf.readVReg128 3#5 = cst16_3_val ∧
        (Pf ⊢ Vec128At (sp + 1904#64) cst16_3_val ∗
          PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) ∗
          Poly32Mem (sp + 11856#64) Vec32.zero ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs0_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 dk0)) = bs0
  have hbs0 : bs0.length = 512 := by rw [← hbs0_def, vecRangeBytes_length]
  have hp11856 : PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk0)) = ((sp + 11856#64) ↦ₛ bs0) := by
    rw [← hbs0_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp22400 : ((sp + 22400#64) ↦ₛ bs0) = PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) := by
    rw [← hbs0_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp11856_32 : ((sp + 11856#64) ↦ₛ bs0) =
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk0))) := by
    rw [← hp11856, poly32Mem_ofFn]
  rw [hp11856]
  wp_cut_codeLoaded
  wp_steps 7
  step_strQ_vec0
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 22400#64, sp + 11856#64, bs0)
  rw [hp22400, hp11856_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hreord0 : PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk0))) ∗
      (Vec128At (sp + 1904#64) cst16_3_val ∗ Rest) ⊢
      Vec128At (sp + 1904#64) cst16_3_val ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk0))) ∗
      PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) ∗ Rest := by sep_frame
  refine SepWP.weaken_pre hreord0 ?_
  wp_steps 2
  step_ldrQ_vec0
  wp_step
  have hreord : Vec128At (sp + 1904#64) cst16_3_val ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk0))) ∗
      PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) ∗ Rest ⊢
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk0))) ∗
      (Vec128At (sp + 1904#64) cst16_3_val ∗
        PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 dk0)) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg1b_loop1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 648#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x20 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst →
      s.readVReg128 0#5 = mvni_4s_3_val →
      s.readVReg128 3#5 = cst16_3_val →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 720#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          sf.readVReg128 3#5 = cst16_3_val ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 648#64) (b + 652#64) (b + 668#64) (b + 672#64) (b + 712#64) Reg.x20

private theorem poly32Mem_zero_eq (ptr : BitVec 64) :
    Poly32Mem ptr Vec32.zero = PolyMem ptr (fun _ => 0#128) :=
  poly32Mem_ofFn ptr (fun _ => 0#128)

/-- Composed Segment 1b contract (`+0x00e8 → +0x02d0`). -/
theorem seg1b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fp0 dkA : BitVec 64) (vInit : Vec32) (v1904 : BitVec 128)
    (dk : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 232#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = fp0)
    (hx20 : s.readReg64 .x20 = dkA + 384#64)
    (hx23 : s.readReg64 .x23 = dkA)
    (hx24 : s.readReg64 .x24 = dkA + 384#64)
    (hx26 : s.readReg64 .x26 = sp + 20704#64)
    (hx28 : s.readReg64 .x28 = sp + 20968#64)
    (hdk : dk.length = 2400) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 720#64) s
      (Poly32Mem (sp + 11856#64) vInit ∗ memRegion (sp + 1872#64) 8 ∗
        Vec128At (sp + 1904#64) v1904 ∗ memRegion (sp + 22400#64) 512 ∗
        (dkA ↦ₛ dk.take 384) ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fp0 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readReg64 .x24 = dkA + 384#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        (Pf ⊢ ((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
          PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
          PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
          (dkA ↦ₛ dk.take 384) ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗ Rest)) := by
  have hl0 : (dk.take 384).length = 384 := by simp [hdk]
  have hl1 : ((dk.drop 384).take 384).length = 384 := by simp [hdk]
  refine sepWP_seq_env hcl hro
    (seg1b_setup0 hb hbase s sp dkA vInit _ hpc hrun hsp hspA hro hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hfp_1, hx20_1, hx24_1, hx26_1, hx28_1, hv0_1, hv3_1, hP1⟩
  have hP1' : P1 ⊢ (dkA ↦ₛ dk.take 384) ∗ PolyMem (sp + 11856#64) (fun _ => 0#128) ∗
      (((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) v1904 ∗
        memRegion (sp + 22400#64) 512 ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗ Rest) := by
    refine Entails.trans hP1 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg1b_loop0 hb dkA (sp + 11856#64) (dk.take 384) _ hl0 15 0 rfl s1 (fun _ => 0#128)
        hpc1 hrun1 hspA1 (by simp [hx10_1]) (by simp [hx8_1]) hx9_1 hv0_1 hv3_1 (by omega)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx20_2, hfp_2, hx24_2, hx26_2, hx28_2, hv3_2, hP2⟩
  have hP2' : P2 ⊢ Vec128At (sp + 1904#64) v1904 ∗ memRegion (sp + 22400#64) 512 ∗
      PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
      (((sp + 1872#64) ↦₆₄ dkA) ∗
        (dkA ↦ₛ dk.take 384) ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗ Rest) :=
    Entails.trans hP2 (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg1b_copy0_zero1 hb hbase s2 sp v1904 (dk.take 384) _
        hpc2 hrun2 (hsp2.trans hsp1) hspA2 hv3_2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 _
    ⟨hsp3, hspA3, hx8_3, hfp_3, hx20_3, hx21_3, hx24_3, hx26_3, hx28_3, hv0_3, hv3_3, hP3⟩
  have hP3' : P3 ⊢ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗
      PolyMem (sp + 11856#64) (fun _ => 0#128) ∗
      (((sp + 1872#64) ↦₆₄ dkA) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
        (dkA ↦ₛ dk.take 384) ∗ Rest) := by
    refine Entails.trans hP3 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP3'
    (SepWP.mono
      (seg1b_loop1 hb (dkA + 384#64) (sp + 11856#64) ((dk.drop 384).take 384) _ hl1 15 0 rfl s3
        (fun _ => 0#128) hpc3 hrun3 hspA3
        (by simp [hx20_3, hx20_2, hx20_1, hx20]) (by simp [hx8_3]) hx21_3 hv0_3 hv3_3 (by omega)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx21_f, hfp_f, hx24_f, hx26_f, hx28_f, _, hPf⟩
  refine ⟨hsp_f.trans hsp3, hspA_f,
    by rw [hfp_f, hfp_3, hfp_2, hfp_1, hfp],
    hx21_f.trans hx21_3,
    by rw [hx24_f, hx24_3, hx24_2, hx24_1, hx24],
    by rw [hx26_f, hx26_3, hx26_2, hx26_1, hx26],
    by rw [hx28_f, hx28_3, hx28_2, hx28_1, hx28],
    Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
