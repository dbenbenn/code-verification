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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `kyber_decapsulate` (`B06`) — Segment 1b (`+0x0098 .. +0x0380`)

`.rodata.cst16.3` load, AdvSIMD unreduced `deserialize_12` loops 0–2, and `B28` (`memcpy`)
copies producing `sHat[0]` at `[sp + 30448, sp + 30960)`, `sHat[1]` at `[sp + 30960, sp + 31472)`,
and `sHat[2]` staged at `[sp + 14432, sp + 14944)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
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
  VecRangeMem
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq
  blk06_tree_size
  blkLib06
  blkPC06
  blkPl06
  blkPlaceable06
  blkTree06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x0098 → 0x037c]
gen_placed_odd_sites blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x0098 → 0x00a4]

@[simp, arm64_norm]
private theorem blkPC06_rebase_cst16_3_ldr [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + BitVec.ofNat 64 164) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 3)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 164)
    (r := { off := 164, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 164)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 41) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

theorem blk28_memcpy_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC06

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
theorem exec_simdMvni_4s_3 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 26#5 3#5 rd) s =
      (s.writeVReg128 rd 0xfffc0000fffc0000fffc0000fffc0000#128).advancePC := by
  simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
theorem exec_simdBic_8h_240 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 7#3 22#5 16#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& 0x0fff0fff0fff0fff0fff0fff0fff0fff#128)).advancePC := by
  simp [execInstWithSvc]

attribute [local wp_norm ↓ high]
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdDup_8h
  exec_simdMovi_2d_0 exec_simdMvni_4s_3 exec_simdBic_8h_240

/-! ## 1. `sk` Byte-Slice Split, `uHatZetaSpill40`, & Shared Step Macros -/

theorem sk_pointsTo_split (skA : BitVec 64) {sk : List (BitVec 8)} (hsk : sk.length = 3168) :
    (skA ↦ₛ sk) =
      (skA ↦ₛ sk.take 384) ∗
      ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      ((skA + 1536#64) ↦ₛ sk.drop 1536) := by
  have h0 : sk = sk.take 384 ++ sk.drop 384 := (List.take_append_drop 384 sk).symm
  have h1 : sk.drop 384 = (sk.drop 384).take 384 ++ sk.drop 768 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (sk.drop 384)).symm
  have h2 : sk.drop 768 = (sk.drop 768).take 384 ++ sk.drop 1152 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (sk.drop 768)).symm
  have h3 : sk.drop 1152 = (sk.drop 1152).take 384 ++ sk.drop 1536 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (sk.drop 1152)).symm
  have hl0 : (sk.take 384).length = 384 := by simp [hsk]
  have hl1 : ((sk.drop 384).take 384).length = 384 := by simp [hsk]
  have hl2 : ((sk.drop 768).take 384).length = 384 := by simp [hsk]
  have hl3 : ((sk.drop 1152).take 384).length = 384 := by simp [hsk]
  conv_lhs => rw [h0]
  rw [pointsToBytes_append, hl0, show BitVec.ofNat 64 384 = 384#64 from rfl]
  conv_lhs => rhs; rw [h1]
  rw [pointsToBytes_append, hl1, show skA + 384#64 + BitVec.ofNat 64 384 = skA + 768#64 by bv_omega]
  conv_lhs => rhs; rhs; rw [h2]
  rw [pointsToBytes_append, hl2, show skA + 768#64 + BitVec.ofNat 64 384 = skA + 1152#64 by bv_omega]
  conv_lhs => rhs; rhs; rhs; rw [h3]
  rw [pointsToBytes_append, hl3, show skA + 1152#64 + BitVec.ofNat 64 384 = skA + 1536#64 by bv_omega]

abbrev cst16_3_val : BitVec 128 := 0x0b0a0a09080707060504040302010100#128

/-- 21-slot precomputed NTT zeta table written at `[sp + 2064, sp + 2400)` in `+0x04c0..+0x05d8`. -/
@[expose] def uHatZetaVal : Nat → BitVec 16
  | 0 => 962#16 | 1 => 49846#16 | 2 => 61737#16 | 3 => 1577#16 | 4 => 27758#16
  | 5 => 622#16 | 6 => 44629#16 | 7 => 48842#16 | 8 => 28191#16 | 9 => 287#16
  | 10 => 53134#16 | 11 => 1422#16 | 12 => 13525#16 | 13 => 1493#16 | 14 => 787#16
  | 15 => 64019#16 | 16 => 14745#16 | 17 => 65177#16 | 18 => 3329#16 | 19 => 31498#16
  | 20 => 64778#16 | _ => 0#16

@[expose] def uHatZetaSpill40 : Spill40 :=
  Spill40.ofFn fun i => if i < 21 then dup8x16 (uHatZetaVal i) else 0#128

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
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hkr_f, hx20_f, hx22_f, hx25_f, hx26_f, hv3_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hfp_f, by simpa using hkr_f,
          by simpa using hx20_f, by simpa using hx22_f, by simpa using hx25_f,
          by simpa using hx26_f, hv3_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa [hx8] using hne
        have hlt1 : 32 * k < 18446744073709551616 := by omega
        have hlt2 : 32 * k + 32 < 18446744073709551616 := by omega
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
          by simp, by simp, by simp, by simp, by simp, by simp, by simp [hv3], ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _))

/-! ## 2. Sub-Segments of `Seg1b` (`+0x0098 .. +0x0380`) -/

private theorem seg1b_setup0 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA : BitVec 64) (vInit : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0098#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx21 : s.readReg64 .x21 = skA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x013c#64) s
      (Poly32Mem (sp + 14432#64) vInit ∗ memRegion (sp + 2032#64) 8 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 14432#64 ∧
        sf.readReg64 .x10 = skA ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Poly32Mem (sp + 14432#64) Vec32.zero ∗ ((sp + 2032#64) ↦₆₄ skA) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 2032#64)); intro c2032
  wp_step; wp_step; wp_step
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_3 mlkemData05Bytes_length cst16_3_vec (by wp_norm_lhs) ?_
  wp_steps 5
  have hreord : ((sp + 2032#64) ↦₆₄ skA) ∗ Poly32Mem (sp + 14432#64) vInit ∗ Rest ⊢
      Poly32Mem (sp + 14432#64) vInit ∗ (((sp + 2032#64) ↦₆₄ skA) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg1b_loop0 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x013c#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x10 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x9 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = cst16_3_val →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0184#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readVReg128 3#5 = cst16_3_val ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 0x013c#64) (b + 0x0140#64) (b + 0x0150#64) (b + 0x0154#64) (b + 0x017c#64) Reg.x10

private theorem seg1b_copy0_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (v2048 : BitVec 128) (sk0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0184#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = cst16_3_val)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0238#64) s
      (Vec128At (sp + 2048#64) v2048 ∗ memRegion (sp + 30448#64) 512 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk0)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 3#5 = cst16_3_val ∧
        (Pf ⊢ Vec128At (sp + 2048#64) cst16_3_val ∗
          PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) ∗
          Poly32Mem (sp + 14432#64) Vec32.zero ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs0_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 sk0)) = bs0
  have hbs0 : bs0.length = 512 := by rw [← hbs0_def, vecRangeBytes_length]
  have hp14432 : PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk0)) = ((sp + 14432#64) ↦ₛ bs0) := by
    rw [← hbs0_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp30448 : ((sp + 30448#64) ↦ₛ bs0) = PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) := by
    rw [← hbs0_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp14432_32 : ((sp + 14432#64) ↦ₛ bs0) =
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk0))) := by
    rw [← hp14432, poly32Mem_ofFn]
  rw [hp14432]
  wp_cut_codeLoaded
  wp_steps 7
  step_strQ_vec0
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 30448#64, sp + 14432#64, bs0)
  rw [hp30448, hp14432_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hreord0 : PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk0))) ∗
      (Vec128At (sp + 2048#64) cst16_3_val ∗ Rest) ⊢
      Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk0))) ∗
      PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) ∗ Rest := by sep_frame
  refine SepWP.weaken_pre hreord0 ?_
  wp_steps 2
  step_ldrQ_vec0
  wp_step
  have hreord : Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk0))) ∗
      PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) ∗ Rest ⊢
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk0))) ∗
      (Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 sk0)) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg1b_loop1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0238#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0280#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 0x0238#64) (b + 0x023c#64) (b + 0x024c#64) (b + 0x0250#64) (b + 0x0278#64) Reg.x19

private theorem seg1b_copy1_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA : BitVec 64) (sk1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0280#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = skA + 384#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0338#64) s
      (Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 30960#64) 512 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk1)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = skA + 768#64 ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = skA + 384#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 2048#64) cst16_3_val ∗
          PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) ∗
          Poly32Mem (sp + 14432#64) Vec32.zero ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs1_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 sk1)) = bs1
  have hbs1 : bs1.length = 512 := by rw [← hbs1_def, vecRangeBytes_length]
  have hp14432 : PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk1)) = ((sp + 14432#64) ↦ₛ bs1) := by
    rw [← hbs1_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp30960 : ((sp + 30960#64) ↦ₛ bs1) = PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) := by
    rw [← hbs1_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp14432_32 : ((sp + 14432#64) ↦ₛ bs1) =
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk1))) := by
    rw [← hp14432, poly32Mem_ofFn]
  have ha768 : skA + 384#64 + 384#64 = skA + 768#64 := by clear * -; bv_omega
  rw [hp14432]
  wp_cut_codeLoaded
  wp_steps 8
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 30960#64, sp + 14432#64, bs1)
  rw [hp30960, hp14432_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hreord0 : PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk1))) ∗
      (Vec128At (sp + 2048#64) cst16_3_val ∗ Rest) ⊢
      Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk1))) ∗
      PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) ∗ Rest := by sep_frame
  refine SepWP.weaken_pre hreord0 ?_
  wp_steps 2
  step_ldrQ_vec0
  wp_steps 2
  have hreord : Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk1))) ∗
      PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) ∗ Rest ⊢
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk1))) ∗
      (Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 sk1)) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg1b_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0338#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x19 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0380#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 0x0338#64) (b + 0x033c#64) (b + 0x034c#64) (b + 0x0350#64) (b + 0x0378#64) Reg.x9

private theorem poly32Mem_zero_eq (ptr : BitVec 64) :
    Poly32Mem ptr Vec32.zero = PolyMem ptr (fun _ => 0#128) :=
  poly32Mem_ofFn ptr (fun _ => 0#128)

/-- Composed Segment 1b contract (`+0x0098 → +0x0380`). -/
theorem seg1b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (vInit : Vec32) (v2048 : BitVec 128)
    (sk : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0098#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = skA + 384#64)
    (hx20 : s.readReg64 .x20 = ctA)
    (hx21 : s.readReg64 .x21 = skA)
    (hx22 : s.readReg64 .x22 = skA + 384#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hsk : sk.length = 3168) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0380#64) s
      (Poly32Mem (sp + 14432#64) vInit ∗ memRegion (sp + 2032#64) 8 ∗
        Vec128At (sp + 2048#64) v2048 ∗
        memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 512 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x20 = ctA ∧
        sf.readReg64 .x22 = skA + 384#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .x26 = sp + 28632#64 ∧
        (Pf ⊢ ((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (sp + 2048#64) cst16_3_val ∗
          PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 (sk.take 384))) ∗
          PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 ((sk.drop 384).take 384))) ∗
          PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
          (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
          ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest)) := by
  have hl0 : (sk.take 384).length = 384 := by simp [hsk]
  have hl1 : ((sk.drop 384).take 384).length = 384 := by simp [hsk]
  have hl2 : ((sk.drop 768).take 384).length = 384 := by simp [hsk]
  refine sepWP_seq_env hcl hro
    (seg1b_setup0 hb hbase s sp skA vInit _ hpc hrun hsp hspA hro hx21) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp_1, hx8_1, hx9_1, hx10_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hv0_1, hv3_1, hP1⟩
  have hP1' : P1 ⊢ (skA ↦ₛ sk.take 384) ∗ PolyMem (sp + 14432#64) (fun _ => 0#128) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (sp + 2048#64) v2048 ∗
        memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 512 ∗
        ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest) := by
    refine Entails.trans hP1 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg1b_loop0 hb skA (sp + 14432#64) (sk.take 384) _ hl0 15 0 rfl s1 (fun _ => 0#128)
        hpc1 hrun1 hspA1 (by simp [hx10_1]) (by simp [hx8_1]) hx9_1 hv0_1 hv3_1 (by omega)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp_2, hx19_2, hx20_2, hx22_2, hx25_2, hx26_2, hv3_2, hP2⟩
  have hP2' : P2 ⊢ Vec128At (sp + 2048#64) v2048 ∗ memRegion (sp + 30448#64) 512 ∗
      PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 (sk.take 384))) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗ memRegion (sp + 30960#64) 512 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest) :=
    Entails.trans hP2 (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg1b_copy0_zero1 hb hbase s2 sp v2048 (sk.take 384) _
        hpc2 hrun2 (hsp2.trans hsp1) hspA2 hv3_2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp_3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx25_3, hx26_3, hv0_3, hv3_3, hP3⟩
  have hP3' : P3 ⊢ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      PolyMem (sp + 14432#64) (fun _ => 0#128) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 (sk.take 384))) ∗
        memRegion (sp + 30960#64) 512 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest) := by
    refine Entails.trans hP3 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP3'
    (sepWP_seq_env hcl3 hro3
      (seg1b_loop1 hb (skA + 384#64) (sp + 14432#64) ((sk.drop 384).take 384) _ hl1 15 0 rfl s3
        (fun _ => 0#128) hpc3 hrun3 hspA3
        (by simp [hx19_3, hx19_2, hx19_1, hx19]) (by simp [hx8_3]) hx21_3 hv0_3 hv3_3 (by omega)) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hfp_4, _hx21_4, hx20_4, hx22_4, hx25_4, hx26_4, _hv3_4, hP4⟩
  have hP4' : P4 ⊢ Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 30960#64) 512 ∗
      PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 384).take 384))) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗
        PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 (sk.take 384))) ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗ Rest) :=
    Entails.trans hP4 (by sep_frame)
  refine SepWP.weaken_pre hP4'
    (sepWP_seq_env hcl4 hro4
      (seg1b_copy1_zero2 hb hbase s4 sp skA ((sk.drop 384).take 384) _
        hpc4 hrun4 (hsp4.trans hsp3) hspA4
        (by rw [hx22_4, hx22_3, hx22_2, hx22_1, hx22]) hcl4) ?_)
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspA5, hfp_5, hx8_5, hx9_5, hx19_5, hx20_5, hx22_5, hx25_5, hx26_5, hv0_5, hv3_5, hP5⟩
  have hP5' : P5 ⊢ ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      PolyMem (sp + 14432#64) (fun _ => 0#128) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 30448#64) (polyVecNat (tHatPoly16 (sk.take 384))) ∗
        PolyMem (sp + 30960#64) (polyVecNat (tHatPoly16 ((sk.drop 384).take 384))) ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗ Rest) := by
    refine Entails.trans hP5 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP5'
    (SepWP.mono
      (seg1b_loop2 hb (skA + 768#64) (sp + 14432#64) ((sk.drop 768).take 384) _ hl2 15 0 rfl s5
        (fun _ => 0#128) hpc5 hrun5 hspA5
        (by simp [hx9_5]) (by simp [hx8_5]) hx19_5 hv0_5 hv3_5 (by omega)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx19_f, hx20_f, hx22_f, hx25_f, hx26_f, _, hPf⟩
  refine ⟨hsp_f.trans hsp5, hspA_f,
    by rw [hfp_f, hfp_5, hfp_4, hfp_3, hfp_2, hfp_1],
    hx19_f.trans hx19_5,
    by rw [hx20_f, hx20_5, hx20_4, hx20_3, hx20_2, hx20_1, hx20],
    hx22_f.trans hx22_5,
    by rw [hx25_f, hx25_5, hx25_4, hx25_3, hx25_2, hx25_1, hx25],
    by rw [hx26_f, hx26_5, hx26_4, hx26_3, hx26_2, hx26_1, hx26],
    Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
