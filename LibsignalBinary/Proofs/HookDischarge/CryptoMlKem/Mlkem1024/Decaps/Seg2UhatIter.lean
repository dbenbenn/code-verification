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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Decompress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2FwdLow

/-!
# `kyber_decapsulate` (`B06`) — Segment 2 Single-Iteration `uHat` Body (`+0x05dc .. +0x1840`)

Proves one iteration (`idx < 4`) of the `uHat` decompression + 7-stage forward `NTT` + Barrett
reduction loop (`+0x05dc → +0x05dc` for `idx < 3`, `+0x05dc → +0x1840` for `idx = 3`), together
with pure `uHatPoly16` soundness (`PolyBounded16 1664` + `PolyRepresents`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_ro00)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 byteDecodeRaw decodeAndDecompress neonBarrettReduce16 polyNtt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  neonNttStage16 neonPolyNtt16 neonPolyNtt16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem Vec32 VecRangeMem poly32Mem_ofFn polyVecNat
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  fwdNttAfterStage4 lowerFwdNtt16 lowerFwdNtt16_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr SpillSliceMem SymEnv SymGprs SymSpill40 SymState SymVec32
  evalSExpr evalSymGpr symInitState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SymSpatial SymStateMatches blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (
  sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  lowerNtt5_16 lowerNtt5_16_size neonPolyNtt16_of_lower5 poly_eq_barrett poly_eq_lowerNtt5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (
  blk28_memcpy_06 uHatZetaSpill40)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase (
  decompressPoly16 decompressPoly16_size decompressPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Decompress (
  seg2_decompress11_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1a (
  cfgSeg2Fwd symSeg2Init)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1b (
  symSeg2MidB)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatSym1c (
  cfgSeg2Barrett run_seg2_barrett run_seg2_fwd1ab run_seg2_fwd1c
  seg2_barrett_ast_eq seg2_barrett_noSpillVreg seg2_hi_ast_eq seg2_hi_noSpillVreg
  symSeg2BarrettEnd symSeg2HiEnd symSeg2PreHi2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2FwdLow (
  ro00Sym seg2_fwd_low_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06
  [0x06f0 → 0x0704, 0x1434 → 0x1438, 0x1834 → 0x183c]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC06 polyVecNat

/-! ## 1. Pure `uHatPoly16` Soundness & Symbolic Environment Bridges -/

/-- `Poly16` result of `decompress_11` followed by 7-stage NEON forward `NTT` + Barrett reduction. -/
def uHatPoly16 (ctSlice : List (BitVec 8)) : Poly16 :=
  neonPolyNtt16 (decompressPoly16 11 ctSlice)

theorem uHatPoly16_spec (ctSlice : List (BitVec 8)) :
    (polyNtt (decodeAndDecompress 11 ctSlice)).size = 256 ∧
    PolyBounded16 1664 (uHatPoly16 ctSlice) ∧
    PolyRepresents (uHatPoly16 ctSlice) (polyNtt (decodeAndDecompress 11 ctSlice)) := by
  unfold uHatPoly16
  obtain ⟨hb, hr⟩ := decompressPoly16_spec ctSlice (Or.inr rfl)
  exact neonPolyNtt16_spec hb hr (by simp [decodeAndDecompress, byteDecodeRaw])

@[simp] theorem uHatPoly16_size (ctSlice : List (BitVec 8)) :
    (uHatPoly16 ctSlice).size = 256 :=
  (uHatPoly16_spec ctSlice).2.1.1

private theorem barrett_lowerFwd_lower5 (p0 : Poly16) :
    (lowerFwdNtt16 (lowerNtt5_16 p0)).map neonBarrettReduce16 = neonPolyNtt16 p0 := by
  have h := neonPolyNtt16_of_lower5 p0
  dsimp only [lowerFwdNtt16, fwdNttAfterStage4] at h ⊢
  rcases h1 : neonNttStage16 4 32 (lowerNtt5_16 p0) with ⟨p6, k6⟩
  rcases h2 : neonNttStage16 2 64 p6 with ⟨p7, k7⟩
  simpa [h1, h2] using h

private theorem noReloc_fwd1ab : blk06NoRelocInRange 450 1293 = true := by decide +kernel
private theorem noReloc_fwd1c : blk06NoRelocInRange 1295 1322 = true := by decide +kernel
private theorem noReloc_barrett : blk06NoRelocInRange 1383 1549 = true := by decide +kernel

private def mkSymEnv (s : State) (p : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := uHatZetaSpill40
  poly0   := Vec32.ofFn (polyVecNat p)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_seg2Init {sp : BitVec 64} {s : State} (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SymStateMatches sp (mkSymEnv s p) symSeg2Init s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symSeg2Init, SymGprs.get, evalSymGpr, mkSymEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem matches_initState {sp : BitVec 64} {s : State} (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SymStateMatches sp (mkSymEnv s p) symInitState s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symInitState, SymGprs.ofFn, SymGprs.get, evalSymGpr, mkSymEnv]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega
private theorem evalSExpr_gpr0_irrel (env : SymEnv) (g' : BitVec 5 → BitVec 64) (e : SExpr) :
    evalSExpr { env with gpr0 := g' } e = evalSExpr env e := by
  induction e <;> simp [evalSExpr, *]

private theorem spillSlice21_seg2Init (sp : BitVec 64) (env : SymEnv) :
    SpillSliceMem 21 (sp + 2064#64) (symSeg2Init.spill.eval env) =
      SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 :=
  vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
    | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
    | _ + 21 => omega

private theorem spillSlice21_seg2HiEnd (sp : BitVec 64) (env : SymEnv) :
    SpillSliceMem 21 (sp + 2064#64) (symSeg2HiEnd.spill.eval env) =
      SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 :=
  vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
    | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
    | _ + 21 => omega

/-! ## 2. Glue Helpers (`+0x06f0..+0x0708`, `+0x1434..+0x143c`, `+0x1834..+0x1840`) -/

private theorem seg2_memcpy_512 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (_hidx : idx < 4) (p0 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + 0x06f0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 idx)
    (hv8 : (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64) :
    let polyAddr := sp + 14432#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0708#64) s
      (PolyMem (sp + 4160#64) (polyVecNat p0) ∗ memRegion polyAddr 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x22 = polyAddr ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (sf.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 ∧
        (Pf ⊢ Poly32Mem polyAddr (Vec32.ofFn (polyVecNat p0)) ∗
          memRegion (sp + 4160#64) 512 ∗ Rest)) := by
  dsimp only
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set polyAddr := sp + 14432#64 + BitVec.ofNat 64 (512 * idx)
  have haddr : (sp + 14432#64) + (BitVec.ofNat 64 idx <<< 9) = polyAddr := by
    dsimp only [polyAddr]; clear * -; bv_omega
  generalize hbs_def : vecRangeBytes 32 (polyVecNat p0) = bs0
  have hbs_len : bs0.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp4160 : PolyMem (sp + 4160#64) (polyVecNat p0) = ((sp + 4160#64) ↦ₛ bs0) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp_dst : (polyAddr ↦ₛ bs0) = Poly32Mem polyAddr (Vec32.ofFn (polyVecNat p0)) := by
    rw [poly32Mem_ofFn, ← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have h4160_reg : ((sp + 4160#64) ↦ₛ bs0) ⊢ memRegion (sp + 4160#64) 512 := by
    simpa [hbs_len] using pointsToBytes_entails_memRegion (sp + 4160#64) bs0
  rw [hp4160]
  wp_cut_codeLoaded
  wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (polyAddr, sp + 4160#64, bs0)
  rw [hp_dst]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hv8_sf : (sf.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 := by
    have h64 : (sf.readVReg128 8#5).truncate 64 = (s.readVReg128 8#5).truncate 64 :=
      congrArg Prod.fst hvregs
    exact h64.trans hv8
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], hv8_sf, ?_⟩
  exact entails_sub h4160_reg (by sep_frame) (by sep_frame)

private theorem seg2_adrp_ro00 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (P : SepProp)
    (hpc : s.pc = b + 0x1434#64) (hrun : s.status = .Running) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x143c#64) s P
      (fun sf Pf =>
        sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.pstate = s.pstate ∧
        sf.vregs = s.vregs ∧
        sf.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 31#5 → sf.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        Pf = P) := by
  subst hbase
  wp_steps 2
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨rfl, rfl, rfl, rfl,
      by simp [ro00Sym], fun r hr8 hr31 => ?_, rfl⟩
  rcases r with ⟨rv, hrv⟩
  match rv with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => simp
  | 8 => exact absurd rfl hr8
  | 31 => exact absurd rfl hr31
  | _ + 32 => omega

private theorem seg2_loop_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp nextCt : BitVec 64) {idx : Nat} (hidx : idx < 4) (Rest : SepProp)
    (hpc : s.pc = b + 0x1834#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + 0x05dc#64 else b + 0x1840#64) s
      (((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
        ((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.vregs = s.vregs ∧
        (Pf ⊢ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_chk : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hspA
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 by omega) with rfl | rfl | rfl | rfl <;> {
    simp only [show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide,
      show (2 : Nat) < 3 by decide, Nat.lt_irrefl, ↓reduceIte]
    wp_steps 3
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, spAligned_of_chk (by simp) hsp_chk,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, rfl,
        sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))⟩
  }

/-! ## 3. Full 1-Iteration `uHat` Body (`+0x05dc → +0x05dc / +0x1840`) -/

theorem seg2_uhat_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctPtr : BitVec 64) {idx : Nat} (hidx : idx < 4)
    (ctSlice : List (BitVec 8)) (hct : ctSlice.length = 352) (Rest : SepProp)
    (hpc : s.pc = b + 0x05dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = ctPtr)
    (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 idx)
    (hx23 : s.readReg64 .x23 = sp + 14448#64 + BitVec.ofNat 64 (512 * idx))
    (hx24 : s.readReg64 .x24 = 16#64 + BitVec.ofNat 64 (512 * idx))
    (hx27 : s.readReg64 .x27 = sp + 4160#64)
    (hx28 : s.readReg64 .x28 = 62209#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64) :
    let polyAddr := sp + 14432#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC06.rebase b (fun _ => none))
      (if idx < 3 then b + 0x05dc#64 else b + 0x1840#64) s
      (stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
        memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
        memRegion polyAddr 512 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = ctPtr + 352#64 ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x23 = sp + 14448#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x24 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = 62209#64 ∧
        (sf.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
          memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
          PolyMem polyAddr (polyVecNat (uHatPoly16 ctSlice)) ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest)) := by
  dsimp only
  set polyAddr := sp + 14432#64 + BitVec.ofNat 64 (512 * idx)
  set p0 := decompressPoly16 11 ctSlice
  have hp0 : p0.size = 256 := decompressPoly16_size 11 ctSlice
  refine SepWP.weaken_pre
    (show stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
        memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
        memRegion polyAddr 512 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest ⊢
      stackAt sp 1136 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
        (ctPtr ↦ₛ ctSlice) ∗
        (SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗ memRegion polyAddr 512 ∗ Rest) by
      sep_frame)
    (sepWP_seq_env hcl hro
      (seg2_decompress11_ok hb hbase s sp ctPtr (BitVec.ofNat 64 idx) ctSlice _
        hpc hrun hsp hspA hcl hx0 hx22 hx27 hv8 hct) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp_1, hx19_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show _ ⊢ PolyMem (sp + 4160#64) (polyVecNat p0) ∗ memRegion polyAddr 512 ∗
        (stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          ((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
          ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
          memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest) by sep_frame))
    (sepWP_seq_env hcl1 hro1
      (seg2_memcpy_512 hb hbase s1 sp hidx p0 _ hpc1 hrun1 hsp1 hspA1 hcl1
        (hx19_1.trans hx19) hx22_1 (hv8_1 ▸ hv8)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp_2, hx19_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hv8_2, hP2⟩
  set env := mkSymEnv s2 p0
  set F_fwd := memRegion (sp + 4160#64) 512 ∗ stackAt sp 1136 ∗
    ((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
    ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
    memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest
  have hP2_sym : P2 ⊢ SymSpatial cfgSeg2Fwd sp env symSeg2Init F_fwd := by
    refine Entails.trans hP2 ?_
    dsimp only [SymSpatial, cfgSeg2Fwd, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem, env, mkSymEnv]
    rw [spillSlice21_seg2Init, hx22_2]
    change _ ⊢ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      Poly32Mem polyAddr (Vec32.ofFn (polyVecNat p0)) ∗ emp ∗ F_fwd
    sep_frame
  refine SepWP.weaken_pre hP2_sym
    (sepWP_seq_env hcl2 hro2
      (sepWP_of_runSymRange (cfg := cfgSeg2Fwd) (env := env) (F := F_fwd)
        843 450 noReloc_fwd1ab (by decide) (by decide) (by decide)
        run_seg2_fwd1ab (matches_seg2Init p0 hsp2 hspA2) hpc2 hrun2
        (post := fun s3 P3 => SymStateMatches sp env symSeg2MidB s3 ∧
          P3 = SymSpatial cfgSeg2Fwd sp env symSeg2MidB F_fwd)
        (fun s3 _ _ hm3 => ⟨hm3, rfl⟩)) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hm3, rfl⟩
  refine sepWP_seq_env hcl3 hro3 (seg2_adrp_ro00 hb hbase s3 _ hpc3 hrun3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hpst4, hvregs4, hx8_4, hgpr4, rfl⟩
  let env' : SymEnv :=
    { env with gpr0 := fun r => if r = 8#5 then mlkemMpl.ρ ro00Sym + 66#64 else env.gpr0 r }
  have hm4 : SymStateMatches sp env' symSeg2PreHi2 s4 := by
    refine ⟨hsp4.trans hm3.hsp, hspA4.trans hm3.hsp_al, hpst4.trans hm3.hpstate,
      fun r => ?_, fun r hr => ?_⟩
    · have hvr : s4.readVReg128 r = s3.readVReg128 r := by simp [State.readVReg128, hvregs4]
      rw [hvr, hm3.hvregs r]; exact (evalSExpr_gpr0_irrel env _ _).symm
    · by_cases hr8 : r = 8#5
      · subst hr8
        simpa [symSeg2PreHi2, SymGprs.get, SymGprs.set, evalSymGpr, env'] using hx8_4
      · rw [hgpr4 r hr8 hr, hm3.hgprs r hr]
        rcases r with ⟨rv, hrv⟩
        match rv with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15
        | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
        | 8 => exact absurd rfl hr8
        | 31 => exact absurd rfl hr
        | _ + 32 => omega
  have hspat4 : SymSpatial cfgSeg2Fwd sp env symSeg2MidB F_fwd =
      SymSpatial cfgSeg2Fwd sp env' symSeg2PreHi2 F_fwd := by
    dsimp only [SymSpatial, cfgSeg2Fwd, PolySymBridge.polyPtr, symSeg2PreHi2,
      SymSpill40.eval, SymVec32.eval, env']
    simp only [evalSExpr_gpr0_irrel, show ¬ (22#5 = 8#5) by decide, ↓reduceIte]
  rw [hspat4]
  refine sepWP_seq_env hcl4 hro4
    (sepWP_of_runSymRange (cfg := cfgSeg2Fwd) (env := env') (F := F_fwd)
      27 1295 noReloc_fwd1c (by decide) (by decide) (by decide)
      run_seg2_fwd1c hm4 hpc4 hrun4
      (post := fun s5 P5 => SymStateMatches sp env' symSeg2HiEnd s5 ∧
        P5 = SymSpatial cfgSeg2Fwd sp env' symSeg2HiEnd F_fwd)
      (fun s5 _ _ hm5 => ⟨hm5, rfl⟩)) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hm5, rfl⟩
  have hx23_s2 : s2.readReg64 .x23 = polyAddr + 16#64 := by
    rw [hx23_2, hx23_1, hx23]; dsimp only [polyAddr]; clear * -; bv_omega
  have hx24_s2 : s2.readReg64 .x24 = 16#64 + BitVec.ofNat 64 (512 * idx) :=
    hx24_2.trans (hx24_1.trans hx24)
  have hx8_5 : s5.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64 :=
    (hm5.hgprs 8#5 (by decide)).trans (BitVec.add_zero _)
  have hx9_5 : s5.readReg64 .x9 = polyAddr + 16#64 :=
    (hm5.hgprs 9#5 (by decide)).trans ((BitVec.add_zero (s2.readReg64 .x23)).trans hx23_s2)
  have hx10_5 : s5.readReg64 .x10 = 16#64 := hm5.hgprs 10#5 (by decide)
  have hx19_5 : s5.readReg64 .x19 = sp + 14432#64 :=
    (hm5.hgprs 19#5 (by decide)).trans ((BitVec.add_zero (s2.readReg64 .x19)).trans hx19_2)
  have hx22_5 : s5.readReg64 .x22 = polyAddr :=
    (hm5.hgprs 22#5 (by decide)).trans ((BitVec.add_zero (s2.readReg64 .x22)).trans hx22_2)
  have hx23_5 : s5.readReg64 .x23 = polyAddr + 16#64 :=
    (hm5.hgprs 23#5 (by decide)).trans ((BitVec.add_zero (s2.readReg64 .x23)).trans hx23_s2)
  have hx24_5 : s5.readReg64 .x24 = 16#64 + BitVec.ofNat 64 (512 * idx) :=
    (hm5.hgprs 24#5 (by decide)).trans ((BitVec.add_zero (s2.readReg64 .x24)).trans hx24_s2)
  have hfp_5 : s5.readReg64 .fp = s.readReg64 .fp :=
    (hm5.hgprs 29#5 (by decide)).trans
      ((BitVec.add_zero (s2.readReg64 .fp)).trans (hfp_2.trans hfp_1))
  have hx25_5 : s5.readReg64 .x25 = s.readReg64 .x25 :=
    (hm5.hgprs 25#5 (by decide)).trans
      ((BitVec.add_zero (s2.readReg64 .x25)).trans (hx25_2.trans hx25_1))
  have hx26_5 : s5.readReg64 .x26 = s.readReg64 .x26 :=
    (hm5.hgprs 26#5 (by decide)).trans
      ((BitVec.add_zero (s2.readReg64 .x26)).trans (hx26_2.trans hx26_1))
  have hx27_5 : s5.readReg64 .x27 = sp + 4160#64 :=
    (hm5.hgprs 27#5 (by decide)).trans
      ((BitVec.add_zero (s2.readReg64 .x27)).trans (hx27_2.trans hx27_1))
  have hx28_5 : s5.readReg64 .x28 = 62209#64 :=
    (hm5.hgprs 28#5 (by decide)).trans
      ((BitVec.add_zero (s2.readReg64 .x28)).trans (hx28_2.trans (hx28_1.trans hx28)))
  have hv8_5 : (s5.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 := by
    have hv : s5.readVReg128 8#5 = s2.readVReg128 8#5 := hm5.hvregs 8#5
    exact hv ▸ hv8_2
  have hv11_5 : s5.readVReg128 11#5 = dup8x16 3329#16 := hm5.hvregs 11#5
  have hp5_mem : Poly32Mem (PolySymBridge.polyPtr cfgSeg2Fwd sp env') (symSeg2HiEnd.poly.eval env') =
      PolyMem polyAddr (polyVecNat (lowerNtt5_16 p0)) := by
    have hptr : PolySymBridge.polyPtr cfgSeg2Fwd sp env' = polyAddr := hx22_2
    rw [hptr]
    exact poly_eq_lowerNtt5 polyAddr hp0 env' rfl symSeg2HiEnd.poly seg2_hi_noSpillVreg seg2_hi_ast_eq
  set p5 := lowerNtt5_16 p0
  have hp5 : p5.size = 256 := (lowerNtt5_16_size p0).trans hp0
  have hP5 : SymSpatial cfgSeg2Fwd sp env' symSeg2HiEnd F_fwd ⊢
      PolyMem polyAddr (polyVecNat p5) ∗ ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
        (SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 4160#64) 512 ∗ stackAt sp 1136 ∗
          ((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
          memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest) := by
    dsimp only [SymSpatial, F_fwd]
    rw [hp5_mem]
    have hsrc0 : PolySymBridge.SrcOptMem cfgSeg2Fwd.hasSrc sp env'.src0 = emp := rfl
    rw [hsrc0]
    dsimp only [cfgSeg2Fwd]
    rw [spillSlice21_seg2HiEnd]
    sep_frame
  refine SepWP.weaken_pre hP5
    (sepWP_seq_env hcl5 hro5
      (seg2_fwd_low_ok hb s5 sp polyAddr (ctPtr + 352#64) hp5 _
        hpc5 hrun5 hm5.hsp hm5.hsp_al hcl5 hro5 hx8_5 hx9_5 hx10_5 hx28_5
        (by rw [hx19_5, hx24_5]; dsimp only [polyAddr]; clear * -; bv_omega) hv11_5) ?_)
  rintro s6 P6 hpc6 hrun6 hcl6 hro6 ⟨hsp6, hspA6, hx0_6, hpres6, rfl⟩
  rcases hpres6 with ⟨hp8, _, hpfp, hp19, _, _, hp22, hp23, hp24, hp25, hp26, hp27, hp28⟩
  set q := lowerFwdNtt16 p5
  have hq : q.size = 256 := (lowerFwdNtt16_size p5).trans hp5
  set envB := mkSymEnv s6 q
  set F_bar := ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
    SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
    memRegion (sp + 4160#64) 512 ∗ stackAt sp 1136 ∗
    ((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
    memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest
  have hP6 : PolyMem polyAddr (polyVecNat q) ∗ F_bar ⊢
      SymSpatial cfgSeg2Barrett sp envB symInitState F_bar := by
    dsimp only [SymSpatial, cfgSeg2Barrett, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem,
      SpillSliceMem, VecRangeMem, envB, mkSymEnv]
    rw [hp22.trans hx22_5, ← poly32Mem_ofFn polyAddr (polyVecNat q)]
    change Poly32Mem polyAddr _ ∗ F_bar ⊢ emp ∗ Poly32Mem polyAddr _ ∗ emp ∗ F_bar
    sep_frame
  refine SepWP.weaken_pre hP6
    (sepWP_seq_env hcl6 hro6
      (sepWP_of_runSymRange (cfg := cfgSeg2Barrett) (env := envB) (F := F_bar)
        166 1383 noReloc_barrett (by decide) (by decide) (by decide)
        run_seg2_barrett (matches_initState q hsp6 hspA6) hpc6 hrun6
        (post := fun s7 P7 => SymStateMatches sp envB symSeg2BarrettEnd s7 ∧
          P7 = SymSpatial cfgSeg2Barrett sp envB symSeg2BarrettEnd F_bar)
        (fun s7 _ _ hm7 => ⟨hm7, rfl⟩)) ?_)
  rintro s7 P7 hpc7 hrun7 _ _ ⟨hm7, rfl⟩
  have hp7_mem : Poly32Mem (PolySymBridge.polyPtr cfgSeg2Barrett sp envB)
      (symSeg2BarrettEnd.poly.eval envB) =
      PolyMem polyAddr (polyVecNat (uHatPoly16 ctSlice)) := by
    have hptr : PolySymBridge.polyPtr cfgSeg2Barrett sp envB = polyAddr := hp22.trans hx22_5
    rw [hptr, poly_eq_barrett polyAddr hq envB rfl symSeg2BarrettEnd.poly
      seg2_barrett_noSpillVreg seg2_barrett_ast_eq, barrett_lowerFwd_lower5 p0]
    rfl
  have hP7 : SymSpatial cfgSeg2Barrett sp envB symSeg2BarrettEnd F_bar ⊢
      ((sp + 2400#64) ↦₆₄ (BitVec.ofNat 64 idx + 1#64)) ∗
        ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
        (stackAt sp 1136 ∗ SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
          PolyMem polyAddr (polyVecNat (uHatPoly16 ctSlice)) ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest) := by
    dsimp only [SymSpatial, F_bar]
    rw [hp7_mem]
    have hsp0 : SpillSliceMem cfgSeg2Barrett.spillLen
        (sp + BitVec.ofNat 64 cfgSeg2Barrett.spillOff)
        (symSeg2BarrettEnd.spill.eval envB) = emp := rfl
    have hsrc0 : PolySymBridge.SrcOptMem cfgSeg2Barrett.hasSrc sp envB.src0 = emp := rfl
    rw [hsp0, hsrc0]
    sep_frame
  refine SepWP.weaken_pre hP7
    (SepWP.mono (seg2_loop_tail hb hbase s7 sp (ctPtr + 352#64) hidx _
      hpc7 hrun7 hm7.hsp hm7.hsp_al) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx0_f, hx19_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hvregs_f, hPf⟩
  have hfp_7 : s7.readReg64 .fp = s.readReg64 .fp := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hpfp.trans hfp_5] using
      hm7.hgprs 29#5 (by decide)
  have hx0_7 : s7.readReg64 .x0 = ctPtr + 352#64 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hx0_6] using
      hm7.hgprs 0#5 (by decide)
  have hx19_7 : s7.readReg64 .x19 = sp + 14432#64 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hp19.trans hx19_5] using
      hm7.hgprs 19#5 (by decide)
  have hx23_7 : s7.readReg64 .x23 = sp + 14448#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    have h7 := hm7.hgprs 23#5 (by decide)
    simp only [BitVec.toNat_ofNat, symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv] at h7
    rw [show s7.readReg64 (.gpr 23#5) = s7.readReg64 .x23 from rfl,
      show s6.readReg64 (.gpr 23#5) = s6.readReg64 .x23 from rfl, hp23, hx23_5] at h7
    rw [h7]; dsimp only [polyAddr]; clear * - hidx; bv_omega
  have hx24_7 : s7.readReg64 .x24 = 16#64 + BitVec.ofNat 64 (512 * (idx + 1)) := by
    have h7 := hm7.hgprs 24#5 (by decide)
    simp only [BitVec.toNat_ofNat, symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv] at h7
    rw [show s7.readReg64 (.gpr 24#5) = s7.readReg64 .x24 from rfl,
      show s6.readReg64 (.gpr 24#5) = s6.readReg64 .x24 from rfl, hp24, hx24_5] at h7
    rw [h7]; clear * - hidx; bv_omega
  have hx25_7 : s7.readReg64 .x25 = s.readReg64 .x25 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hp25.trans hx25_5] using
      hm7.hgprs 25#5 (by decide)
  have hx26_7 : s7.readReg64 .x26 = s.readReg64 .x26 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hp26.trans hx26_5] using
      hm7.hgprs 26#5 (by decide)
  have hx27_7 : s7.readReg64 .x27 = sp + 4160#64 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hp27.trans hx27_5] using
      hm7.hgprs 27#5 (by decide)
  have hx28_7 : s7.readReg64 .x28 = 62209#64 := by
    simpa [symSeg2BarrettEnd, SymGprs.get, evalSymGpr, envB, mkSymEnv, hp28.trans hx28_5] using
      hm7.hgprs 28#5 (by decide)
  have hv8_f : (sf.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 := by
    have h7 : s7.readVReg128 8#5 = s6.readVReg128 8#5 := hm7.hvregs 8#5
    have hf7 : sf.readVReg128 8#5 = s7.readVReg128 8#5 := by simp [State.readVReg128, hvregs_f]
    rw [hf7, h7, hp8]; exact hv8_5
  exact ⟨hsp_f, hspA_f, hfp_f.trans hfp_7, hx0_f.trans hx0_7, hx19_f.trans hx19_7, hx22_f,
    hx23_f.trans hx23_7, hx24_f.trans hx24_7, hx25_f.trans hx25_7, hx26_f.trans hx26_7,
    hx27_f.trans hx27_7, hx28_f.trans hx28_7, hv8_f, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2UhatIter
