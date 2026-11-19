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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 8c (`+0xcfb4 .. +0xd13c` `ret`)

Steps Loop 2 (`compress_and_serialize_4` writing `c₂'` at `sp + 18992`), `B28` `memcpy` of the
`1,088`-byte `c' = c₁' ++ c₂'` into `sp + 22400`, `B16` Fujisaki–Okamoto constant-time ciphertext
comparison & shared-secret selection, and the callee-saved frame restoration + `ret` epilogue.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8c

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData09Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemCall_of_blockOk mlkemMpl resolve_ro09)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs (
  CtCompareSelectArgs CtCompareSelectPurePre mlkemCompareSelectRWSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps (blk16_compare_select_RW_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_7_vec mlkemData09Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonCompressSerialize4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane32 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdExt16b simdSqdmulh4s simdTrn1_8h simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (simdAddv4h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow (
  neonSerialize4Bytes neonSerialize4HalfWord32 neonSerialize4Lowt neonSerialize4Word64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 Vec128At VecRangeMem SepWP.of_memRegion_vecRangeMem
  append_extractLsb64 oct8Mem_ofFn polyVecNat step_ldpQ128 unpack128 vecRangeBytes
  vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdUshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_fmov_w_s exec_simdAdd_4s exec_simdAddv_4h exec_simdAnd_16b exec_simdBic_4s_15
  exec_simdCmltZero_8h exec_simdDup_4s exec_simdMovi_8h_15 exec_simdShl_4s_4
  exec_simdSqdmulh_4s exec_simdUshr_4s_4 exec_simdUshr_4s_12
  seg5Loop2_addv4h_ext8_eq seg5Loop2_compress_eq seg5Loop2_lowt_eq seg5_compressSerialize4_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04
  savedFrame04_entails_memRegion160)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8b (offSeg8bEnd)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xcfb4 → 0xd13c]
gen_placed_odd_sites blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xcfdc → 0xcfe8]

@[simp, arm64_norm]
private theorem blkPC04_rebase_fetchOff_cfe8 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 53224) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 5)
        (.Offset (.gpr (BitVec.ofNat 5 8))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.7")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04) (b := b) (X := X) (off := 53224)
    (r := { off := 53224, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.7" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 53224)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 13306) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

private theorem blk28_memcpy_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk28_memcpy_ok

private theorem blk16_ct_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 16)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemCompareSelectRWSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk16_compare_select_RW_ok

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC04
attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_15 exec_simdBic_4s_15 exec_simdAnd_16b exec_fmov_w_s
  exec_simdDup_4s exec_simdCmltZero_8h exec_simdShl_4s_4 exec_simdUshr_4s_12
  exec_simdUshr_4s_4 exec_simdAdd_4s exec_simdSqdmulh_4s exec_simdAddv_4h
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h svc_simdExt_16b_8 exec_simdUshl_8h

@[simp, arm64_norm, wp_norm] abbrev offCffc : BitVec 64 := BitVec.ofNat 64 53244
@[simp, arm64_norm, wp_norm] abbrev offD020 : BitVec 64 := BitVec.ofNat 64 53280
@[simp, arm64_norm, wp_norm] abbrev offD03c : BitVec 64 := BitVec.ofNat 64 53308
@[simp, arm64_norm, wp_norm] abbrev offD040 : BitVec 64 := BitVec.ofNat 64 53312
@[simp, arm64_norm, wp_norm] abbrev offD044 : BitVec 64 := BitVec.ofNat 64 53316
@[simp, arm64_norm, wp_norm] abbrev offD054 : BitVec 64 := BitVec.ofNat 64 53332
@[simp, arm64_norm, wp_norm] abbrev offD06c : BitVec 64 := BitVec.ofNat 64 53356
@[simp, arm64_norm, wp_norm] abbrev offD088 : BitVec 64 := BitVec.ofNat 64 53384
@[simp, arm64_norm, wp_norm] abbrev offD0bc : BitVec 64 := BitVec.ofNat 64 53436
@[simp, arm64_norm, wp_norm] abbrev offD0c0 : BitVec 64 := BitVec.ofNat 64 53440
@[simp, arm64_norm, wp_norm] abbrev offD0cc : BitVec 64 := BitVec.ofNat 64 53452
@[simp, arm64_norm, wp_norm] abbrev offD0e4 : BitVec 64 := BitVec.ofNat 64 53476
@[simp, arm64_norm, wp_norm] abbrev offD10c : BitVec 64 := BitVec.ofNat 64 53516

/-! ## 1. 64-Bit Scratch Array (`WordRangeMem`) & Byte-Packing Bridges -/

private def serWord (re : Poly16) (c : Nat) : BitVec 64 :=
  neonSerialize4Word64 (neonCompress8h 4 (polyVecNat re (2 * c)))
    (neonCompress8h 4 (polyVecNat re (2 * c + 1)))

private def serVec (re : Poly16) (k : Nat) : BitVec 128 := serWord re (2 * k + 1) ++ serWord re (2 * k)

private def WordRangeMem : Nat → BitVec 64 → (Nat → BitVec 64) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, w => (ptr ↦₆₄ w 0) ∗ WordRangeMem n (ptr + 8#64) (fun i => w (i + 1))

private theorem wordRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 64}
    (h : ∀ i, i < n → f i = g i) : WordRangeMem n ptr f = WordRangeMem n ptr g := by
  induction n generalizing ptr f g with
  | zero => rfl
  | succ n ih =>
    simp only [WordRangeMem, h 0 (Nat.zero_lt_succ n),
      ih (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))]

private theorem SepStore64.wordRange {n c : Nat} {ea ptr val : BitVec 64} {w : Nat → BitVec 64}
    (hc : c < n) (ha : ptr + BitVec.ofNat 64 (8 * c) = ea) :
    SepStore64 ea val (WordRangeMem n ptr w) (WordRangeMem n ptr (Function.update w c val)) := by
  induction n generalizing c ptr w with
  | zero => omega
  | succ n ih =>
    rcases c with _ | c
    · simp only [Nat.mul_zero, BitVec.add_zero] at ha
      have htail : WordRangeMem n (ptr + 8#64) (fun i => Function.update w 0 val (i + 1)) =
          WordRangeMem n (ptr + 8#64) (fun i => w (i + 1)) :=
        wordRangeMem_congr fun i _ => Function.update_of_ne (Nat.succ_ne_zero i) val w
      simp only [WordRangeMem, Function.update_self, htail]; exact (SepStore64.here ha).left
    · have ha' : (ptr + 8#64) + BitVec.ofNat 64 (8 * c) = ea := by
        rw [← ha, BitVec.add_assoc]; congr 1
        rw [show 8 * (c + 1) = 8 + 8 * c by omega, BitVec.ofNat_add]
      have hhead : Function.update w (c + 1) val 0 = w 0 :=
        Function.update_of_ne (Nat.succ_ne_zero c).symm val w
      have htail : (fun i => Function.update w (c + 1) val (i + 1)) =
          Function.update (fun i => w (i + 1)) c val := by
        funext i; by_cases h : i = c
        · subst h; simp
        · simp [Function.update_of_ne h, Function.update_of_ne (show i + 1 ≠ c + 1 by omega)]
      simp only [WordRangeMem, hhead, htail]; exact (ih (by omega) ha').right

private theorem wordRangeMem_eq_vecRangeMem (m : Nat) (ptr : BitVec 64) (w : Nat → BitVec 64) :
    WordRangeMem (2 * m) ptr w = VecRangeMem m ptr (fun k => w (2 * k + 1) ++ w (2 * k)) := by
  induction m generalizing ptr w with
  | zero => rfl
  | succ m ih =>
    have hmul : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    have ha16 : (ptr + 8#64) + 8#64 = ptr + 16#64 := by bv_omega
    have hlo : (w 1 ++ w 0).extractLsb' 0 64 = w 0 := by bv_bits
    have hhi : (w 1 ++ w 0).extractLsb' 64 64 = w 1 := by bv_bits
    rw [hmul]; simp only [WordRangeMem, VecRangeMem, Vec128At, Nat.mul_zero, Nat.zero_add,
      hlo, hhi, ha16, ih (ptr + 16#64) (fun i => w (i + 2))]
    rw [← sepConj_assoc]; rfl

private theorem vecRangeMem_eq_wordRangeMem (m : Nat) (ptr : BitVec 64) (f : Nat → BitVec 128) :
    VecRangeMem m ptr f = WordRangeMem (2 * m) ptr
      (fun i => if i % 2 = 0 then (f (i / 2)).extractLsb' 0 64 else (f (i / 2)).extractLsb' 64 64) := by
  rw [wordRangeMem_eq_vecRangeMem]; exact vecRangeMem_congr fun k _ => by
    simp only [show (2 * k + 1) % 2 = 1 by omega, show 1 ≠ 0 by decide, ↓reduceIte,
      show (2 * k + 1) / 2 = k by omega, show (2 * k) % 2 = 0 by omega,
      show (2 * k) / 2 = k by omega, append_extractLsb64]

private theorem oct8Mem_serVec_eq_pointsTo (ret : BitVec 64) (re : Poly16) :
    Oct8Mem ret (Oct8.ofFn (serVec re)) = (ret ↦ₛ neonCompressSerialize4 re) := by
  rw [oct8Mem_ofFn]; change VecRangeMem 8 ret (serVec re) = (ret ↦ₛ neonCompressSerialize4 re)
  rw [vecRangeMem_eq_pointsToBytes 8 ret (serVec re), ← seg5_compressSerialize4_eq re]; congr 1
  have hu (k : Nat) : unpack128 (serVec re k) =
      neonSerialize4Bytes (neonCompress8h 4 (polyVecNat re (2 * (2 * k))))
        (neonCompress8h 4 (polyVecNat re (2 * (2 * k) + 1))) ++
      neonSerialize4Bytes (neonCompress8h 4 (polyVecNat re (2 * (2 * k + 1))))
        (neonCompress8h 4 (polyVecNat re (2 * (2 * k + 1) + 1))) := by
    have hlo : (serWord re (2 * k + 1) ++ serWord re (2 * k)).extractLsb' 0 64 = serWord re (2 * k) := by bv_bits
    have hhi : (serWord re (2 * k + 1) ++ serWord re (2 * k)).extractLsb' 64 64 = serWord re (2 * k + 1) := by bv_bits
    unfold unpack128 serVec; rw [hlo, hhi]; rfl
  have hr16 : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  rw [hr16]; dsimp only [vecRangeBytes, List.map, List.flatten]
  simp only [hu, List.append_assoc, List.append_nil]; rfl

/-! ## 2. Loop-2 Setup (`+0xcfb4 → +0xcffc`) & 16-Iter `compress_and_serialize_4` (`+0xcffc → +0xd0cc`) -/

attribute [local irreducible]
  WordRangeMem dup8x16 pack4x32 lane32 polyVecNat simdAdd8h simdCmltZero8h simdSqdmulh4s
  simdAddv4h simdTrn1_8h simdExt16b simdUshl8h neonCompress8h neonSerialize4Lowt

private def Loop2Inv (s : State) (sp fpVal : BitVec 64) (c : Nat) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * c) ∧
  s.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x10 = sp + 18032#64 ∧ s.readReg64 .fp = fpVal ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128

private theorem seg8c_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offSeg8bEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offCffc) s P
      (fun sm Pm => Loop2Inv sm sp fpVal 0 ∧ Pm = P) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  wp_steps
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_7 mlkemData09Bytes_length cst16_7_vec (by wp_norm_lhs) ?_
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  refine ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
    by simp, by simp, by simp, by simp [hfp], by simp, by simp, by simp, by simp, ?_, by simp⟩, rfl⟩
  congr 1

attribute [local irreducible] evalBitfield neonSerialize4Word64

private def Loop2Mid (s : State) (sp fpVal : BitVec 64) (re : Poly16) (c : Nat) : Prop :=
  let lowt0 := neonSerialize4Lowt (neonCompress8h 4 (polyVecNat re (2 * c)))
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
  s.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x10 = sp + 18032#64 ∧ s.readReg64 .fp = fpVal ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
  s.readVReg128 6#5 = (simdAddv4h lowt0).zeroExtend 128 ∧
  s.readVReg128 7#5 = neonCompress8h 4 (polyVecNat re (2 * c + 1)) ∧
  s.readVReg128 16#5 = (lowt0.truncate 64 ++ lowt0.extractLsb' 64 64)

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

private theorem seg8c_iter_a1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (Rest : SepProp) (hpc : s.pc = b + offCffc)
    (hrun : s.status = .Running) (hinv : Loop2Inv s sp fpVal c) :
    let u0 := simdAdd8h (simdCmltZero8h (polyVecNat re (2 * c)) &&& dup8x16 3329#16)
      (polyVecNat re (2 * c))
    let u1 := simdAdd8h (simdCmltZero8h (polyVecNat re (2 * c + 1)) &&& dup8x16 3329#16)
      (polyVecNat re (2 * c + 1))
    let ev0 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j <<< 4) &&& (pack4x32 fun _ => 1048560#32)) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    let od0 := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j >>> 12) &&& 0xfffffff0fffffff0fffffff0fffffff0#128) k +
        lane32 (pack4x32 fun _ => 1664#32) k
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD03c) s
      (PolyMem (sp + 23936#64) (polyVecNat re) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
        s1.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
        s1.readReg64 .x10 = sp + 18032#64 ∧ s1.readReg64 .fp = fpVal ∧
        s1.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s1.readVReg128 1#5 = dup8x16 3329#16 ∧
        s1.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
        s1.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
        s1.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
        s1.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
        s1.readVReg128 6#5 = od0 ∧ s1.readVReg128 7#5 = (pack4x32 fun j => lane32 u1 j >>> 12) ∧
        s1.readVReg128 16#5 = ev0 ∧ s1.readVReg128 17#5 = (pack4x32 fun j => lane32 u1 j <<< 4) ∧
        P1 = (PolyMem (sp + 23936#64) (polyVecNat re) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  intro u0 u1 ev0 od0
  rcases hinv with ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5⟩
  have hea1 : (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * c)) + 16#64 =
      (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * c + 1)) := by clear * - hc; bv_omega
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * c)))
    (ea16 := (sp + 23936#64) + BitVec.ofNat 64 (16 * (2 * c + 1)))
    (by wp_norm_lhs) hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hc; bv_omega) hea1
    (SepLoad128.vecRange (n := 32) (k := 2 * c) (by omega) rfl).left
    (SepLoad128.vecRange (n := 32) (k := 2 * c + 1) (by omega) rfl).left
    (by wp_norm_lhs) ?_
  wp_steps 8
  refine sepWP_cut (fun sm => sm.pc = blkPl04.base + offD020 ∧ sm.status = .Running ∧
    sm.sp = sp ∧ sm.spAligned = true ∧
    sm.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
    sm.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
    sm.readReg64 .x10 = sp + 18032#64 ∧ sm.readReg64 .fp = fpVal ∧
    sm.readVReg128 0#5 = dup8x16 0x000f#16 ∧ sm.readVReg128 1#5 = dup8x16 3329#16 ∧
    sm.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
    sm.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
    sm.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
    sm.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
    sm.readVReg128 6#5 = (pack4x32 fun j => lane32 u0 j >>> 12) ∧
    sm.readVReg128 7#5 = polyVecNat re (2 * c + 1) ∧
    sm.readVReg128 16#5 = (simdCmltZero8h (polyVecNat re (2 * c + 1)) &&& dup8x16 3329#16) ∧
    sm.readVReg128 17#5 = (pack4x32 fun j => lane32 u0 j <<< 4))
    ⟨by wp_norm_lhs, by simp [hrun], by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp; clear * - hc; bv_omega, by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl⟩ ?_
  clear hpc hrun hsp hspA hx8 hx9 hx10 hfp hv0 hv1 hv2 hv3 hv4 hv5 hea1
  rintro sm ⟨hpc, hrun, hsp, hspA, hx8, hx9, hx10, hfp,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩
  wp_steps 7
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl, rfl⟩

private def IterAState (s : State) (sp fpVal : BitVec 64) (c : Nat)
    (v6 v7 v16 v17 : BitVec 128) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
  s.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x10 = sp + 18032#64 ∧ s.readReg64 .fp = fpVal ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
  s.readVReg128 6#5 = v6 ∧ s.readVReg128 7#5 = v7 ∧
  s.readVReg128 16#5 = v16 ∧ s.readVReg128 17#5 = v17

private theorem seg8c_iter_a2_s1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s1 : State) (sp fpVal : BitVec 64) (od0 v7_in ev0 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + offD03c) (hrun1 : s1.status = .Running)
    (h1 : IterAState s1 sp fpVal c od0 v7_in ev0 v17_in) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD040) s1 P1
      (fun sm Pm => IterAState sm sp fpVal c od0 v7_in
        (simdSqdmulh4s ev0 (pack4x32 fun _ => 10321340#32)) v17_in ∧ Pm = P1) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩
  wp_step
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp [hv6], by simp [hv7],
      by simp only [wp_norm, arm64_norm]; try rfl, by simp [hv17]⟩, rfl⟩

private theorem seg8c_iter_a2_s2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s1 : State) (sp fpVal : BitVec 64) (od0 v7_in ev1 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + offD040) (hrun1 : s1.status = .Running)
    (h1 : IterAState s1 sp fpVal c od0 v7_in ev1 v17_in) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD044) s1 P1
      (fun sm Pm => IterAState sm sp fpVal c
        (simdSqdmulh4s od0 (pack4x32 fun _ => 10321340#32)) v7_in ev1 v17_in ∧ Pm = P1) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩
  wp_step
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp [hv7], by simp [hv16], by simp [hv17]⟩, rfl⟩

private theorem seg8c_iter_a2_s3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s1 : State) (sp fpVal : BitVec 64) (od1 v7_in ev1 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + offD044) (hrun1 : s1.status = .Running)
    (h1 : IterAState s1 sp fpVal c od1 v7_in ev1 v17_in) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD054) s1 P1
      (fun sm Pm => IterAState sm sp fpVal c od1
        (v7_in &&& 0xfffffff0fffffff0fffffff0fffffff0#128)
        (pack4x32 fun k => lane32 ev1 k >>> 4)
        (pack4x32 fun k =>
          lane32 (v17_in &&& (pack4x32 fun _ => 1048560#32)) k +
            lane32 (pack4x32 fun _ => 1664#32) k) ∧ Pm = P1) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩
  wp_steps 4
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp [hv6],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl⟩, rfl⟩

private theorem seg8c_iter_a2 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s1 : State) (sp fpVal : BitVec 64) (od0 v7_in ev0 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + offD03c) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (h1 : IterAState s1 sp fpVal c od0 v7_in ev0 v17_in) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD06c) s1 P1
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
        s2.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
        s2.readReg64 .x10 = sp + 18032#64 ∧ s2.readReg64 .fp = fpVal ∧
        s2.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s2.readVReg128 1#5 = dup8x16 3329#16 ∧
        s2.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
        s2.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
        s2.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
        s2.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
        s2.readVReg128 6#5 = simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s ev0 (pack4x32 fun _ => 10321340#32)) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s od0 (pack4x32 fun _ => 10321340#32)) k >>> 4) ∧
        s2.readVReg128 7#5 = simdSqdmulh4s
          (pack4x32 fun k =>
            lane32 (v7_in &&& 0xfffffff0fffffff0fffffff0fffffff0#128) k +
              lane32 (pack4x32 fun _ => 1664#32) k)
          (pack4x32 fun _ => 10321340#32) ∧
        s2.readVReg128 16#5 =
          (pack4x32 fun k =>
            lane32 (simdSqdmulh4s
              (pack4x32 fun k =>
                lane32 (v17_in &&& (pack4x32 fun _ => 1048560#32)) k +
                  lane32 (pack4x32 fun _ => 1664#32) k)
              (pack4x32 fun _ => 10321340#32)) k >>> 4) ∧ P2 = P1) := by
  refine sepWP_seq_env hcl1 hro1
    (seg8c_iter_a2_s1 hb s1 sp fpVal od0 v7_in ev0 v17_in c P1 hpc1 hrun1 h1) ?_
  clear hpc1 hrun1 hcl1 hro1 h1
  rintro sa _ hpca hruna hcla hroa ⟨ha, rfl⟩
  refine sepWP_seq_env hcla hroa
    (seg8c_iter_a2_s2 hb sa sp fpVal od0 v7_in _ v17_in c _ hpca hruna ha) ?_
  clear hpca hruna hcla hroa ha
  rintro sb _ hpcb hrunb hclb hrob ⟨hb_st, rfl⟩
  refine sepWP_seq_env hclb hrob
    (seg8c_iter_a2_s3 hb sb sp fpVal _ v7_in _ v17_in c _ hpcb hrunb hb_st) ?_
  clear hpcb hrunb hclb hrob hb_st
  rintro sm _ hpc hrun _ _ ⟨⟨hsp, hspA, hx8, hx9, hx10, hfp,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩, rfl⟩
  have hbase : blkPl04.base = b := hb.symm; subst hbase
  wp_steps 6
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl, rfl⟩

private theorem seg8c_iter_a [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (Rest : SepProp) (hpc : s.pc = b + offCffc) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hinv : Loop2Inv s sp fpVal c) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD088) s
      (PolyMem (sp + 23936#64) (polyVecNat re) ∗ Rest)
      (fun sm Pm => Loop2Mid sm sp fpVal re c ∧
        Pm = (PolyMem (sp + 23936#64) (polyVecNat re) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg8c_iter_a1 hb s sp fpVal re hc Rest hpc hrun hinv) ?_
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp, hspA, hx8, hx9, hx10, hfp,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg8c_iter_a2 hb s1 sp fpVal _ _ _ _ c _ hpc1 hrun1 hcl1 hro1
      ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17⟩) ?_
  clear hpc1 hrun1 hcl1 hro1 hsp hspA hx8 hx9 hx10 hfp hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv16 hv17
  rintro s2 _ hpc hrun _ _ ⟨hsp, hspA, hx8, hx9, hx10, hfp,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, rfl⟩
  have hbase : blkPl04.base = b := hb.symm; subst hbase
  wp_steps 7
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) ⟨⟨by simp [hsp],
    by simpa [State.spAligned, hsp] using hspA, by simp [hx8], by simp [hx9],
    by simp [hx10], by simp [hfp],
    by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
    ?_, ?_, ?_⟩, rfl⟩
  · conv => lhs; simp only [wp_norm, arm64_norm]
    rw [seg5Loop2_compress_eq (polyVecNat re (2 * c)), seg5Loop2_lowt_eq (polyVecNat re (2 * c))]
  · conv => lhs; simp only [wp_norm, arm64_norm]
    exact seg5Loop2_compress_eq (polyVecNat re (2 * c + 1))
  · conv => lhs; simp only [wp_norm, arm64_norm]
    rw [seg5Loop2_compress_eq (polyVecNat re (2 * c)), seg5Loop2_lowt_eq (polyVecNat re (2 * c))]

private theorem word64_assemble_bits (s1_6 s0_6 s1_7 s0_7 : BitVec 16) :
    let w11 := ((s1_6.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_0 := ((s0_6.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_1 := ((s0_7.zeroExtend 128).truncate 32).zeroExtend 64
    let w12_2 := ((s1_7.zeroExtend 128).truncate 32).zeroExtend 64
    (((BitVec.zeroExtend 64 (BitVec.truncate 32 (w11 <<< 16)) &&& 0xffffffffffff0000#64) |||
      (w12_0 >>> 0 &&& 65535#64)) ||| (w12_1 <<< 32)) ||| (w12_2 <<< 48) =
    (s1_7 ++ s0_7) ++ (s1_6 ++ s0_6) := by
  dsimp only
  have hz32 (x : BitVec 16) :
      ((x.zeroExtend 128).truncate 32).zeroExtend 64 = x.zeroExtend 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
  have hm1 : ∀ k : Fin 64, (0xffffffffffff0000#64).getLsbD k.val = decide (16 ≤ k.val) := by decide
  have hm0 : ∀ k : Fin 64, (65535#64).getLsbD k.val = decide (k.val < 16) := by decide
  rw [hz32, hz32, hz32, hz32, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hm1k := hm1 ⟨k, hk⟩; have hm0k := hm0 ⟨k, hk⟩
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.truncate_eq_setWidth, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth, hm1k, hm0k, hk, decide_true, Bool.true_and]
  by_cases hk16 : k < 16
  · simp [hk16, show k < 32 by omega, show k < 48 by omega, show ¬ (16 ≤ k) by omega]
  · by_cases hk32 : k < 32
    · simp [hk16, hk32, show k < 48 by omega, show 16 ≤ k by omega,
        show k - 16 < 64 by omega, show k - 16 < 16 by omega]
    · by_cases hk48 : k < 48
      · simp [hk16, hk32, hk48, show k - 32 < 64 by omega, show k - 32 < 16 by omega]
      · simp [hk16, hk32, hk48, show k - 32 < 64 by omega,
          BitVec.getLsbD_of_ge s0_7 (k - 32) (by omega), show ¬ (k - 32 < 16) by omega,
          show k - 48 < 64 by omega, show k - 32 - 16 = k - 48 by omega]

private theorem seg8c_iter_b [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (w : Nat → BitVec 64) (Rest : SepProp) (hpc : s.pc = b + offD088)
    (hrun : s.status = .Running) (hmid : Loop2Mid s sp fpVal re c) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + offCffc else b + offD0cc) s
      (WordRangeMem 16 (sp + 18992#64) w ∗ Rest)
      (fun s' P' => Loop2Inv s' sp fpVal (c + 1) ∧
        P' = (WordRangeMem 16 (sp + 18992#64) (Function.update w c (serWord re c)) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  rcases hmid with ⟨hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16⟩
  wp_steps 13
  refine sepWP_cut (fun s1 => s1.pc = blkPl04.base + offD0bc ∧ s1.status = .Running ∧
    s1.sp = sp ∧ s1.spAligned = true ∧
    s1.readReg64 .x8 = sp + 23952#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
    s1.readReg64 .x9 = 960#64 + BitVec.ofNat 64 (8 * c) ∧
    s1.readReg64 .x10 = sp + 18032#64 ∧ s1.readReg64 .fp = fpVal ∧
    s1.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s1.readVReg128 1#5 = dup8x16 3329#16 ∧
    s1.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
    s1.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
    s1.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
    s1.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
    s1.readReg64 .x11 = serWord re c)
    ⟨by wp_norm_lhs, by simp [hrun], by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5], ?_⟩ ?_
  · have htr32 (x : BitVec 32) : (x.zeroExtend 64).truncate 32 = x := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
    conv => lhs; simp only [wp_norm, arm64_norm, htr32]
    rw [seg5Loop2_lowt_eq (polyVecNat re (2 * c + 1)),
        seg5Loop2_addv4h_ext8_eq, seg5Loop2_addv4h_ext8_eq]
    unfold serWord neonSerialize4Word64 neonSerialize4HalfWord32; dsimp only
    exact word64_assemble_bits _ _ _ _
  clear hpc hrun hsp hspA hx8 hx9 hx10 hfp hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv16
  rintro s1 ⟨hpc, hrun, hsp, hspA, hx8, hx9, hx10, hfp, hv0, hv1, hv2, hv3, hv4, hv5, hx11⟩
  refine SepWP.step_str64 (s' := s1.setPC (blkPl04.base + offD0c0))
    (ea := (sp + 18992#64) + BitVec.ofNat 64 (8 * c)) (wb := none)
    (val := serWord re c) hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx10, hx9]; clear * -; bv_omega) hx11
    (SepStore64.wordRange (n := 16) (c := c) hc rfl).left
    (by simp [applyWriteback]) ?_
  intro m'
  wp_steps 3
  wp_if hne
  · have hlt : c < 15 := by
      clear * - hc hne hx9
      by_contra hge; have hc15 : c = 15 := by omega
      subst hc15; simp_all
    simp only [hlt, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp [hx8], by simp; clear * - hc; bv_omega, by simp [hx10], by simp [hfp],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5]⟩, rfl⟩
  · have hlt : ¬ c < 15 := by
      clear * - hne hx9
      intro h; rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | c
      all_goals try simp_all
      omega
    have hc15 : c = 15 := by omega
    simp only [hlt, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp [hx8], by simp [hc15], by simp [hx10], by simp [hfp],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5]⟩, rfl⟩

private theorem seg8c_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (w : Nat → BitVec 64) (Rest : SepProp) (hpc : s.pc = b + offCffc) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hinv : Loop2Inv s sp fpVal c) :
    SepWP (blkPC04.rebase b (fun _ => none)) (if c < 15 then b + offCffc else b + offD0cc) s
      (PolyMem (sp + 23936#64) (polyVecNat re) ∗ WordRangeMem 16 (sp + 18992#64) w ∗ Rest)
      (fun s' P' => Loop2Inv s' sp fpVal (c + 1) ∧ P' = (PolyMem (sp + 23936#64) (polyVecNat re) ∗
        WordRangeMem 16 (sp + 18992#64) (Function.update w c (serWord re c)) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg8c_iter_a hb s sp fpVal re hc _ hpc hrun hcl hro hinv) ?_
  rintro sm _ hpcm hrunm _ _ ⟨hmid, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (SepWP.mono (seg8c_iter_b hb sm sp fpVal re hc w _ hpcm hrunm hmid) ?_)
  rintro s' _ _ _ ⟨hinv', rfl⟩; exact ⟨hinv', sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem update_serWord_prefix {re : Poly16} {w : Nat → BitVec 64} {c : Nat}
    (hw : ∀ j, j < c → w j = serWord re j) :
    ∀ j, j < c + 1 → Function.update w c (serWord re c) j = serWord re j := by
  intro j hj; by_cases h : j = c
  · subst h; simp
  · rw [Function.update_of_ne h]; exact hw j (by omega)

private theorem seg8c_loop2 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp fpVal : BitVec 64) (re : Poly16) (Rest : SepProp) :
    ∀ (rem c : Nat), c + rem = 15 → ∀ (s : State) (w : Nat → BitVec 64),
      s.pc = b + offCffc → s.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      Loop2Inv s sp fpVal c → (∀ j, j < c → w j = serWord re j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offD0cc) s
        (PolyMem (sp + 23936#64) (polyVecNat re) ∗ WordRangeMem 16 (sp + 18992#64) w ∗ Rest)
        (fun s' P' => s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = fpVal ∧
          P' = (PolyMem (sp + 23936#64) (polyVecNat re) ∗
            ((sp + 18992#64) ↦ₛ neonCompressSerialize4 re) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro c hrem s w hpc hrun hcl hro hinv hw; have hc15 : c = 15 := by omega
    subst hc15
    have hstep := seg8c_iter hb s sp fpVal re (c := 15) (by decide) w Rest hpc hrun hcl hro hinv
    simp only [Nat.lt_irrefl, ↓reduceIte] at hstep; refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨⟨hsp', hspA', _, _, _, hfp', _, _, _, _, _, _⟩, hP'⟩
    refine ⟨hsp', hspA', hfp', ?_⟩
    rw [hP', wordRangeMem_congr (update_serWord_prefix hw),
      wordRangeMem_eq_vecRangeMem 8 (sp + 18992#64) (serWord re)]
    change PolyMem (sp + 23936#64) (polyVecNat re) ∗
        PolyOctMem (sp + 18992#64) (serVec re) ∗ Rest = _
    rw [← oct8Mem_ofFn (sp + 18992#64) (serVec re), oct8Mem_serVec_eq_pointsTo]
  | succ rem ih =>
    intro c hrem s w hpc hrun hcl hro hinv hw; have hlt : c < 15 := by omega
    have hstep := seg8c_iter hb s sp fpVal re (c := c) (by omega) w Rest hpc hrun hcl hro hinv
    simp only [hlt, ↓reduceIte] at hstep; refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro' ⟨hinv', rfl⟩
    exact ih (c + 1) (by omega) sm _ hpc' hrun' hcl' hro' hinv' (update_serWord_prefix hw)

/-! ## 3. `B28` `memcpy`, `B16` FO Constant-Time Select & Epilogue (`+0xd0cc → ret`) -/

private theorem seg8c_memcpy [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal : BitVec 64) (c' : List (BitVec 8)) (Rest : SepProp)
    (hc' : c'.length = 1088)
    (hpc : s.pc = b + offD0cc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD0e4) s
      (((sp + 18032#64) ↦ₛ c') ∗ memRegion (sp + 22400#64) 1088 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = fpVal ∧
        Pf = (((sp + 18032#64) ↦ₛ c') ∗ ((sp + 22400#64) ↦ₛ c') ∗ Rest)) := by
  have hbase : blkPl04.base = b := hb.symm; subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 5
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 22400#64, sp + 18032#64, c')
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*],
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg8c_b16 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp fpVal ret : BitVec 64) (ct c' kGood kRej : List (BitVec 8)) (Rest : SepProp)
    (hct : ct.length = 1088) (hc' : c'.length = 1088)
    (hkGood : kGood.length = 32) (hkRej : kRej.length = 32)
    (hfp_sub : fpVal - 112#64 = sp + 25616#64)
    (hpc : s.pc = b + offD0e4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offD10c) s
      (((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ ((sp + 22400#64) ↦ₛ c') ∗
        ((sp + 4496#64) ↦ₛ kGood) ∗ ((sp + 25616#64) ↦ₛ kRej) ∗ stackAt sp 1136 ∗
        memRegion ret 32 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        Pf = ((ret ↦ₛ (if ct == c' then kGood else kRej)) ∗
          ((sp + 136#64) ↦₆₄ ret) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ ((sp + 22400#64) ↦ₛ c') ∗
          ((sp + 4496#64) ↦ₛ kGood) ∗ ((sp + 25616#64) ↦ₛ kRej) ∗ stackAt sp 1136 ∗ Rest)) := by
  have hbase : blkPl04.base = b := hb.symm; subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [stackAt_shrink sp 1136 112 (by decide) (by decide)]
  wp_steps 9
  have hfp_x6 : fpVal - 112#64 = sp + 25616#64 := hfp_sub
  wp_call (blk16_ct_04 blkPl04.base)
    ({ outPtr := ret, lhsCtPtr := sp + 3344#64, rhsCtPtr := sp + 22400#64,
       lhsSsPtr := sp + 4496#64, rhsSsPtr := sp + 25616#64,
       lhsCt := ct, rhsCt := c', lhsSs := kGood, rhsSs := kRej } : CtCompareSelectArgs)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*]) ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, ?_⟩
  rw [← stackAt_shrink sp 1136 112 (by decide) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

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

private theorem seg8c_epilogue [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (Rest : SepProp) (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + offD10c) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 25824#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame04 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  dsimp only [SavedFrame04]
  have hsp160 : (s0.sp - 25824#64) + 24576#64 + 1088#64 = s0.sp - 160#64 := by clear * -; bv_omega
  have hsp160_al : ((((s0.sp - 25824#64) + 24576#64 + 1088#64) &&& 15#64) == 0#64) = true := by
    rw [hsp160]; exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega), ?_⟩,
    sepConj_mono_left (savedFrame04_entails_memRegion160 s0.sp s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

/-- Segment 8c (`+0xcfb4 → ret`): `compress_and_serialize_4`, `memcpy` of `c'`, `B16` FO select,
    and callee-saved frame restoration + `ret`. -/
theorem seg8c_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (ret : BitVec 64) (re : Poly16)
    (ct ct1' kGood kRej : List (BitVec 8)) (Rest : SepProp)
    (hct : ct.length = 1088) (hct1' : ct1'.length = 960)
    (hkGood : kGood.length = 32) (hkRej : kRej.length = 32)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + offSeg8bEnd) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 25824#64) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let sp := s0.sp - 25824#64
    let c' := ct1' ++ neonCompressSerialize4 re
    SepWP (blkPC04.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (PolyMem (sp + 23936#64) (polyVecNat re) ∗
        ((sp + 18032#64) ↦ₛ ct1') ∗ memRegion (sp + 18992#64) 128 ∗
        memRegion (sp + 22400#64) 1088 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
        ((sp + 3344#64) ↦ₛ ct) ∗ ((sp + 4496#64) ↦ₛ kGood) ∗
        ((sp + 25616#64) ↦ₛ kRej) ∗ stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
        memRegion ret 32 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ (if ct == c' then kGood else kRej)) ∗
          memRegion (sp + 136#64) 8 ∗ memRegion (sp + 3344#64) 1088 ∗
          memRegion (sp + 4496#64) 32 ∗ memRegion (sp + 18032#64) 1088 ∗
          memRegion (sp + 22400#64) 1088 ∗ memRegion (sp + 23936#64) 512 ∗
          memRegion (sp + 25616#64) 32 ∗ stackAt sp 1136 ∗
          memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  intro sp c'
  have hc2' : (neonCompressSerialize4 re).length = 128 := by
    rw [← seg5_compressSerialize4_eq]
    have hr16 : List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
    rw [hr16]; simp [neonSerialize4Bytes, unpack64_length]
  have hc' : c'.length = 1088 := by dsimp only [c']; rw [List.length_append, hct1', hc2']
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 18992#64) (by decide) (by sep_focus); intro f0
  rw [vecRangeMem_eq_wordRangeMem 8 (sp + 18992#64) f0, show 2 * 8 = 16 from rfl]
  set w0 : Nat → BitVec 64 :=
    fun i => if i % 2 = 0 then (f0 (i / 2)).extractLsb' 0 64 else (f0 (i / 2)).extractLsb' 64 64
  refine sepWP_seq_env hcl hro (seg8c_setup hb s sp (s0.sp - 96#64) _ hpc hrun hsp hspA hfp hro) ?_
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hinv1, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg8c_loop2 hb sp (s0.sp - 96#64) re _ 15 0 rfl s1 w0 hpc1 hrun1 hcl1 hro1 hinv1
        (fun _ hj => by omega)) ?_)
  rintro s2 _ hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, rfl⟩
  have happ : ((sp + 18032#64) ↦ₛ c') =
      ((sp + 18032#64) ↦ₛ ct1') ∗ ((sp + 18992#64) ↦ₛ neonCompressSerialize4 re) := by
    dsimp only [c']; rw [pointsToBytes_append, hct1']
    have ha : (sp + 18032#64) + BitVec.ofNat 64 960 = sp + 18992#64 := by clear * -; bv_omega
    rw [ha]
  refine SepWP.weaken_pre (by rw [happ]; sep_frame)
    (sepWP_seq_env hcl2 hro2
      (seg8c_memcpy hb s2 sp (s0.sp - 96#64) c' _ hc' hpc2 hrun2 hsp2 hspA2 hfp2 hcl2) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hfp3, rfl⟩
  have hfp_sub : (s0.sp - 96#64) - 112#64 = sp + 25616#64 := by
    dsimp only [sp]; clear * -; bv_omega
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl3 hro3
      (seg8c_b16 hb s3 sp (s0.sp - 96#64) ret ct c' kGood kRej _ hct hc' hkGood hkRej
        hfp_sub hpc3 hrun3 hsp3 hspA3 hfp3 hcl3) ?_)
  rintro s4 _ hpc4 hrun4 _ _ ⟨hsp4, _, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (SepWP.mono (seg8c_epilogue hb s0 s4 _ (by simpa [State.spAligned] using hsp0) hpc4 hrun4 hsp4) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have h136 : ((sp + 136#64) ↦₆₄ ret) ⊢ memRegion (sp + 136#64) 8 := pointsTo64_entails_memRegion _ _
  have h3344 : ((sp + 3344#64) ↦ₛ ct) ⊢ memRegion (sp + 3344#64) 1088 := by
    simpa only [hct] using pointsToBytes_entails_memRegion (sp + 3344#64) ct
  have h4496 : ((sp + 4496#64) ↦ₛ kGood) ⊢ memRegion (sp + 4496#64) 32 := by
    simpa only [hkGood] using pointsToBytes_entails_memRegion (sp + 4496#64) kGood
  have h18032 : ((sp + 18032#64) ↦ₛ c') ⊢ memRegion (sp + 18032#64) 1088 := by
    simpa only [hc'] using pointsToBytes_entails_memRegion (sp + 18032#64) c'
  have h22400 : ((sp + 22400#64) ↦ₛ c') ⊢ memRegion (sp + 22400#64) 1088 := by
    simpa only [hc'] using pointsToBytes_entails_memRegion (sp + 22400#64) c'
  have h23936 : PolyMem (sp + 23936#64) (polyVecNat re) ⊢ memRegion (sp + 23936#64) 512 :=
    vecRangeMem_entails_memRegion 32 (sp + 23936#64) (polyVecNat re)
  have h25616 : ((sp + 25616#64) ↦ₛ kRej) ⊢ memRegion (sp + 25616#64) 32 := by
    simpa only [hkRej] using pointsToBytes_entails_memRegion (sp + 25616#64) kRej
  have hsub := sepConj_mono h136 (sepConj_mono h3344 (sepConj_mono h4496
    (sepConj_mono h18032 (sepConj_mono h22400 (sepConj_mono h23936 h25616)))))
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8c
