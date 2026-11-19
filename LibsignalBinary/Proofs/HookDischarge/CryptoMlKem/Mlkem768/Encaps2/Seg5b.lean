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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd

/-!
# `encapsulate2` (`B20`) — Segment 5b (`+0x29a8 .. +0x2b10` `ret`)

Steps Loop 2 (`compress_and_serialize_4`, `+0x29a8 .. +0x2ab8`), the 128-byte output copy
(`+0x2ab8 .. +0x2ae8`), and the callee-saved frame restoration + `ret` epilogue (`+0x2ae8 .. +0x2b10`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5b

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData09Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl resolve_ro09)
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
  SavedFrame20 UnspilledSaved20 blk20_code_eq blk20_tree_size blkLib20 blkPC20 blkPl20
  blkPlaceable20 blkTree20 savedFrame20_entails_memRegion128 sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem SepLoad128 SepStore128 Vec128At VecRangeMem
  SepWP.of_memRegion_vecRangeMem append_extractLsb64 oct8Mem_entails_memRegion oct8Mem_ofFn
  polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128 unpack128 vecRangeBytes
  vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdUshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_fmov_w_s exec_simdAdd_4s exec_simdAddv_4h exec_simdAnd_16b exec_simdBic_4s_15
  exec_simdCmltZero_8h exec_simdDup_4s exec_simdMovi_8h_15 exec_simdShl_4s_4
  exec_simdSqdmulh_4s exec_simdUshr_4s_4 exec_simdUshr_4s_12
  seg5Loop2_addv4h_ext8_eq seg5Loop2_compress_eq seg5Loop2_lowt_eq seg5_compressSerialize4_eq)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x29a8 → 0x2b10]
gen_placed_odd_sites blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x29d0 → 0x29e0]

@[simp, arm64_norm]
private theorem blkPC20_rebase_fetchOff_29dc [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC20.rebase b X).fetch (b + BitVec.ofNat 64 10716) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 5)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl20.ρ "libcrux_ml_kem:.rodata.cst16.7")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib20) (prog := blkPC20) (pl := blkPl20) (b := b) (X := X) (off := 10716)
    (r := { off := 10716, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.7" })
    rfl blkPlaceable20 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 10716)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 2679) blk20_code_eq blk20_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl20_ρ [MlKemPlacement] (sym : String) :
    blkPl20.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC20
attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_15 exec_simdBic_4s_15 exec_simdAnd_16b exec_fmov_w_s
  exec_simdDup_4s exec_simdCmltZero_8h exec_simdShl_4s_4 exec_simdUshr_4s_12
  exec_simdUshr_4s_4 exec_simdAdd_4s exec_simdSqdmulh_4s exec_simdAddv_4h
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdTrn1_8h svc_simdExt_16b_8 exec_simdUshl_8h

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

/-! ## 2. Loop-2 Setup (`+0x29a8 → +0x29e8`) & 16-Iter `compress_and_serialize_4` (`+0x29e8 → +0x2ab8`) -/

attribute [local irreducible]
  WordRangeMem dup8x16 pack4x32 lane32 polyVecNat simdAdd8h simdCmltZero8h simdSqdmulh4s
  simdAddv4h simdTrn1_8h simdExt16b simdUshl8h neonCompress8h neonSerialize4Lowt

private def Loop2Inv (s0 s : State) (sp ret : BitVec 64) (c : Nat) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * c) ∧
  s.readReg64 .x10 = sp + 2288#64 ∧ s.readReg64 .x19 = ret ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧ UnspilledSaved20 s0 s

private theorem seg5b_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s : State) (sp ret : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + 0x29a8#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hspA : s.spAligned = true) (hx19 : s.readReg64 .x19 = ret)
    (hus : UnspilledSaved20 s0 s) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x29e8#64) s P
      (fun sm Pm => Loop2Inv s0 sm sp ret 0 ∧ Pm = P) := by
  subst hbase
  wp_steps
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_7 mlkemData09Bytes_length cst16_7_vec (by wp_norm_lhs) ?_
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  refine ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
    by simp, by simp, by simp, by simp [hx19], by simp, by simp, by simp, by simp, ?_, by simp,
    ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩
  congr 1

attribute [local irreducible] evalBitfield neonSerialize4Word64

private def Loop2Mid (s0 s : State) (sp ret : BitVec 64) (re : Poly16) (c : Nat) : Prop :=
  let lowt0 := neonSerialize4Lowt (neonCompress8h 4 (polyVecNat re (2 * c)))
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
  s.readReg64 .x10 = sp + 2288#64 ∧ s.readReg64 .x19 = ret ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
  s.readVReg128 6#5 = (simdAddv4h lowt0).zeroExtend 128 ∧
  s.readVReg128 7#5 = neonCompress8h 4 (polyVecNat re (2 * c + 1)) ∧
  s.readVReg128 16#5 = (lowt0.truncate 64 ++ lowt0.extractLsb' 64 64) ∧
  UnspilledSaved20 s0 s

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

private theorem seg5b_iter_a1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (Rest : SepProp) (hpc : s.pc = b + 0x29e8#64)
    (hrun : s.status = .Running) (hinv : Loop2Inv s0 s sp ret c) :
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
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a28#64) s
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧ s1.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
        s1.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
        s1.readReg64 .x10 = sp + 2288#64 ∧ s1.readReg64 .x19 = ret ∧
        s1.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s1.readVReg128 1#5 = dup8x16 3329#16 ∧
        s1.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
        s1.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
        s1.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
        s1.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
        s1.readVReg128 6#5 = od0 ∧ s1.readVReg128 7#5 = (pack4x32 fun j => lane32 u1 j >>> 12) ∧
        s1.readVReg128 16#5 = ev0 ∧ s1.readVReg128 17#5 = (pack4x32 fun j => lane32 u1 j <<< 4) ∧
        UnspilledSaved20 s0 s1 ∧ P1 = (PolyMem (sp + 3440#64) (polyVecNat re) ∗ Rest)) := by
  intro u0 u1 ev0 od0
  rcases hinv with ⟨hsp, hspA, hx8, hx9, hx10, hx19, hv0, hv1, hv2, hv3, hv4, hv5, hus⟩
  have hea1 : (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * c)) + 16#64 =
      (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * c + 1)) := by clear * - hc; bv_omega
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * c)))
    (ea16 := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * c + 1)))
    (by wp_norm_lhs) hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hc; bv_omega) hea1
    (SepLoad128.vecRange (n := 32) (k := 2 * c) (by omega) rfl).left
    (SepLoad128.vecRange (n := 32) (k := 2 * c + 1) (by omega) rfl).left
    (by wp_norm_lhs) ?_
  wp_steps 8
  refine sepWP_cut (fun sm => sm.pc = b + 0x2a0c#64 ∧ sm.status = .Running ∧
    sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
    sm.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
    sm.readReg64 .x10 = sp + 2288#64 ∧ sm.readReg64 .x19 = ret ∧
    sm.readVReg128 0#5 = dup8x16 0x000f#16 ∧ sm.readVReg128 1#5 = dup8x16 3329#16 ∧
    sm.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
    sm.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
    sm.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
    sm.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
    sm.readVReg128 6#5 = (pack4x32 fun j => lane32 u0 j >>> 12) ∧
    sm.readVReg128 7#5 = polyVecNat re (2 * c + 1) ∧
    sm.readVReg128 16#5 = (simdCmltZero8h (polyVecNat re (2 * c + 1)) &&& dup8x16 3329#16) ∧
    sm.readVReg128 17#5 = (pack4x32 fun j => lane32 u0 j <<< 4) ∧
    UnspilledSaved20 s0 sm)
    ⟨by wp_norm_lhs, by simp [hrun], by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp; clear * - hc; bv_omega, by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩ ?_
  clear hpc hrun hsp hspA hx8 hx9 hx10 hx19 hv0 hv1 hv2 hv3 hv4 hv5 hus hea1
  rintro sm ⟨hpc, hrun, hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩
  wp_steps 7
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private def IterAState (s0 s : State) (sp ret : BitVec 64) (c : Nat)
    (v6 v7 v16 v17 : BitVec 128) : Prop :=
  s.sp = sp ∧ s.spAligned = true ∧ s.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
  s.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
  s.readReg64 .x10 = sp + 2288#64 ∧ s.readReg64 .x19 = ret ∧
  s.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s.readVReg128 1#5 = dup8x16 3329#16 ∧
  s.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
  s.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
  s.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
  s.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
  s.readVReg128 6#5 = v6 ∧ s.readVReg128 7#5 = v7 ∧
  s.readVReg128 16#5 = v16 ∧ s.readVReg128 17#5 = v17 ∧
  UnspilledSaved20 s0 s

private theorem seg5b_iter_a2_s1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s1 : State) (sp ret : BitVec 64) (od0 v7_in ev0 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + 0x2a28#64) (hrun1 : s1.status = .Running)
    (h1 : IterAState s0 s1 sp ret c od0 v7_in ev0 v17_in) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a2c#64) s1 P1
      (fun sm Pm => IterAState s0 sm sp ret c od0 v7_in
        (simdSqdmulh4s ev0 (pack4x32 fun _ => 10321340#32)) v17_in ∧ Pm = P1) := by
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩
  wp_step
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp [hv6], by simp [hv7],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp [hv17],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩

private theorem seg5b_iter_a2_s2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s1 : State) (sp ret : BitVec 64) (od0 v7_in ev1 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + 0x2a2c#64) (hrun1 : s1.status = .Running)
    (h1 : IterAState s0 s1 sp ret c od0 v7_in ev1 v17_in) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a30#64) s1 P1
      (fun sm Pm => IterAState s0 sm sp ret c
        (simdSqdmulh4s od0 (pack4x32 fun _ => 10321340#32)) v7_in ev1 v17_in ∧ Pm = P1) := by
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩
  wp_step
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp [hv7], by simp [hv16], by simp [hv17],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩

private theorem seg5b_iter_a2_s3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s1 : State) (sp ret : BitVec 64) (od1 v7_in ev1 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + 0x2a30#64) (hrun1 : s1.status = .Running)
    (h1 : IterAState s0 s1 sp ret c od1 v7_in ev1 v17_in) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a40#64) s1 P1
      (fun sm Pm => IterAState s0 sm sp ret c od1
        (v7_in &&& 0xfffffff0fffffff0fffffff0fffffff0#128)
        (pack4x32 fun k => lane32 ev1 k >>> 4)
        (pack4x32 fun k =>
          lane32 (v17_in &&& (pack4x32 fun _ => 1048560#32)) k +
            lane32 (pack4x32 fun _ => 1664#32) k) ∧ Pm = P1) := by
  rcases h1 with ⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩
  wp_steps 4
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
    ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp [hv6],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩

private theorem seg5b_iter_a2 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s1 : State) (sp ret : BitVec 64) (od0 v7_in ev0 v17_in : BitVec 128) (c : Nat)
    (P1 : SepProp) (hpc1 : s1.pc = b + 0x2a28#64) (hrun1 : s1.status = .Running)
    (hcl1 : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro1 : MlKemRoOk mlkemMpl s1.mem)
    (h1 : IterAState s0 s1 sp ret c od0 v7_in ev0 v17_in) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a58#64) s1 P1
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧ s2.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
        s2.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
        s2.readReg64 .x10 = sp + 2288#64 ∧ s2.readReg64 .x19 = ret ∧
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
              (pack4x32 fun _ => 10321340#32)) k >>> 4) ∧
        UnspilledSaved20 s0 s2 ∧ P2 = P1) := by
  refine sepWP_seq_env hcl1 hro1
    (seg5b_iter_a2_s1 hb s0 s1 sp ret od0 v7_in ev0 v17_in c P1 hpc1 hrun1 h1) ?_
  clear hpc1 hrun1 hcl1 hro1 h1
  rintro sa _ hpca hruna hcla hroa ⟨ha, rfl⟩
  refine sepWP_seq_env hcla hroa
    (seg5b_iter_a2_s2 hb s0 sa sp ret od0 v7_in _ v17_in c _ hpca hruna ha) ?_
  clear hpca hruna hcla hroa ha
  rintro sb _ hpcb hrunb hclb hrob ⟨hb_st, rfl⟩
  refine sepWP_seq_env hclb hrob
    (seg5b_iter_a2_s3 hb s0 sb sp ret _ v7_in _ v17_in c _ hpcb hrunb hb_st) ?_
  clear hpcb hrunb hclb hrob hb_st
  rintro sm _ hpc hrun _ _ ⟨⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩, rfl⟩
  wp_steps 6
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      by simp only [wp_norm, arm64_norm]; try rfl,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem seg5b_iter_a [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (Rest : SepProp) (hpc : s.pc = b + 0x29e8#64)
    (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hinv : Loop2Inv s0 s sp ret c) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2a74#64) s
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ Rest)
      (fun sm Pm => Loop2Mid s0 sm sp ret re c ∧
        Pm = (PolyMem (sp + 3440#64) (polyVecNat re) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg5b_iter_a1 hb s0 s sp ret re hc Rest hpc hrun hinv) ?_
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg5b_iter_a2 hb s0 s1 sp ret _ _ _ _ c _ hpc1 hrun1 hcl1 hro1
      ⟨hsp, hspA, hx8, hx9, hx10, hx19,
        hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hv17, hus⟩) ?_
  clear hpc1 hrun1 hcl1 hro1 hsp hspA hx8 hx9 hx10 hx19 hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv16 hv17 hus
  rintro s2 _ hpc hrun _ _ ⟨hsp, hspA, hx8, hx9, hx10, hx19,
    hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hus, rfl⟩
  wp_steps 7
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) ⟨⟨by simp [hsp],
    by simpa [State.spAligned, hsp] using hspA, by simp [hx8], by simp [hx9],
    by simp [hx10], by simp [hx19],
    by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
    ?_, ?_, ?_,
    ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩
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
  have hm1 : ∀ k : Fin 64, (0xffffffffffff0000#64).getLsbD k.val = decide (16 ≤ k.val) := by
    decide
  have hm0 : ∀ k : Fin 64, (65535#64).getLsbD k.val = decide (k.val < 16) := by
    decide
  rw [hz32, hz32, hz32, hz32, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hm1k := hm1 ⟨k, hk⟩
  have hm0k := hm0 ⟨k, hk⟩
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

private theorem seg5b_iter_b [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (w : Nat → BitVec 64) (Rest : SepProp) (hpc : s.pc = b + 0x2a74#64)
    (hrun : s.status = .Running) (hmid : Loop2Mid s0 s sp ret re c) :
    SepWP (blkPC20.rebase b (fun _ => none))
      (if c < 15 then b + 0x29e8#64 else b + 0x2ab8#64) s
      (WordRangeMem 16 (sp + 2288#64) w ∗ Rest)
      (fun s' P' => Loop2Inv s0 s' sp ret (c + 1) ∧
        P' = (WordRangeMem 16 (sp + 2288#64) (Function.update w c (serWord re c)) ∗ Rest)) := by
  rcases hmid with ⟨hsp, hspA, hx8, hx9, hx10, hx19, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv16, hus⟩
  wp_steps 13
  refine sepWP_cut (fun s1 => s1.pc = b + 0x2aa8#64 ∧ s1.status = .Running ∧
    s1.sp = sp ∧ s1.spAligned = true ∧
    s1.readReg64 .x8 = BitVec.ofNat 64 (8 * c) ∧
    s1.readReg64 .x9 = sp + 3456#64 + BitVec.ofNat 64 (32 * (c + 1)) ∧
    s1.readReg64 .x10 = sp + 2288#64 ∧ s1.readReg64 .x19 = ret ∧
    s1.readVReg128 0#5 = dup8x16 0x000f#16 ∧ s1.readVReg128 1#5 = dup8x16 3329#16 ∧
    s1.readVReg128 2#5 = (pack4x32 fun _ => 1048560#32) ∧
    s1.readVReg128 3#5 = (pack4x32 fun _ => 1664#32) ∧
    s1.readVReg128 4#5 = (pack4x32 fun _ => 10321340#32) ∧
    s1.readVReg128 5#5 = 0x000c000800040000000c000800040000#128 ∧
    UnspilledSaved20 s0 s1 ∧ s1.readReg64 .x11 = serWord re c)
    ⟨by wp_norm_lhs, by simp [hrun], by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx19],
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, ?_⟩ ?_
  · have htr32 (x : BitVec 32) : (x.zeroExtend 64).truncate 32 = x := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
    conv => lhs; simp only [wp_norm, arm64_norm, htr32]
    rw [seg5Loop2_lowt_eq (polyVecNat re (2 * c + 1)),
        seg5Loop2_addv4h_ext8_eq, seg5Loop2_addv4h_ext8_eq]
    unfold serWord neonSerialize4Word64 neonSerialize4HalfWord32; dsimp only
    exact word64_assemble_bits _ _ _ _
  clear hpc hrun hsp hspA hx8 hx9 hx10 hx19 hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv16 hus
  rintro s1 ⟨hpc, hrun, hsp, hspA, hx8, hx9, hx10, hx19, hv0, hv1, hv2, hv3, hv4, hv5, hus, hx11⟩
  refine SepWP.step_str64 (s' := s1.setPC (b + 0x2aac#64))
    (ea := (sp + 2288#64) + BitVec.ofNat 64 (8 * c)) (wb := none)
    (val := serWord re c) hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx10, hx8]) hx11
    (SepStore64.wordRange (n := 16) (c := c) hc rfl).left
    (by simp [applyWriteback]) ?_
  intro m'
  wp_steps 3
  wp_if hne
  · have hlt : c < 15 := by
      clear * - hc hne hx8
      by_contra hge; have hc15 : c = 15 := by omega
      subst hc15; simp_all
    simp only [hlt, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp; clear * - hc; bv_omega, by simp [hx9], by simp [hx10], by simp [hx19],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩
  · have hlt : ¬ c < 15 := by
      clear * - hne hx8
      intro h; rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | c
      all_goals try simp_all
      omega
    have hc15 : c = 15 := by omega
    simp only [hlt, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp [hc15], by simp [hx9], by simp [hx10], by simp [hx19],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], by simp [hv4], by simp [hv5],
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩⟩, rfl⟩

private theorem seg5b_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (re : Poly16) {c : Nat} (hc : c < 16)
    (w : Nat → BitVec 64) (Rest : SepProp) (hpc : s.pc = b + 0x29e8#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hinv : Loop2Inv s0 s sp ret c) :
    SepWP (blkPC20.rebase b (fun _ => none)) (if c < 15 then b + 0x29e8#64 else b + 0x2ab8#64) s
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ WordRangeMem 16 (sp + 2288#64) w ∗ Rest)
      (fun s' P' => Loop2Inv s0 s' sp ret (c + 1) ∧ P' = (PolyMem (sp + 3440#64) (polyVecNat re) ∗
        WordRangeMem 16 (sp + 2288#64) (Function.update w c (serWord re c)) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg5b_iter_a hb s0 s sp ret re hc _ hpc hrun hcl hro hinv) ?_
  rintro sm _ hpcm hrunm _ _ ⟨hmid, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (SepWP.mono (seg5b_iter_b hb s0 sm sp ret re hc w _ hpcm hrunm hmid) ?_)
  rintro s' _ _ _ ⟨hinv', rfl⟩; exact ⟨hinv', sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem update_serWord_prefix {re : Poly16} {w : Nat → BitVec 64} {c : Nat}
    (hw : ∀ j, j < c → w j = serWord re j) :
    ∀ j, j < c + 1 → Function.update w c (serWord re c) j = serWord re j := by
  intro j hj; by_cases h : j = c
  · subst h; simp
  · rw [Function.update_of_ne h]; exact hw j (by omega)

private theorem seg5b_loop2 [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 : State) (sp ret : BitVec 64) (re : Poly16) (Rest : SepProp) :
    ∀ (rem c : Nat), c + rem = 15 → ∀ (s : State) (w : Nat → BitVec 64),
      s.pc = b + 0x29e8#64 → s.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      Loop2Inv s0 s sp ret c → (∀ j, j < c → w j = serWord re j) →
      SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2ab8#64) s
        (PolyMem (sp + 3440#64) (polyVecNat re) ∗ WordRangeMem 16 (sp + 2288#64) w ∗ Rest)
        (fun s' P' => s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x19 = ret ∧
          UnspilledSaved20 s0 s' ∧ P' = (PolyMem (sp + 3440#64) (polyVecNat re) ∗
            Oct8Mem (sp + 2288#64) (Oct8.ofFn (serVec re)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro c hrem s w hpc hrun hcl hro hinv hw; have hc15 : c = 15 := by omega
    subst hc15
    have hstep := seg5b_iter hb s0 s sp ret re (c := 15) (by decide) w Rest hpc hrun hcl hro hinv
    simp only [Nat.lt_irrefl, ↓reduceIte] at hstep; refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨⟨hsp', hspA', _, _, _, hx19', _, _, _, _, _, _, hus'⟩, hP'⟩
    refine ⟨hsp', hspA', hx19', hus', ?_⟩
    rw [hP', wordRangeMem_congr (update_serWord_prefix hw),
      wordRangeMem_eq_vecRangeMem 8 (sp + 2288#64) (serWord re)]
    change PolyMem (sp + 3440#64) (polyVecNat re) ∗
        VecMem.PolyOctMem (sp + 2288#64) (serVec re) ∗ Rest = _
    rw [← oct8Mem_ofFn (sp + 2288#64) (serVec re)]
  | succ rem ih =>
    intro c hrem s w hpc hrun hcl hro hinv hw; have hlt : c < 15 := by omega
    have hstep := seg5b_iter hb s0 s sp ret re (c := c) (by omega) w Rest hpc hrun hcl hro hinv
    simp only [hlt, ↓reduceIte] at hstep; refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro' ⟨hinv', rfl⟩
    exact ih (c + 1) (by omega) sm _ hpc' hrun' hcl' hro' hinv' (update_serWord_prefix hw)

/-! ## 3. 128-Byte Output Copy (`+0x2ab8 → +0x2ae8`) & Epilogue (`+0x2ae8 → ret`) -/

local macro "ldr_src " k:num : tactic => `(tactic|
  refine step_ldrQ128 (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *])
    (by wp_norm_lhs) (SepLoad128.oct8 (k := $k) (by decide) (by simp [*]; try bv_omega) rfl).left
    (by wp_norm_lhs) ?_)

local macro "stp_dst " k1:num k2:num : tactic => `(tactic|
  refine step_stpQ128 (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs) rfl
    (by wp_norm_lhs) rfl (by wp_norm_lhs) (by wp_norm_lhs)
    (SepStore128.oct8 (k := $k1) (by decide) (by simp [*]; try bv_omega) rfl).left.right
    (SepStore128.oct8 (k := $k2) (by decide) (by simp [*]; try bv_omega) rfl).left.right
    (by wp_norm_lhs) fun _ => ?_)

private theorem seg5b_copy [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (src dst : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + 0x2ab8#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hspA : s.spAligned = true) (hx19 : s.readReg64 .x19 = ret) (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x2ae8#64) s
      (Oct8Mem (sp + 2288#64) src ∗ Oct8Mem ret dst ∗ Rest)
      (fun s' P' => s'.sp = sp ∧ s'.spAligned = true ∧ UnspilledSaved20 s0 s' ∧
        P' = (Oct8Mem (sp + 2288#64) src ∗ Oct8Mem ret src ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_src 4; ldr_src 5; ldr_src 7; stp_dst 4 5
  ldr_src 6; ldr_src 0; stp_dst 6 7
  ldr_src 1; ldr_src 2; stp_dst 0 1
  ldr_src 3; stp_dst 2 3
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  refine ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
    ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, ?_⟩
  cases src; rfl

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

private theorem seg5b_epilogue [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (Rest : SepProp) (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + 0x2ae8#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 6128#64) (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame20 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 128#64) 128 ∗ Rest)) := by
  dsimp only [SavedFrame20]
  have hsp128 : (s0.sp - 6128#64) + 4096#64 + 1904#64 = s0.sp - 128#64 := by bv_omega
  have hsp128_al : ((((s0.sp - 6128#64) + 4096#64 + 1904#64) &&& 15#64) == 0#64) = true := by
    rw [hsp128]; exact spAligned_sub s0.sp 128#64 hsp0 (by decide)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by bv_omega), ?_⟩,
    sepConj_mono_left (savedFrame20_entails_memRegion128 s0.sp s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2],
    by wp_norm_lhs, by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

/-- Segment 5b (`+0x29a8 → ret`): `neonCompressSerialize4` loop, 128-byte copy, and epilogue. -/
theorem seg5b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s5 : State) (ret : BitVec 64) (re : Poly16) (Frame : SepProp)
    (hsp0 : s0.spAligned = true) (hpc : s5.pc = b + 0x29a8#64)
    (hrun : s5.status = .Running) (hsp : s5.sp = s0.sp - 6128#64) (hspA : s5.spAligned = true)
    (hx19 : s5.readReg64 .x19 = ret) (hus : UnspilledSaved20 s0 s5)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s5.mem) (hro : MlKemRoOk mlkemMpl s5.mem) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s5
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ Frame)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ neonCompressSerialize4 re) ∗ memRegion (sp + 3440#64) 512 ∗
          memRegion (sp + 2288#64) 128 ∗ memRegion (s0.sp - 128#64) 128 ∗ Frame)) := by
  intro sp
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2288#64) (by decide) (by sep_focus); intro f0
  apply SepWP.of_memRegion_vecRangeMem 8 ret (by decide) (by sep_focus); intro g0
  rw [vecRangeMem_eq_wordRangeMem 8 (sp + 2288#64) f0, show 2 * 8 = 16 from rfl]
  set w0 : Nat → BitVec 64 :=
    fun i => if i % 2 = 0 then (f0 (i / 2)).extractLsb' 0 64 else (f0 (i / 2)).extractLsb' 64 64
  change SepWP _ _ _ (VecMem.PolyOctMem ret g0 ∗ _) _; rw [← oct8Mem_ofFn ret g0]
  have hreord0 : (Oct8Mem ret (Oct8.ofFn g0) ∗ (WordRangeMem 16 (sp + 2288#64) w0 ∗
        (PolyMem (sp + 3440#64) (polyVecNat re) ∗ SavedFrame20 s0.sp s0 ∗ Frame))) =
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ WordRangeMem 16 (sp + 2288#64) w0 ∗
        (Oct8Mem ret (Oct8.ofFn g0) ∗ SavedFrame20 s0.sp s0 ∗ Frame)) :=
    sepProp_ext (by sep_frame) (by sep_frame)
  rw [hreord0]
  refine sepWP_seq_env hcl hro
    (seg5b_setup hb hbase s0 s5 sp ret _ hpc hrun hsp hspA hx19 hus hro) ?_
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hinv1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg5b_loop2 hb s0 sp ret re (Oct8Mem ret (Oct8.ofFn g0) ∗ SavedFrame20 s0.sp s0 ∗ Frame)
      15 0 rfl s1 w0 hpc1 hrun1 hcl1 hro1 hinv1 (fun _ hj => by omega)) ?_
  rintro s2 _ hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hus2, rfl⟩
  have hreord2 : (PolyMem (sp + 3440#64) (polyVecNat re) ∗
        Oct8Mem (sp + 2288#64) (Oct8.ofFn (serVec re)) ∗
        (Oct8Mem ret (Oct8.ofFn g0) ∗ SavedFrame20 s0.sp s0 ∗ Frame)) =
      (Oct8Mem (sp + 2288#64) (Oct8.ofFn (serVec re)) ∗ Oct8Mem ret (Oct8.ofFn g0) ∗
        (PolyMem (sp + 3440#64) (polyVecNat re) ∗ SavedFrame20 s0.sp s0 ∗ Frame)) :=
    sepProp_ext (by sep_frame) (by sep_frame)
  rw [hreord2]
  refine sepWP_seq_env hcl2 hro2
    (seg5b_copy hb s0 s2 sp ret (Oct8.ofFn (serVec re)) (Oct8.ofFn g0)
      (PolyMem (sp + 3440#64) (polyVecNat re) ∗ SavedFrame20 s0.sp s0 ∗ Frame)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hus2) ?_
  rintro s3 _ hpc3 hrun3 _ _ ⟨hsp3, _, hus3, rfl⟩
  have hreord3 : (Oct8Mem (sp + 2288#64) (Oct8.ofFn (serVec re)) ∗
        Oct8Mem ret (Oct8.ofFn (serVec re)) ∗
        (PolyMem (sp + 3440#64) (polyVecNat re) ∗ SavedFrame20 s0.sp s0 ∗ Frame)) =
      (SavedFrame20 s0.sp s0 ∗ (Oct8Mem ret (Oct8.ofFn (serVec re)) ∗
        PolyMem (sp + 3440#64) (polyVecNat re) ∗
        Oct8Mem (sp + 2288#64) (Oct8.ofFn (serVec re)) ∗ Frame)) :=
    sepProp_ext (by sep_frame) (by sep_frame)
  rw [hreord3]
  refine SepWP.mono
    (seg5b_epilogue hb s0 s3 _ (by simpa [State.spAligned] using hsp0) hpc3 hrun3 hsp3 hus3) ?_
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  rw [oct8Mem_serVec_eq_pointsTo]
  have hpoly : PolyMem (sp + 3440#64) (polyVecNat re) ⊢ memRegion (sp + 3440#64) 512 :=
    vecRangeMem_entails_memRegion 32 (sp + 3440#64) (polyVecNat re)
  have hsub := sepConj_mono hpoly (oct8Mem_entails_memRegion (sp + 2288#64) (Oct8.ofFn (serVec re)))
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5b
