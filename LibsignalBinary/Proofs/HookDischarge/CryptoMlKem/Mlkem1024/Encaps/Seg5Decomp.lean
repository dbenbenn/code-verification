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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `kyber_encapsulate` (`B07`) — Segment 5 `e₂` Copy, `decompress_1(m)`, & Dot Init (`+0x7954 .. +0x7f10`)

Proves `seg5_decomp_ok` (`+0x7954 → +0x7f10`):
1. Copies `e₂` (`512` B) from `PolyMem (sp + 1488#64)` to `PolyMem (sp + 31408#64)`.
2. Runs AdvSIMD `decompress_1(m)` from `SpilledMsgWords sp m` to `PolyMem (sp + 24720#64) (polyVecNat (msgPoly16 m))`.
3. Zeroes `Poly32Mem (sp + 26768#64) Vec32.zero`, `Spill13Mem (sp + 2224#64) (AccSpill polyZero16)`,
   and establishes `AccRegs polyZero16` plus `Seg5Dot` entry GPRs (`x8..x12`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Decomp

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemBlockPlacement_ρ mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_6_vec mlkemData08Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdCmeqZero8h simdSshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Spill13 Spill13Mem
  Vec32 VecRangeMem poly32Mem_ofFn polyVecNat spill13Mem_ofFn spill13_ofFn_get step_ldrQ128
  step_strQ128 vec32_ofFn_get vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  spAligned_of_chk spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  msgPoly16 neonDecompress1Byte neonDecompress1Byte_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdCmeqZero_8h exec_simdDup_8h exec_simdSshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (polyZero16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (
  AccRegs AccSpill accRegs_zero_iff accSpill_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  SpilledMsgHi SpilledMsgLo SpilledMsgWords msgW32)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x7954 → 0x7984, 0x798c → 0x7f0c]
gen_placed_odd_sites blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x7988 → 0x7988]

@[simp, arm64_norm]
private theorem blkPC07_rebase_fetchOff_799c [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 31132) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 1)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.6")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07)
    (b := b) (X := X) (off := 31132)
    (r := { off := 31132, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 31132)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 7783) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)

@[simp, arm64_norm, wp_norm] abbrev offSeg5Start  : BitVec 64 := BitVec.ofNat 64 31060
@[simp, arm64_norm, wp_norm] abbrev offSeg5Ro     : BitVec 64 := BitVec.ofNat 64 31132
@[simp, arm64_norm, wp_norm] abbrev offSeg5Mid1   : BitVec 64 := BitVec.ofNat 64 31564
@[simp, arm64_norm, wp_norm] abbrev offSeg5Mid2   : BitVec 64 := BitVec.ofNat 64 31944
@[simp, arm64_norm, wp_norm] abbrev offSeg5Zero   : BitVec 64 := BitVec.ofNat 64 32208
@[simp, arm64_norm, wp_norm] abbrev offSeg5Dot    : BitVec 64 := BitVec.ofNat 64 32528

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_8h_1 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10000#5 1#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1#16)).advancePC := by simp [execInstWithSvc]; rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem exec_simdAnd_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b00#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn &&& s.readVReg128 rm)).advancePC := by
  simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem exec_simdBic_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn &&& ~~~s.readVReg128 rm)).advancePC := by
  simp [execInstWithSvc]

@[simp, arm64_norm, wp_norm]
private theorem zext32_trunc32_zext64_8 (b : BitVec 8) :
    ((b.zeroExtend 64).truncate 32).zeroExtend 64 = b.zeroExtend 64 := by bv_omega

@[simp, arm64_norm, wp_norm]
private theorem zext64_zext32_8 (b : BitVec 8) :
    (b.zeroExtend 32).zeroExtend 64 = b.zeroExtend 64 := by bv_omega

@[simp, arm64_norm, wp_norm]
private theorem trunc16_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 64).truncate 16 = b.zeroExtend 16 := by bv_omega

@[simp, arm64_norm, wp_norm]
private theorem trunc16_1665 : (1665#64 : BitVec 64).truncate 16 = 1665#16 := rfl

@[simp, arm64_norm, wp_norm]
private theorem bic_1665_cmeq_eq (w16 : BitVec 16) :
    dup8x16 1665#16 &&&
      ~~~simdCmeqZero8h
        (simdSshl8h (dup8x16 w16) 0xfff9fffafffbfffcfffdfffe00ff0000#128 &&& dup8x16 1#16) =
      neonDecompress1Byte w16 := rfl

attribute [local irreducible]
  blkPC07 dup8x16 polyVecNat simdSshl8h simdCmeqZero8h neonDecompress1Byte

attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_1 exec_simdMovi_2d_0 exec_simdAnd_16b exec_simdBic_16b
  exec_simdDup_8h exec_simdSshl_8h exec_simdCmeqZero_8h
  zext32_trunc32_zext64_8 zext64_zext32_8 trunc16_zext64_8 trunc16_1665 bic_1665_cmeq_eq

private abbrev mbZ64 (m : List (BitVec 8)) (j : Nat) : BitVec 64 := (m.getD j 0#8).zeroExtend 64
private abbrev mbW16 (m : List (BitVec 8)) (j : Nat) : BitVec 16 := (m.getD j 0#8).zeroExtend 16
private abbrev mbSshl (m : List (BitVec 8)) (j : Nat) : BitVec 128 :=
  simdSshl8h (dup8x16 (mbW16 m j)) 0xfff9fffafffbfffcfffdfffe00ff0000#128
private abbrev mbAnd (m : List (BitVec 8)) (j : Nat) : BitVec 128 := mbSshl m j &&& dup8x16 1#16
private abbrev mbCmeq (m : List (BitVec 8)) (j : Nat) : BitVec 128 := simdCmeqZero8h (mbAnd m j)
private abbrev mbDec (m : List (BitVec 8)) (j : Nat) : BitVec 128 := neonDecompress1Byte (mbW16 m j)

private def msgSlotIdx : Nat → Nat
  | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 4 | 4 => 5 | 5 => 7 | 6 => 6 | 7 => 2
  | 8 => 8 | 9 => 9 | 10 => 11 | 11 => 10 | 12 => 12 | 13 => 13 | 14 => 14 | 15 => 15
  | 16 => 17 | 17 => 16 | 18 => 18 | 19 => 19 | 20 => 21 | 21 => 20 | 22 => 22 | 23 => 23
  | 24 => 25 | 25 => 24 | 26 => 26 | 27 => 29 | 28 => 27 | 29 => 30 | 30 => 28 | _ => 31

private def msgSlotWord (m : List (BitVec 8)) (k : Nat) : BitVec 32 :=
  msgW32 m (msgSlotIdx k)

private theorem spilledMsgWords_eq_wordRangeMem (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledMsgWords sp m = WordRangeMem 32 (sp + 16#64) (msgSlotWord m) := by
  dsimp only [SpilledMsgWords, SpilledMsgLo, SpilledMsgHi, WordRangeMem, msgSlotWord, msgSlotIdx,
    Nat.reduceAdd]
  have ha (k : Nat) (imm : BitVec 64) (h : 16#64 + BitVec.ofNat 64 (4 * k) = imm) :
      (sp + 16#64) + BitVec.ofNat 64 (4 * k) = sp + imm := by rw [← h]; clear * -; bv_omega
  rw [emp_sepConj,
    ha 0 16#64 rfl, ha 1 20#64 rfl, ha 2 24#64 rfl, ha 3 28#64 rfl,
    ha 4 32#64 rfl, ha 5 36#64 rfl, ha 6 40#64 rfl, ha 7 44#64 rfl,
    ha 8 48#64 rfl, ha 9 52#64 rfl, ha 10 56#64 rfl, ha 11 60#64 rfl,
    ha 12 64#64 rfl, ha 13 68#64 rfl, ha 14 72#64 rfl, ha 15 76#64 rfl,
    ha 16 80#64 rfl, ha 17 84#64 rfl, ha 18 88#64 rfl, ha 19 92#64 rfl,
    ha 20 96#64 rfl, ha 21 100#64 rfl, ha 22 104#64 rfl, ha 23 108#64 rfl,
    ha 24 112#64 rfl, ha 25 116#64 rfl, ha 26 120#64 rfl, ha 27 124#64 rfl,
    ha 28 128#64 rfl, ha 29 132#64 rfl, ha 30 136#64 rfl, ha 31 140#64 rfl]
  sep_ac_rfl

private theorem step_ldr_msgW {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {rt : Reg} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 16#64 + BitVec.ofNat 64 (4 * k) = imm := by decide)
    (hexec : (s.writeReg .W32 rt ((m.getD (msgSlotIdx k) 0#8).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ Rest) post) :
    SepWP prog target_pc s (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ Rest) post := by
  have ha : (sp + 16#64) + BitVec.ofNat 64 (4 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact SepWP.step_ldr32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) (SepLoad32.left (SepLoad32.wordRange hk ha))
    (by simpa only [applyWriteback, msgSlotWord, msgW32, zext64_zext32_8] using hexec) hnext

private theorem step_ldp_msgW {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {rt1 rt2 : Reg} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk1 : k + 1 < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W32 false rt1 rt2 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 16#64 + BitVec.ofNat 64 (4 * k) = imm := by decide)
    (hexec : (((s.writeReg .W32 rt1 ((m.getD (msgSlotIdx k) 0#8).zeroExtend 64)).writeReg .W32 rt2
      ((m.getD (msgSlotIdx (k + 1)) 0#8).zeroExtend 64))).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ Rest) post) :
    SepWP prog target_pc s (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ Rest) post := by
  have ha1 : (sp + 16#64) + BitVec.ofNat 64 (4 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have ha2 : (sp + 16#64) + BitVec.ofNat 64 (4 * (k + 1)) = (s.sp + imm) + 4#64 := by
    rw [← ha1]; clear * - hk1; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact SepWP.step_ldp32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) rfl
    (SepLoad32.left (SepLoad32.wordRange (by omega) ha1))
    (SepLoad32.left (SepLoad32.wordRange hk1 ha2))
    (by simpa only [applyWriteback, msgSlotWord, msgW32, zext64_zext32_8] using hexec) hnext

private theorem step_ldr_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 1488#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hexec : (s.writeVReg128 vt (polyVecNat e2 k)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Rest) post := by
  have ha : (sp + 1488#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange hk ha))) hexec hnext

private theorem step_str_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16}
    {pMsg pE2 pE2' : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 31408#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = polyVecNat e2 k) (hp : pE2.set k (polyVecNat e2 k) = pE2')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 31408#64) pE2' ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 31408#64) pE2 ∗ Rest) post := by
  have ha : (sp + 31408#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp)))))
    hexec hnext

private theorem step_msg_strQ {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16}
    {pMsg pMsg' pE2 : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hm : m.length = 32) (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 24720#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = neonDecompress1Byte ((m.getD k 0#8).zeroExtend 16))
    (hp : pMsg.set k (polyVecNat (msgPoly16 m) k) = pMsg') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg' ∗ Poly32Mem (sp + 31408#64) pE2 ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 31408#64) pE2 ∗ Rest) post := by
  have ha : (sp + 24720#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  have hv : s.readVReg128 vt = polyVecNat (msgPoly16 m) k := by
    rw [hval]; exact neonDecompress1Byte_eq hm k hk _ (by clear * -; bv_omega)
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp))))
    hexec hnext

local macro "s5_ldrw " k:num : tactic => `(tactic|
  refine step_ldr_msgW $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s5_ldpw " k:num : tactic => `(tactic|
  refine step_ldp_msgW $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s5_ldre2 " k:num : tactic => `(tactic|
  refine step_ldr_e2 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s5_stre2 " k:num : tactic => `(tactic| (
  refine step_str_e2 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "s5_strmsg " k:num : tactic => `(tactic| (
  refine step_msg_strQ $k (by assumption) (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide)
    (by first | wp_norm_lhs | simp [wp_norm, arm64_norm, *]) rfl (by wp_norm_lhs) ?_
  intro _))

private theorem seg5_decomp_pre_ro [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x19Val x20Val fpVal : BitVec 64) (m : List (BitVec 8))
    (e2 : Poly16) (pMsg0 pE2_0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Ro) s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg0 ∗ Poly32Mem (sp + 31408#64) pE2_0 ∗ Rest)
      (fun s0 P0 =>
        s0.sp = sp ∧ s0.spAligned = true ∧
        s0.readReg64 .x8 = 0#64 ∧
        s0.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6") ∧
        s0.readReg64 .x10 = mbZ64 m 2 ∧ s0.readReg64 .x11 = 3329#64 ∧
        s0.readReg64 .x12 = sp + 28672#64 ∧
        s0.readReg64 .x19 = x19Val ∧ s0.readReg64 .x20 = x20Val ∧ s0.readReg64 .fp = fpVal ∧
        s0.readVReg128 0#5 = polyVecNat e2 3 ∧
        s0.readVReg128 2#5 = dup8x16 (mbW16 m 0) ∧
        s0.readVReg128 3#5 = dup8x16 (mbW16 m 1) ∧
        s0.readVReg128 4#5 = polyVecNat e2 5 ∧
        P0 = (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 24720#64) pMsg0 ∗
          Poly32Mem (sp + 31408#64) ((((pE2_0.set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)) ∗ Rest)) := by
  have hbase : blkPl07.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s5_ldre2 0; s5_ldre2 4; wp_step; s5_ldpw 1; s5_stre2 0; s5_ldre2 1; wp_step; s5_stre2 4
  s5_ldre2 5; wp_step; s5_stre2 1; s5_ldre2 2; wp_step; wp_step; wp_step; s5_ldrw 7; s5_stre2 2; s5_ldre2 3
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp, by simp, by simp [msgSlotIdx], by simp,
      by simp,
      by simp [hx19], by simp [hx20], by simp [hfp],
      by wp_norm_lhs, by simp [msgSlotIdx], by simp [msgSlotIdx], by wp_norm_lhs, rfl⟩

private theorem seg5_decomp_part1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg0 pE2_0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Mid1) s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg0 ∗ Poly32Mem (sp + 31408#64) pE2_0 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x11 = 3329#64 ∧
        s1.readReg64 .x12 = sp + 28848#64 ∧
        s1.readReg64 .x19 = x19Val ∧ s1.readReg64 .x20 = x20Val ∧ s1.readReg64 .fp = fpVal ∧
        s1.readVReg128 0#5 = dup8x16 1#16 ∧
        s1.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s1.readVReg128 2#5 = dup8x16 1665#16 ∧
        s1.readVReg128 7#5 = mbDec m 7 ∧
        s1.readVReg128 19#5 = mbSshl m 8 ∧ s1.readVReg128 20#5 = mbSshl m 9 ∧
        s1.readVReg128 21#5 = dup8x16 (mbW16 m 10) ∧ s1.readVReg128 22#5 = mbSshl m 11 ∧
        s1.readVReg128 25#5 = polyVecNat e2 27 ∧
        P1 = (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 24720#64) (((((((pMsg0.set 0 (polyVecNat (msgPoly16 m) 0)).set 1 (polyVecNat (msgPoly16 m) 1)).set 3 (polyVecNat (msgPoly16 m) 3)).set 2 (polyVecNat (msgPoly16 m) 2)).set 4 (polyVecNat (msgPoly16 m) 4)).set 6 (polyVecNat (msgPoly16 m) 6)).set 5 (polyVecNat (msgPoly16 m) 5)) ∗
          Poly32Mem (sp + 31408#64) (((((((((((((((((((((((((((pE2_0.set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)).set 5 (polyVecNat e2 5)).set 3 (polyVecNat e2 3)).set 6 (polyVecNat e2 6)).set 9 (polyVecNat e2 9)).set 11 (polyVecNat e2 11)).set 7 (polyVecNat e2 7)).set 10 (polyVecNat e2 10)).set 8 (polyVecNat e2 8)).set 12 (polyVecNat e2 12)).set 25 (polyVecNat e2 25)).set 13 (polyVecNat e2 13)).set 18 (polyVecNat e2 18)).set 26 (polyVecNat e2 26)).set 14 (polyVecNat e2 14)).set 15 (polyVecNat e2 15)).set 16 (polyVecNat e2 16)).set 17 (polyVecNat e2 17)).set 19 (polyVecNat e2 19)).set 20 (polyVecNat e2 20)).set 21 (polyVecNat e2 21)).set 22 (polyVecNat e2 22)).set 23 (polyVecNat e2 23)).set 24 (polyVecNat e2 24)) ∗ Rest)) := by
  have hbase : blkPl07.base = b := _hb.symm; subst hbase
  refine sepWP_seq_env hcl hro
    (seg5_decomp_pre_ro _hb s sp x19Val x20Val fpVal m e2 pMsg0 pE2_0 Rest
      hpc hrun hsp hspA hx19 hx20 hfp) ?_
  rintro s0 P0 hpc0 hrun0 _ hro0
    ⟨hsp0, hspA0, hx8_0, hx9_0, hx10_0, hx11_0, hx12_0, hx19_0, hx20_0, hfp0,
      hv0_0, hv2_0, hv3_0, hv4_0, rfl⟩
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspA0
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6")
    (by simp [evalAddrMode, pageOf_add_lo12Of, *])
    (by simpa using hro0.cst16_6) mlkemData08Bytes_length cst16_6_vec (by wp_norm_lhs) ?_
  s5_stre2 5; wp_step; s5_ldre2 6; s5_stre2 3; wp_steps 2; s5_ldrw 0; s5_ldre2 9; wp_step
  s5_stre2 6; wp_step; s5_ldre2 11; wp_step; s5_ldrw 3; s5_stre2 9; wp_step; s5_ldre2 7
  s5_ldre2 10; wp_step; s5_ldre2 12; s5_stre2 11; s5_stre2 7; s5_ldre2 8; wp_step
  s5_stre2 10; wp_steps 2; s5_stre2 8; wp_step; s5_ldrw 4; s5_stre2 12; wp_steps 3
  s5_ldre2 25; wp_step; s5_ldpw 5; wp_steps 2; s5_ldre2 13; s5_stre2 25; s5_ldre2 26
  wp_steps 2; s5_stre2 13; wp_steps 3; s5_ldre2 18; s5_ldpw 8; wp_step; s5_ldre2 14
  s5_stre2 18; wp_steps 2; s5_stre2 26; s5_stre2 14; wp_step; s5_ldre2 15; wp_steps 3
  s5_stre2 15; wp_step; s5_ldre2 16; wp_step; s5_strmsg 0; s5_ldre2 27; s5_stre2 16
  s5_ldre2 17; wp_steps 2; s5_ldre2 19; s5_strmsg 1; s5_stre2 17; wp_steps 2; s5_stre2 19
  s5_ldre2 20; wp_steps 3; s5_strmsg 3; s5_stre2 20; wp_step; s5_ldre2 21; s5_ldpw 10
  s5_stre2 21; wp_step; s5_ldre2 22; s5_strmsg 2; wp_step; s5_stre2 22; wp_step; s5_ldre2 23
  wp_step; s5_strmsg 4; s5_stre2 23; wp_steps 2; s5_ldre2 24; s5_strmsg 6; wp_step
  s5_strmsg 5; s5_stre2 24; wp_steps 2
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp0], spAligned_of_chk (by simp [hsp0]) hchk,
      by simp [hx8_0],
      by simp [hx11_0],
      by simp,
      by simp [hx19_0], by simp [hx20_0], by simp [hfp0],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, rfl⟩

private theorem seg5_decomp_part2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg1 pE2_1 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Mid1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv7 : s.readVReg128 7#5 = mbDec m 7)
    (hv19 : s.readVReg128 19#5 = mbSshl m 8) (hv20 : s.readVReg128 20#5 = mbSshl m 9)
    (hv21 : s.readVReg128 21#5 = dup8x16 (mbW16 m 10)) (hv22 : s.readVReg128 22#5 = mbSshl m 11)
    (hv25 : s.readVReg128 25#5 = polyVecNat e2 27) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Mid2) s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg1 ∗ Poly32Mem (sp + 31408#64) pE2_1 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x10 = mbZ64 m 24 ∧
        s2.readReg64 .x11 = 3329#64 ∧ s2.readReg64 .x12 = sp + 28848#64 ∧
        s2.readReg64 .x19 = x19Val ∧ s2.readReg64 .x20 = x20Val ∧ s2.readReg64 .fp = fpVal ∧
        s2.readVReg128 0#5 = dup8x16 1#16 ∧
        s2.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s2.readVReg128 2#5 = dup8x16 1665#16 ∧
        s2.readVReg128 4#5 = mbCmeq m 20 ∧ s2.readVReg128 5#5 = mbSshl m 23 ∧
        s2.readVReg128 6#5 = mbDec m 21 ∧ s2.readVReg128 7#5 = mbDec m 19 ∧
        s2.readVReg128 16#5 = dup8x16 (mbW16 m 25) ∧ s2.readVReg128 19#5 = mbSshl m 22 ∧
        P2 = (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 24720#64) ((((((((((((pMsg1.set 7 (polyVecNat (msgPoly16 m) 7)).set 8 (polyVecNat (msgPoly16 m) 8)).set 9 (polyVecNat (msgPoly16 m) 9)).set 11 (polyVecNat (msgPoly16 m) 11)).set 10 (polyVecNat (msgPoly16 m) 10)).set 12 (polyVecNat (msgPoly16 m) 12)).set 13 (polyVecNat (msgPoly16 m) 13)).set 14 (polyVecNat (msgPoly16 m) 14)).set 15 (polyVecNat (msgPoly16 m) 15)).set 16 (polyVecNat (msgPoly16 m) 16)).set 18 (polyVecNat (msgPoly16 m) 18)).set 17 (polyVecNat (msgPoly16 m) 17)) ∗
          Poly32Mem (sp + 31408#64) (((((pE2_1.set 27 (polyVecNat e2 27)).set 28 (polyVecNat e2 28)).set 29 (polyVecNat e2 29)).set 30 (polyVecNat e2 30)).set 31 (polyVecNat e2 31)) ∗ Rest)) := by
  have hbase : blkPl07.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s5_ldpw 12; wp_steps 2; s5_strmsg 7; wp_steps 2; s5_stre2 27; wp_steps 2; s5_ldre2 28
  wp_steps 4; s5_stre2 28; wp_steps 2; s5_ldre2 29; wp_steps 4; s5_stre2 29; wp_steps 2
  s5_ldre2 30; s5_ldpw 14; wp_step; s5_strmsg 8; wp_steps 2; s5_strmsg 9; wp_steps 2
  s5_strmsg 11; s5_ldpw 16; wp_steps 2; s5_strmsg 10; wp_steps 2; s5_stre2 30; wp_steps 2
  s5_ldre2 31; s5_ldpw 18; wp_steps 2; s5_strmsg 12; wp_steps 2; s5_strmsg 13; wp_steps 2
  s5_stre2 31; s5_ldpw 20; wp_steps 16; s5_ldpw 22; wp_steps 5; s5_strmsg 14; wp_step
  s5_strmsg 15; wp_steps 3; s5_strmsg 16; wp_steps 3; s5_ldpw 24; wp_step; s5_strmsg 18
  wp_steps 2; s5_strmsg 17; wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [msgSlotIdx], by simp [hx11], by simp [hx12],
      by simp [hx19], by simp [hx20], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg5_decomp_part3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg2 pE2_2 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Mid2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx10 : s.readReg64 .x10 = mbZ64 m 24)
    (hx11 : s.readReg64 .x11 = 3329#64) (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv4 : s.readVReg128 4#5 = mbCmeq m 20) (hv5 : s.readVReg128 5#5 = mbSshl m 23)
    (hv6 : s.readVReg128 6#5 = mbDec m 21) (hv7 : s.readVReg128 7#5 = mbDec m 19)
    (hv16 : s.readVReg128 16#5 = dup8x16 (mbW16 m 25)) (hv19 : s.readVReg128 19#5 = mbSshl m 22) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Zero) s
      (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg2 ∗ Poly32Mem (sp + 31408#64) pE2_2 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s3.readReg64 .x10 = 62209#64 ∧ s3.readReg64 .x11 = 3329#64 ∧
        s3.readReg64 .x12 = sp + 28848#64 ∧
        s3.readReg64 .x19 = x19Val ∧ s3.readReg64 .x20 = x20Val ∧ s3.readReg64 .fp = fpVal ∧
        s3.readVReg128 1#5 = polyVecNat (msgPoly16 m) 30 ∧
        s3.readVReg128 2#5 = polyVecNat (msgPoly16 m) 31 ∧
        P3 = (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 24720#64) (((((((((((pMsg2.set 19 (polyVecNat (msgPoly16 m) 19)).set 21 (polyVecNat (msgPoly16 m) 21)).set 20 (polyVecNat (msgPoly16 m) 20)).set 22 (polyVecNat (msgPoly16 m) 22)).set 23 (polyVecNat (msgPoly16 m) 23)).set 25 (polyVecNat (msgPoly16 m) 25)).set 24 (polyVecNat (msgPoly16 m) 24)).set 27 (polyVecNat (msgPoly16 m) 27)).set 26 (polyVecNat (msgPoly16 m) 26)).set 28 (polyVecNat (msgPoly16 m) 28)).set 29 (polyVecNat (msgPoly16 m) 29)) ∗
          Poly32Mem (sp + 31408#64) pE2_2 ∗ Rest)) := by
  have hbase : blkPl07.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s5_ldrw 26; wp_steps 2; s5_strmsg 19; wp_steps 2; s5_ldrw 28; s5_strmsg 21; s5_strmsg 20
  wp_steps 3; s5_ldrw 30; wp_steps 5; s5_ldrw 27; wp_steps 5; s5_ldrw 29; wp_steps 5
  s5_ldrw 31; wp_steps 12; s5_strmsg 22; wp_steps 2; s5_strmsg 23; wp_steps 2; s5_strmsg 25
  wp_step; s5_strmsg 24; wp_step; wp_step; wp_steps 4; s5_strmsg 27; wp_steps 2; s5_strmsg 26; wp_step
  s5_strmsg 28; s5_strmsg 29; wp_step
  have hv1_eq : neonDecompress1Byte ((m.getD 30 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 30 :=
    neonDecompress1Byte_eq hm 30 (by decide) _ (by simp)
  have hv2_eq : neonDecompress1Byte ((m.getD 31 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 31 :=
    neonDecompress1Byte_eq hm 31 (by decide) _ (by simp)
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp, by simp, by simp [hx11], by simp [hx12],
      by simp [hx19], by simp [hx20], by simp [hfp],
      by rw [← hv1_eq]; wp_norm_lhs,
      by rw [← hv2_eq]; wp_norm_lhs, rfl⟩


private theorem step_strQ_dot5 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot pDot' : Vec32} {sp13 : Spill13}
    {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 26768#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = 0#128) (hp : pDot.set k 0#128 = pDot') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot' ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post := by
  have ha : (sp + 26768#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp))) hexec hnext

private theorem step_ldrQ_dot5 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp13 : Spill13}
    {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 26768#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : pDot.get k = 0#128 := by rfl)
    (hexec : (s.writeVReg128 vt 0#128).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post := by
  have ha : (sp + 26768#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange hk ha)))
    (by simpa [hval] using hexec) hnext

private theorem step_strQ_sp13 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp13 sp13' : Spill13}
    {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 13 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2224#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = 0#128) (hp : sp13.set k 0#128 = sp13') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post := by
  have ha : (sp + 2224#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.spill13 hk ha hp))))
    hexec hnext

private theorem step_strQ_msg_fin {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pMsg' pDot : Vec32} {sp13 : Spill13}
    {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} {val : BitVec 128} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 24720#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = val) (hp : pMsg.set k val = pMsg') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 24720#64) pMsg' ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 24720#64) pMsg ∗ Poly32Mem (sp + 26768#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post := by
  have ha : (sp + 24720#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.left (SepStore128.vec32 hk ha hp)) hexec hnext

local macro "s5_strdot " k:num : tactic => `(tactic| (
  refine step_strQ_dot5 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "s5_ldrdot " k:num : tactic => `(tactic|
  refine step_ldrQ_dot5 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) rfl (by wp_norm_lhs) ?_)

local macro "s5_strsp " k:num : tactic => `(tactic| (
  refine step_strQ_sp13 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "s5_strmsg_z " k:num : tactic => `(tactic| (
  refine step_strQ_msg_fin $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

private theorem seg5_decomp_zero [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x9Val x10Val x11Val x12Val x19Val x20Val fpVal : BitVec 64)
    (v30 v31 : BitVec 128) (pMsg3 pDot0 : Vec32) (sp0 : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Zero) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = x9Val)
    (hx10 : s.readReg64 .x10 = x10Val) (hx11 : s.readReg64 .x11 = x11Val)
    (hx12 : s.readReg64 .x12 = x12Val) (hx19 : s.readReg64 .x19 = x19Val)
    (hx20 : s.readReg64 .x20 = x20Val) (hfp : s.readReg64 .fp = fpVal)
    (hv1 : s.readVReg128 1#5 = v30) (hv2 : s.readVReg128 2#5 = v31) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Dot) s
      (Poly32Mem (sp + 24720#64) pMsg3 ∗ Poly32Mem (sp + 26768#64) pDot0 ∗
        Spill13Mem (sp + 2224#64) sp0 ∗ Rest)
      (fun s4 P4 =>
        s4.sp = sp ∧ s4.spAligned = true ∧
        s4.readReg64 .x8 = 0#64 ∧ s4.readReg64 .x9 = x9Val ∧
        s4.readReg64 .x10 = x10Val ∧ s4.readReg64 .x11 = x11Val ∧
        s4.readReg64 .x12 = x12Val ∧ s4.readReg64 .x19 = x19Val ∧
        s4.readReg64 .x20 = x20Val ∧ s4.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 s4 ∧
        P4 = (Poly32Mem (sp + 24720#64) ((pMsg3.set 30 v30).set 31 v31) ∗
          Poly32Mem (sp + 26768#64) ((((((((((((((((((((((((((((((((pDot0.set 0 0#128).set 1 0#128).set 2 0#128).set 3 0#128).set 4 0#128).set 5 0#128).set 6 0#128).set 7 0#128).set 8 0#128).set 9 0#128).set 10 0#128).set 11 0#128).set 12 0#128).set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 27 0#128).set 25 0#128).set 23 0#128).set 21 0#128).set 19 0#128).set 17 0#128).set 15 0#128).set 13 0#128).set 14 0#128).set 16 0#128).set 18 0#128).set 20 0#128).set 22 0#128).set 24 0#128).set 26 0#128) ∗
          Spill13Mem (sp + 2224#64) (((((((((((((sp0.set 12 0#128).set 11 0#128).set 10 0#128).set 9 0#128).set 8 0#128).set 7 0#128).set 6 0#128).set 5 0#128).set 4 0#128).set 3 0#128).set 2 0#128).set 1 0#128).set 0 0#128) ∗ Rest)) := by
  have hbase : blkPl07.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_step; s5_strmsg_z 30; s5_strmsg_z 31; s5_strdot 0; s5_ldrdot 0; s5_strdot 1
  s5_strdot 2; s5_strsp 12; s5_ldrdot 1; s5_strdot 3; s5_strsp 11; s5_ldrdot 2; s5_strdot 4
  s5_strsp 10; s5_ldrdot 3; s5_strdot 5; s5_strsp 9; s5_ldrdot 4; s5_strdot 6; s5_strsp 8
  s5_ldrdot 5; s5_strdot 7; s5_strsp 7; s5_ldrdot 6; s5_strdot 8; s5_strsp 6; s5_ldrdot 7
  s5_strdot 9; s5_strsp 5; s5_ldrdot 8; s5_strdot 10; s5_strsp 4; s5_ldrdot 9; s5_strdot 11
  s5_strsp 3; s5_ldrdot 10; s5_strdot 12; s5_strsp 2; s5_ldrdot 11; s5_strdot 31; s5_strsp 1
  s5_ldrdot 12; s5_strdot 30; s5_strdot 29; s5_ldrdot 30; s5_strdot 28; s5_ldrdot 29
  s5_strdot 27; s5_ldrdot 28; s5_strdot 25; s5_ldrdot 27; s5_strdot 23; s5_ldrdot 25
  s5_strdot 21; s5_ldrdot 23; s5_strdot 19; s5_ldrdot 21; s5_strdot 17; s5_ldrdot 19
  s5_strdot 15; s5_ldrdot 17; s5_strdot 13; s5_ldrdot 15; s5_strdot 14; s5_ldrdot 13
  s5_strdot 16; s5_ldrdot 14; s5_strdot 18; s5_ldrdot 16; s5_strdot 20; s5_ldrdot 18
  s5_strdot 22; s5_ldrdot 20; s5_strdot 24; s5_ldrdot 22; s5_strdot 26; s5_ldrdot 24
  s5_strsp 0; s5_ldrdot 26; s5_ldrdot 31
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx19], by simp [hx20], by simp [hfp],
      (accRegs_zero_iff _).mpr ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs⟩, rfl⟩

theorem seg5_decomp_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5Dot) s
      (SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        memRegion (sp + 2224#64) 208 ∗ memRegion (sp + 24720#64) 512 ∗
        memRegion (sp + 26768#64) 512 ∗ memRegion (sp + 31408#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x10 = 62209#64 ∧ sf.readReg64 .x11 = 3329#64 ∧
        sf.readReg64 .x12 = sp + 28848#64 ∧
        sf.readReg64 .x19 = x19Val ∧ sf.readReg64 .x20 = x20Val ∧ sf.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 sf ∧
        (Pf ⊢ SpilledMsgWords sp m ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
          PolyMem (sp + 24720#64) (polyVecNat (msgPoly16 m)) ∗
          PolyMem (sp + 26768#64) (fun _ => 0#128) ∗
          PolyMem (sp + 31408#64) (polyVecNat e2) ∗ Rest)) := by
  rw [spilledMsgWords_eq_wordRangeMem]
  refine SepWP.of_memRegion_vecRangeMem 13 (sp + 2224#64) (by decide) (by sep_focus) fun fSp => ?_
  rw [show VecRangeMem 13 (sp + 2224#64) fSp = Spill13Mem (sp + 2224#64) (Spill13.ofFn fSp) from
    (spill13Mem_ofFn (sp + 2224#64) fSp).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 24720#64) (by decide) (by sep_focus) fun fMsg => ?_
  rw [show VecRangeMem 32 (sp + 24720#64) fMsg = Poly32Mem (sp + 24720#64) (Vec32.ofFn fMsg) from
    (poly32Mem_ofFn _ _).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 26768#64) (by decide) (by sep_focus) fun fDot => ?_
  rw [show VecRangeMem 32 (sp + 26768#64) fDot = Poly32Mem (sp + 26768#64) (Vec32.ofFn fDot) from
    (poly32Mem_ofFn _ _).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 31408#64) (by decide) (by sep_focus) fun fE2 => ?_
  rw [show VecRangeMem 32 (sp + 31408#64) fE2 = Poly32Mem (sp + 31408#64) (Vec32.ofFn fE2) from
    (poly32Mem_ofFn _ _).symm]
  let Rest0 : SepProp :=
    Spill13Mem (sp + 2224#64) (Spill13.ofFn fSp) ∗
      Poly32Mem (sp + 26768#64) (Vec32.ofFn fDot) ∗ Rest
  refine SepWP.weaken_pre (by dsimp only [Rest0]; sep_frame)
    (sepWP_seq_env hcl hro
      (seg5_decomp_part1 hb s sp x19Val x20Val fpVal hm e2 (Vec32.ofFn fMsg) (Vec32.ofFn fE2) Rest0
        hpc hrun hsp hspA hcl hro hx19 hx20 hfp) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx11_1, hx12_1, hx19_1, hx20_1, hfp1,
      hv0_1, hv1_1, hv2_1, hv7_1, hv19_1, hv20_1, hv21_1, hv22_1, hv25_1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg5_decomp_part2 hb s1 sp x19Val x20Val fpVal hm e2 _ _ Rest0
      hpc1 hrun1 hsp1 hspA1 hx8_1 hx11_1 hx12_1 hx19_1 hx20_1 hfp1
      hv0_1 hv1_1 hv2_1 hv7_1 hv19_1 hv20_1 hv21_1 hv22_1 hv25_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hfp2,
      hv0_2, hv1_2, hv2_2, hv4_2, hv5_2, hv6_2, hv7_2, hv16_2, hv19_2, rfl⟩
  refine sepWP_seq_env hcl2 hro2
    (seg5_decomp_part3 hb s2 sp x19Val x20Val fpVal hm e2 _ _ Rest0
      hpc2 hrun2 hsp2 hspA2 hx8_2 hx10_2 hx11_2 hx12_2 hx19_2 hx20_2 hfp2
      hv0_2 hv1_2 hv2_2 hv4_2 hv5_2 hv6_2 hv7_2 hv16_2 hv19_2) ?_
  rintro s3 P3 hpc3 hrun3 _ _
    ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hfp3, hv1_3, hv2_3, hP3⟩
  let pMsg3 : Vec32 := (((((((((((((((((((((((((((((((Vec32.ofFn fMsg).set 0 (polyVecNat (msgPoly16 m) 0)).set 1 (polyVecNat (msgPoly16 m) 1)).set 3 (polyVecNat (msgPoly16 m) 3)).set 2 (polyVecNat (msgPoly16 m) 2)).set 4 (polyVecNat (msgPoly16 m) 4)).set 6 (polyVecNat (msgPoly16 m) 6)).set 5 (polyVecNat (msgPoly16 m) 5)).set 7 (polyVecNat (msgPoly16 m) 7)).set 8 (polyVecNat (msgPoly16 m) 8)).set 9 (polyVecNat (msgPoly16 m) 9)).set 11 (polyVecNat (msgPoly16 m) 11)).set 10 (polyVecNat (msgPoly16 m) 10)).set 12 (polyVecNat (msgPoly16 m) 12)).set 13 (polyVecNat (msgPoly16 m) 13)).set 14 (polyVecNat (msgPoly16 m) 14)).set 15 (polyVecNat (msgPoly16 m) 15)).set 16 (polyVecNat (msgPoly16 m) 16)).set 18 (polyVecNat (msgPoly16 m) 18)).set 17 (polyVecNat (msgPoly16 m) 17)).set 19 (polyVecNat (msgPoly16 m) 19)).set 21 (polyVecNat (msgPoly16 m) 21)).set 20 (polyVecNat (msgPoly16 m) 20)).set 22 (polyVecNat (msgPoly16 m) 22)).set 23 (polyVecNat (msgPoly16 m) 23)).set 25 (polyVecNat (msgPoly16 m) 25)).set 24 (polyVecNat (msgPoly16 m) 24)).set 27 (polyVecNat (msgPoly16 m) 27)).set 26 (polyVecNat (msgPoly16 m) 26)).set 28 (polyVecNat (msgPoly16 m) 28)).set 29 (polyVecNat (msgPoly16 m) 29))
  have hpE2 : (((((((((((((((((((((((((((((((((Vec32.ofFn fE2).set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)).set 5 (polyVecNat e2 5)).set 3 (polyVecNat e2 3)).set 6 (polyVecNat e2 6)).set 9 (polyVecNat e2 9)).set 11 (polyVecNat e2 11)).set 7 (polyVecNat e2 7)).set 10 (polyVecNat e2 10)).set 8 (polyVecNat e2 8)).set 12 (polyVecNat e2 12)).set 25 (polyVecNat e2 25)).set 13 (polyVecNat e2 13)).set 18 (polyVecNat e2 18)).set 26 (polyVecNat e2 26)).set 14 (polyVecNat e2 14)).set 15 (polyVecNat e2 15)).set 16 (polyVecNat e2 16)).set 17 (polyVecNat e2 17)).set 19 (polyVecNat e2 19)).set 20 (polyVecNat e2 20)).set 21 (polyVecNat e2 21)).set 22 (polyVecNat e2 22)).set 23 (polyVecNat e2 23)).set 24 (polyVecNat e2 24)).set 27 (polyVecNat e2 27)).set 28 (polyVecNat e2 28)).set 29 (polyVecNat e2 29)).set 30 (polyVecNat e2 30)).set 31 (polyVecNat e2 31)) =
      Vec32.ofFn (polyVecNat e2) := rfl
  have hP3' : P3 = (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
      Poly32Mem (sp + 24720#64) pMsg3 ∗ Poly32Mem (sp + 31408#64) (Vec32.ofFn (polyVecNat e2)) ∗
      Rest0) := by
    rw [hP3, hpE2]
  rw [hP3']
  dsimp only [Rest0]
  refine SepWP.weaken_pre (show
      WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 24720#64) pMsg3 ∗ Poly32Mem (sp + 31408#64) (Vec32.ofFn (polyVecNat e2)) ∗
        (Spill13Mem (sp + 2224#64) (Spill13.ofFn fSp) ∗
          Poly32Mem (sp + 26768#64) (Vec32.ofFn fDot) ∗ Rest) ⊢
      Poly32Mem (sp + 24720#64) pMsg3 ∗ Poly32Mem (sp + 26768#64) (Vec32.ofFn fDot) ∗
        Spill13Mem (sp + 2224#64) (Spill13.ofFn fSp) ∗
        (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 31408#64) (Vec32.ofFn (polyVecNat e2)) ∗ Rest) by sep_frame)
    (SepWP.mono
      (seg5_decomp_zero hb s3 sp (mlkemMpl.ρ ro00Sym + 134#64) 62209#64 3329#64 (sp + 28848#64)
        x19Val x20Val fpVal (polyVecNat (msgPoly16 m) 30) (polyVecNat (msgPoly16 m) 31)
        pMsg3 (Vec32.ofFn fDot) (Spill13.ofFn fSp)
        (WordRangeMem 32 (sp + 16#64) (msgSlotWord m) ∗ PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 31408#64) (Vec32.ofFn (polyVecNat e2)) ∗ Rest)
        hpc3 hrun3 hsp3 hspA3 hx8_3 hx9_3 hx10_3 hx11_3 hx12_3 hx19_3 hx20_3 hfp3 hv1_3 hv2_3) ?_)
  rintro s4 P4 _ _
    ⟨hsp4, hspA4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4, hx19_4, hx20_4, hfp4, hacc4, rfl⟩
  have hpMsg : ((pMsg3.set 30 (polyVecNat (msgPoly16 m) 30)).set 31 (polyVecNat (msgPoly16 m) 31)) =
      Vec32.ofFn (polyVecNat (msgPoly16 m)) := rfl
  have hpDot : (((((((((((((((((((((((((((((((((Vec32.ofFn fDot).set 0 0#128).set 1 0#128).set 2 0#128).set 3 0#128).set 4 0#128).set 5 0#128).set 6 0#128).set 7 0#128).set 8 0#128).set 9 0#128).set 10 0#128).set 11 0#128).set 12 0#128).set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 27 0#128).set 25 0#128).set 23 0#128).set 21 0#128).set 19 0#128).set 17 0#128).set 15 0#128).set 13 0#128).set 14 0#128).set 16 0#128).set 18 0#128).set 20 0#128).set 22 0#128).set 24 0#128).set 26 0#128) =
      Vec32.zero := rfl
  have hpSp : ((((((((((((((Spill13.ofFn fSp).set 12 0#128).set 11 0#128).set 10 0#128).set 9 0#128).set 8 0#128).set 7 0#128).set 6 0#128).set 5 0#128).set 4 0#128).set 3 0#128).set 2 0#128).set 1 0#128).set 0 0#128) =
      Spill13.zero := rfl
  refine ⟨hsp4, hspA4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4, hx19_4, hx20_4, hfp4, hacc4, ?_⟩
  rw [hpMsg, hpDot, hpSp, ← spilledMsgWords_eq_wordRangeMem, poly32Mem_ofFn, poly32Mem_ofFn,
      show Poly32Mem (sp + 26768#64) Vec32.zero = PolyMem (sp + 26768#64) (fun _ => 0#128) from
        poly32Mem_ofFn _ _,
      ← accSpill_zero]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Decomp
