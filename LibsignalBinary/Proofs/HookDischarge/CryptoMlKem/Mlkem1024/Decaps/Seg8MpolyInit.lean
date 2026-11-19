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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1

/-!
# `kyber_decapsulate` (`B06`) — Segment 8 `e₂` Copy, `decompress_1(m')`, & Dot Init (`+0xb308 .. +0xb8bc`)

Proves `seg8_mpoly_init_ok` (`+0xb308 → +0xb8bc`):
1. Copies `e₂` (`512` B) from `PolyMem (sp + 1488#64)` to `PolyMem (sp + 33008#64)`.
2. Runs AdvSIMD `decompress_1(m')` from `SpilledDecapsWords sp m'` to
   `PolyMem (sp + 26320#64) (polyVecNat (msgPoly16 m'))` and reloads `x22 = ctA` from `[sp, #136]`.
3. Zeroes `Poly32Mem (sp + 28368#64) Vec32.zero`, `Spill13Mem (sp + 2224#64) (AccSpill polyZero16)`,
   and establishes `AccRegs polyZero16` plus `Seg8DotInv` entry GPRs (`x8..x12`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8MpolyInit

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
  Vec32 VecRangeMem poly32Mem_ofFn polyVecNat spill13Mem_ofFn step_ldrQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  msgPoly16 neonDecompress1Byte neonDecompress1Byte_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdCmeqZero_8h exec_simdDup_8h exec_simdSshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (polyZero16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (
  AccRegs AccSpill accRegs_zero_iff accSpill_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (msgW32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (
  SpilledDecapsHi SpilledDecapsLo SpilledDecapsWords)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xb308 → 0xb338, 0xb340 → 0xb8b8]
gen_placed_odd_sites blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xb33c → 0xb33c]

@[simp, arm64_norm]
private theorem blkPC06_rebase_fetchOff_b350 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC06.rebase b X).fetch (b + BitVec.ofNat 64 45904) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 1)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl06.ρ "libcrux_ml_kem:.rodata.cst16.6")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib06) (prog := blkPC06) (pl := blkPl06)
    (b := b) (X := X) (off := 45904)
    (r := { off := 45904, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" })
    rfl blkPlaceable06 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 45904)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 11476) blk06_code_eq blk06_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm] abbrev offSeg8Start : BitVec 64 := BitVec.ofNat 64 45832
@[simp, arm64_norm, wp_norm] abbrev offSeg8Ro    : BitVec 64 := BitVec.ofNat 64 45904
@[simp, arm64_norm, wp_norm] abbrev offSeg8Mid1  : BitVec 64 := BitVec.ofNat 64 46344
@[simp, arm64_norm, wp_norm] abbrev offSeg8Mid2  : BitVec 64 := BitVec.ofNat 64 46684
@[simp, arm64_norm, wp_norm] abbrev offSeg8Zero1 : BitVec 64 := BitVec.ofNat 64 46964
@[simp, arm64_norm, wp_norm] abbrev offSeg8Zero2 : BitVec 64 := BitVec.ofNat 64 47124
@[simp, arm64_norm, wp_norm] abbrev offSeg8Dot   : BitVec 64 := BitVec.ofNat 64 47292

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

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

@[simp, arm64_norm, wp_norm]
private theorem spA_writeVReg128 (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm]
private theorem spA_writeGPR (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm]
private theorem spA_writeReg32 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg .W32 (.gpr i) v).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm]
private theorem spA_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm]
private theorem spA_setMem (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := rfl

attribute [local irreducible]
  blkPC06 dup8x16 polyVecNat simdSshl8h simdCmeqZero8h neonDecompress1Byte

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

private def decapsSlotIdx : Nat → Nat
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6
  | 8 => 8 | 9 => 9 | 10 => 11 | 11 => 10 | 12 => 12 | 13 => 13 | 14 => 14 | 15 => 15
  | 16 => 17 | 17 => 16 | 18 => 18 | 19 => 19 | 20 => 21 | 21 => 20 | 22 => 22 | 23 => 23
  | 24 => 25 | 25 => 24 | 26 => 29 | 27 => 26 | 28 => 27 | 29 => 31 | 30 => 30 | _ => 28

private def decapsSlotWord (m : List (BitVec 8)) (k : Nat) : BitVec 32 :=
  msgW32 m (decapsSlotIdx k)

private theorem spilledDecapsWords_eq_wordRangeMem (sp : BitVec 64) (m : List (BitVec 8)) :
    SpilledDecapsWords sp m = WordRangeMem 32 sp (decapsSlotWord m) := by
  dsimp only [SpilledDecapsWords, SpilledDecapsLo, SpilledDecapsHi, WordRangeMem,
    decapsSlotWord, decapsSlotIdx, Nat.reduceAdd]
  rw [emp_sepConj, show sp + BitVec.ofNat 64 (4 * 0) = sp by bv_omega]
  sep_ac_rfl

private theorem step_ldr_msgW {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {rt : Reg} {imm : BitVec 64} (k : Nat)
    (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : BitVec.ofNat 64 (4 * k) = imm := by decide)
    (hexec : (s.writeReg .W32 rt ((m.getD (decapsSlotIdx k) 0#8).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 sp (decapsSlotWord m) ∗ Rest) post) :
    SepWP prog target_pc s (WordRangeMem 32 sp (decapsSlotWord m) ∗ Rest) post := by
  have ha : sp + BitVec.ofNat 64 (4 * k) = s.sp + imm := by rw [hsp_eq, himm]
  exact SepWP.step_ldr32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) (SepLoad32.left (SepLoad32.wordRange hk ha))
    (by simpa only [applyWriteback, decapsSlotWord, msgW32, zext64_zext32_8] using hexec) hnext

private theorem step_ldp_msgW {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {m : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {rt1 rt2 : Reg} {imm : BitVec 64} (k : Nat)
    (hk1 : k + 1 < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W32 false rt1 rt2 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : BitVec.ofNat 64 (4 * k) = imm := by decide)
    (hexec : (((s.writeReg .W32 rt1 ((m.getD (decapsSlotIdx k) 0#8).zeroExtend 64)).writeReg .W32 rt2
      ((m.getD (decapsSlotIdx (k + 1)) 0#8).zeroExtend 64))).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 sp (decapsSlotWord m) ∗ Rest) post) :
    SepWP prog target_pc s (WordRangeMem 32 sp (decapsSlotWord m) ∗ Rest) post := by
  have ha1 : sp + BitVec.ofNat 64 (4 * k) = s.sp + imm := by rw [hsp_eq, himm]
  have ha2 : sp + BitVec.ofNat 64 (4 * (k + 1)) = (s.sp + imm) + 4#64 := by
    rw [← ha1]; clear * - hk1; bv_omega
  exact SepWP.step_ldp32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) rfl
    (SepLoad32.left (SepLoad32.wordRange (by omega) ha1))
    (SepLoad32.left (SepLoad32.wordRange hk1 ha2))
    (by simpa only [applyWriteback, decapsSlotWord, msgW32, zext64_zext32_8] using hexec) hnext

private theorem step_ldr_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp ctA : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 1488#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hexec : (s.writeVReg128 vt (polyVecNat e2 k)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Rest) post := by
  have ha : (sp + 1488#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange hk ha)))) hexec hnext

private theorem step_str_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp ctA : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16}
    {pMsg pE2 pE2' : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 33008#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = polyVecNat e2 k) (hp : pE2.set k (polyVecNat e2 k) = pE2')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 33008#64) pE2' ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 33008#64) pE2 ∗ Rest) post := by
  have ha : (sp + 33008#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp))))))
    hexec hnext

private theorem step_msg_strQ {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp ctA : BitVec 64} {m : List (BitVec 8)} {e2 : Poly16}
    {pMsg pMsg' pE2 : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hm : m.length = 32) (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 26320#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = neonDecompress1Byte ((m.getD k 0#8).zeroExtend 16))
    (hp : pMsg.set k (polyVecNat (msgPoly16 m) k) = pMsg') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg' ∗ Poly32Mem (sp + 33008#64) pE2 ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 33008#64) pE2 ∗ Rest) post := by
  have ha : (sp + 26320#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hv : s.readVReg128 vt = polyVecNat (msgPoly16 m) k := by
    rw [hval]; exact neonDecompress1Byte_eq hm k hk _ (by clear * -; bv_omega)
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.left (SepStore128.vec32 hk ha hp)))))
    hexec hnext

local macro "s8_ldrw " k:num : tactic => `(tactic|
  refine step_ldr_msgW $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs)
    (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s8_ldpw " k:num : tactic => `(tactic|
  refine step_ldp_msgW $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs)
    (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s8_ldre2 " k:num : tactic => `(tactic|
  refine step_ldr_e2 $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs)
    (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "s8_stre2 " k:num : tactic => `(tactic| (
  refine step_str_e2 $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs)
    (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*]) (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "s8_strmsg " k:num : tactic => `(tactic| (
  refine step_msg_strQ $k (by assumption) (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
    (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*]) (by decide)
    (by first | wp_norm_lhs | simp [wp_norm, arm64_norm, *]) rfl (by wp_norm_lhs) ?_
  intro _))

private theorem step_strQ_dot {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot pDot' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 0#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 28368#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv0 : s.readVReg128 0#5 = 0#128) (hd : pDot.set k 0#128 = pDot')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot ∗ Rest) post := by
  have ha : (sp + 28368#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv0
    (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hd))) hexec hnext

private theorem step_ldrQ_dot {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 28368#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hget : pDot.get k = 0#128) (hexec : (s.writeVReg128 vt 0#128).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot ∗ Rest) post := by
  have ha : (sp + 28368#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha hget))) hexec hnext



private theorem step_strQ_sp {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp13 sp13' : Spill13} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 13 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 1#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2224#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv1 : s.readVReg128 1#5 = 0#128) (hsp13 : sp13.set k 0#128 = sp13')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) pDot ∗
        Spill13Mem (sp + 2224#64) sp13 ∗ Rest) post := by
  have ha : (sp + 2224#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv1
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.spill13 hk ha hsp13))))
    hexec hnext

private theorem step_msg_strQ_z {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pMsg' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64}
    {val : BitVec 128} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 26320#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = val) (hp : pMsg.set k val = pMsg')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 26320#64) pMsg' ∗ Rest) post) :
    SepWP prog target_pc s (Poly32Mem (sp + 26320#64) pMsg ∗ Rest) post := by
  have ha : (sp + 26320#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hval (SepStore128.left (SepStore128.vec32 hk ha hp)) hexec hnext

local macro "s8_strdot " k:num : tactic => `(tactic| (
  refine step_strQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [*]) rfl (by wp_norm_lhs) ?_; intro _))

local macro "s8_ldrdot " k:num : tactic => `(tactic|
  refine step_ldrQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) rfl (by wp_norm_lhs) ?_)

local macro "s8_strsp " k:num : tactic => `(tactic| (
  refine step_strQ_sp $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [*]) rfl (by wp_norm_lhs) ?_; intro _))

local macro "s8_strmsg_z " k:num hv:term:arg : tactic => `(tactic| (
  refine step_msg_strQ_z $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [$hv:term]; rfl) rfl (by wp_norm_lhs) ?_; intro _))

private theorem seg8_mpoly_pre [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64) (m : List (BitVec 8))
    (e2 : Poly16) (pMsg0 pE2_0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Ro) s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg0 ∗ Poly32Mem (sp + 33008#64) pE2_0 ∗ Rest)
      (fun s0 P0 =>
        s0.sp = sp ∧ s0.spAligned = true ∧ s0.readReg64 .x8 = 0#64 ∧
        s0.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6") ∧
        s0.readReg64 .x12 = sp + 30448#64 ∧
        s0.readReg64 .x19 = x19Val ∧ s0.readReg64 .x20 = x20Val ∧ s0.readReg64 .fp = fpVal ∧
        s0.readVReg128 0#5 = polyVecNat e2 3 ∧
        s0.readVReg128 2#5 = dup8x16 (mbW16 m 0) ∧ s0.readVReg128 3#5 = dup8x16 (mbW16 m 1) ∧
        s0.readVReg128 4#5 = polyVecNat e2 5 ∧ s0.readVReg128 5#5 = polyVecNat e2 6 ∧
        P0 = (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗ Poly32Mem (sp + 26320#64) pMsg0 ∗
          Poly32Mem (sp + 33008#64) ((((pE2_0.set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)) ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s8_ldre2 0; s8_ldre2 4; wp_step; s8_ldpw 0; s8_stre2 0; s8_ldre2 1; wp_step; s8_stre2 4
  s8_ldre2 5; wp_step; s8_stre2 1; s8_ldre2 2; wp_step; wp_step; wp_step; s8_ldre2 6; s8_stre2 2; s8_ldre2 3
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk, by simp, by simp,
      by simp, by simp [hx19], by simp [hx20], by simp [hfp],
      by wp_norm_lhs, by simp [decapsSlotIdx], by simp [decapsSlotIdx],
      by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8_mpoly_part1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg0 pE2_a : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Ro) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6"))
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = polyVecNat e2 3)
    (hv2 : s.readVReg128 2#5 = dup8x16 (mbW16 m 0)) (hv3 : s.readVReg128 3#5 = dup8x16 (mbW16 m 1))
    (hv4 : s.readVReg128 4#5 = polyVecNat e2 5) (hv5 : s.readVReg128 5#5 = polyVecNat e2 6) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Mid1) s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg0 ∗ Poly32Mem (sp + 33008#64) pE2_a ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = mbZ64 m 13 ∧ s1.readReg64 .x10 = mbZ64 m 12 ∧
        s1.readReg64 .x11 = 3329#64 ∧ s1.readReg64 .x12 = sp + 30448#64 ∧
        s1.readReg64 .x19 = x19Val ∧ s1.readReg64 .x20 = x20Val ∧
        s1.readReg64 .x22 = ctA ∧ s1.readReg64 .fp = fpVal ∧
        s1.readVReg128 0#5 = dup8x16 1#16 ∧
        s1.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s1.readVReg128 2#5 = dup8x16 1665#16 ∧
        s1.readVReg128 7#5 = mbDec m 7 ∧ s1.readVReg128 18#5 = mbDec m 5 ∧
        s1.readVReg128 19#5 = mbAnd m 8 ∧ s1.readVReg128 20#5 = mbSshl m 9 ∧
        s1.readVReg128 21#5 = dup8x16 (mbW16 m 10) ∧ s1.readVReg128 22#5 = mbAnd m 11 ∧
        s1.readVReg128 25#5 = polyVecNat e2 27 ∧
        P1 = (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 26320#64) ((((((pMsg0.set 0 (polyVecNat (msgPoly16 m) 0)).set 1 (polyVecNat (msgPoly16 m) 1)).set 3 (polyVecNat (msgPoly16 m) 3)).set 4 (polyVecNat (msgPoly16 m) 4)).set 2 (polyVecNat (msgPoly16 m) 2)).set 6 (polyVecNat (msgPoly16 m) 6)) ∗
          Poly32Mem (sp + 33008#64) (((((((((((((((((((((((pE2_a.set 3 (polyVecNat e2 3)).set 5 (polyVecNat e2 5)).set 6 (polyVecNat e2 6)).set 9 (polyVecNat e2 9)).set 10 (polyVecNat e2 10)).set 7 (polyVecNat e2 7)).set 11 (polyVecNat e2 11)).set 8 (polyVecNat e2 8)).set 12 (polyVecNat e2 12)).set 25 (polyVecNat e2 25)).set 13 (polyVecNat e2 13)).set 18 (polyVecNat e2 18)).set 14 (polyVecNat e2 14)).set 26 (polyVecNat e2 26)).set 15 (polyVecNat e2 15)).set 16 (polyVecNat e2 16)).set 17 (polyVecNat e2 17)).set 19 (polyVecNat e2 19)).set 20 (polyVecNat e2 20)).set 21 (polyVecNat e2 21)).set 22 (polyVecNat e2 22)).set 23 (polyVecNat e2 23)).set 24 (polyVecNat e2 24)) ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6")
    (by simp [evalAddrMode, pageOf_add_lo12Of, *])
    (by simpa using hro.cst16_6) mlkemData08Bytes_length cst16_6_vec (by wp_norm_lhs) ?_
  s8_ldpw 2; s8_stre2 3; wp_steps 2; s8_ldre2 9; wp_step; s8_stre2 5; wp_step; s8_stre2 6
  wp_step; s8_ldrw 4; s8_stre2 9; s8_ldre2 10; wp_step; s8_ldre2 7; s8_ldre2 11; wp_step
  s8_stre2 10; wp_step; s8_stre2 7; s8_ldre2 8; s8_ldre2 12; wp_step; s8_stre2 11; wp_step
  s8_stre2 8; wp_step; s8_ldrw 5; s8_stre2 12; wp_steps 4; s8_ldre2 25; s8_ldpw 6; wp_steps 2
  s8_ldre2 13; wp_step; s8_stre2 25; s8_ldre2 26; wp_step; s8_stre2 13; wp_steps 3; s8_ldre2 18
  s8_ldpw 8; wp_step; s8_ldre2 14; s8_stre2 18; wp_steps 3; s8_stre2 14; wp_step; s8_ldre2 15
  wp_step; s8_stre2 26; wp_step; s8_stre2 15; wp_step; s8_ldre2 16; wp_steps 2; s8_strmsg 0
  s8_stre2 16; s8_ldre2 17; wp_steps 2; s8_ldre2 19; s8_ldre2 27; s8_stre2 17; wp_steps 2
  s8_stre2 19; s8_ldre2 20; wp_steps 2; s8_strmsg 1; wp_step; s8_stre2 20; wp_step; s8_ldre2 21
  s8_ldpw 10; s8_stre2 21; wp_step; s8_ldre2 22; s8_strmsg 3; wp_step; wp_step; s8_stre2 22
  wp_step; s8_ldre2 23; wp_step; s8_strmsg 4; s8_stre2 23; wp_steps 2; s8_ldre2 24; s8_strmsg 2
  wp_step; s8_strmsg 6; s8_stre2 24; wp_steps 2; s8_ldpw 12; wp_steps 2
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [decapsSlotIdx], by simp [decapsSlotIdx], by simp,
      by simp [hx12], by simp [hx19], by simp [hx20], by simp, by simp [hfp],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8_mpoly_part2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg1 pE2_1 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Mid1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mbZ64 m 13)
    (hx10 : s.readReg64 .x10 = mbZ64 m 12) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv7 : s.readVReg128 7#5 = mbDec m 7) (hv18 : s.readVReg128 18#5 = mbDec m 5)
    (hv19 : s.readVReg128 19#5 = mbAnd m 8) (hv20 : s.readVReg128 20#5 = mbSshl m 9)
    (hv21 : s.readVReg128 21#5 = dup8x16 (mbW16 m 10)) (hv22 : s.readVReg128 22#5 = mbAnd m 11)
    (hv25 : s.readVReg128 25#5 = polyVecNat e2 27) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Mid2) s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg1 ∗ Poly32Mem (sp + 33008#64) pE2_1 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x11 = 3329#64 ∧ s2.readReg64 .x12 = sp + 30448#64 ∧
        s2.readReg64 .x19 = x19Val ∧ s2.readReg64 .x20 = x20Val ∧
        s2.readReg64 .x22 = ctA ∧ s2.readReg64 .fp = fpVal ∧
        s2.readVReg128 0#5 = dup8x16 1#16 ∧
        s2.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s2.readVReg128 2#5 = dup8x16 1665#16 ∧
        s2.readVReg128 3#5 = mbDec m 17 ∧ s2.readVReg128 4#5 = mbCmeq m 20 ∧
        s2.readVReg128 5#5 = mbCmeq m 18 ∧ s2.readVReg128 7#5 = mbDec m 19 ∧
        s2.readVReg128 16#5 = mbCmeq m 21 ∧ s2.readVReg128 17#5 = dup8x16 (mbW16 m 23) ∧
        s2.readVReg128 19#5 = dup8x16 (mbW16 m 22) ∧
        P2 = (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 26320#64) (((((((((((pMsg1.set 7 (polyVecNat (msgPoly16 m) 7)).set 5 (polyVecNat (msgPoly16 m) 5)).set 8 (polyVecNat (msgPoly16 m) 8)).set 9 (polyVecNat (msgPoly16 m) 9)).set 11 (polyVecNat (msgPoly16 m) 11)).set 10 (polyVecNat (msgPoly16 m) 10)).set 12 (polyVecNat (msgPoly16 m) 12)).set 13 (polyVecNat (msgPoly16 m) 13)).set 14 (polyVecNat (msgPoly16 m) 14)).set 15 (polyVecNat (msgPoly16 m) 15)).set 16 (polyVecNat (msgPoly16 m) 16)) ∗
          Poly32Mem (sp + 33008#64) (((((pE2_1.set 27 (polyVecNat e2 27)).set 28 (polyVecNat e2 28)).set 29 (polyVecNat e2 29)).set 30 (polyVecNat e2 30)).set 31 (polyVecNat e2 31)) ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s8_strmsg 7; wp_steps 2; s8_strmsg 5; wp_steps 2; s8_stre2 27; wp_steps 2; s8_ldre2 28
  wp_steps 4; s8_stre2 28; wp_steps 2; s8_ldre2 29; wp_steps 4; s8_stre2 29; s8_ldpw 14; wp_step
  s8_strmsg 8; s8_ldre2 30; wp_steps 2; s8_strmsg 9; wp_steps 2; s8_strmsg 11; s8_ldpw 16
  wp_steps 2; s8_strmsg 10; wp_steps 2; s8_stre2 30; wp_steps 2; s8_ldre2 31; s8_ldpw 18
  wp_steps 2; s8_strmsg 12; wp_steps 2; s8_strmsg 13; wp_steps 2; s8_stre2 31; s8_ldpw 20
  wp_steps 16; s8_ldpw 22; wp_steps 2; s8_strmsg 14; wp_steps 2; s8_strmsg 15; wp_steps 4
  s8_strmsg 16; wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [hx11], by simp [hx12],
      by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8_mpoly_part3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (pMsg2 pE2_2 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Mid2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv3 : s.readVReg128 3#5 = mbDec m 17) (hv4 : s.readVReg128 4#5 = mbCmeq m 20)
    (hv5 : s.readVReg128 5#5 = mbCmeq m 18) (hv7 : s.readVReg128 7#5 = mbDec m 19)
    (hv16 : s.readVReg128 16#5 = mbCmeq m 21) (hv17 : s.readVReg128 17#5 = dup8x16 (mbW16 m 23))
    (hv19 : s.readVReg128 19#5 = dup8x16 (mbW16 m 22)) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Zero1) s
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 26320#64) pMsg2 ∗ Poly32Mem (sp + 33008#64) pE2_2 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s3.readReg64 .x10 = 62209#64 ∧ s3.readReg64 .x11 = 3329#64 ∧
        s3.readReg64 .x12 = sp + 30448#64 ∧
        s3.readReg64 .x19 = x19Val ∧ s3.readReg64 .x20 = x20Val ∧
        s3.readReg64 .x22 = ctA ∧ s3.readReg64 .fp = fpVal ∧
        s3.readVReg128 1#5 = polyVecNat (msgPoly16 m) 30 ∧
        s3.readVReg128 2#5 = polyVecNat (msgPoly16 m) 31 ∧
        s3.readVReg128 3#5 = polyVecNat (msgPoly16 m) 28 ∧
        s3.readVReg128 4#5 = polyVecNat (msgPoly16 m) 29 ∧
        P3 = (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 26320#64) (((((((((((pMsg2.set 17 (polyVecNat (msgPoly16 m) 17)).set 19 (polyVecNat (msgPoly16 m) 19)).set 21 (polyVecNat (msgPoly16 m) 21)).set 20 (polyVecNat (msgPoly16 m) 20)).set 18 (polyVecNat (msgPoly16 m) 18)).set 22 (polyVecNat (msgPoly16 m) 22)).set 23 (polyVecNat (msgPoly16 m) 23)).set 24 (polyVecNat (msgPoly16 m) 24)).set 25 (polyVecNat (msgPoly16 m) 25)).set 26 (polyVecNat (msgPoly16 m) 26)).set 27 (polyVecNat (msgPoly16 m) 27)) ∗
          Poly32Mem (sp + 33008#64) pE2_2 ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  s8_ldpw 24; s8_strmsg 17; wp_steps 4; s8_strmsg 19; wp_steps 2; s8_ldpw 27; s8_strmsg 21; wp_step
  s8_strmsg 20; wp_steps 3; s8_ldrw 31; s8_strmsg 18; wp_steps 4; s8_ldrw 26; wp_steps 6
  s8_ldpw 29; wp_steps 20; s8_strmsg 22; s8_strmsg 23; wp_step; wp_step; wp_step; wp_steps 4
  s8_strmsg 24; s8_strmsg 25; wp_steps 5; s8_strmsg 26; s8_strmsg 27; wp_steps 2
  have hv1_eq : neonDecompress1Byte ((m.getD 30 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 30 :=
    neonDecompress1Byte_eq hm 30 (by decide) _ (by bv_omega)
  have hv2_eq : neonDecompress1Byte ((m.getD 31 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 31 :=
    neonDecompress1Byte_eq hm 31 (by decide) _ (by bv_omega)
  have hv3_eq : neonDecompress1Byte ((m.getD 28 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 28 :=
    neonDecompress1Byte_eq hm 28 (by decide) _ (by bv_omega)
  have hv4_eq : neonDecompress1Byte ((m.getD 29 0#8).zeroExtend 16) = polyVecNat (msgPoly16 m) 29 :=
    neonDecompress1Byte_eq hm 29 (by decide) _ (by bv_omega)
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp, by simp, by simp [hx11], by simp [hx12],
      by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
      by rw [← hv1_eq]; wp_norm_lhs, by rw [← hv2_eq]; wp_norm_lhs,
      by rw [← hv3_eq]; wp_norm_lhs, by rw [← hv4_eq]; wp_norm_lhs, rfl⟩

private theorem seg8_mpoly_zero1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64)
    (v1Val v2Val v3Val v4Val : BitVec 128) (pMsg d0 : Vec32) (sp0 : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Zero1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hv1 : s.readVReg128 1#5 = v1Val) (hv2 : s.readVReg128 2#5 = v2Val)
    (hv3 : s.readVReg128 3#5 = v3Val) (hv4 : s.readVReg128 4#5 = v4Val) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Zero2) s
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) d0 ∗
        Spill13Mem (sp + 2224#64) sp0 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = x19Val ∧
        s'.readReg64 .x20 = x20Val ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = 0#128 ∧ s'.readVReg128 2#5 = v2Val ∧
        P' = (Poly32Mem (sp + 26320#64) (((pMsg.set 28 v3Val).set 29 v4Val).set 30 v1Val) ∗
          Poly32Mem (sp + 28368#64) (((((((((((((d0.set 0 0#128).set 1 0#128).set 2 0#128).set 3 0#128).set 4 0#128).set 5 0#128).set 6 0#128).set 7 0#128).set 8 0#128).set 9 0#128).set 10 0#128).set 11 0#128).set 12 0#128) ∗
          Spill13Mem (sp + 2224#64) (((((((((((sp0.set 12 0#128).set 11 0#128).set 10 0#128).set 9 0#128).set 8 0#128).set 7 0#128).set 6 0#128).set 5 0#128).set 4 0#128).set 3 0#128).set 2 0#128) ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  wp_step; s8_strmsg_z 28 hv3; s8_strmsg_z 29 hv4; s8_strmsg_z 30 hv1
  s8_strdot 0; s8_ldrdot 0; s8_strdot 1; s8_strdot 2; s8_strsp 12; s8_ldrdot 1; s8_strdot 3
  s8_strsp 11; s8_ldrdot 2; s8_strdot 4; s8_strsp 10; s8_ldrdot 3; s8_strdot 5; s8_strsp 9
  s8_ldrdot 4; s8_strdot 6; s8_strsp 8; s8_ldrdot 5; s8_strdot 7; s8_strsp 7; s8_ldrdot 6
  s8_strdot 8; s8_strsp 6; s8_ldrdot 7; s8_strdot 9; s8_strsp 5; s8_ldrdot 8; s8_strdot 10
  s8_strsp 4; s8_ldrdot 9; s8_strdot 11; s8_strsp 3; s8_ldrdot 10; s8_strdot 12; s8_strsp 2
  s8_ldrdot 11
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
      by wp_norm_lhs, by wp_norm_lhs, by simp [hv2], rfl⟩

private theorem seg8_mpoly_zero2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64)
    (v2Val : BitVec 128) (pMsg d1 : Vec32) (sp1 : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Zero2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = 0#128) (hv1 : s.readVReg128 1#5 = 0#128)
    (hv2 : s.readVReg128 2#5 = v2Val) (hd12 : d1.get 12 = 0#128) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Dot) s
      (Poly32Mem (sp + 26320#64) pMsg ∗ Poly32Mem (sp + 28368#64) d1 ∗
        Spill13Mem (sp + 2224#64) sp1 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = x19Val ∧
        s'.readReg64 .x20 = x20Val ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 s' ∧
        P' = (Poly32Mem (sp + 26320#64) (pMsg.set 31 v2Val) ∗
          Poly32Mem (sp + 28368#64) (((((((((((((((((((d1.set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 27 0#128).set 25 0#128).set 23 0#128).set 21 0#128).set 19 0#128).set 17 0#128).set 15 0#128).set 13 0#128).set 14 0#128).set 16 0#128).set 18 0#128).set 20 0#128).set 22 0#128).set 24 0#128).set 26 0#128) ∗
          Spill13Mem (sp + 2224#64) ((sp1.set 1 0#128).set 0 0#128) ∗ Rest)) := by
  have hbase : blkPl06.base = b := _hb.symm; subst hbase
  s8_strdot 31; s8_strsp 1
  refine step_ldrQ_dot 12 (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) hd12 (by wp_norm_lhs) ?_
  s8_strdot 30; s8_strdot 29; s8_ldrdot 30; s8_strdot 28; s8_ldrdot 29; s8_strdot 27
  s8_ldrdot 28; s8_strdot 25; s8_ldrdot 27; s8_strdot 23; s8_ldrdot 25; s8_strdot 21
  s8_ldrdot 23; s8_strdot 19; s8_ldrdot 21; s8_strdot 17; s8_ldrdot 19; s8_strdot 15
  s8_ldrdot 17; s8_strdot 13; s8_ldrdot 15; s8_strdot 14; s8_ldrdot 13; s8_strdot 16
  s8_ldrdot 14; s8_strdot 18; s8_ldrdot 16; s8_strdot 20; s8_ldrdot 18; s8_strdot 22
  s8_ldrdot 20; s8_strdot 24; s8_ldrdot 22; s8_strdot 26; s8_ldrdot 24; s8_strsp 0
  s8_ldrdot 26; s8_ldrdot 31; s8_strmsg_z 31 hv2
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
      (accRegs_zero_iff _).mpr ⟨by simp [hv0], by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs⟩, rfl⟩


theorem seg8_mpoly_init_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA x19Val x20Val fpVal : BitVec 64) {m : List (BitVec 8)} (hm : m.length = 32)
    (e2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hx20 : s.readReg64 .x20 = x20Val)
    (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Dot) s
      (SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗ memRegion (sp + 2224#64) 208 ∗
        memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 28368#64) 512 ∗
        memRegion (sp + 33008#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = x19Val ∧
        s'.readReg64 .x20 = x20Val ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 s' ∧
        P' = (SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          PolyMem (sp + 1488#64) (polyVecNat e2) ∗
          Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
          PolyMem (sp + 26320#64) (polyVecNat (msgPoly16 m)) ∗
          Poly32Mem (sp + 28368#64) Vec32.zero ∗
          PolyMem (sp + 33008#64) (polyVecNat e2) ∗ Rest)) := by
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [spilledDecapsWords_eq_wordRangeMem]
  refine SepWP.of_memRegion_vecRangeMem 13 (sp + 2224#64) (by decide) (by sep_focus) fun fSp => ?_
  rw [show VecRangeMem 13 (sp + 2224#64) fSp = Spill13Mem (sp + 2224#64) (Spill13.ofFn fSp) from
    (spill13Mem_ofFn _ _).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 26320#64) (by decide) (by sep_focus) fun fMsg => ?_
  rw [show VecRangeMem 32 (sp + 26320#64) fMsg = Poly32Mem (sp + 26320#64) (Vec32.ofFn fMsg) from
    (poly32Mem_ofFn _ _).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 28368#64) (by decide) (by sep_focus) fun fDot => ?_
  rw [show VecRangeMem 32 (sp + 28368#64) fDot = Poly32Mem (sp + 28368#64) (Vec32.ofFn fDot) from
    (poly32Mem_ofFn _ _).symm]
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 33008#64) (by decide) (by sep_focus) fun fE2 => ?_
  rw [show VecRangeMem 32 (sp + 33008#64) fE2 = Poly32Mem (sp + 33008#64) (Vec32.ofFn fE2) from
    (poly32Mem_ofFn _ _).symm]
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {s : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      SepWP prog pc1 s P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 s P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  refine stepf hcl hro
    (seg8_mpoly_pre hb s sp ctA x19Val x20Val fpVal m e2 (Vec32.ofFn fMsg) (Vec32.ofFn fE2) _
      hpc hrun hsp hspA hx19 hx20 hfp) (by sep_frame) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0 ⟨hsp0, hspA0, hx8_0, hx9_0, hx12_0, hx19_0, hx20_0, hfp0,
    hv0_0, hv2_0, hv3_0, hv4_0, hv5_0, rfl⟩
  refine stepf hcl0 hro0
    (seg8_mpoly_part1 hb s0 sp ctA x19Val x20Val fpVal hm e2 (Vec32.ofFn fMsg) _ _
      hpc0 hrun0 hsp0 hspA0 hro0 hx8_0 hx9_0 hx12_0 hx19_0 hx20_0 hfp0
      hv0_0 hv2_0 hv3_0 hv4_0 hv5_0) (by sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1,
    hx19_1, hx20_1, hx22_1, hfp1, hv0_1, hv1_1, hv2_1, hv7_1, hv18_1, hv19_1, hv20_1, hv21_1, hv22_1, hv25_1, rfl⟩
  refine stepf hcl1 hro1
    (seg8_mpoly_part2 hb s1 sp ctA x19Val x20Val fpVal hm e2 _ _ _
      hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx19_1 hx20_1 hx22_1 hfp1
      hv0_1 hv1_1 hv2_1 hv7_1 hv18_1 hv19_1 hv20_1 hv21_1 hv22_1 hv25_1) (by sep_frame) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx8_2, hx11_2, hx12_2, hx19_2, hx20_2, hx22_2, hfp2,
    hv0_2, hv1_2, hv2_2, hv3_2, hv4_2, hv5_2, hv7_2, hv16_2, hv17_2, hv19_2, rfl⟩
  refine stepf hcl2 hro2
    (seg8_mpoly_part3 hb s2 sp ctA x19Val x20Val fpVal hm e2 _ _ _
      hpc2 hrun2 hsp2 hspA2 hx8_2 hx11_2 hx12_2 hx19_2 hx20_2 hx22_2 hfp2
      hv0_2 hv1_2 hv2_2 hv3_2 hv4_2 hv5_2 hv7_2 hv16_2 hv17_2 hv19_2) (by sep_frame) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, _, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3,
    hx19_3, hx20_3, hx22_3, hfp3, hv1_3, hv2_3, hv3_3, hv4_3, rfl⟩
  refine stepf hcl3 hro3
    (seg8_mpoly_zero1 hb s3 sp ctA x19Val x20Val fpVal _ _ _ _ _ (Vec32.ofFn fDot) (Spill13.ofFn fSp) _
      hpc3 hrun3 hsp3 hchk hx8_3 hx9_3 hx10_3 hx11_3 hx12_3 hx19_3 hx20_3 hx22_3 hfp3
      hv1_3 hv2_3 hv3_3 hv4_3) (by sep_frame) ?_
  rintro s4 P4 hpc4 hrun4 _ _ ⟨hsp4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4,
    hx19_4, hx20_4, hx22_4, hfp4, hv0_4, hv1_4, hv2_4, rfl⟩
  refine SepWP.mono
    (seg8_mpoly_zero2 hb s4 sp ctA x19Val x20Val fpVal _ _ _ _ _
      hpc4 hrun4 hsp4 hchk hx8_4 hx9_4 hx10_4 hx11_4 hx12_4 hx19_4 hx20_4 hx22_4 hfp4
      hv0_4 hv1_4 hv2_4 rfl) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hx22', hfp', hacc', rfl⟩
  refine ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hx22', hfp', hacc', ?_⟩
  change (Poly32Mem (sp + 26320#64) (Vec32.ofFn (polyVecNat (msgPoly16 m))) ∗
      Poly32Mem (sp + 28368#64) Vec32.zero ∗
      Spill13Mem (sp + 2224#64) Spill13.zero ∗
      (WordRangeMem 32 sp (decapsSlotWord m) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        PolyMem (sp + 1488#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 33008#64) (Vec32.ofFn (polyVecNat e2)) ∗ Rest)) = _
  rw [poly32Mem_ofFn, poly32Mem_ofFn, ← accSpill_zero, ← spilledDecapsWords_eq_wordRangeMem]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8MpolyInit
