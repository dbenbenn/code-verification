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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 8a (`+0xabd8 .. +0xb058`)

Copies `e₂` (`PolyMem (sp + 1312#64)`) to `PolyMem (sp + 24448#64)`, runs the unrolled AdvSIMD
`decompress_1(m')` pipeline reading `WordRangeMem 32 (sp + 8#64) (msgWordFn m')` into
`Poly32Mem (sp + 19168#64)` slots `0..30` with slot `31` in `v2`, and initializes `DotLoops3`
entry registers (`x8..x13`, `v0 = 0#128`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_6_vec mlkemData08Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdCmeqZero8h simdSshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 poly32Mem_ofFn polyVecNat
  step_ldrQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  msgPoly16 neonDecompress1Byte neonDecompress1Byte_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdCmeqZero_8h exec_simdDup_8h exec_simdSshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (polyZero16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs accRegs_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepStore128.spill21 Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (AccSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (sepWP_elim_poly32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c (sepWP_elim_spill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem msgSlotIdx msgWordFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b (offSeg8Start)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xabd8 → 0xb18c]
gen_placed_odd_sites blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xac0c → 0xac0c]

@[simp, arm64_norm]
private theorem blkPC04_rebase_fetchOff_ac20 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 44064) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 1)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.6")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := 44064)
    (r := { off := 44064, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 44064)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 11016) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_8h_1 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10000#5 1#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1#16)).advancePC := by
  simp [execInstWithSvc]; rfl

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
  blkPC04 dup8x16 polyVecNat simdSshl8h simdCmeqZero8h neonDecompress1Byte

attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_1 exec_simdMovi_2d_0 exec_simdAnd_16b exec_simdBic_16b
  exec_simdDup_8h exec_simdSshl_8h exec_simdCmeqZero_8h
  zext32_trunc32_zext64_8 trunc16_zext64_8 trunc16_1665 bic_1665_cmeq_eq

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"
private abbrev mbZ64 (msg : List (BitVec 8)) (j : Nat) : BitVec 64 := (msg.getD j 0#8).zeroExtend 64
private abbrev mbW16 (msg : List (BitVec 8)) (j : Nat) : BitVec 16 := (msg.getD j 0#8).zeroExtend 16
private abbrev mbSshl (msg : List (BitVec 8)) (j : Nat) : BitVec 128 :=
  simdSshl8h (dup8x16 (mbW16 msg j)) 0xfff9fffafffbfffcfffdfffe00ff0000#128
private abbrev mbAnd (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := mbSshl msg j &&& dup8x16 1#16
private abbrev mbCmeq (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := simdCmeqZero8h (mbAnd msg j)
private abbrev mbDec (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := neonDecompress1Byte (mbW16 msg j)

private theorem zext64_msgWordFn_eq (msg : List (BitVec 8)) (slot j : Nat)
    (hj : msgSlotIdx.getD slot 0 = j) :
    (msgWordFn msg slot).zeroExtend 64 = mbZ64 msg j := by
  subst hj; simp [msgWordFn, mbZ64]

@[simp, arm64_norm, wp_norm] abbrev offAc20 : BitVec 64 := BitVec.ofNat 64 44064
@[simp, arm64_norm, wp_norm] abbrev offAd64 : BitVec 64 := BitVec.ofNat 64 44388
@[simp, arm64_norm, wp_norm] abbrev offAf00 : BitVec 64 := BitVec.ofNat 64 44800
@[simp, arm64_norm, wp_norm] abbrev offSeg8aEnd : BitVec 64 := BitVec.ofNat 64 45144
@[simp, arm64_norm, wp_norm] abbrev offB0f4 : BitVec 64 := BitVec.ofNat 64 45300
@[simp, arm64_norm, wp_norm] abbrev offSeg8Dot : BitVec 64 := BitVec.ofNat 64 45456

private theorem step_ldr32_msg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {R : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {imm : BitVec 64} (slot : Nat) {j : Nat}
    (hchk : (sp &&& 15#64 == 0#64) = true)
    (hslot : slot < 32 := by decide) (hj : msgSlotIdx.getD slot 0 = j := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 8#64 + BitVec.ofNat 64 (4 * slot) = imm := by decide)
    (hexec : (s.writeReg .W32 rt (mbZ64 msg j)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗ R) post) :
    SepWP prog target_pc s (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗ R) post := by
  have ha : (sp + 8#64) + BitVec.ofNat 64 (4 * slot) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  have hw : (msgWordFn msg slot).zeroExtend 64 = mbZ64 msg j := zext64_msgWordFn_eq msg slot j hj
  exact SepWP.step_ldr32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) (SepLoad32.left (SepLoad32.wordRange hslot ha))
    (by simpa [applyWriteback, hw] using hexec) hnext

private theorem step_ldp32_msg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {R : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt1 rt2 : Reg} {imm : BitVec 64} (slot : Nat) {j1 j2 : Nat}
    (hchk : (sp &&& 15#64 == 0#64) = true) (hslot : slot + 1 < 32 := by decide)
    (hj1 : msgSlotIdx.getD slot 0 = j1 := by decide)
    (hj2 : msgSlotIdx.getD (slot + 1) 0 = j2 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W32 false rt1 rt2 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 8#64 + BitVec.ofNat 64 (4 * slot) = imm := by decide)
    (hexec : ((s.writeReg .W32 rt1 (mbZ64 msg j1)).writeReg .W32 rt2 (mbZ64 msg j2)).setPC
      (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗ R) post) :
    SepWP prog target_pc s (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗ R) post := by
  have ha1 : (sp + 8#64) + BitVec.ofNat 64 (4 * slot) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have ha2 : (sp + 8#64) + BitVec.ofNat 64 (4 * (slot + 1)) = (s.sp + imm) + 4#64 := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  have hw1 : (msgWordFn msg slot).zeroExtend 64 = mbZ64 msg j1 := zext64_msgWordFn_eq msg slot j1 hj1
  have hw2 : (msgWordFn msg (slot + 1)).zeroExtend 64 = mbZ64 msg j2 :=
    zext64_msgWordFn_eq msg (slot + 1) j2 hj2
  exact SepWP.step_ldp32 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) rfl
    (SepLoad32.left (SepLoad32.wordRange (by omega) ha1))
    (SepLoad32.left (SepLoad32.wordRange hslot ha2))
    (by simpa [applyWriteback, hw1, hw2] using hexec) hnext

private theorem step_ldr_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {e2 : Poly16} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 1312#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hexec : (s.writeVReg128 vt (polyVecNat e2 k)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗ Rest) post := by
  have ha : (sp + 1312#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange hk ha))) hexec hnext

private theorem step_str_e2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {e2 : Poly16}
    {pMsg pE2 pE2' : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 24448#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv : s.readVReg128 vt = polyVecNat e2 k) (hp : pE2.set k (polyVecNat e2 k) = pE2')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 24448#64) pE2' ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 24448#64) pE2 ∗ Rest) post := by
  have ha : (sp + 24448#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.left (SepStore128.vec32 hk ha hp)))))
    hexec hnext

private theorem step_msg_strQ {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {e2 : Poly16}
    {pMsg pMsg' pE2 : Vec32} {Rest : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hm : msg.length = 32) (hk : k < 32 := by decide) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (hspA : s.spAligned = true)
    (himm : 19168#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = neonDecompress1Byte ((msg.getD k 0#8).zeroExtend 16))
    (hp : pMsg.set k (polyVecNat (msgPoly16 msg) k) = pMsg') (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg' ∗ Poly32Mem (sp + 24448#64) pE2 ∗ Rest) post) :
    SepWP prog target_pc s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 24448#64) pE2 ∗ Rest) post := by
  have ha : (sp + 19168#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hv : s.readVReg128 vt = polyVecNat (msgPoly16 msg) k := by
    rw [hval]; exact neonDecompress1Byte_eq hm k hk _ (by clear * -; bv_omega)
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp))))
    hexec hnext

local macro "m_ldr32 " k:num : tactic => do
  let tbl : Array Nat := #[1, 0, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 14, 15,
    17, 16, 18, 19, 21, 20, 22, 23, 25, 24, 29, 26, 27, 31, 30, 28]
  let j := Lean.Syntax.mkNumLit (toString (tbl.getD k.getNat 0))
  `(tactic|
    refine step_ldr32_msg (j := $j) $k (by assumption) (by decide) (by decide) (by wp_norm_lhs)
      (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
      (by decide) (by wp_norm_lhs) ?_)

local macro "m_ldp32 " k:num : tactic => do
  let tbl : Array Nat := #[1, 0, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 14, 15,
    17, 16, 18, 19, 21, 20, 22, 23, 25, 24, 29, 26, 27, 31, 30, 28]
  let j1 := Lean.Syntax.mkNumLit (toString (tbl.getD k.getNat 0))
  let j2 := Lean.Syntax.mkNumLit (toString (tbl.getD (k.getNat + 1) 0))
  `(tactic|
    refine step_ldp32_msg (j1 := $j1) (j2 := $j2) $k (by assumption) (by decide) (by decide)
      (by decide) (by wp_norm_lhs)
      (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
      (by decide) (by wp_norm_lhs) ?_)

local macro "e2_ldr " k:num : tactic => `(tactic|
  refine step_ldr_e2 $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
    (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*])
    (by decide) (by wp_norm_lhs) ?_)

local macro "e2_str " k:num : tactic => `(tactic| (
  refine step_str_e2 $k (by decide) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
    (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*]) (by first | wp_norm_lhs | simp [*])
    (by decide) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_; intro _))

local macro "m_str " k:num : tactic => `(tactic| (
  refine step_msg_strQ $k (by assumption) (by decide) (by wp_norm_lhs)
    (by first | wp_norm_lhs | simp [*]) (by wp_norm_lhs) (by first | wp_norm_lhs | simp [*])
    (by first | wp_norm_lhs | simp [*]) (by decide)
    (by first | wp_norm_lhs | simp [wp_norm, arm64_norm, *]) rfl (by wp_norm_lhs) ?_; intro _))

private theorem step_strQ_dot {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot pDot' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 0#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 20704#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv0 : s.readVReg128 0#5 = 0#128) (hd : pDot.set k 0#128 = pDot')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot ∗ Rest) post := by
  have ha : (sp + 20704#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
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
    (hsp_eq : s.sp = sp) (himm : 20704#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hget : pDot.get k = 0#128) (hexec : (s.writeVReg128 vt 0#128).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot ∗ Rest) post := by
  have ha : (sp + 20704#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha hget))) hexec hnext

private theorem step_strQ_sp21 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp21 sp21' : Spill21} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 21 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 1#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 1920#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv1 : s.readVReg128 1#5 = 0#128) (hsp21 : sp21.set k 0#128 = sp21')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot ∗
        Spill21Mem (sp + 1920#64) sp21' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) pDot ∗
        Spill21Mem (sp + 1920#64) sp21 ∗ Rest) post := by
  have ha : (sp + 1920#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hv1
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.spill21 hk ha hsp21))))
    hexec hnext

private theorem step_msg_strQ_z {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pMsg' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64}
    {val : BitVec 128} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 19168#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = val) (hp : pMsg.set k val = pMsg')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 19168#64) pMsg' ∗ Rest) post) :
    SepWP prog target_pc s (Poly32Mem (sp + 19168#64) pMsg ∗ Rest) post := by
  have ha : (sp + 19168#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; clear * -; bv_omega
  have hspA : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hspA])
    (by simp [evalAddrMode]) hval (SepStore128.left (SepStore128.vec32 hk ha hp)) hexec hnext

local macro "p_str " k:num : tactic => `(tactic| (
  refine step_strQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [*]) rfl (by wp_norm_lhs) ?_; intro _))

local macro "p_ldr " k:num : tactic => `(tactic|
  refine step_ldrQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) rfl (by wp_norm_lhs) ?_)

local macro "sp21_str " k:num : tactic => `(tactic| (
  refine step_strQ_sp21 $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [*]) rfl (by wp_norm_lhs) ?_; intro _))

local macro "m_str_z " k:num hv:term:arg : tactic => `(tactic| (
  refine step_msg_strQ_z $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [$hv:term]; rfl) rfl (by wp_norm_lhs) ?_; intro _))

private theorem seg8a_pre [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64) (msg : List (BitVec 8))
    (e2 : Poly16) (pMsg0 pE2_0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offAc20) s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg0 ∗ Poly32Mem (sp + 24448#64) pE2_0 ∗ Rest)
      (fun s0 P0 =>
        s0.sp = sp ∧ s0.spAligned = true ∧ s0.readReg64 .x8 = 0#64 ∧
        s0.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6") ∧
        s0.readReg64 .x12 = 3329#64 ∧ s0.readReg64 .x13 = sp + 20480#64 ∧
        s0.readReg64 .x19 = x19Val ∧ s0.readReg64 .fp = fpVal ∧
        s0.readVReg128 0#5 = polyVecNat e2 3 ∧
        s0.readVReg128 2#5 = dup8x16 (mbW16 msg 0) ∧ s0.readVReg128 3#5 = dup8x16 (mbW16 msg 1) ∧
        s0.readVReg128 4#5 = polyVecNat e2 5 ∧ s0.readVReg128 5#5 = polyVecNat e2 6 ∧
        P0 = (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
          PolyMem (sp + 1312#64) (polyVecNat e2) ∗ Poly32Mem (sp + 19168#64) pMsg0 ∗
          Poly32Mem (sp + 24448#64) ((((pE2_0.set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  e2_ldr 0; e2_ldr 4; wp_step; m_ldp32 0; e2_str 0; e2_ldr 1; wp_step; e2_str 4
  e2_ldr 5; wp_step; e2_str 1; e2_ldr 2; wp_steps 4; e2_ldr 6; e2_str 2; e2_ldr 3
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk, by simp, by simp,
      by simp, by simp, by simp [hx19], by simp [hfp],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8a_part1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64) {msg : List (BitVec 8)} (hm : msg.length = 32)
    (e2 : Poly16) (pMsg0 pE2_a : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offAc20) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6"))
    (hx12 : s.readReg64 .x12 = 3329#64) (hx13 : s.readReg64 .x13 = sp + 20480#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = polyVecNat e2 3)
    (hv2 : s.readVReg128 2#5 = dup8x16 (mbW16 msg 0))
    (hv3 : s.readVReg128 3#5 = dup8x16 (mbW16 msg 1))
    (hv4 : s.readVReg128 4#5 = polyVecNat e2 5) (hv5 : s.readVReg128 5#5 = polyVecNat e2 6) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offAd64) s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg0 ∗ Poly32Mem (sp + 24448#64) pE2_a ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = mbZ64 msg 9 ∧
        s1.readReg64 .x10 = mbZ64 msg 8 ∧ s1.readReg64 .x12 = 3329#64 ∧
        s1.readReg64 .x13 = sp + 20480#64 ∧ s1.readReg64 .x19 = x19Val ∧
        s1.readReg64 .fp = fpVal ∧
        s1.readVReg128 0#5 = dup8x16 1#16 ∧
        s1.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s1.readVReg128 2#5 = dup8x16 1665#16 ∧
        s1.readVReg128 5#5 = mbDec msg 2 ∧ s1.readVReg128 6#5 = mbDec msg 3 ∧
        s1.readVReg128 7#5 = mbCmeq msg 5 ∧ s1.readVReg128 16#5 = mbCmeq msg 6 ∧
        s1.readVReg128 17#5 = mbAnd msg 7 ∧ s1.readVReg128 18#5 = mbCmeq msg 4 ∧
        s1.readVReg128 19#5 = polyVecNat e2 20 ∧ s1.readVReg128 20#5 = dup8x16 (mbW16 msg 8) ∧
        s1.readVReg128 21#5 = dup8x16 (mbW16 msg 9) ∧ s1.readVReg128 25#5 = polyVecNat e2 27 ∧
        P1 = (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
          PolyMem (sp + 1312#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 19168#64) ((pMsg0.set 0 (polyVecNat (msgPoly16 msg) 0)).set 1 (polyVecNat (msgPoly16 msg) 1)) ∗
          Poly32Mem (sp + 24448#64) ((((((((((((((((((pE2_a.set 3 (polyVecNat e2 3)).set 5 (polyVecNat e2 5)).set 6 (polyVecNat e2 6)).set 9 (polyVecNat e2 9)).set 10 (polyVecNat e2 10)).set 7 (polyVecNat e2 7)).set 11 (polyVecNat e2 11)).set 8 (polyVecNat e2 8)).set 12 (polyVecNat e2 12)).set 25 (polyVecNat e2 25)).set 13 (polyVecNat e2 13)).set 18 (polyVecNat e2 18)).set 14 (polyVecNat e2 14)).set 26 (polyVecNat e2 26)).set 15 (polyVecNat e2 15)).set 16 (polyVecNat e2 16)).set 17 (polyVecNat e2 17)).set 19 (polyVecNat e2 19)) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs) rfl
    (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6")
    (by simp [evalAddrMode, pageOf_add_lo12Of, *])
    (by simpa using hro.cst16_6) mlkemData08Bytes_length cst16_6_vec (by wp_norm_lhs) ?_
  m_ldp32 2; e2_str 3; wp_steps 2; e2_ldr 9; wp_step; e2_str 5; wp_step; e2_str 6
  wp_step; m_ldr32 4; e2_str 9; e2_ldr 10; wp_step; e2_ldr 7; e2_ldr 11; wp_step
  e2_str 10; wp_step; e2_str 7; e2_ldr 8; e2_ldr 12; wp_step; e2_str 11; wp_step
  e2_str 8; wp_step; m_ldr32 5; e2_str 12; wp_steps 4; e2_ldr 25; m_ldp32 6; wp_steps 2
  e2_ldr 13; wp_step; e2_str 25; e2_ldr 26; wp_step; e2_str 13; wp_steps 3; e2_ldr 18
  m_ldp32 8; wp_step; e2_ldr 14; e2_str 18; wp_steps 3; e2_str 14; wp_step; e2_ldr 15
  wp_step; e2_str 26; wp_step; e2_str 15; wp_step; e2_ldr 16; wp_steps 2; m_str 0
  e2_str 16; e2_ldr 17; wp_steps 2; e2_ldr 19; e2_ldr 27; e2_str 17; wp_steps 2
  e2_str 19; e2_ldr 20; wp_steps 2; m_str 1
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp, by simp, by simp [hx12], by simp [hx13],
      by simp [hx19], by simp [hfp],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8a_part2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64) {msg : List (BitVec 8)} (hm : msg.length = 32)
    (e2 : Poly16) (pMsg1 pE2_1 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offAd64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (_hx9 : s.readReg64 .x9 = mbZ64 msg 9)
    (_hx10 : s.readReg64 .x10 = mbZ64 msg 8) (hx12 : s.readReg64 .x12 = 3329#64)
    (_hx13 : s.readReg64 .x13 = sp + 20480#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv5 : s.readVReg128 5#5 = mbDec msg 2) (hv6 : s.readVReg128 6#5 = mbDec msg 3)
    (hv7 : s.readVReg128 7#5 = mbCmeq msg 5) (hv16 : s.readVReg128 16#5 = mbCmeq msg 6)
    (hv17 : s.readVReg128 17#5 = mbAnd msg 7) (hv18 : s.readVReg128 18#5 = mbCmeq msg 4)
    (hv19 : s.readVReg128 19#5 = polyVecNat e2 20)
    (hv20 : s.readVReg128 20#5 = dup8x16 (mbW16 msg 8))
    (hv21 : s.readVReg128 21#5 = dup8x16 (mbW16 msg 9))
    (hv25 : s.readVReg128 25#5 = polyVecNat e2 27) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offAf00) s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg1 ∗ Poly32Mem (sp + 24448#64) pE2_1 ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x9 = mbZ64 msg 23 ∧
        s2.readReg64 .x10 = mbZ64 msg 22 ∧ s2.readReg64 .x11 = 62209#64 ∧
        s2.readReg64 .x12 = 3329#64 ∧ s2.readReg64 .x13 = sp + 22400#64 ∧
        s2.readReg64 .x19 = x19Val ∧ s2.readReg64 .fp = fpVal ∧
        s2.readVReg128 0#5 = dup8x16 1#16 ∧
        s2.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s2.readVReg128 2#5 = dup8x16 1665#16 ∧
        s2.readVReg128 4#5 = mbCmeq msg 17 ∧ s2.readVReg128 5#5 = mbAnd msg 18 ∧
        s2.readVReg128 6#5 = mbDec msg 16 ∧ s2.readVReg128 7#5 = mbDec msg 15 ∧
        s2.readVReg128 16#5 = mbCmeq msg 19 ∧ s2.readVReg128 17#5 = mbSshl msg 20 ∧
        s2.readVReg128 18#5 = mbSshl msg 21 ∧
        P2 = (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
          PolyMem (sp + 1312#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 19168#64) (((((((((((((pMsg1.set 3 (polyVecNat (msgPoly16 msg) 3)).set 4 (polyVecNat (msgPoly16 msg) 4)).set 2 (polyVecNat (msgPoly16 msg) 2)).set 6 (polyVecNat (msgPoly16 msg) 6)).set 7 (polyVecNat (msgPoly16 msg) 7)).set 5 (polyVecNat (msgPoly16 msg) 5)).set 8 (polyVecNat (msgPoly16 msg) 8)).set 9 (polyVecNat (msgPoly16 msg) 9)).set 11 (polyVecNat (msgPoly16 msg) 11)).set 10 (polyVecNat (msgPoly16 msg) 10)).set 12 (polyVecNat (msgPoly16 msg) 12)).set 13 (polyVecNat (msgPoly16 msg) 13)).set 14 (polyVecNat (msgPoly16 msg) 14)) ∗
          Poly32Mem (sp + 24448#64) ((((((((((pE2_1.set 20 (polyVecNat e2 20)).set 21 (polyVecNat e2 21)).set 22 (polyVecNat e2 22)).set 23 (polyVecNat e2 23)).set 24 (polyVecNat e2 24)).set 27 (polyVecNat e2 27)).set 28 (polyVecNat e2 28)).set 29 (polyVecNat e2 29)).set 30 (polyVecNat e2 30)).set 31 (polyVecNat e2 31)) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_step; e2_str 20; wp_step; e2_ldr 21; m_ldp32 10; e2_str 21; wp_step; e2_ldr 22; m_str 3
  wp_steps 2; e2_str 22; wp_step; e2_ldr 23; wp_step; m_str 4; e2_str 23; wp_steps 2; e2_ldr 24
  m_str 2; wp_step; m_str 6; e2_str 24; wp_steps 2; m_ldp32 12; wp_steps 2; m_str 7; wp_steps 2
  m_str 5; wp_steps 2; e2_str 27; wp_steps 2; e2_ldr 28; wp_steps 4; e2_str 28; wp_steps 2
  e2_ldr 29; wp_steps 4; e2_str 29; m_ldp32 14; wp_step; m_str 8; e2_ldr 30; wp_steps 2; m_str 9
  wp_steps 2; m_str 11; m_ldp32 16; wp_steps 2; m_str 10; wp_steps 2; e2_str 30; wp_steps 2
  e2_ldr 31; m_ldp32 18; wp_steps 2; m_str 12; wp_steps 2; m_str 13; wp_steps 2; e2_str 31
  m_ldp32 20; wp_steps 16; m_ldp32 22; wp_steps 2; m_str 14
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp, by simp, by simp, by simp [hx12],
      by simp, by simp [hx19], by simp [hfp],
      by simp [hv0], by simp [hv1], by simp [hv2],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, rfl⟩

private theorem seg8a_part3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64) {msg : List (BitVec 8)} (hm : msg.length = 32)
    (e2 : Poly16) (pMsg2 pE2_2 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offAf00) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mbZ64 msg 23)
    (hx10 : s.readReg64 .x10 = mbZ64 msg 22) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx13 : s.readReg64 .x13 = sp + 22400#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16)
    (hv1 : s.readVReg128 1#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv2 : s.readVReg128 2#5 = dup8x16 1665#16)
    (hv4 : s.readVReg128 4#5 = mbCmeq msg 17) (hv5 : s.readVReg128 5#5 = mbAnd msg 18)
    (hv6 : s.readVReg128 6#5 = mbDec msg 16) (hv7 : s.readVReg128 7#5 = mbDec msg 15)
    (hv16 : s.readVReg128 16#5 = mbCmeq msg 19) (hv17 : s.readVReg128 17#5 = mbSshl msg 20)
    (hv18 : s.readVReg128 18#5 = mbSshl msg 21) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8aEnd) s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        Poly32Mem (sp + 19168#64) pMsg2 ∗ Poly32Mem (sp + 24448#64) pE2_2 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s3.readReg64 .x10 = sp + 5680#64 ∧ s3.readReg64 .x11 = 62209#64 ∧
        s3.readReg64 .x12 = 3329#64 ∧ s3.readReg64 .x13 = sp + 22400#64 ∧
        s3.readReg64 .x19 = x19Val ∧ s3.readReg64 .fp = fpVal ∧
        s3.readVReg128 0#5 = 0#128 ∧ s3.readVReg128 2#5 = polyVecNat (msgPoly16 msg) 31 ∧
        P3 = (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
          PolyMem (sp + 1312#64) (polyVecNat e2) ∗
          Poly32Mem (sp + 19168#64) ((((((((((((((((pMsg2.set 15 (polyVecNat (msgPoly16 msg) 15)).set 16 (polyVecNat (msgPoly16 msg) 16)).set 17 (polyVecNat (msgPoly16 msg) 17)).set 19 (polyVecNat (msgPoly16 msg) 19)).set 21 (polyVecNat (msgPoly16 msg) 21)).set 20 (polyVecNat (msgPoly16 msg) 20)).set 18 (polyVecNat (msgPoly16 msg) 18)).set 22 (polyVecNat (msgPoly16 msg) 22)).set 23 (polyVecNat (msgPoly16 msg) 23)).set 24 (polyVecNat (msgPoly16 msg) 24)).set 25 (polyVecNat (msgPoly16 msg) 25)).set 26 (polyVecNat (msgPoly16 msg) 26)).set 27 (polyVecNat (msgPoly16 msg) 27)).set 28 (polyVecNat (msgPoly16 msg) 28)).set 29 (polyVecNat (msgPoly16 msg) 29)).set 30 (polyVecNat (msgPoly16 msg) 30)) ∗
          Poly32Mem (sp + 24448#64) pE2_2 ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 2; m_str 15; wp_steps 4; m_str 16; wp_steps 3; m_ldp32 24; m_str 17; wp_steps 4
  m_str 19; wp_steps 2; m_ldp32 27; m_str 21; wp_step; m_str 20; wp_steps 3; m_ldr32 31
  m_str 18; wp_steps 4; m_ldr32 26; wp_steps 6; m_ldp32 29; wp_steps 20; m_str 22; m_str 23
  wp_steps 6; m_str 24; wp_steps 2; m_str 25; wp_steps 4; m_str 26; wp_step; m_str 27
  wp_steps 3; m_str 28; m_str 29; m_str 30
  have hv2_eq : neonDecompress1Byte ((msg.getD 31 0#8).zeroExtend 16) = polyVecNat (msgPoly16 msg) 31 :=
    neonDecompress1Byte_eq hm 31 (by decide) _ (by clear * -; bv_omega)
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [ro00Sym], by simp,
      by simp [hx11], by simp [hx12], by simp [hx13], by simp [hx19], by simp [hfp],
      by wp_norm_lhs, by rw [← hv2_eq]; simp [wp_norm, arm64_norm, *],
      rfl⟩

private theorem seg8a_zero1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64)
    (v2Val : BitVec 128) (pMsg d0 : Vec32) (sp0 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8aEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 5680#64) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx13 : s.readReg64 .x13 = sp + 22400#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = 0#128) (hv2 : s.readVReg128 2#5 = v2Val) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offB0f4) s
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) d0 ∗
        Spill21Mem (sp + 1920#64) sp0 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 5680#64 ∧ s'.readReg64 .x11 = 62209#64 ∧
        s'.readReg64 .x12 = 3329#64 ∧ s'.readReg64 .x13 = sp + 22400#64 ∧
        s'.readReg64 .x19 = x19Val ∧ s'.readReg64 .fp = fpVal ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = 0#128 ∧ s'.readVReg128 2#5 = v2Val ∧
        P' = (Poly32Mem (sp + 19168#64) pMsg ∗
          Poly32Mem (sp + 20704#64) ((((((((((((((d0.set 0 0#128).set 1 0#128).set 2 0#128).set 3 0#128).set 4 0#128).set 5 0#128).set 6 0#128).set 7 0#128).set 8 0#128).set 9 0#128).set 10 0#128).set 11 0#128).set 12 0#128).set 31 0#128) ∗
          Spill21Mem (sp + 1920#64) ((((((((((((sp0.set 20 0#128).set 19 0#128).set 18 0#128).set 17 0#128).set 16 0#128).set 15 0#128).set 14 0#128).set 13 0#128).set 12 0#128).set 11 0#128).set 10 0#128).set 9 0#128) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  cases d0; cases sp0
  p_str 0; p_ldr 0; p_str 1; p_str 2; sp21_str 20; p_ldr 1; p_str 3; sp21_str 19
  p_ldr 2; p_str 4; sp21_str 18; p_ldr 3; p_str 5; sp21_str 17; p_ldr 4; p_str 6
  sp21_str 16; p_ldr 5; p_str 7; sp21_str 15; p_ldr 6; p_str 8; sp21_str 14; p_ldr 7
  p_str 9; sp21_str 13; p_ldr 8; p_str 10; sp21_str 12; p_ldr 9; p_str 11; sp21_str 11
  p_ldr 10; p_str 12; sp21_str 10; p_ldr 11; p_str 31; sp21_str 9; p_ldr 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx13], by simp [hx19], by simp [hfp],
      by simp [hv0], by wp_norm_lhs, by simp [hv2], rfl⟩

private theorem seg8a_zero2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64)
    (v2Val : BitVec 128) (pMsg d1 : Vec32) (sp1 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + offB0f4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 5680#64) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx13 : s.readReg64 .x13 = sp + 22400#64)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal)
    (hv0 : s.readVReg128 0#5 = 0#128) (hv1 : s.readVReg128 1#5 = 0#128)
    (hv2 : s.readVReg128 2#5 = v2Val) (hd31 : d1.get 31 = 0#128) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8Dot) s
      (Poly32Mem (sp + 19168#64) pMsg ∗ Poly32Mem (sp + 20704#64) d1 ∗
        Spill21Mem (sp + 1920#64) sp1 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 5680#64 ∧ s'.readReg64 .x11 = 62209#64 ∧
        s'.readReg64 .x12 = 3329#64 ∧ s'.readReg64 .x13 = sp + 22400#64 ∧
        s'.readReg64 .x19 = x19Val ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 s' ∧
        P' = (Poly32Mem (sp + 19168#64) (pMsg.set 31 v2Val) ∗
          Poly32Mem (sp + 20704#64) ((((((((((((((((((d1.set 30 0#128).set 29 0#128).set 28 0#128).set 25 0#128).set 24 0#128).set 21 0#128).set 20 0#128).set 17 0#128).set 16 0#128).set 13 0#128).set 15 0#128).set 14 0#128).set 19 0#128).set 18 0#128).set 23 0#128).set 22 0#128).set 27 0#128).set 26 0#128) ∗
          Spill21Mem (sp + 1920#64) (sp1.set 8 0#128) ∗ Rest)) := by
  have hbase : blkPl04.base = b := _hb.symm; subst hbase
  cases d1; cases sp1
  p_str 30; p_str 29; p_ldr 30; p_str 28; p_ldr 29; p_str 25; p_ldr 28; p_str 24
  p_ldr 25; p_str 21; p_ldr 24; p_str 20; p_ldr 21; p_str 17; p_ldr 20; p_str 16
  p_ldr 17; p_str 13; p_ldr 16; p_str 15; p_ldr 13; p_str 14; p_ldr 15; p_str 19
  p_ldr 14; p_str 18; p_ldr 19; p_str 23; p_ldr 18; p_str 22; p_ldr 23; p_str 27
  p_ldr 22; p_str 26; p_ldr 27; sp21_str 8; p_ldr 26
  refine step_ldrQ_dot 31 (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) hd31 (by wp_norm_lhs) ?_
  m_str_z 31 hv2
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx13], by simp [hx19], by simp [hfp],
      (accRegs_zero_iff _).mpr ⟨by simp [hv0], by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs⟩, rfl⟩

/-- Segment 8a (`+0xabd8 → +0xb190`): copies `e₂` to `sp + 24448`, decompresses `m'` into
    `PolyMem (sp + 19168)` (`msgPoly16 m'`), and initializes `DotLoops3` registers and zero
    accumulators (`AccRegs polyZero16`, `Poly32Mem (sp + 20704) Vec32.zero`, `AccSpill21`). -/
theorem seg8a_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp x19Val fpVal : BitVec 64) {msg : List (BitVec 8)} (hm : msg.length = 32)
    (e2 old19168 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = x19Val) (hfp : s.readReg64 .fp = fpVal) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8Dot) s
      (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
        PolyMem (sp + 1312#64) (polyVecNat e2) ∗
        memRegion (sp + 1920#64) 336 ∗
        PolyMem (sp + 19168#64) (polyVecNat old19168) ∗
        memRegion (sp + 20704#64) 512 ∗
        memRegion (sp + 24448#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 5680#64 ∧ s'.readReg64 .x11 = 62209#64 ∧
        s'.readReg64 .x12 = 3329#64 ∧ s'.readReg64 .x13 = sp + 22400#64 ∧
        s'.readReg64 .x19 = x19Val ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs polyZero16 s' ∧
        ∃ t0 : Spill21,
          P' = (WordRangeMem 32 (sp + 8#64) (msgWordFn msg) ∗
            PolyMem (sp + 1312#64) (polyVecNat e2) ∗
            Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗
            PolyMem (sp + 19168#64) (polyVecNat (msgPoly16 msg)) ∗
            Poly32Mem (sp + 20704#64) Vec32.zero ∗
            PolyMem (sp + 24448#64) (polyVecNat e2) ∗ Rest)) := by
  have hchk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_spill21 (a := sp + 1920#64)); intro t0
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 20704#64)); intro vDot
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 24448#64)); intro vE2
  rw [show PolyMem (sp + 19168#64) (polyVecNat old19168) =
    Poly32Mem (sp + 19168#64) (Vec32.ofFn (polyVecNat old19168)) from (poly32Mem_ofFn _ _).symm]
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {st : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl st.mem → MlKemRoOk mlkemMpl st.mem →
      SepWP prog pc1 st P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 st P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  refine stepf hcl hro
    (seg8a_pre hb s sp x19Val fpVal msg e2 (Vec32.ofFn (polyVecNat old19168)) vE2 _
      hpc hrun hsp hspA hx19 hfp) (by sep_frame) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0 ⟨hsp0, hspA0, hx8_0, hx9_0, hx12_0, hx13_0, hx19_0, hfp0,
    hv0_0, hv2_0, hv3_0, hv4_0, hv5_0, rfl⟩
  refine stepf hcl0 hro0
    (seg8a_part1 hb s0 sp x19Val fpVal hm e2 _ _ _
      hpc0 hrun0 hsp0 hspA0 hro0 hx8_0 hx9_0 hx12_0 hx13_0 hx19_0 hfp0
      hv0_0 hv2_0 hv3_0 hv4_0 hv5_0) (by sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx12_1, hx13_1,
    hx19_1, hfp1, hv0_1, hv1_1, hv2_1, hv5_1, hv6_1, hv7_1, hv16_1, hv17_1, hv18_1,
    hv19_1, hv20_1, hv21_1, hv25_1, rfl⟩
  refine stepf hcl1 hro1
    (seg8a_part2 hb s1 sp x19Val fpVal hm e2 _ _ _
      hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx12_1 hx13_1 hx19_1 hfp1
      hv0_1 hv1_1 hv2_1 hv5_1 hv6_1 hv7_1 hv16_1 hv17_1 hv18_1 hv19_1 hv20_1 hv21_1 hv25_1)
    (by sep_frame) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2,
    hx19_2, hfp2, hv0_2, hv1_2, hv2_2, hv4_2, hv5_2, hv6_2, hv7_2, hv16_2, hv17_2, hv18_2, rfl⟩
  refine stepf hcl2 hro2
    (seg8a_part3 hb s2 sp x19Val fpVal hm e2 _ _ _
      hpc2 hrun2 hsp2 hspA2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx19_2 hfp2
      hv0_2 hv1_2 hv2_2 hv4_2 hv5_2 hv6_2 hv7_2 hv16_2 hv17_2 hv18_2) (by sep_frame) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, _, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3,
    hx19_3, hfp3, hv0_3, hv2_3, rfl⟩
  refine stepf hcl3 hro3
    (seg8a_zero1 hb s3 sp x19Val fpVal _ _ vDot t0 _
      hpc3 hrun3 hsp3 hchk hx8_3 hx9_3 hx10_3 hx11_3 hx12_3 hx13_3 hx19_3 hfp3 hv0_3 hv2_3)
    (by sep_frame) ?_
  rintro s4 P4 hpc4 hrun4 _ _ ⟨hsp4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4, hx13_4,
    hx19_4, hfp4, hv0_4, hv1_4, hv2_4, rfl⟩
  refine SepWP.mono
    (seg8a_zero2 hb s4 sp x19Val fpVal _ _ _ _ _
      hpc4 hrun4 hsp4 hchk hx8_4 hx9_4 hx10_4 hx11_4 hx12_4 hx13_4 hx19_4 hfp4
      hv0_4 hv1_4 hv2_4 rfl) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx19', hfp', hacc', rfl⟩
  refine ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx19', hfp', hacc', t0, ?_⟩
  have hm_all : ∀ vOld : Vec32, (((((((((((((((((((((((((((((((vOld.set 0 (polyVecNat (msgPoly16 msg) 0)).set 1 (polyVecNat (msgPoly16 msg) 1)).set 3 (polyVecNat (msgPoly16 msg) 3)).set 4 (polyVecNat (msgPoly16 msg) 4)).set 2 (polyVecNat (msgPoly16 msg) 2)).set 6 (polyVecNat (msgPoly16 msg) 6)).set 7 (polyVecNat (msgPoly16 msg) 7)).set 5 (polyVecNat (msgPoly16 msg) 5)).set 8 (polyVecNat (msgPoly16 msg) 8)).set 9 (polyVecNat (msgPoly16 msg) 9)).set 11 (polyVecNat (msgPoly16 msg) 11)).set 10 (polyVecNat (msgPoly16 msg) 10)).set 12 (polyVecNat (msgPoly16 msg) 12)).set 13 (polyVecNat (msgPoly16 msg) 13)).set 14 (polyVecNat (msgPoly16 msg) 14)).set 15 (polyVecNat (msgPoly16 msg) 15)).set 16 (polyVecNat (msgPoly16 msg) 16)).set 17 (polyVecNat (msgPoly16 msg) 17)).set 19 (polyVecNat (msgPoly16 msg) 19)).set 21 (polyVecNat (msgPoly16 msg) 21)).set 20 (polyVecNat (msgPoly16 msg) 20)).set 18 (polyVecNat (msgPoly16 msg) 18)).set 22 (polyVecNat (msgPoly16 msg) 22)).set 23 (polyVecNat (msgPoly16 msg) 23)).set 24 (polyVecNat (msgPoly16 msg) 24)).set 25 (polyVecNat (msgPoly16 msg) 25)).set 26 (polyVecNat (msgPoly16 msg) 26)).set 27 (polyVecNat (msgPoly16 msg) 27)).set 28 (polyVecNat (msgPoly16 msg) 28)).set 29 (polyVecNat (msgPoly16 msg) 29)).set 30 (polyVecNat (msgPoly16 msg) 30)).set 31 (polyVecNat (msgPoly16 msg) 31) =
      Vec32.ofFn (polyVecNat (msgPoly16 msg)) := fun vOld => by cases vOld; rfl
  have hm_eq := hm_all (Vec32.ofFn (polyVecNat old19168))
  have he2_eq : (((((((((((((((((((((((((((((((vE2.set 0 (polyVecNat e2 0)).set 4 (polyVecNat e2 4)).set 1 (polyVecNat e2 1)).set 2 (polyVecNat e2 2)).set 3 (polyVecNat e2 3)).set 5 (polyVecNat e2 5)).set 6 (polyVecNat e2 6)).set 9 (polyVecNat e2 9)).set 10 (polyVecNat e2 10)).set 7 (polyVecNat e2 7)).set 11 (polyVecNat e2 11)).set 8 (polyVecNat e2 8)).set 12 (polyVecNat e2 12)).set 25 (polyVecNat e2 25)).set 13 (polyVecNat e2 13)).set 18 (polyVecNat e2 18)).set 14 (polyVecNat e2 14)).set 26 (polyVecNat e2 26)).set 15 (polyVecNat e2 15)).set 16 (polyVecNat e2 16)).set 17 (polyVecNat e2 17)).set 19 (polyVecNat e2 19)).set 20 (polyVecNat e2 20)).set 21 (polyVecNat e2 21)).set 22 (polyVecNat e2 22)).set 23 (polyVecNat e2 23)).set 24 (polyVecNat e2 24)).set 27 (polyVecNat e2 27)).set 28 (polyVecNat e2 28)).set 29 (polyVecNat e2 29)).set 30 (polyVecNat e2 30)).set 31 (polyVecNat e2 31) =
      Vec32.ofFn (polyVecNat e2) := by cases vE2; rfl
  have hd_eq : (((((((((((((((((((((((((((((((vDot.set 0 0#128).set 1 0#128).set 2 0#128).set 3 0#128).set 4 0#128).set 5 0#128).set 6 0#128).set 7 0#128).set 8 0#128).set 9 0#128).set 10 0#128).set 11 0#128).set 12 0#128).set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 25 0#128).set 24 0#128).set 21 0#128).set 20 0#128).set 17 0#128).set 16 0#128).set 13 0#128).set 15 0#128).set 14 0#128).set 19 0#128).set 18 0#128).set 23 0#128).set 22 0#128).set 27 0#128).set 26 0#128 =
      Vec32.zero := by cases vDot; rfl
  have hsp21_eq : ((((((((((((t0.set 20 0#128).set 19 0#128).set 18 0#128).set 17 0#128).set 16 0#128).set 15 0#128).set 14 0#128).set 13 0#128).set 12 0#128).set 11 0#128).set 10 0#128).set 9 0#128).set 8 0#128 =
      AccSpill21 t0 polyZero16 := by cases t0; simp [AccSpill21, Spill21.set]
  rw [hm_eq, he2_eq, hd_eq, hsp21_eq, poly32Mem_ofFn, poly32Mem_ofFn]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8a
