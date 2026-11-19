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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `encapsulate2` (`B20`) — Segment 2b1 (`+0x0710 .. +0x0ab8`)

Steps the unrolled AdvSIMD `decompress_1(m)` pipeline reading `(sp + 2256#64) ↦ₛ msg`,
storing vector slots `0..27, 30, 31` into `Poly32Mem (sp + 2416#64)` with slots `28, 29`
held in `v4, v3`, and loading `Seg3` entry GPRs (`x8..x12`) and `v0 = 0#128`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b1

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_6_vec mlkemData08Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdCmeqZero8h simdSshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  UnspilledSaved20 blk20_code_eq blk20_tree_size blkLib20 blkPC20 blkPl20
  blkPlaceable20 blkTree20 sepWP_seq_env step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem SepStore128 Vec32 polyVecNat step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  msgPoly16 neonDecompress1Byte neonDecompress1Byte_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdCmeqZero_8h exec_simdDup_8h exec_simdSshl_8h)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0710 → 0x0ab4]
gen_placed_odd_sites blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0718 → 0x0718]

@[simp, arm64_norm]
private theorem blkPC20_rebase_fetchOff_71c [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC20.rebase b X).fetch (b + BitVec.ofNat 64 1820) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 2)
        (.Offset (.gpr (BitVec.ofNat 5 11))
          (lo12Of (blkPl20.ρ "libcrux_ml_kem:.rodata.cst16.6")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib20) (prog := blkPC20) (pl := blkPl20)
    (b := b) (X := X) (off := 1820)
    (r := { off := 1820, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" })
    rfl blkPlaceable20 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 1820)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 455) blk20_code_eq blk20_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl20_ρ [MlKemPlacement] (sym : String) :
    blkPl20.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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
  blkPC20 dup8x16 polyVecNat simdSshl8h simdCmeqZero8h neonDecompress1Byte

attribute [local wp_norm ↓ high]
  exec_simdMovi_8h_1 exec_simdMovi_2d_0 exec_simdAnd_16b exec_simdBic_16b
  exec_simdDup_8h exec_simdSshl_8h exec_simdCmeqZero_8h
  zext32_trunc32_zext64_8 trunc16_zext64_8 trunc16_1665 bic_1665_cmeq_eq

private abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"
private abbrev mbZ64 (msg : List (BitVec 8)) (j : Nat) : BitVec 64 := (msg.getD j 0#8).zeroExtend 64
private abbrev mbW16 (msg : List (BitVec 8)) (j : Nat) : BitVec 16 := (msg.getD j 0#8).zeroExtend 16
private abbrev mbSshl (msg : List (BitVec 8)) (j : Nat) : BitVec 128 :=
  simdSshl8h (dup8x16 (mbW16 msg j)) 0xfff9fffafffbfffcfffdfffe00ff0000#128
private abbrev mbAnd (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := mbSshl msg j &&& dup8x16 1#16
private abbrev mbCmeq (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := simdCmeqZero8h (mbAnd msg j)
private abbrev mbDec (msg : List (BitVec 8)) (j : Nat) : BitVec 128 := neonDecompress1Byte (mbW16 msg j)

private theorem step_ldrb_msg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {imm : BitVec 64} (j : Nat)
    (hmsg : msg.length = 32) (hchk : (sp &&& 15#64 == 0#64) = true) (hj : j < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2256#64 + BitVec.ofNat 64 j = imm := by decide)
    (hexec : (s.writeReg .W32 rt ((msg.getD j 0#8).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' (((sp + 2256#64) ↦ₛ msg) ∗ Rest) post) :
    SepWP prog target_pc s (((sp + 2256#64) ↦ₛ msg) ∗ Rest) post := by
  have ha : (sp + 2256#64) + BitVec.ofNat 64 j = s.sp + imm := by rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact SepWP.step_ldr8 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) (SepLoad8.of_pointsToBytes rfl (by omega) ha) hexec hnext

private theorem step_strQ_msg {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {msg : List (BitVec 8)} {pMsg pMsg' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hmsg : msg.length = 32) (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2416#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = neonDecompress1Byte ((msg.getD k 0#8).zeroExtend 16))
    (hp : pMsg.set k (polyVecNat (msgPoly16 msg) k) = pMsg')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) pMsg' ∗ Rest) post) :
    SepWP prog target_pc s
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) pMsg ∗ Rest) post := by
  have ha : (sp + 2416#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  have hv : s.readVReg128 vt = polyVecNat (msgPoly16 msg) k := by
    rw [hval]; exact neonDecompress1Byte_eq hmsg k hk _ (by bv_omega)
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) hv
    (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hp))) hexec hnext

local macro "step_msg_ldrb " j:num : tactic => `(tactic|
  refine step_ldrb_msg $j (by assumption) (by assumption) (by decide) (by wp_norm_lhs)
    (by simp [*]) (by wp_norm_lhs) (by simp [*]) (by decide) (by wp_norm_lhs) ?_)

local macro "step_msg_strQ " k:num : tactic => `(tactic| (
  refine step_strQ_msg $k (by assumption) (by assumption) (by decide) (by wp_norm_lhs)
    (by simp [*]) (by wp_norm_lhs) (by simp [*]) (by decide)
    (by first | wp_norm_lhs | simp [wp_norm, arm64_norm, *]) rfl (by wp_norm_lhs) ?_
  intro _))

private theorem seg2b1_part1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) {msg : List (BitVec 8)} (hmsg : msg.length = 32)
    (p0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0710#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3952#64)
    (hx21 : s.readReg64 .x21 = sp + 5488#64) (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0858#64) s
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) p0 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = mbZ64 msg 12 ∧ s'.readReg64 .x10 = mbZ64 msg 13 ∧
        s'.readReg64 .x11 = mbZ64 msg 16 ∧ s'.readReg64 .x12 = mbZ64 msg 17 ∧
        s'.readReg64 .x19 = ret ∧ s'.readReg64 .x20 = sp + 3952#64 ∧
        s'.readReg64 .x21 = sp + 5488#64 ∧
        s'.readVReg128 0#5 = dup8x16 1#16 ∧ s'.readVReg128 1#5 = dup8x16 1665#16 ∧
        s'.readVReg128 2#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s'.readVReg128 3#5 = mbCmeq msg 8 ∧ s'.readVReg128 4#5 = mbCmeq msg 11 ∧
        s'.readVReg128 5#5 = mbDec msg 10 ∧ s'.readVReg128 16#5 = mbCmeq msg 5 ∧
        s'.readVReg128 17#5 = mbCmeq msg 6 ∧ s'.readVReg128 19#5 = mbAnd msg 9 ∧
        UnspilledSaved20 s0 s' ∧
        P' = (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) ((((((p0.set 0 (polyVecNat (msgPoly16 msg) 0)).set 1 (polyVecNat (msgPoly16 msg) 1)).set 2 (polyVecNat (msgPoly16 msg) 2)).set 3 (polyVecNat (msgPoly16 msg) 3)).set 7 (polyVecNat (msgPoly16 msg) 7)).set 4 (polyVecNat (msgPoly16 msg) 4)) ∗ Rest)) := by
  step_msg_ldrb 0; step_msg_ldrb 1; wp_step
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (roAddr := mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.6") (by simp [evalAddrMode, pageOf_add_lo12Of]) (by simpa using hro.cst16_6) mlkemData08Bytes_length cst16_6_vec (by wp_norm_lhs) ?_
  step_msg_ldrb 3; wp_steps 3; step_msg_ldrb 2; wp_steps 2; step_msg_ldrb 7; wp_step
  step_msg_ldrb 4; wp_steps 3; step_msg_ldrb 5; wp_step; step_msg_ldrb 6; wp_steps 3
  step_msg_ldrb 8; wp_steps 4; step_msg_ldrb 9; wp_steps 2; step_msg_ldrb 10; wp_steps 9
  step_msg_ldrb 11; wp_steps 5; step_msg_ldrb 13; wp_steps 2; step_msg_ldrb 12
  step_msg_strQ 0; wp_steps 2; step_msg_strQ 1; wp_steps 3; step_msg_strQ 2; wp_step
  step_msg_strQ 3; wp_steps 4; step_msg_ldrb 16; wp_steps 2; step_msg_ldrb 17; wp_steps 9
  step_msg_strQ 7; wp_steps 2; step_msg_strQ 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by simp [hx19], by simp [hx20], by simp [hx21],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem seg2b1_part2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) {msg : List (BitVec 8)} (hmsg : msg.length = 32)
    (p1 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0858#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = mbZ64 msg 12) (hx10 : s.readReg64 .x10 = mbZ64 msg 13)
    (hx11 : s.readReg64 .x11 = mbZ64 msg 16) (hx12 : s.readReg64 .x12 = mbZ64 msg 17)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3952#64)
    (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16) (hv1 : s.readVReg128 1#5 = dup8x16 1665#16)
    (hv2 : s.readVReg128 2#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv3 : s.readVReg128 3#5 = mbCmeq msg 8) (hv4 : s.readVReg128 4#5 = mbCmeq msg 11)
    (hv5 : s.readVReg128 5#5 = mbDec msg 10) (hv16 : s.readVReg128 16#5 = mbCmeq msg 5)
    (hv17 : s.readVReg128 17#5 = mbCmeq msg 6) (hv19 : s.readVReg128 19#5 = mbAnd msg 9)
    (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0988#64) s
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) p1 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = mbZ64 msg 23 ∧ s'.readReg64 .x10 = mbZ64 msg 24 ∧
        s'.readReg64 .x11 = mbZ64 msg 25 ∧ s'.readReg64 .x12 = mbZ64 msg 28 ∧
        s'.readReg64 .x19 = ret ∧ s'.readReg64 .x20 = sp + 3952#64 ∧
        s'.readReg64 .x21 = sp + 5488#64 ∧
        s'.readVReg128 0#5 = dup8x16 1#16 ∧ s'.readVReg128 1#5 = dup8x16 1665#16 ∧
        s'.readVReg128 2#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128 ∧
        s'.readVReg128 3#5 = mbDec msg 18 ∧ s'.readVReg128 4#5 = mbDec msg 20 ∧
        s'.readVReg128 5#5 = mbCmeq msg 21 ∧ s'.readVReg128 16#5 = mbCmeq msg 17 ∧
        s'.readVReg128 18#5 = mbCmeq msg 19 ∧ s'.readVReg128 19#5 = dup8x16 (mbW16 msg 22) ∧
        UnspilledSaved20 s0 s' ∧
        P' = (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) (((((((((((p1.set 10 (polyVecNat (msgPoly16 msg) 10)).set 8 (polyVecNat (msgPoly16 msg) 8)).set 5 (polyVecNat (msgPoly16 msg) 5)).set 11 (polyVecNat (msgPoly16 msg) 11)).set 6 (polyVecNat (msgPoly16 msg) 6)).set 9 (polyVecNat (msgPoly16 msg) 9)).set 13 (polyVecNat (msgPoly16 msg) 13)).set 12 (polyVecNat (msgPoly16 msg) 12)).set 14 (polyVecNat (msgPoly16 msg) 14)).set 15 (polyVecNat (msgPoly16 msg) 15)).set 16 (polyVecNat (msgPoly16 msg) 16)) ∗ Rest)) := by
  wp_steps 2; step_msg_ldrb 15; wp_steps 2; step_msg_ldrb 14; wp_steps 2; step_msg_strQ 10
  wp_steps 2; step_msg_ldrb 18; step_msg_strQ 8; wp_step; step_msg_strQ 5; wp_steps 2
  step_msg_strQ 11; wp_steps 3; step_msg_strQ 6; wp_steps 2; step_msg_ldrb 20; wp_steps 3
  step_msg_ldrb 19; wp_steps 3; step_msg_strQ 9; wp_step; step_msg_ldrb 21; wp_steps 5
  step_msg_ldrb 22; wp_steps 2; step_msg_ldrb 24; step_msg_strQ 13; wp_steps 3
  step_msg_strQ 12; wp_steps 3; step_msg_ldrb 25; wp_steps 2; step_msg_ldrb 28; wp_steps 9
  step_msg_ldrb 23; wp_steps 2; step_msg_strQ 14; wp_steps 2; step_msg_strQ 15; wp_steps 2
  step_msg_strQ 16; wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [hx8], by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hv0], by simp [hv1], by simp [hv2],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem seg2b1_part3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) {msg : List (BitVec 8)} (hmsg : msg.length = 32)
    (p2 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0988#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = mbZ64 msg 23) (hx10 : s.readReg64 .x10 = mbZ64 msg 24)
    (hx11 : s.readReg64 .x11 = mbZ64 msg 25) (hx12 : s.readReg64 .x12 = mbZ64 msg 28)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3952#64)
    (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1#16) (hv1 : s.readVReg128 1#5 = dup8x16 1665#16)
    (hv2 : s.readVReg128 2#5 = 0xfff9fffafffbfffcfffdfffe00ff0000#128)
    (hv3 : s.readVReg128 3#5 = mbDec msg 18) (hv4 : s.readVReg128 4#5 = mbDec msg 20)
    (hv5 : s.readVReg128 5#5 = mbCmeq msg 21) (hv16 : s.readVReg128 16#5 = mbCmeq msg 17)
    (hv18 : s.readVReg128 18#5 = mbCmeq msg 19) (hv19 : s.readVReg128 19#5 = dup8x16 (mbW16 msg 22))
    (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0ab8#64) s
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) p2 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 208#64 ∧
        s'.readReg64 .x11 = 62209#64 ∧ s'.readReg64 .x12 = 3329#64 ∧
        s'.readReg64 .x19 = ret ∧ s'.readReg64 .x20 = sp + 3952#64 ∧
        s'.readReg64 .x21 = sp + 5488#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 3#5 = polyVecNat (msgPoly16 msg) 29 ∧
        s'.readVReg128 4#5 = polyVecNat (msgPoly16 msg) 28 ∧
        UnspilledSaved20 s0 s' ∧
        P' = (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) (((((((((((((p2.set 18 (polyVecNat (msgPoly16 msg) 18)).set 20 (polyVecNat (msgPoly16 msg) 20)).set 19 (polyVecNat (msgPoly16 msg) 19)).set 17 (polyVecNat (msgPoly16 msg) 17)).set 21 (polyVecNat (msgPoly16 msg) 21)).set 23 (polyVecNat (msgPoly16 msg) 23)).set 22 (polyVecNat (msgPoly16 msg) 22)).set 24 (polyVecNat (msgPoly16 msg) 24)).set 26 (polyVecNat (msgPoly16 msg) 26)).set 25 (polyVecNat (msgPoly16 msg) 25)).set 27 (polyVecNat (msgPoly16 msg) 27)).set 30 (polyVecNat (msgPoly16 msg) 30)).set 31 (polyVecNat (msgPoly16 msg) 31)) ∗ Rest)) := by
  wp_step; step_msg_strQ 18; wp_steps 2; step_msg_ldrb 26; wp_steps 2; step_msg_strQ 20
  wp_step; step_msg_ldrb 27; step_msg_strQ 19; wp_steps 2; step_msg_strQ 17; wp_step
  step_msg_ldrb 30; step_msg_strQ 21; wp_step; step_msg_ldrb 29; wp_step; step_msg_ldrb 31
  wp_steps 34; step_msg_strQ 23; wp_steps 5; step_msg_strQ 22; wp_steps 2; step_msg_strQ 24
  wp_steps 2; step_msg_strQ 26; wp_steps 2; step_msg_strQ 25; wp_steps 2; step_msg_strQ 27
  step_msg_strQ 30; step_msg_strQ 31
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk, by simp [hx8],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by simp [hx19], by simp [hx20], by simp [hx21], by wp_norm_lhs,
      by trans mbDec msg 29
         · wp_norm_lhs
         · exact neonDecompress1Byte_eq hmsg 29 (by decide) _ (by bv_omega),
      by trans mbDec msg 28
         · wp_norm_lhs
         · exact neonDecompress1Byte_eq hmsg 28 (by decide) _ (by bv_omega),
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

@[expose] def msgVec32Pre (msg : List (BitVec 8)) (p0 : Vec32) : Vec32 :=
  { Vec32.ofFn (polyVecNat (msgPoly16 msg)) with v28 := p0.v28, v29 := p0.v29 }

@[expose] def Seg2b1Post [MlKemPlacement] (s0 s : State) (ret : BitVec 64)
    (msg : List (BitVec 8)) : Prop :=
  let sp := s0.sp - 6128#64
  s.sp = sp ∧ s.spAligned = true ∧
  s.readReg64 .x8 = 0#64 ∧
  s.readReg64 .x9 =
    mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0" + 134#64 ∧
  s.readReg64 .x10 = sp + 208#64 ∧
  s.readReg64 .x11 = 62209#64 ∧ s.readReg64 .x12 = 3329#64 ∧
  s.readReg64 .x19 = ret ∧ s.readReg64 .x20 = sp + 3952#64 ∧
  s.readReg64 .x21 = sp + 5488#64 ∧
  s.readVReg128 0#5 = 0#128 ∧
  s.readVReg128 3#5 = polyVecNat (msgPoly16 msg) 29 ∧
  s.readVReg128 4#5 = polyVecNat (msgPoly16 msg) 28 ∧
  UnspilledSaved20 s0 s

theorem seg2b1_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s : State) (ret : BitVec 64) {msg : List (BitVec 8)} (hmsg : msg.length = 32)
    (p0 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0710#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 6128#64) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = (s0.sp - 6128#64) + 3952#64)
    (hx21 : s.readReg64 .x21 = (s0.sp - 6128#64) + 5488#64) (hus : UnspilledSaved20 s0 s) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0ab8#64) s
      (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) p0 ∗ Rest)
      (fun s' P' =>
        Seg2b1Post s0 s' ret msg ∧
        P' = (((sp + 2256#64) ↦ₛ msg) ∗ Poly32Mem (sp + 2416#64) (msgVec32Pre msg p0) ∗ Rest)) := by
  let sp := s0.sp - 6128#64
  have hchk : (sp &&& 15#64 == 0#64) = true := by dsimp [sp]; rw [← hsp]; exact hspA
  refine sepWP_seq_env hcl hro
    (seg2b1_part1 hb s0 s sp ret hmsg p0 Rest hpc hrun hsp hchk hro hx19 hx20 hx21 hus) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1,
     hv0_1, hv1_1, hv2_1, hv3_1, hv4_1, hv5_1, hv16_1, hv17_1, hv19_1, hus1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg2b1_part2 hb s0 s1 sp ret hmsg _ Rest hpc1 hrun1 hsp1 hchk hx8_1 hx9_1 hx10_1 hx11_1 hx12_1
      hx19_1 hx20_1 hx21_1 hv0_1 hv1_1 hv2_1 hv3_1 hv4_1 hv5_1 hv16_1 hv17_1 hv19_1 hus1) ?_
  rintro s2 P2 hpc2 hrun2 _ _
    ⟨hsp2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2,
     hv0_2, hv1_2, hv2_2, hv3_2, hv4_2, hv5_2, hv16_2, hv18_2, hv19_2, hus2, rfl⟩
  refine SepWP.mono
    (seg2b1_part3 hb s0 s2 sp ret hmsg _ Rest hpc2 hrun2 hsp2 hchk hx8_2 hx9_2 hx10_2 hx11_2 hx12_2
      hx19_2 hx20_2 hx21_2 hv0_2 hv1_2 hv2_2 hv3_2 hv4_2 hv5_2 hv16_2 hv18_2 hv19_2 hus2) ?_
  rintro s3 P3 _ _ ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hx21_3,
    hv0_3, hv3_3, hv4_3, hus3, rfl⟩
  have hp : ((((((((((((((((((((((((((((((p0.set 0 (polyVecNat (msgPoly16 msg) 0)).set 1 (polyVecNat (msgPoly16 msg) 1)).set 2 (polyVecNat (msgPoly16 msg) 2)).set 3 (polyVecNat (msgPoly16 msg) 3)).set 7 (polyVecNat (msgPoly16 msg) 7)).set 4 (polyVecNat (msgPoly16 msg) 4)).set 10 (polyVecNat (msgPoly16 msg) 10)).set 8 (polyVecNat (msgPoly16 msg) 8)).set 5 (polyVecNat (msgPoly16 msg) 5)).set 11 (polyVecNat (msgPoly16 msg) 11)).set 6 (polyVecNat (msgPoly16 msg) 6)).set 9 (polyVecNat (msgPoly16 msg) 9)).set 13 (polyVecNat (msgPoly16 msg) 13)).set 12 (polyVecNat (msgPoly16 msg) 12)).set 14 (polyVecNat (msgPoly16 msg) 14)).set 15 (polyVecNat (msgPoly16 msg) 15)).set 16 (polyVecNat (msgPoly16 msg) 16)).set 18 (polyVecNat (msgPoly16 msg) 18)).set 20 (polyVecNat (msgPoly16 msg) 20)).set 19 (polyVecNat (msgPoly16 msg) 19)).set 17 (polyVecNat (msgPoly16 msg) 17)).set 21 (polyVecNat (msgPoly16 msg) 21)).set 23 (polyVecNat (msgPoly16 msg) 23)).set 22 (polyVecNat (msgPoly16 msg) 22)).set 24 (polyVecNat (msgPoly16 msg) 24)).set 26 (polyVecNat (msgPoly16 msg) 26)).set 25 (polyVecNat (msgPoly16 msg) 25)).set 27 (polyVecNat (msgPoly16 msg) 27)).set 30 (polyVecNat (msgPoly16 msg) 30)).set 31 (polyVecNat (msgPoly16 msg) 31)) = msgVec32Pre msg p0 := by
    cases p0; rfl
  exact ⟨⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hx21_3,
    hv0_3, hv3_3, hv4_3, hus3⟩, by rw [hp]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b1
