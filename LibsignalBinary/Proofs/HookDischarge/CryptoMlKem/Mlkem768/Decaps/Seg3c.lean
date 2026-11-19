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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 3c (`+0x3948 → +0x39f4`)

Proves the 16-iteration `compress_1 + serialize_1` loop (`+0x3948 → +0x39f4`) writing
`compressAndEncode 1 (polySub vSpec invSpec)` (`32` B) to `sp + 20704`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData06Bytes mlkemData07Bytes mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement fetch_rebase_ldst128Lo12_site mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk cst16_4_vec cst16_5_vec mlkemData06Bytes_length mlkemData07Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 compressAndEncode neonMontgomeryMul16 polySub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 getSimdLane_16_eq lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdSub8h simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress1PreShift8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (simdAddv8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow (neonSerialize1MsbHalf)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (step_ldrQ128_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  applySimdResult_ok exec_simdUshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdSub_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_fmov_w_s exec_simdAnd_16b exec_simdCmltZero_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 Vec128At VecRangeMem polyVecNat step_ldpQ128 step_strQ128
  vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3b (offSeg3bEnd seg3SubPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange bfi_ser1_eq halfRangeMem_congr halfRangeMem_serHalf1_eq
  serHalf1 vec128Zero2_eq_halfRangeMem)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x3948 → 0x39f0]
gen_placed_odd_sites blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x3954 → 0x3958]

private abbrev off3964Nat : Nat := 14692
private abbrev off3968Nat : Nat := 14696

@[simp, arm64_norm]
private theorem blkPC04_rebase_ldst128_cst16_4 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 off3964Nat) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 2)
        (.Offset (.gpr (BitVec.ofNat 5 11))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.4")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := off3964Nat)
    (r := { off := off3964Nat, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.4" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) off3964Nat)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 3673) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)

@[simp, arm64_norm]
private theorem blkPC04_rebase_ldst128_cst16_5 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC04.rebase b X).fetch (b + BitVec.ofNat 64 off3968Nat) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 3)
        (.Offset (.gpr (BitVec.ofNat 5 12))
          (lo12Of (blkPl04.ρ "libcrux_ml_kem:.rodata.cst16.5")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib04) (prog := blkPC04) (pl := blkPl04)
    (b := b) (X := X) (off := off3968Nat)
    (r := { off := off3968Nat, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.5" })
    rfl blkPlaceable04 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) off3968Nat)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 3674) blk04_code_eq blk04_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

attribute [local irreducible] blkPC04

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem evalSimdModImmExt_bic_8h_13_lsl8 (vd : BitVec 128) :
    evalSimdModImmExt true true 0#3 22#5 13#5 vd = .ok (vd &&& dup8x16 62207#16) := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdEor_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b00#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn ^^^ s.readVReg128 rm)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdBic_8h_13_lsl8 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10110#5 13#5 rd) s =
      (s.writeVReg128 rd (s.readVReg128 rd &&& dup8x16 62207#16)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.true_and, decide_true, ↓reduceIte,
    evalSimdModImmExt_bic_8h_13_lsl8, applySimdResult_ok]
  rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdUshl_8h_svc {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b01000#5 rn rd) s =
      (s.writeVReg128 rd (simdUshl8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdUshl_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdAddv_8h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdAcrossLanes true false 0b01#2 0b11011#5 rn rd) s =
      (s.writeVReg128 rd ((simdAddv8h (s.readVReg128 rn)).zeroExtend 128)).advancePC := by
  simp only [execInstWithSvc, BEq.beq, Bool.false_and, Bool.not_false, Bool.true_and,
    Bool.false_or, Bool.or_true, Bool.false_eq_true, decide_false, decide_true, ↓reduceIte,
    BitVec.reduceEq, Std.Legacy.Range.forIn_eq_forIn_range',
    show (8 <<< (0b01#2).toNat) = 16 from rfl,
    show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl]
  congr 1; congr 1
  set vn := s.readVReg128 rn
  have h0 : (vn >>> 0) &&& 65535#128 = (lane16 vn 0).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 0
  have h1 : (vn >>> 16) &&& 65535#128 = (lane16 vn 1).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 1
  have h2 : (vn >>> 32) &&& 65535#128 = (lane16 vn 2).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 2
  have h3 : (vn >>> 48) &&& 65535#128 = (lane16 vn 3).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 3
  have h4 : (vn >>> 64) &&& 65535#128 = (lane16 vn 4).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 4
  have h5 : (vn >>> 80) &&& 65535#128 = (lane16 vn 5).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 5
  have h6 : (vn >>> 96) &&& 65535#128 = (lane16 vn 6).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 6
  have h7 : (vn >>> 112) &&& 65535#128 = (lane16 vn 7).zeroExtend 128 := by simpa [getSimdLane] using getSimdLane_16_eq vn 7
  change ((((((((0#128 + ((vn >>> 0) &&& 65535#128)) + ((vn >>> 16) &&& 65535#128)) +
      ((vn >>> 32) &&& 65535#128)) + ((vn >>> 48) &&& 65535#128)) +
      ((vn >>> 64) &&& 65535#128)) + ((vn >>> 80) &&& 65535#128)) +
      ((vn >>> 96) &&& 65535#128)) + ((vn >>> 112) &&& 65535#128)) &&& 65535#128 =
    (((lane16 vn 0 + lane16 vn 1) + (lane16 vn 2 + lane16 vn 3)) +
      ((lane16 vn 4 + lane16 vn 5) + (lane16 vn 6 + lane16 vn 7))).zeroExtend 128
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  set a0 := lane16 vn 0; set a1 := lane16 vn 1; set a2 := lane16 vn 2; set a3 := lane16 vn 3
  set a4 := lane16 vn 4; set a5 := lane16 vn 5; set a6 := lane16 vn 6; set a7 := lane16 vn 7
  bv_bits

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdDup_8h_gpr exec_simdMovi_2d_0
  exec_simdEor_16b exec_simdBic_8h_13_lsl8 exec_simdUshl_8h_svc exec_simdAddv_8h
  exec_simdCmltZero_8h exec_simdAnd_16b exec_fmov_w_s

abbrev offSeg3cEnd : BitVec 64 := 14836#64
private abbrev off397c : BitVec 64 := 14716#64
private abbrev off39ec : BitVec 64 := 14828#64
private abbrev off39f0 : BitVec 64 := 14832#64

private theorem sepWP_cut {prog : Program} {t : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (Q : State → Prop) (hQ : Q s)
    (hk : ∀ s1, Q s1 → SepWP prog t s1 P post) : SepWP prog t s P post := hk s hQ

private theorem seg3_ser1_setup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (v0 v1 : BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg3bEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off397c) s
      (Vec128At (sp + 20704#64) v0 ∗ Vec128At (sp + 20720#64) v1 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 11872#64 ∧
        sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 1664#16 ∧
        sf.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
        sf.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
        sf.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
        Pf = (HalfRangeMem 16 (sp + 20704#64) (fun _ => 0#16) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_4 mlkemData06Bytes_length cst16_4_vec (by wp_norm_lhs) ?_
  refine step_ldrQ128_ro (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, pageOf_add_lo12Of])
    hro.cst16_5 mlkemData07Bytes_length cst16_5_vec (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 20720#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp] using hsp_chk)
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  intro m1
  refine step_strQ128 (wb := none) (ea := sp + 20704#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp] using hsp_chk)
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.left (SepStore128.vec128At rfl))
    (by wp_norm_lhs) ?_
  intro m2
  have hzero : Vec128At (sp + 20704#64) 0#128 ∗ Vec128At (sp + 20720#64) 0#128 =
      HalfRangeMem 16 (sp + 20704#64) (fun _ => 0#16) := by
    simpa [show (sp + 20704#64) + 16#64 = sp + 20720#64 by bv_omega] using
      vec128Zero2_eq_halfRangeMem (sp + 20704#64)
  rw [← sepConj_assoc, hzero]
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp [hx20], by simp [hx21],
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, rfl⟩

private theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

private theorem step_bCond_not_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = false) (hdst : pc + 4#64 = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        cases s; subst hpc; subst hdst
        simp [wp_norm, arm64_norm, hcond, State.advancePC, State.setPC])
    rfl hnext

attribute [local irreducible]
  polyVecNat dup8x16 simdAdd8h simdSub8h simdCmltZero8h simdUshl8h simdAddv8h

private abbrev off3980 : BitVec 64 := BitVec.ofNat 64 14720

private theorem seg3_ser1_body [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (s : State) (sp : BitVec 64) (w : Poly16) (r : Nat) (P : SepProp)
    (hpc : s.pc = b + off3980) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 r)
    (hx9 : s.readReg64 .x9 = sp + 11872#64 + BitVec.ofNat 64 (32 * r))
    (hx20 : s.readReg64 .x20 = sp + 20704#64) (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1664#16) (hv1 : s.readVReg128 1#5 = dup8x16 0xfcc0#16)
    (hv2 : s.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128)
    (hv3 : s.readVReg128 3#5 = 0x00800040002000100008000400020001#128)
    (hv4 : s.readVReg128 4#5 = polyVecNat w (2 * r))
    (hv5 : s.readVReg128 5#5 = polyVecNat w (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off39ec) s P
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.pstate = subsPState64 (BitVec.ofNat 64 r + 1#64) 16#64 ∧
        s1.readReg64 .x8 = BitVec.ofNat 64 r + 1#64 ∧
        s1.readReg64 .x9 = sp + 11872#64 + BitVec.ofNat 64 (32 * r) + 32#64 ∧
        s1.readReg64 .x10 = BitVec.ofNat 64 r ∧
        s1.readReg64 .x20 = sp + 20704#64 ∧ s1.readReg64 .x21 = sp + 11856#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 0#5 = dup8x16 1664#16 ∧ s1.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
        s1.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
        s1.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
        (s1.readReg32 .x11).truncate 16 = serHalf1 w r ∧ P1 = P) := by
  have hbase : blkPl04.base = b := _hb.symm
  subst hbase
  dsimp only [off3980, off39ec] at *
  wp_steps 27
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp, by simp,
      by simp [hx20], by simp [hx21], by simp, by simp, by simp, by simp,
      by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3],
      by simp [State.readReg32,
           serHalf1, neonCompress1PreShift8h, neonSerialize1MsbHalf]
         exact bfi_ser1_eq _ _, rfl⟩

private theorem seg3_ser1_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b)
    (s : State) (sp : BitVec 64) (w : Poly16) {r : Nat} (hr : r < 16)
    (h : Nat → BitVec 16) (Rest : SepProp)
    (hpc : s.pc = b + off397c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 r)
    (hx9 : s.readReg64 .x9 = sp + 11872#64 + BitVec.ofNat 64 (32 * r))
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1664#16)
    (hv1 : s.readVReg128 1#5 = dup8x16 0xfcc0#16)
    (hv2 : s.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128)
    (hv3 : s.readVReg128 3#5 = 0x00800040002000100008000400020001#128)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + off397c else b + offSeg3cEnd) s
      (HalfRangeMem 16 (sp + 20704#64) h ∗ PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (r + 1) ∧
        s'.readReg64 .x9 = sp + 11872#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x20 = sp + 20704#64 ∧
        s'.readReg64 .x21 = sp + 11856#64 ∧
        s'.readReg64 .x23 = s.readReg64 .x23 ∧
        s'.readReg64 .x26 = s.readReg64 .x26 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 0#5 = dup8x16 1664#16 ∧
        s'.readVReg128 1#5 = dup8x16 0xfcc0#16 ∧
        s'.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 ∧
        s'.readVReg128 3#5 = 0x00800040002000100008000400020001#128 ∧
        P' = (HalfRangeMem 16 (sp + 20704#64) (Function.update h r (serHalf1 w r)) ∗
          PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest)) := by
  have _ : b = blkPl04.base := _hb
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat w (2 * r)) (v2 := polyVecNat w (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  refine sepWP_seq_env hcl hro
    (seg3_ser1_body _hb _ sp w r _
      (by dsimp [off397c, off3980]; simp) (by simp [hrun])
      (by simp [hsp]) (by simpa [State.spAligned] using hspA)
      (by simp [hx8]) (by simp [hx9]) (by simp [hx20]) (by simp [hx21])
      (by simp [hv0]) (by simp [hv1]) (by simp [hv2]) (by simp [hv3])
      (by simp) (by simp)) ?_
  clear hpc hrun hsp hspA hx8 hx9 hx20 hx21 hv0 hv1 hv2 hv3 hcl hro
  rintro s1 _ hpc hrun _ _ ⟨hsp, hspA, hpst, hx8, hx9, hx10, hx20, hx21,
    hx23, hx26, hx28, hfp, hv0, hv1, hv2, hv3, hx11, rfl⟩
  dsimp only [off39ec] at hpc
  have hx23' : s1.readReg64 .x23 = s.readReg64 .x23 := by simpa using hx23
  have hx26' : s1.readReg64 .x26 = s.readReg64 .x26 := by simpa using hx26
  have hx28' : s1.readReg64 .x28 = s.readReg64 .x28 := by simpa using hx28
  have hfp' : s1.readReg64 .fp = s.readReg64 .fp := by simpa using hfp
  clear hx23 hx26 hx28 hfp
  refine SepWP.step_str16 (s' := s1.setPC (b + off39f0))
    (wb := none) (ea := (sp + 20704#64) + BitVec.ofNat 64 (2 * r))
    (val := serHalf1 w r)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx20, hx10]; clear * - hr; bv_omega)
    hx11
    (SepStore16.left (SepStore16.halfRange (n := 16) (c := r) hr rfl))
    (by simp [State.setPC]) ?_
  intro m'
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE ((s1.setPC (b + off39f0)).setMem m').pstate = true := by
      simp only [State.setMem, State.setPC, hpst]
      clear * - hr15
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
      all_goals first | omega | simp [wp_norm, arm64_norm]
    refine step_bCond_taken (pc := b + off39f0) (dst := b + off397c)
      rfl (by simp [hrun]) (by wp_norm_lhs) hcond (by bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8]; clear * - hr15; bv_omega,
        by simp [hx9]; clear * - hr15; bv_omega,
        by simp [hx20], by simp [hx21],
        by simp [hx23'], by simp [hx26'], by simp [hx28'], by simp [hfp'],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], rfl⟩
  · have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    have hcond : ConditionHolds .NE ((s1.setPC (b + off39f0)).setMem m').pstate = false := by
      simp [hpst, hr_eq, wp_norm, arm64_norm]
    refine step_bCond_not_taken (pc := b + off39f0) (dst := b + offSeg3cEnd)
      rfl (by simp [hrun]) (by wp_norm_lhs) hcond (by bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8, hr_eq], by simp [hx9, hr_eq],
        by simp [hx20], by simp [hx21],
        by simp [hx23'], by simp [hx26'], by simp [hx28'], by simp [hfp'],
        by simp [hv0], by simp [hv1], by simp [hv2], by simp [hv3], rfl⟩

private theorem seg3_ser1_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b)
    (sp x23Val x26Val x28Val fpVal : BitVec 64) (w : Poly16) (Rest : SepProp) :
    ∀ (rem r : Nat), rem + r = 15 →
    ∀ (s : State) (h : Nat → BitVec 16),
      s.pc = b + off397c → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 r →
      s.readReg64 .x9 = sp + 11872#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x20 = sp + 20704#64 → s.readReg64 .x21 = sp + 11856#64 →
      s.readReg64 .x23 = x23Val → s.readReg64 .x26 = x26Val →
      s.readReg64 .x28 = x28Val → s.readReg64 .fp = fpVal →
      s.readVReg128 0#5 = dup8x16 1664#16 → s.readVReg128 1#5 = dup8x16 0xfcc0#16 →
      s.readVReg128 2#5 = 0xfff8fff7fff6fff5fff4fff3fff2fff1#128 →
      s.readVReg128 3#5 = 0x00800040002000100008000400020001#128 →
      (∀ j, j < r → h j = serHalf1 w j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3cEnd) s
        (HalfRangeMem 16 (sp + 20704#64) h ∗ PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x23 = x23Val ∧ sf.readReg64 .x26 = x26Val ∧
          sf.readReg64 .x28 = x28Val ∧ sf.readReg64 .fp = fpVal ∧
          Pf = (HalfRangeMem 16 (sp + 20704#64) (serHalf1 w) ∗
            PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest))
  | 0, r, hrem, s, h, hpc, hrun, hsp, hspA, hcl, hro,
      hx8, hx9, hx20, hx21, hx23, hx26, hx28, hfp, hv0, hv1, hv2, hv3, hlo => by
    have hr15 : r = 15 := by omega
    subst hr15
    have hit := seg3_ser1_iter hb s sp w (r := 15) (by decide) h Rest
      hpc hrun hsp hspA hx8 hx9 hx20 hx21 hv0 hv1 hv2 hv3 hcl hro
    simp only [Nat.lt_irrefl, ↓reduceIte] at hit
    refine SepWP.mono hit ?_
    rintro sf Pf _ _ ⟨hsp', hspA', _, _, _, _, hx23', hx26', hx28', hfp', _, _, _, _, rfl⟩
    refine ⟨hsp', hspA', hx23'.trans hx23, hx26'.trans hx26, hx28'.trans hx28, hfp'.trans hfp, ?_⟩
    rw [halfRangeMem_congr (f := Function.update h 15 (serHalf1 w 15)) (g := serHalf1 w)
      (fun j hj => by
        by_cases heq : j = 15
        · subst heq; simp
        · rw [Function.update_of_ne heq]; exact hlo j (by omega))]
  | rem + 1, r, hrem, s, h, hpc, hrun, hsp, hspA, hcl, hro,
      hx8, hx9, hx20, hx21, hx23, hx26, hx28, hfp, hv0, hv1, hv2, hv3, hlo => by
    have hr15 : r < 15 := by omega
    have hit := seg3_ser1_iter hb s sp w (r := r) (by omega) h Rest
      hpc hrun hsp hspA hx8 hx9 hx20 hx21 hv0 hv1 hv2 hv3 hcl hro
    simp only [hr15, ↓reduceIte] at hit
    refine sepWP_seq_env hcl hro hit ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx8_1, hx9_1, hx20_1, hx21_1, hx23_1, hx26_1, hx28_1, hfp1,
        hv0_1, hv1_1, hv2_1, hv3_1, rfl⟩
    exact seg3_ser1_loop hb sp x23Val x26Val x28Val fpVal w Rest rem (r + 1) (by omega) s1
      (Function.update h r (serHalf1 w r)) hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      hx8_1 hx9_1 hx20_1 hx21_1
      (hx23_1.trans hx23) (hx26_1.trans hx26) (hx28_1.trans hx28) (hfp1.trans hfp)
      hv0_1 hv1_1 hv2_1 hv3_1
      (fun j hj => by
        by_cases heq : j = r
        · subst heq; simp
        · rw [Function.update_of_ne heq]; exact hlo j (by omega))

theorem seg3_ser1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {inv vPoly : Poly16} {vSpec invSpec : Poly}
    (hv_sz : vSpec.size = 256) (hinv_sz : invSpec.size = 256)
    (hv_bnd : ∀ i, i < 256 → -3329 ≤ (vPoly.getD i 0#16).toInt ∧ (vPoly.getD i 0#16).toInt < 3329)
    (hv_rep : ∀ i, i < 256 → (vPoly.getD i 0#16).toInt % 3329 = (vSpec.getD i 0 : Int) % 3329)
    (hn_bnd : ∀ i, i < 256 →
      -2496 ≤ (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ∧
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt ≤ 2496)
    (hn_rep : ∀ i, i < 256 →
      (neonMontgomeryMul16 (inv.getD i 0#16) 1441#16).toInt % 3329 = (invSpec.getD i 0 : Int) % 3329)
    (Rest : SepProp)
    (hpc : s.pc = b + offSeg3bEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64) :
    let w := seg3SubPoly inv vPoly
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg3cEnd) s
      (PolyMem (sp + 20704#64) (polyVecNat w) ∗ PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 20704#64) ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) ∗
          memRegion (sp + 20736#64) 480 ∗ PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest)) := by
  intro w
  have hsplit : PolyMem (sp + 20704#64) (polyVecNat w) =
      (Vec128At (sp + 20704#64) (polyVecNat w 0) ∗
        Vec128At (sp + 20720#64) (polyVecNat w 1) ∗
        VecRangeMem 30 (sp + 20736#64) (fun i => polyVecNat w (i + 2))) := by
    change VecRangeMem 32 (sp + 20704#64) (polyVecNat w) = _
    rw [VecRangeMem, VecRangeMem]
    simp only [show (sp + 20704#64) + 16#64 = sp + 20720#64 by bv_omega,
      show (sp + 20720#64) + 16#64 = sp + 20736#64 by bv_omega]
  rw [hsplit, sepConj_assoc, sepConj_assoc]
  refine sepWP_seq_env hcl hro
    (seg3_ser1_setup hb hbase s sp (polyVecNat w 0) (polyVecNat w 1) _
      hpc hrun hsp hspA hcl hro hx20 hx21) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx20_1, hx21_1, hx23_1, hx26_1, hx28_1, hfp1,
      hv0_1, hv1_1, hv2_1, hv3_1, rfl⟩
  rw [show (HalfRangeMem 16 (sp + 20704#64) (fun _ => 0#16) ∗
        (VecRangeMem 30 (sp + 20736#64) (fun i => polyVecNat w (i + 2)) ∗
          (PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest))) =
      (HalfRangeMem 16 (sp + 20704#64) (fun _ => 0#16) ∗
        PolyMem (sp + 11856#64) (polyVecNat w) ∗
        (VecRangeMem 30 (sp + 20736#64) (fun i => polyVecNat w (i + 2)) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.mono
    (seg3_ser1_loop hb sp (s.readReg64 .x23) (s.readReg64 .x26) (s.readReg64 .x28) (s.readReg64 .fp)
      w _ 15 0 rfl s1 (fun _ => 0#16)
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 (by simpa using hx9_1) hx20_1 hx21_1
      hx23_1 hx26_1 hx28_1 hfp1 hv0_1 hv1_1 hv2_1 hv3_1 (fun _ hj => by omega)) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx23_f, hx26_f, hx28_f, hfp_f, rfl⟩
  refine ⟨hsp_f, hspA_f, hx23_f, hx26_f, hx28_f, hfp_f, ?_⟩
  rw [halfRangeMem_serHalf1_eq hv_sz hinv_sz hv_bnd hv_rep hn_bnd hn_rep (sp + 20704#64)]
  have h480 := vecRangeMem_entails_memRegion 30 (sp + 20736#64) (fun i => polyVecNat w (i + 2))
  exact Entails.trans
    (by sep_frame : _ ⊢
      VecRangeMem 30 (sp + 20736#64) (fun i => polyVecNat w (i + 2)) ∗
      (((sp + 20704#64) ↦ₛ compressAndEncode 1 (polySub vSpec invSpec)) ∗
        PolyMem (sp + 11856#64) (polyVecNat w) ∗ Rest))
    (Entails.trans (sepConj_mono_left h480) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3c
