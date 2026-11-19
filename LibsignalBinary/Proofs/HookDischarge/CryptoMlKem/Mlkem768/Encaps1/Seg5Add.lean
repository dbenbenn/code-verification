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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd

/-!
# `encapsulate1_serialized` (`B03`) — `Seg5` Setup, `montgomery(1441) + e1` Loop & Outer Tail

Covers:
1. Pre-loop setup (`+0x4e38 .. +0x4e9c`)
2. Post-`InvNTT` `montgomery_multiply_by_constant(1441) + e1 + barrett` loop (`+0x69d8 .. +0x6a60`)
3. Outer 3-row loop tail (`+0x6a60 .. +0x6a78`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 ext_lane16 lane16 lane16_dup8x16 lane16_pack8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  lane16_simdAdd8h simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_ldrQ128 step_strQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_simdAdd_8h exec_simdDup_8h_gpr exec_simdMla_8h exec_simdMovi_8h_1024
  exec_simdMul_8h exec_simdMvni_8h_f2ff exec_simdSqdmulh_8h exec_simdSshr_8h_1
  exec_simdSshr_8h_11 exec_simdSub_8h sqdmulh8hFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  seg5FinalPoly seg5Loop1_vec_eq)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x4e38 → 0x4e9c, 0x69d8 → 0x6a78]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg5Pre  : BitVec 64 := BitVec.ofNat 64 20024
@[simp, arm64_norm, wp_norm] abbrev offDotStart : BitVec 64 := BitVec.ofNat 64 20124
@[simp, arm64_norm, wp_norm] abbrev offAddStart : BitVec 64 := BitVec.ofNat 64 27096
@[simp, arm64_norm, wp_norm] abbrev offAddTail  : BitVec 64 := BitVec.ofNat 64 27232
@[simp, arm64_norm, wp_norm] abbrev offSeg5End  : BitVec 64 := BitVec.ofNat 64 27256

@[simp, arm64_norm, wp_norm]
private theorem blkPl03_ρ [MlKemPlacement] (sym : String) :
    blkPl03.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r

@[simp, arm64_norm, wp_norm]
private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r

@[simp, arm64_norm, wp_norm]
private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := rfl

@[simp, arm64_norm, wp_norm]
private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdAdd_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdAdd_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdSub_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdSub8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSub_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMul_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10011#5 rn rd) s =
      (s.writeVReg128 rd (simdMul8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMul_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMla_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10010#5 rn rd) s =
      (s.writeVReg128 rd
        (simdMla8h (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMla_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdSqdmulh_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh8h (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSqdmulh_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_1' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0011#4 0b111#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 1)).advancePC :=
  exec_simdSshr_8h_1 rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_11' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0010#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 11)).advancePC :=
  exec_simdSshr_8h_11 rn rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_8h_1024' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10100#5 4#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC :=
  exec_simdMovi_8h_1024 rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMvni_8h_f2ff' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC :=
  exec_simdMvni_8h_f2ff rd s

@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_8h_gpr' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC :=
  exec_simdDup_8h_gpr rn rd s

attribute [local wp_norm ↓ high]
  exec_simdAdd_8h' exec_simdSub_8h' exec_simdMul_8h' exec_simdMla_8h'
  exec_simdSqdmulh_8h' exec_simdSshr_8h_1' exec_simdSshr_8h_11'
  exec_simdMovi_8h_1024' exec_simdMvni_8h_f2ff' exec_simdDup_8h_gpr'

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

/-- Final `u[i]` polynomial computed in `B03` post-`InvNTT` loop (`montgomery(1441) + e1 + barrett`). -/
@[expose] def seg5AddPoly (inv e1 : Poly16) : Poly16 :=
  seg5FinalPoly inv e1 (Array.replicate 256 0#16)

theorem seg5Add_vec_eq (inv e1 : Poly16) (idx : Nat) (hidx : idx < 32) :
    let qx := polyVecNat inv idx
    let qe := polyVecNat e1 idx
    let normal := simdSub8h
      (simdSshr8h (simdSqdmulh8h qx (dup8x16 1441#16)) 1)
      (simdSshr8h (simdSqdmulh8h (simdMul8h qx (dup8x16 55457#16)) (dup8x16 3329#16)) 1)
    let tot := simdAdd8h qe normal
    let quot := simdSshr8h (simdAdd8h (simdSqdmulh8h tot (dup8x16 20159#16)) (dup8x16 1024#16)) 11
    simdMla8h tot quot (dup8x16 0xf2ff#16) = polyVecNat (seg5AddPoly inv e1) idx := by
  have hz : polyVecNat (Array.replicate 256 0#16) idx = 0#128 := by
    apply ext_lane16; intro j
    rw [polyVecNat, lane16_pack8x16]
    have hj : 8 * idx + j.val < 256 := by omega
    simp [Array.getD, hj, lane16]
  have hadd : simdAdd8h (polyVecNat e1 idx) (polyVecNat (Array.replicate 256 0#16) idx) = polyVecNat e1 idx := by
    rw [hz]; apply ext_lane16; intro j
    rw [lane16_simdAdd8h]; simp [lane16]
  have h := seg5Loop1_vec_eq inv e1 (Array.replicate 256 0#16) idx hidx true
  dsimp only [↓reduceIte] at h
  rwa [hadd] at h

attribute [local irreducible]
  blkPC03 dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h simdMla8h

/-- Pre-loop setup (`+0x4e38 → +0x4e9c`). -/
theorem seg5_init [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s : State) (sp : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + offSeg5Pre) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 2192#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotStart) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x1 = 20159#64 ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = sp + 2208#64 ∧
        s'.readReg64 .x11 = sp + 13984#64 ∧
        s'.readReg64 .x12 = 16#64 ∧
        s'.readReg64 .x13 = 0#64 ∧
        s'.readReg64 .x14 = sp + 12448#64 ∧
        s'.readReg64 .x16 = 62209#64 ∧
        s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧
        s'.readReg64 .x19 = sp + 2192#64 ∧
        s'.readReg64 .x21 = 64778#64 ∧
        s'.readReg64 .x22 = 31498#64 ∧
        s'.readReg64 .x23 = 1441#64 ∧
        s'.readReg64 .x24 = 55457#64 ∧
        s'.readReg64 .x25 = 4608#64 ∧
        s'.readReg64 .x28 = sp + 6832#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        s'.readVReg128 27#5 = dup8x16 1024#16 ∧
        P' = P) := by
  have _ : b = blkPl03.base := hb
  wp_steps
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp [hx19], by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, rfl⟩

/-- Outer-loop GPRs and SIMD constants untouched across `seg5_add_loop` (`+0x69d8 → +0x6a60`). -/
structure Seg5AddPreserved (s0 s : State) : Prop where
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x4  : s.readReg64 .x4  = s0.readReg64 .x4
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  v0  : s.readVReg128 0#5  = s0.readVReg128 0#5
  v23 : s.readVReg128 23#5 = s0.readVReg128 23#5
  v27 : s.readVReg128 27#5 = s0.readVReg128 27#5

set_option maxRecDepth 100000 in
private theorem seg5_add_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) {r : Nat} (hr : r < 16)
    (inv e1 : Poly16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offAddStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx10 : s.readReg64 .x10 = polyPtr + 16#64) (hx11 : s.readReg64 .x11 = e1Ptr)
    (hx23 : s.readReg64 .x23 = 1441#64) (hx24 : s.readReg64 .x24 = 55457#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (32 * r))
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg5AddPreserved s0 s)
    (hf0 : f (2 * r) = polyVecNat inv (2 * r))
    (hf1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if r < 15 then b + offAddStart else b + offAddTail) s
      (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x10 = polyPtr + 16#64 ∧ s'.readReg64 .x11 = e1Ptr ∧
        s'.readReg64 .x23 = 1441#64 ∧ s'.readReg64 .x24 = 55457#64 ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s'.readVReg128 27#5 = dup8x16 1024#16 ∧
        Seg5AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update
            (Function.update f (2 * r + 1) (polyVecNat (seg5AddPoly inv e1) (2 * r + 1)))
            (2 * r) (polyVecNat (seg5AddPoly inv e1) (2 * r))) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  have _ : b = blkPl03.base := hb
  rcases hpres with ⟨p1, p4, p8, p9, p11, p12, p13, p14, p16, p17,
    p18, p19, p21, p22, p23, p24, p25, p28, pv0, pv23, pv27⟩
  wp_steps 2
  refine step_ldrQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1))) (v := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx10, hx27]; clear * - hr; bv_omega)
    (hf1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r))) (v := polyVecNat inv (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (hf0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 14
  refine step_ldpQ128 (wb := none)
    (ea := e1Ptr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := e1Ptr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat e1 (2 * r)) (v2 := polyVecNat e1 (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 10
  have hv2_eq := seg5Add_vec_eq inv e1 (2 * r + 1) (by omega)
  have hv1_eq := seg5Add_vec_eq inv e1 (2 * r) (by omega)
  dsimp only at hv2_eq hv1_eq
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (val := polyVecNat (seg5AddPoly inv e1) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx10, hx27]; clear * - hr; bv_omega)
    (by simp [← hv2_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m1; wp_steps 2
  refine step_strQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (val := polyVecNat (seg5AddPoly inv e1) (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (by simp [← hv1_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m2; wp_step; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx10], by simp [hx11], by simp [hx23], by simp [hx24],
        by simp; clear * - hr15; bv_omega,
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p1], by simp [p4], by simp [p8], by simp [p9], by simp [p11], by simp [p12],
          by simp [p13], by simp [p14], by simp [p16], by simp [p17], by simp [p18], by simp [p19],
          by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p28],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt; clear * - hne hr hlt; bv_omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx10], by simp [hx11], by simp [hx23], by simp [hx24],
        by simp [hr_eq],
        by simp [hv16], by simp [hv17], by simp [hv23], by simp [hv27],
        ⟨by simp [p1], by simp [p4], by simp [p8], by simp [p9], by simp [p11], by simp [p12],
          by simp [p13], by simp [p14], by simp [p16], by simp [p17], by simp [p18], by simp [p19],
          by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p28],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩

private theorem seg5_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offAddStart → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x10 = polyPtr + 16#64 → s.readReg64 .x11 = e1Ptr →
      s.readReg64 .x23 = 1441#64 → s.readReg64 .x24 = 55457#64 →
      s.readReg64 .x27 = BitVec.ofNat 64 (32 * r) →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 23#5 = dup8x16 0xf2ff#16 → s.readVReg128 27#5 = dup8x16 1024#16 →
      Seg5AddPreserved s0 s →
      (∀ idx, idx < 2 * r → f idx = polyVecNat (seg5AddPoly inv e1) idx) →
      (∀ idx, 2 * r ≤ idx → idx < 32 → f idx = polyVecNat inv idx) →
      SepWP (blkPC03.rebase b (fun _ => none)) (b + offAddTail) s
        (PolyMem polyPtr f ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
          s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s'.readVReg128 27#5 = dup8x16 1024#16 ∧
          Seg5AddPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) ∗
            PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  intro rem
  induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _ _ hx10 hx11 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg5_add_iter hb s0 s sp polyPtr e1Ptr (r := 15) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx10 hx11 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hv16', hv17', hv23', hv27', hpres', rfl⟩
    refine ⟨hsp', hspA', hv16', hv17', hv23', hv27', hpres', ?_⟩
    have hmem : PolyMem polyPtr
        (Function.update
          (Function.update f 31 (polyVecNat (seg5AddPoly inv e1) 31))
          30 (polyVecNat (seg5AddPoly inv e1) 30)) =
        PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) := by
      apply vecRangeMem_congr; intro idx hidx
      by_cases h30 : idx = 30
      · subst h30; simp
      · by_cases h31 : idx = 31
        · subst h31; simp
        · simp [Function.update_of_ne h30, Function.update_of_ne h31, hlo idx (by omega)]
    rw [hmem]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx10 hx11 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hstep := seg5_add_iter hb s0 s sp polyPtr e1Ptr (r := r) (by omega) inv e1 f Rest
      hpc hrun hsp hspA hx10 hx11 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1
      ⟨hsp1, hspA1, hx10_1, hx11_1, hx23_1, hx24_1, hx27_1, hv16_1, hv17_1, hv23_1, hv27_1, hpres1, rfl⟩
    refine ih (r + 1) (by omega) s1 _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1
      hx10_1 hx11_1 hx23_1 hx24_1 hx27_1 hv16_1 hv17_1 hv23_1 hv27_1 hpres1 ?_ ?_
    · intro idx hidx
      by_cases h0 : idx = 2 * r
      · subst h0; simp
      · by_cases h1 : idx = 2 * r + 1
        · subst h1; simp
        · simp [Function.update_of_ne h0, Function.update_of_ne h1, hlo idx (by omega)]
    · intro idx hge hlt
      have h0 : idx ≠ 2 * r := by omega
      have h1 : idx ≠ 2 * r + 1 := by omega
      simp [Function.update_of_ne h0, Function.update_of_ne h1, hhi idx (by omega) hlt]

theorem seg5_add_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr e1Ptr : BitVec 64) (inv e1 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offAddStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx10 : s.readReg64 .x10 = polyPtr + 16#64) (hx11 : s.readReg64 .x11 = e1Ptr)
    (hx23 : s.readReg64 .x23 = 1441#64) (hx24 : s.readReg64 .x24 = 55457#64)
    (hx27 : s.readReg64 .x27 = 0#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16) (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Seg5AddPreserved s0 s) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offAddTail) s
      (PolyMem polyPtr (polyVecNat inv) ∗ PolyMem e1Ptr (polyVecNat e1) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Seg5AddPreserved s0 s' ∧
        P' = (PolyMem polyPtr (polyVecNat (seg5AddPoly inv e1)) ∗
          PolyMem e1Ptr (polyVecNat e1) ∗ Rest)) := by
  refine SepWP.mono (seg5_add_loop hb s0 sp polyPtr e1Ptr inv e1 Rest 15 0 rfl s (polyVecNat inv)
    hpc hrun hsp hspA hcl hro hx10 hx11 hx23 hx24 hx27 hv16 hv17 hv23 hv27 hpres
    (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hpres', hP'⟩
  exact ⟨hsp', hspA', hpres', hP'⟩

/-- Outer 3-row loop tail (`+0x6a60 → +0x4e9c / +0x6a78`). -/
theorem seg5_outer_tail [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s : State) {i : Nat} (hi : i < 3) (P : SepProp)
    (hpc : s.pc = b + offAddTail) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (1536 * (i + 1)))
    (hx25 : s.readReg64 .x25 = 4608#64) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if i < 2 then b + offDotStart else b + offSeg5End) s P
      (fun s' P' =>
        s'.sp = s.sp ∧ s'.spAligned = s.spAligned ∧ s'.vregs = s.vregs ∧
        s'.readReg64 .x9 = s.readReg64 .x9 + 512#64 ∧
        s'.readReg64 .x11 = s.readReg64 .x11 + 512#64 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 + 512#64 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 + 1536#64 ∧
        (∀ r : BitVec 5, r ≠ 9#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 28#5 → r ≠ 31#5 →
          s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        P' = P) := by
  have _ : b = blkPl03.base := hb
  wp_steps 5; wp_step; wp_if hne
  · have hi2 : i < 2 := by
      by_contra hge; have hi_eq : i = 2 := by omega
      subst hi_eq; simp at hne
    simp only [hi2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp, by simp,
        fun r h9 h11 h12 h28 h31 => by simp [h9, h11, h12, h28, h31], rfl⟩
  · have hi2 : ¬ i < 2 := by
      intro hlt; rcases i with _ | _ | i
      · simp at hne
      · simp at hne
      · omega
    simp only [hi2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨rfl, rfl, rfl, by simp, by simp, by simp, by simp,
        fun r h9 h11 h12 h28 h31 => by simp [h9, h11, h12, h28, h31], rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Add
