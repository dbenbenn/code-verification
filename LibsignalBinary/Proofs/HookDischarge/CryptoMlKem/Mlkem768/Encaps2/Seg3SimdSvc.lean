/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdPerm

/-!
# `encapsulate2` (`B20`) — Segment 3 `{svc}`-Polymorphic AdvSIMD Bridges (`Seg3SimdSvc`)

Lifts the `Syscall.standard` instruction bridges from `Seg3Simd` and `Seg3SimdPerm` to arbitrary
`{svc : State → State}` by definitional equality so `wp_steps` rewrites them in `O(1)` under
`attribute [local irreducible] blkPC20`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane64 pack2x64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSmlal4s simdSmull4s simdSqdmulh8h simdSshr8h simdSub8h
  simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_fmov_s_w exec_simdAdd_8h exec_simdDup_8h_gpr
  exec_simdIns_d1_d0 exec_simdIns_h1 exec_simdIns_h2 exec_simdIns_h3
  exec_simdIns_h4 exec_simdIns_h5 exec_simdIns_h6 exec_simdIns_h7
  exec_simdMla_8h exec_simdMovi_8h_1024 exec_simdMul_8h exec_simdMvni_8h_f2ff
  exec_simdOrr_16b exec_simdSqdmulh_8h exec_simdSshr_8h_1 exec_simdSshr_8h_11
  exec_simdSub_8h simdRev64_4s simdUzp1_4s sqdmulh8hFlags
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdPerm (
  exec_simdExt_16b_8 exec_simdRev64_4s exec_simdSmlal_4s exec_simdSmull_4s
  exec_simdTrn1_4s exec_simdTrn1_8h exec_simdTrn2_4s exec_simdTrn2_8h
  exec_simdUzp1_4s exec_simdZip1_2d exec_simdZip2_2d
)

@[simp, arm64_norm, wp_norm]
theorem svc_simdAdd_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdAdd_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdSub_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdSub8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSub_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdMul_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10011#5 rn rd) s =
      (s.writeVReg128 rd (simdMul8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMul_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdMla_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10010#5 rn rd) s =
      (s.writeVReg128 rd
        (simdMla8h (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMla_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdOrr_16b {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b10#2 rm 0b00011#5 rn rd) s =
      (s.writeVReg128 rd (s.readVReg128 rn ||| s.readVReg128 rm)).advancePC := rfl

@[simp, arm64_norm, wp_norm]
theorem svc_simdSqdmulh_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh8h (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSqdmulh_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdSshr_8h_1 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0011#4 0b111#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 1)).advancePC :=
  exec_simdSshr_8h_1 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdSshr_8h_11 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0010#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 11)).advancePC :=
  exec_simdSshr_8h_11 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdMovi_8h_1024 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10100#5 4#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC :=
  exec_simdMovi_8h_1024 rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdMvni_8h_f2ff {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC :=
  exec_simdMvni_8h_f2ff rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdDup_8h_gpr {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC :=
  exec_simdDup_8h_gpr rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_fmov_s_w {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.fmovGprVec false 0b00#2 0b00#2 0b111#3 rn rd) s =
      (s.writeVReg128 rd (((s.readReg64 (Reg.fromZRBits rn)).truncate 32).zeroExtend 128)).advancePC :=
  exec_fmov_s_w rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h1 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 6#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 1
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h1 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h2 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 10#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 2
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h2 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h3 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 14#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 3
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h3 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h4 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 18#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 4
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h4 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h5 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 22#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 5
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h5 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h6 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 26#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 6
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h6 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_h7 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 30#5 0b0011#4 rn rd) s =
      (s.writeVReg128 rd (setSimdLane (s.readVReg128 rd) 16 7
        (((s.readReg64 (Reg.fromZRBits rn)).truncate 16).zeroExtend 128))).advancePC :=
  exec_simdIns_h7 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdIns_d1_d0 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true true 24#5 0#4 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rd) 0
          else lane64 (s.readVReg128 rn) 0)).advancePC :=
  exec_simdIns_d1_d0 rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdTrn1_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b01#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdTrn1_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdTrn2_8h {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b01#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdTrn2_8h rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdTrn1_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b10#2 rm 0b010#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn1_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdTrn1_4s rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdTrn2_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b10#2 rm 0b110#3 rn rd) s =
      (s.writeVReg128 rd (simdTrn2_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdTrn2_4s rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdUzp1_4s {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b10#2 rm 0b001#3 rn rd) s =
      (s.writeVReg128 rd (simdUzp1_4s (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdUzp1_4s rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdZip1_2d {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b11#2 rm 0b011#3 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rn) 0
          else lane64 (s.readVReg128 rm) 0)).advancePC :=
  exec_simdZip1_2d rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdZip2_2d {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdPermute true 0b11#2 rm 0b111#3 rn rd) s =
      (s.writeVReg128 rd
        (pack2x64 fun c =>
          if c.val = 0 then lane64 (s.readVReg128 rn) 1
          else lane64 (s.readVReg128 rm) 1)).advancePC :=
  exec_simdZip2_2d rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdRev64_4s {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdTwoRegMisc true false 0b10#2 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdRev64_4s (s.readVReg128 rn))).advancePC :=
  exec_simdRev64_4s rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdExt_16b_8 {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdExt true rm 8#4 rn rd) s =
      (s.writeVReg128 rd
        ((s.readVReg128 rm).truncate 64 ++ (s.readVReg128 rn).extractLsb' 64 64)).advancePC :=
  exec_simdExt_16b_8 rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdSmull_4s {svc : State → State} (q : Bool) (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeDiff q false 0b01#2 rm 0b1100#4 rn rd) s =
      (s.writeVReg128 rd (simdSmull4s q (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSmull_4s q rm rn rd s

@[simp, arm64_norm, wp_norm]
theorem svc_simdSmlal_4s {svc : State → State} (q : Bool) (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeDiff q false 0b01#2 rm 0b1000#4 rn rd) s =
      (s.writeVReg128 rd
        (simdSmlal4s q (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSmlal_4s q rm rn rd s

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
