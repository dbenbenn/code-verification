/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import ProofLib

/-!
# `kyber_decapsulate` (`B06`) — Kernel-Transparent Symbolic Stepper (`PolySymFast`)

Provides `@[expose]` boolean equality on `PolyLoc` and `SymGpr` so `rfl_kernel` reduces straight-line
NEON `runSymRangeFast` certificates in `< 1s`, with a one-line soundness bridge `runSymRange_of_fast`
to `PolySymDefs.runSymRange`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
  (PolyLoc SymGpr SymCfg SymState fetchWordTree06 smartMla smartSub stepSymInst runSymRange)

@[expose] def polyLocBeq : PolyLoc → PolyLoc → Bool
  | .spOff a, .spOff b => a == b
  | .gpr a, .gpr b => a == b
  | _, _ => false

@[expose] def symGprBeq : SymGpr → SymGpr → Bool
  | .gpr0 r1 o1, .gpr0 r2 o2 => r1 == r2 && o1 == o2
  | .spAdd o1, .spAdd o2 => o1 == o2
  | .const64 v1, .const64 v2 => v1 == v2
  | .addGpr0 a1 b1, .addGpr0 a2 b2 => a1 == a2 && b1 == b2
  | _, _ => false

theorem polyLocBeq_eq (a b : PolyLoc) : polyLocBeq a b = (a == b) := by
  cases a <;> cases b <;> simp [polyLocBeq, BEq.beq]

theorem symGprBeq_eq (a b : SymGpr) : symGprBeq a b = (a == b) := by
  cases a <;> cases b <;> simp [symGprBeq, BEq.beq]

@[expose] def stepSymInstFast (cfg : SymCfg) (inst : Instr) (st : SymState) : Option SymState :=
  match inst with
  | .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if cfg.spillLen ≤ 40 && cfg.spillOff ≤ o && o < cfg.spillOff + 16 * cfg.spillLen &&
          (o - cfg.spillOff) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.spill.get ((o - cfg.spillOff) / 16)) }
      else match cfg.spPolyOff? with
        | some pOff =>
            if pOff ≤ o && o < pOff + 512 && (o - pOff) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (st.poly.get ((o - pOff) / 16)) }
            else if cfg.hasSrc && 14432 ≤ o && o < 14944 && (o - 14432) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (.src ((o - 14432) / 16)) }
            else none
        | none =>
            if cfg.hasSrc && 14432 ≤ o && o < 14944 && (o - 14432) % 16 == 0 then
              some { st with vregs := st.vregs.set vt.toNat (.src ((o - 14432) / 16)) }
            else none
  | .strSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      let val := st.vregs.get vt.toNat
      if cfg.spillLen ≤ 40 && cfg.spillOff ≤ o && o < cfg.spillOff + 16 * cfg.spillLen &&
          (o - cfg.spillOff) % 16 == 0 then
        some { st with spill := st.spill.set ((o - cfg.spillOff) / 16) val }
      else match cfg.spPolyOff? with
        | some pOff =>
            if pOff ≤ o && o < pOff + 512 && (o - pOff) % 16 == 0 then
              some { st with poly := st.poly.set ((o - pOff) / 16) val }
            else none
        | none => none
  | .ldrSimd .Q128 vt (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && polyLocBeq cfg.polyLoc (.gpr rb) && symGprBeq (st.gprs.get rb.toNat) (.gpr0 rb 0#64) &&
          o < 512 && o % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (st.poly.get (o / 16)) }
      else none
  | .strSimd .Q128 vt (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && polyLocBeq cfg.polyLoc (.gpr rb) && symGprBeq (st.gprs.get rb.toNat) (.gpr0 rb 0#64) &&
          o < 512 && o % 16 == 0 then
        some { st with poly := st.poly.set (o / 16) (st.vregs.get vt.toNat) }
      else none
  | .ldpSimd .Q128 vt1 vt2 (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && polyLocBeq cfg.polyLoc (.gpr rb) && symGprBeq (st.gprs.get rb.toNat) (.gpr0 rb 0#64) &&
          o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with vregs := (st.vregs.set vt1.toNat (st.poly.get k)).set vt2.toNat (st.poly.get (k + 1)) }
      else none
  | .stpSimd .Q128 vt1 vt2 (.Offset (.gpr rb) off) =>
      let o := off.toNat
      if rb != 31#5 && polyLocBeq cfg.polyLoc (.gpr rb) && symGprBeq (st.gprs.get rb.toNat) (.gpr0 rb 0#64) &&
          o + 16 < 512 && o % 16 == 0 then
        let k := o / 16
        some { st with poly := (st.poly.set k (st.vregs.get vt1.toNat)).set (k + 1) (st.vregs.get vt2.toNat) }
      else none
  | .moveWide .W32 .MOVZ (.gpr rd) imm16 0 =>
      if rd != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (.const64 (imm16.zeroExtend 64)) }
      else none
  | .addSubImm .W64 .ADD (.gpr rd) .sp imm12 shift12 =>
      if rd != 31#5 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        some { st with gprs := st.gprs.set rd.toNat (.spAdd off64) }
      else none
  | .addSubImm .W64 .ADD (.gpr rd) (.gpr rn) imm12 shift12 =>
      if rd != 31#5 && rn != 31#5 then
        let off64 : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
        match st.gprs.get rn.toNat with
        | .gpr0 r0 o0 => some { st with gprs := st.gprs.set rd.toNat (.gpr0 r0 (o0 + off64)) }
        | .spAdd o0 => some { st with gprs := st.gprs.set rd.toNat (.spAdd (o0 + off64)) }
        | .const64 v => some { st with gprs := st.gprs.set rd.toNat (.const64 (v + off64)) }
        | _ => none
      else none
  | .logicalShift .W64 .ORR (.gpr rd) .xzr .xzr .LSL 0 =>
      if rd != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (.const64 0#64) }
      else none
  | .logicalShift .W64 .ORR (.gpr rd) .xzr (.gpr rm) .LSL 0 =>
      if rd != 31#5 && rm != 31#5 then
        some { st with gprs := st.gprs.set rd.toNat (st.gprs.get rm.toNat) }
      else none
  | .addSubShift .W64 .ADD (.gpr rd) (.gpr rn) (.gpr rm) .LSL 0 =>
      if rd != 31#5 && rn != 31#5 && rm != 31#5 then
        match st.gprs.get rn.toNat, st.gprs.get rm.toNat with
        | .gpr0 r1 0#64, .gpr0 r2 0#64 =>
            some { st with gprs := st.gprs.set rd.toNat (.addGpr0 r1 r2) }
        | _, _ => none
      else none
  | .simdInsDup true false 2#5 1#4 rn rd =>
      if rn != 31#5 then
        match st.gprs.get rn.toNat with
        | .const64 v => some { st with vregs := st.vregs.set rd.toNat (.const (v.truncate 16)) }
        | _ => none
      else none
  | .simdThreeSame true u sz rm opcode rn rd =>
      if !u && sz == 2#2 && opcode == 0b00011#5 && rm == rn then
        some { st with vregs := st.vregs.set rd.toNat (st.vregs.get rn.toNat) }
      else if !u && sz == 1#2 && opcode == 0b10000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.add (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if u && sz == 1#2 && opcode == 0b10000#5 then
        some { st with vregs := st.vregs.set rd.toNat (smartSub (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10011#5 then
        some { st with vregs := st.vregs.set rd.toNat (.mul (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10010#5 then
        some { st with vregs := st.vregs.set rd.toNat (smartMla (st.vregs.get rd.toNat) (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else if !u && sz == 1#2 && opcode == 0b10110#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sqdmulh (st.vregs.get rn.toNat) (st.vregs.get rm.toNat)) }
      else none
  | .simdImmShift true op immh immb opcode rn rd =>
      if immh == 0#4 && opcode == 0b10000#5 then
        let c16 : BitVec 16 := (immb ++ rn).zeroExtend 16
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if immh == 0#4 && opcode == 0b10100#5 then
        let c16 : BitVec 16 := ((immb ++ rn).zeroExtend 16) <<< 8
        some { st with vregs := st.vregs.set rd.toNat (.const (if op then ~~~c16 else c16)) }
      else if !op && immh == 0b0011#4 && immb == 0b111#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 1) }
      else if !op && immh == 0b0010#4 && immb == 0b101#3 && opcode == 0b00000#5 then
        some { st with vregs := st.vregs.set rd.toNat (.sshr (st.vregs.get rn.toNat) 11) }
      else none
  | _ => none

theorem stepSymInstFast_eq (cfg : SymCfg) (inst : Instr) (st : SymState) :
    stepSymInstFast cfg inst st = stepSymInst cfg inst st := by
  unfold stepSymInstFast stepSymInst
  split <;> simp only [polyLocBeq_eq, symGprBeq_eq] <;> rfl

@[expose] def runSymRangeFast (cfg : SymCfg) : Nat → Nat → SymState → Option SymState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree06 w with
      | some inst =>
          match stepSymInstFast cfg inst st with
          | some st' => runSymRangeFast cfg (w + 1) n st'
          | none => none
      | none => none

theorem runSymRangeFast_eq (cfg : SymCfg) (w n : Nat) (st : SymState) :
    runSymRangeFast cfg w n st = runSymRange cfg w n st := by
  induction n generalizing w st with
  | zero => rfl
  | succ n ih =>
    unfold runSymRangeFast runSymRange
    cases hfw : fetchWordTree06 w with
    | none => rfl
    | some inst =>
      dsimp only
      rw [stepSymInstFast_eq]
      cases stepSymInst cfg inst st with
      | none => rfl
      | some st' => exact ih (w + 1) st'

theorem runSymRange_of_fast {cfg : SymCfg} {w n : Nat} {st st' : SymState}
    (h : runSymRangeFast cfg w n st = some st') :
    runSymRange cfg w n st = some st' :=
  (runSymRangeFast_eq cfg w n st).symm.trans h

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
