/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.Decode
public import ProofLib.GenDecodes
public import ProofLib.GenPlacedFetches
public meta import ProofLib.GenDecodes -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches -- proof-setup: allow-public-import
public meta import Lean -- proof-setup: allow-public-import

/-!
# Pre-Stepped ARM64 Word Decode Lemmas and Direct Placed-Block Fetch Elaborator

Eliminates per-instruction WHNF unfolding of the full 84-branch `Arm64.decode` decision tree and
`CodeBlock` `mkDecideProof` stalls when elaborating and kernel-checking `gen_ls_blk` /
`gen_ls_blk_ultra` blocks:
1. Pre-proves 23 `fast_decode_br*` theorems covering >99.8% of unique machine words across
   `libsignalSession` so each word reduces only its single matching branch body (`Eq.refl` fallback
   on rare encodings).
2. Deduplicates `_gfd_wdec_<word>` per distinct 32-bit machine word across an entire module.
3. Directly proves extern `.call26`/`.jump26` branch fetches and relaxable `.adrpHi21`+`.addLo12`
   `pairStep`s from `RelocTree` + `WordTree` without `mkDecideProof` or `CodeBlock` unfolding,
   falling back to upstream `gen_placed_fetches` only for non-relaxable or intra-block sites.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.FastDecode

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

theorem mask_disjoint {w m1 p1 m2 p2 : BitVec 32}
    (h1 : (w &&& m1 == p1) = true)
    (hdisj : ((m1 &&& m2) &&& (p1 ^^^ p2) == 0#32) = false) :
    (w &&& m2 == p2) = false := by
  cases h2 : (w &&& m2 == p2) with
  | false => rfl
  | true =>
    have e1 : w &&& m1 = p1 := eq_of_beq h1
    have e2 : w &&& m2 = p2 := eq_of_beq h2
    have hz : (m1 &&& m2) &&& (p1 ^^^ p2) = 0#32 := by
      rw [← e1, ← e2]
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_zero]
      cases w[i] <;> cases m1[i] <;> cases m2[i] <;> rfl
    rw [hz] at hdisj
    cases hdisj

theorem eq_disjoint_of_mask {w m1 p1 c : BitVec 32}
    (h1 : (w &&& m1 == p1) = true)
    (hdisj : ((c &&& m1) == p1) = false) :
    (w == c) = false := by
  cases hc : (w == c) with
  | false => rfl
  | true =>
    rw [eq_of_beq hc] at h1
    rw [h1] at hdisj
    cases hdisj

theorem step_bool_false {α : Type} {b : Bool} {t e rhs : α}
    (hb : b = false) (he : e = rhs) :
    (if b = true then t else e) = rhs := by
  rw [hb]; exact he

theorem step_and_false {α : Type} {b1 b2 : Bool} {t e rhs : α}
    (hb1 : b1 = false) (he : e = rhs) :
    (if (b1 && b2) = true then t else e) = rhs := by
  rw [hb1]; exact he

theorem step_bool_true {α : Type} {b : Bool} {t e rhs : α}
    (hb : b = true) (ht : t = rhs) :
    (if b = true then t else e) = rhs := by
  rw [hb]; exact ht

theorem fast_decode_br6 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f000000#32) == 0x10000000#32) = true)
    (hbody : (
    let page := w.getLsbD 31
    let immlo : BitVec 2 := w.extractLsb' 29 2
    let immhi : BitVec 19 := w.extractLsb' 5 19
    let imm21 : BitVec 21 := immhi ++ immlo
    let offset : BitVec 64 :=
      if page then (imm21.signExtend 64) <<< 12
      else imm21.signExtend 64
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.adr page rd offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br7 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f800000#32) == 0x11000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let sh := w.getLsbD 22
    let imm12 : BitVec 12 := w.extractLsb' 10 12
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
    some (.addSubImm width op rd rn imm12 sh)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br8 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f800000#32) == 0x12000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let opc := w.extractLsb' 29 2
    let immN := w.getLsbD 22
    let immr : BitVec 6 := w.extractLsb' 16 6
    let imms : BitVec 6 := w.extractLsb' 10 6
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    if !sf && immN then
      none
    else
      match decodeBitMasks immN imms immr with
      | none => none
      | some mask =>
        let op := LogicalOp.ofBits opc false
        let rd := if opc == 3#2 then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
        some (.logicalImm width op rd rn mask)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br9 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f800000#32) == 0x12800000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let opc := (w.extractLsb' 29 2).toNat
    let hwBits := (w.extractLsb' 21 2).toNat
    let imm16 : BitVec 16 := w.extractLsb' 5 16
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if !sf && hwBits >= 2 then
      none
    else
      let hw := hwBits * 16
      match opc with
      | 0 => some (.moveWide width .MOVN rd imm16 hw)
      | 2 => some (.moveWide width .MOVZ rd imm16 hw)
      | 3 => some (.moveWide width .MOVK rd imm16 hw)
      | _ => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br10 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f800000#32) == 0x13000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let opc := (w.extractLsb' 29 2).toNat
    let nBit := w.getLsbD 22
    let immr := (w.extractLsb' 16 6).toNat
    let imms := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if sf != nBit then
      none
    else if !sf && (immr >= 32 || imms >= 32) then
      none
    else
      match opc with
      | 0 => some (.bitfield width .SBFM rd rn immr imms)
      | 1 => some (.bitfield width .BFM  rd rn immr imms)
      | 2 => some (.bitfield width .UBFM rd rn immr imms)
      | _ => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br12 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x7c000000#32) == 0x14000000#32) = true)
    (hbody : (
    let isBl := w.getLsbD 31
    let imm26 : BitVec 26 := w.extractLsb' 0 26
    let offset : BitVec 64 := (imm26.signExtend 64) <<< 2
    if isBl then
      some (.bl offset)
    else
      some (.b offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br13 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x7e000000#32) == 0x34000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let isNonZero := w.getLsbD 24
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.cbz width isNonZero rt offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br14 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x7e000000#32) == 0x36000000#32) = true)
    (hbody : (
    let b5 := w.getLsbD 31
    let isNonZero := w.getLsbD 24
    let b40 := (w.extractLsb' 19 5).toNat
    let bitPos := (if b5 then 32 else 0) + b40
    let imm14 : BitVec 14 := w.extractLsb' 5 14
    let offset : BitVec 64 := (imm14.signExtend 64) <<< 2
    let tbzW : RegWidth := if b5 then .W64 else .W32
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.tbz tbzW isNonZero rt bitPos offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br15 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0xff000010#32) == 0x54000000#32) = true)
    (hbody : (
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let cond := CondCode.ofBits (w.extractLsb' 0 4)
    some (.bCond cond offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br16 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0xff9ffc1f#32) == 0xd61f0000#32) = true)
    (hbody : (
    let opc := (w.extractLsb' 21 2).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    match opc with
    | 0 => some (.br rn)
    | 1 => some (.blr rn)
    | 2 => some (.ret rn)
    | _ => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br17 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f000000#32) == 0x0a000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let opc := w.extractLsb' 29 2
    let shift := ShiftType.ofBits (w.extractLsb' 22 2)
    let nBit := w.getLsbD 21
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let imm6 := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if !sf && imm6 >= 32 then
      none
    else
      some (.logicalShift width (LogicalOp.ofBits opc nBit) rd rn rm shift imm6)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br18 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1f200000#32) == 0x0b000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let shiftBits := w.extractLsb' 22 2
    if shiftBits == 3#2 then
      none
    else
      let shift := ShiftType.ofBits shiftBits
      let rm := Reg.fromZRBits (w.extractLsb' 16 5)
      let imm6 := (w.extractLsb' 10 6).toNat
      let rn := Reg.fromZRBits (w.extractLsb' 5 5)
      let rd := Reg.fromZRBits (w.extractLsb' 0 5)
      if !sf && imm6 >= 32 then
        none
      else
        some (.addSubShift width op rd rn rm shift imm6)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br19 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x1fe00000#32) == 0x0b200000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let optBits := w.extractLsb' 13 3
    let imm3 := (w.extractLsb' 10 3).toNat
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    if imm3 > 4 then
      none
    else
      let ext := ExtendType.ofBits optBits
      let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
      some (.addSubExt width op rd rn rm ext imm3)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br22 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3fe00800#32) == 0x1a800000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let op := CondSelectOp.ofBits (w.getLsbD 30) (w.getLsbD 10)
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let cond := CondCode.ofBits (w.extractLsb' 12 4)
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.condSelect width op rd rn rm cond)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br23 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x7fff0000#32) == 0x5ac00000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let opcode := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    match opcode with
    | 0 => some (.dataProc1 width .RBIT rd rn)
    | 1 => some (.dataProc1 width .REV16 rd rn)
    | 2 =>
      if sf then some (.dataProc1 .W64 .REV32 rd rn)
      else some (.dataProc1 .W32 .REV rd rn)
    | 3 =>
      if sf then some (.dataProc1 .W64 .REV rd rn)
      else none
    | 4 => some (.dataProc1 width .CLZ rd rn)
    | 5 => some (.dataProc1 width .CLS rd rn)
    | _ => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br26 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x7f000000#32) == 0x1b000000#32) = true)
    (hbody : (
    let sf := w.getLsbD 31
    let width : RegWidth := RegWidth.ofBool sf
    let op31 := (w.extractLsb' 21 3).toNat
    let o0 := w.getLsbD 15
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let raBits := w.extractLsb' 10 5
    let ra := Reg.fromZRBits raBits
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    match sf, op31, o0 with
    | _, 0, false    => some (.dataProc3 width .MADD rd rn rm ra)
    | _, 0, true     => some (.dataProc3 width .MSUB rd rn rm ra)
    | true, 1, false => some (.dataProc3 .W64 .SMADDL rd rn rm ra)
    | true, 1, true  => some (.dataProc3 .W64 .SMSUBL rd rn rm ra)
    | true, 2, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .SMULH rd rn rm .xzr) else none
    | true, 5, false => some (.dataProc3 .W64 .UMADDL rd rn rm ra)
    | true, 5, true  => some (.dataProc3 .W64 .UMSUBL rd rn rm ra)
    | true, 6, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .UMULH rd rn rm .xzr) else none
    | _, _, _        => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br28 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3e000000#32) == 0x28000000#32) = true)
    (hnot_27 : ((w &&& 0x7f800000#32) == 0x28000000#32) = false)
    (hbody : (
    let opc := (w.extractLsb' 30 2).toNat
    let modeBits := (w.extractLsb' 23 2).toNat
    let isLoad := w.getLsbD 22
    let imm7 : BitVec 7 := w.extractLsb' 15 7
    let rt2Bits := w.extractLsb' 10 5
    let rnBits := w.extractLsb' 5 5
    let rt1Bits := w.extractLsb' 0 5
    let scale : Nat := if opc == 2 then 3 else 2
    let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
    let rn := Reg.fromSPBits rnBits
    let rt1 := Reg.fromZRBits rt1Bits
    let rt2 := Reg.fromZRBits rt2Bits
    let addr? : Option AddrMode :=
      match modeBits with
      | 1 => some (.PostIndex rn offset)
      | 2 => some (.Offset rn offset)
      | 3 => some (.PreIndex rn offset)
      | _ => none
    let wbOverlap := (modeBits == 1 || modeBits == 3) && rnBits != 31#5 && (rt1Bits == rnBits || rt2Bits == rnBits)
    let loadPairOverlap := isLoad && rt1Bits == rt2Bits
    match addr? with
    | none => none
    | some addr =>
      if wbOverlap || loadPairOverlap then
        none
      else
        match opc, isLoad with
        | 0, true  => some (.ldp .W32 false rt1 rt2 addr)
        | 0, false => some (.stp .W32 rt1 rt2 addr)
        | 1, true  => some (.ldp .W64 true  rt1 rt2 addr)
        | 2, true  => some (.ldp .W64 false rt1 rt2 addr)
        | 2, false => some (.stp .W64 rt1 rt2 addr)
        | _, _     => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false hnot_27 ?_
  exact step_bool_true hm hbody

theorem fast_decode_br34 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3f000000#32) == 0x39000000#32) = true)
    (hnot_29 : ((w &&& 0xffc00000#32) == 0xf9800000#32) = false)
    (hbody : (
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    let imm12 : BitVec 12 := w.extractLsb' 10 12
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    let offset : BitVec 64 := (imm12.zeroExtend 64) <<< sizeBits
    mkLoadStoreInst sizeBits opc rt (.Offset rn offset)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false hnot_29 ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8a00800#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x38200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br35 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3f000000#32) == 0x38000000#32) = true)
    (hnot_30 : ((w &&& 0xffe00c00#32) == 0xf8800000#32) = false)
    (hnot_31 : ((w &&& 0xffe00c00#32) == 0xf8a00800#32) = false)
    (hnot_32 : ((w &&& 0x3f200c00#32) == 0x38200000#32) = false)
    (hbody : (
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    let rnBits := w.extractLsb' 5 5
    let rtBits := w.extractLsb' 0 5
    let rn := Reg.fromSPBits rnBits
    let rt := Reg.fromZRBits rtBits
    if !(w.getLsbD 21) then
      let imm9 : BitVec 9 := w.extractLsb' 12 9
      let offset : BitVec 64 := imm9.signExtend 64
      let mode2 := (w.extractLsb' 10 2).toNat
      let wbOverlap := (mode2 == 1 || mode2 == 3) && rnBits != 31#5 && rtBits == rnBits
      if wbOverlap then
        none
      else
        match mode2 with
        | 0 => mkLoadStoreInst sizeBits opc rt (.UnscaledOffset rn offset)
        | 1 => mkLoadStoreInst sizeBits opc rt (.PostIndex rn offset)
        | 3 => mkLoadStoreInst sizeBits opc rt (.PreIndex rn offset)
        | _ => none
    else if (w.extractLsb' 10 2) == 2#2 then
      let rm := Reg.fromZRBits (w.extractLsb' 16 5)
      let extBits := w.extractLsb' 13 3
      let ext := ExtendType.ofBits extBits
      let sBit := w.getLsbD 12
      if !extBits.getLsbD 1 || (sizeBits == 0 && sBit) then
        none
      else
        let amount := if sBit then sizeBits else 0
        mkLoadStoreInst sizeBits opc rt (.RegOffset rn rm ext amount)
    else
      none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffc00000#32) (p2 := 0xf9800000#32) hm rfl) ?_
  refine step_bool_false hnot_30 ?_
  refine step_bool_false hnot_31 ?_
  refine step_bool_false hnot_32 ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x39000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br38 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3fbffc00#32) == 0x089ffc00#32) = true)
    (hbody : (
    let sz := MemWidth.ofBits (w.extractLsb' 30 2)
    let isLoad := w.getLsbD 22
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.ldarStlr sz isLoad rn rt)
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffc00000#32) (p2 := 0xf9800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8a00800#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x38200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x39000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x38000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x18000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x1c000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br48 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3e000000#32) == 0x2c000000#32) = true)
    (hnot_47 : ((w &&& 0x3f800000#32) == 0x2c000000#32) = false)
    (hbody : (
    let opc := (w.extractLsb' 30 2).toNat
    let modeBits := (w.extractLsb' 23 2).toNat
    let isLoad := w.getLsbD 22
    let sz? : Option (SimdMemSize × Nat) :=
      match opc with
      | 0 => some (.S32, 2)
      | 1 => some (.D64, 3)
      | 2 => some (.Q128, 4)
      | _ => none
    match sz? with
    | none => none
    | some (sz, scale) =>
      let imm7 : BitVec 7 := w.extractLsb' 15 7
      let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
      let vt2 : BitVec 5 := w.extractLsb' 10 5
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt1 : BitVec 5 := w.extractLsb' 0 5
      let addr? : Option AddrMode :=
        match modeBits with
        | 1 => some (.PostIndex rn offset)
        | 2 => some (.Offset rn offset)
        | 3 => some (.PreIndex rn offset)
        | _ => none
      match addr? with
      | some addr =>
        if isLoad then
          if vt1 == vt2 then none else some (.ldpSimd sz vt1 vt2 addr)
        else some (.stpSimd sz vt1 vt2 addr)
      | none => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffc00000#32) (p2 := 0xf9800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8a00800#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x38200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x39000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x38000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x18000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x1c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fbffc00#32) (p2 := 0x089ffc00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fff7c00#32) (p2 := 0x085f7c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe07c00#32) (p2 := 0x08007c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfff0000#32) (p2 := 0x887f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfe00000#32) (p2 := 0x88200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fa07c00#32) (p2 := 0x08a07c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfa07c00#32) (p2 := 0x08207c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffd00000#32) (p2 := 0xd5100000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503301f#32) hm rfl) ?_
  refine step_bool_false hnot_47 ?_
  exact step_bool_true hm hbody

theorem fast_decode_br49 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3f000000#32) == 0x3d000000#32) = true)
    (hbody : (
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    match decodeSimdLoadStoreType sizeBits opc with
    | some (isLoad, sz, scale) =>
      let imm12 : BitVec 12 := w.extractLsb' 10 12
      let offset : BitVec 64 := (imm12.zeroExtend 64) <<< scale
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt : BitVec 5 := w.extractLsb' 0 5
      let addr := AddrMode.Offset rn offset
      if isLoad then some (.ldrSimd sz vt addr)
      else some (.strSimd sz vt addr)
    | none => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffc00000#32) (p2 := 0xf9800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8a00800#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x38200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x39000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x38000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x18000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x1c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fbffc00#32) (p2 := 0x089ffc00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fff7c00#32) (p2 := 0x085f7c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe07c00#32) (p2 := 0x08007c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfff0000#32) (p2 := 0x887f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfe00000#32) (p2 := 0x88200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fa07c00#32) (p2 := 0x08a07c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfa07c00#32) (p2 := 0x08207c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffd00000#32) (p2 := 0xd5100000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503301f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f800000#32) (p2 := 0x2c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x2c000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem fast_decode_br50 (w : BitVec 32) (inst : Instr)
    (hm : ((w &&& 0x3f000000#32) == 0x3c000000#32) = true)
    (hbody : (
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    match decodeSimdLoadStoreType sizeBits opc with
    | some (isLoad, sz, scale) =>
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt : BitVec 5 := w.extractLsb' 0 5
      let addr? : Option AddrMode :=
        if !(w.getLsbD 21) then
          let imm9 : BitVec 9 := w.extractLsb' 12 9
          let offset : BitVec 64 := imm9.signExtend 64
          match (w.extractLsb' 10 2).toNat with
          | 0 => some (.UnscaledOffset rn offset)
          | 1 => some (.PostIndex rn offset)
          | 3 => some (.PreIndex rn offset)
          | _ => none
        else if (w.extractLsb' 10 2) == 2#2 then
          let rm := Reg.fromZRBits (w.extractLsb' 16 5)
          let extBits := w.extractLsb' 13 3
          let ext := ExtendType.ofBits extBits
          let sBit := w.getLsbD 12
          if !extBits.getLsbD 1 || (scale == 0 && sBit) then
            none
          else
            let amount := if sBit then scale else 0
            some (.RegOffset rn rm ext amount)
        else
          none
      match addr? with
      | some addr =>
        if isLoad then some (.ldrSimd sz vt addr)
        else some (.strSimd sz vt addr)
      | none => none
    | none => none
    : Option Instr) = some inst) :
    Arm64.decode w = some inst := by
  unfold Arm64.decode; dsimp only []
  refine step_bool_false (eq_disjoint_of_mask (c := 0xd503201f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4000001#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe0001f#32) (p2 := 0xd4200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503201f#32) hm rfl) ?_
  refine step_and_false (mask_disjoint (m2 := 0xffff0000#32) (p2 := 0x00000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffffffe0#32) (p2 := 0xd50b7420#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x10000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x11000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x12800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f800000#32) (p2 := 0x13000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x13800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7c000000#32) (p2 := 0x14000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x34000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7e000000#32) (p2 := 0x36000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff000010#32) (p2 := 0x54000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xff9ffc1f#32) (p2 := 0xd61f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f000000#32) (p2 := 0x0a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1f200000#32) (p2 := 0x0b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe00000#32) (p2 := 0x0b200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x1fe0fc00#32) (p2 := 0x1a000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00410#32) (p2 := 0x3a400000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe00800#32) (p2 := 0x1a800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fff0000#32) (p2 := 0x5ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe0e000#32) (p2 := 0x1ac04000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7fe00000#32) (p2 := 0x1ac00000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f000000#32) (p2 := 0x1b000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x7f800000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x28000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffc00000#32) (p2 := 0xf9800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8800000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffe00c00#32) (p2 := 0xf8a00800#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x38200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f200c00#32) (p2 := 0x19000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x39000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x38000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x18000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x1c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fbffc00#32) (p2 := 0x089ffc00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fff7c00#32) (p2 := 0x085f7c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fe07c00#32) (p2 := 0x08007c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfff0000#32) (p2 := 0x887f0000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfe00000#32) (p2 := 0x88200000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3fa07c00#32) (p2 := 0x08a07c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xbfa07c00#32) (p2 := 0x08207c00#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xffd00000#32) (p2 := 0xd5100000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0xfffff01f#32) (p2 := 0xd503301f#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f800000#32) (p2 := 0x2c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3e000000#32) (p2 := 0x2c000000#32) hm rfl) ?_
  refine step_bool_false (mask_disjoint (m2 := 0x3f000000#32) (p2 := 0x3d000000#32) hm rfl) ?_
  exact step_bool_true hm hbody

theorem decode_quad_of_word {b0 b1 b2 b3 : BitVec 8} {w : BitVec 32} {inst : Instr}
    (hw : b3 ++ b2 ++ b1 ++ b0 = w)
    (hdec : Arm64.decode w = some inst) :
    Arm64.decode (b3 ++ b2 ++ b1 ++ b0) = some inst := by
  rw [hw]; exact hdec

theorem fetchDecodeAt_of_quad_decode {t : WordTree} {off j : Nat} {b0 b1 b2 b3 : BitVec 8} {inst : Instr}
    (hoff : off = 4 * j)
    (hquad : t.getQuad? j = some (b0, b1, b2, b3))
    (hdec : Arm64.decode (b3 ++ b2 ++ b1 ++ b0) = some inst) :
    t.fetchDecodeAt off = some inst := by
  subst hoff
  unfold WordTree.fetchDecodeAt
  have hdiv : (4 * j) / 4 = j := Nat.mul_div_right j (by decide)
  have hmul : (4 * j == 4 * ((4 * j) / 4)) = true := by rw [hdiv]; simp
  rw [hmul, hdiv, hquad]
  exact hdec

set_option linter.literalFetch false in
theorem fast_fetch_extern_call26 {A : Sort _} (P : A → Program) (plOf : A → Placement)
    (lib : PlacedLib) (t : WordTree) (n : Nat) (rt : RelocTree)
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes)
    (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rt.toList)
    (hwf : rt.wf = true)
    (hweak_nil : lib.text.weakRefs = [])
    (hn64 : decide (4 * n ≤ 2 ^ 64) = true)
    (off j : Nat) (r : RelocEntry) (e : String)
    (b0 b1 b2 b3 : BitVec 8)
    (hoff4 : off = 4 * j)
    (hlt_n : decide (off < 4 * n) = true)
    (hlookup_r : rt.lookup? off = some r)
    (hr_off : r.off = off)
    (hkind : r.kind = .call26)
    (haddend : r.addend = 0)
    (hsymE : r.sym = e)
    (hsym : lookup e lib.text.symbols = none)
    (hquad : t.getQuad? j = some (b0, b1, b2, b3))
    (hop : wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0xfc000000#32 = 0x94000000#32)
    (a : A) (b : BitVec 64) (X : String → Option (State → State)) :
    ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) =
      some (.bl (((plOf a).ρ e - (plOf a).base) - BitVec.ofNat 64 off)) := by
  have hlt' : off < 4 * n := of_decide_eq_true hlt_n
  have hn64' : 4 * n ≤ 2 ^ 64 := of_decide_eq_true hn64
  have hal : off % 4 = 0 := by rw [hoff4]; omega
  have hlen : off + 4 ≤ 4 * n := by omega
  have hlt64 : off < 2 ^ 64 := Nat.lt_of_lt_of_le hlt' hn64'
  have hr : lib.text.relocAt? off = some r := relocAt?_of_tree hrelocs hwf hlookup_r
  have hb2b : (lib.text.b2bNext? r).isNone = true := b2bNext?_isNone_of_extern hsymE hsym
  have hplain : lib.text.plainSite r = true :=
    plainSite_of_branch (isCall := true) hal hr hr_off hkind hb2b
  have hw : lib.text.wordAt off = wordOfBytesLE [b0, b1, b2, b3] 0 := by
    rw [hoff4]; exact wordAt_of_getQuad? hcode hsize hquad
  have hnh : ((lib.program (plOf a)).rebase b X).hookAtOff? off = none :=
    hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) hlt'
  have hweak : lib.text.weakRefs.contains r.sym = false := by rw [hweak_nil]; rfl
  exact fetch_rebase_congr_prog (hprog a)
    (fetch_rebase_of_externBranch hcode hsize true hal hlen hlt64 hr hr_off hkind hplain
      haddend hsymE hsym hw hop (hPOf a) hnh hweak)

set_option linter.literalFetch false in
theorem fast_fetch_extern_jump26 {A : Sort _} (P : A → Program) (plOf : A → Placement)
    (lib : PlacedLib) (t : WordTree) (n : Nat) (rt : RelocTree)
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes)
    (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rt.toList)
    (hwf : rt.wf = true)
    (hweak_nil : lib.text.weakRefs = [])
    (hn64 : decide (4 * n ≤ 2 ^ 64) = true)
    (off j : Nat) (r : RelocEntry) (e : String)
    (b0 b1 b2 b3 : BitVec 8)
    (hoff4 : off = 4 * j)
    (hlt_n : decide (off < 4 * n) = true)
    (hlookup_r : rt.lookup? off = some r)
    (hr_off : r.off = off)
    (hkind : r.kind = .jump26)
    (haddend : r.addend = 0)
    (hsymE : r.sym = e)
    (hsym : lookup e lib.text.symbols = none)
    (hquad : t.getQuad? j = some (b0, b1, b2, b3))
    (hop : wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0xfc000000#32 = 0x14000000#32)
    (a : A) (b : BitVec 64) (X : String → Option (State → State)) :
    ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) =
      some (.b (((plOf a).ρ e - (plOf a).base) - BitVec.ofNat 64 off)) := by
  have hlt' : off < 4 * n := of_decide_eq_true hlt_n
  have hn64' : 4 * n ≤ 2 ^ 64 := of_decide_eq_true hn64
  have hal : off % 4 = 0 := by rw [hoff4]; omega
  have hlen : off + 4 ≤ 4 * n := by omega
  have hlt64 : off < 2 ^ 64 := Nat.lt_of_lt_of_le hlt' hn64'
  have hr : lib.text.relocAt? off = some r := relocAt?_of_tree hrelocs hwf hlookup_r
  have hb2b : (lib.text.b2bNext? r).isNone = true := b2bNext?_isNone_of_extern hsymE hsym
  have hplain : lib.text.plainSite r = true :=
    plainSite_of_branch (isCall := false) hal hr hr_off hkind hb2b
  have hw : lib.text.wordAt off = wordOfBytesLE [b0, b1, b2, b3] 0 := by
    rw [hoff4]; exact wordAt_of_getQuad? hcode hsize hquad
  have hnh : ((lib.program (plOf a)).rebase b X).hookAtOff? off = none :=
    hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) hlt'
  have hweak : lib.text.weakRefs.contains r.sym = false := by rw [hweak_nil]; rfl
  exact fetch_rebase_congr_prog (hprog a)
    (fetch_rebase_of_externBranch hcode hsize false hal hlen hlt64 hr hr_off hkind hplain
      haddend hsymE hsym hw hop (hPOf a) hnh hweak)

theorem fast_pairStep_extern_zero {A : Sort _} (prog : A → Program) (plOf : A → Placement)
    (lib : PlacedLib) (t : WordTree) (n : Nat) (rt : RelocTree)
    (hprog : ∀ a, prog a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes)
    (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rt.toList)
    (hwf : rt.wf = true)
    (off off4 off8 j j1 : Nat) (r1 r2 : RelocEntry) (sym : String) (rd : BitVec 5)
    (b0 b1 b2 b3 c0 c1 c2 c3 : BitVec 8)
    (hoff : off = 4 * j) (hoff4 : off + 4 = off4) (hoff4j : off4 = 4 * j1) (hoff8 : off + 8 = off8)
    (hlt0 : decide (off < 4 * n) = true) (hlt4 : decide (off4 < 4 * n) = true)
    (hr1 : rt.lookup? off = some r1) (hr2 : rt.lookup? off4 = some r2)
    (hq0 : t.getQuad? j = some (b0, b1, b2, b3))
    (hq1 : t.getQuad? j1 = some (c0, c1, c2, c3))
    (hsym1 : r1.sym = sym) (hsymEq : r1.sym = r2.sym)
    (hsymNone : lookup sym lib.text.symbols = none)
    (hadd0 : r1.addend = 0)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.addend == r2.addend &&
      isAdrpWord (wordOfBytesLE [b0, b1, b2, b3] 0) &&
      isAddImm64Word (wordOfBytesLE [c0, c1, c2, c3] 0) &&
      (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) == (wordOfBytesLE [c0, c1, c2, c3] 0 &&& 0x1f#32) &&
      ((wordOfBytesLE [c0, c1, c2, c3] 0 >>> 5) &&& 0x1f#32) == (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) &&
      (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) != 0x1f#32) = true)
    (hrd : (wordOfBytesLE [b0, b1, b2, b3] 0).extractLsb' 0 5 = rd)
    (hrd31 : decide (rd ≠ 31#5) = true)
    (a : A) (b : BitVec 64) (X : String → Option (State → State))
    (hb : b = (plOf a).base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP ((prog a).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) ((plOf a).ρ sym)).setPC (b + BitVec.ofNat 64 off8)) P post oom) :
    SepWP ((prog a).rebase b X) tgt s P post oom := by
  have hrel1 : lib.text.relocAt? off = some r1 := relocAt?_of_tree hrelocs hwf hr1
  have hrel2 : lib.text.relocAt? (off + 4) = some r2 := by
    rw [hoff4]; exact relocAt?_of_tree hrelocs hwf hr2
  have hw0 : lib.text.wordAt off = wordOfBytesLE [b0, b1, b2, b3] 0 := by
    rw [hoff]; exact wordAt_of_getQuad? hcode hsize hq0
  have hw1 : lib.text.wordAt (off + 4) = wordOfBytesLE [c0, c1, c2, c3] 0 := by
    rw [hoff4, hoff4j]; exact wordAt_of_getQuad? hcode hsize hq1
  have hrel : lib.text.relaxableAt off = true :=
    relaxableAt_of_words_eq hrel1 hrel2 hw0 hw1 hsymEq hchk
  have hrd' : (lib.text.wordAt off).extractLsb' 0 5 = rd := by rw [hw0]; exact hrd
  have hh0 : ((lib.program (plOf a)).rebase b X).hookAtOff? off = none :=
    hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (of_decide_eq_true hlt0)
  have hh4 : ((lib.program (plOf a)).rebase b X).hookAtOff? (off + 4) = none := by
    rw [hoff4]; exact hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (of_decide_eq_true hlt4)
  exact sepWP_rebase_relaxablePair (hprog a) hrel hrel1 hrd' (of_decide_eq_true hrd31) hoff8
    hh0 hh4 (hPOf a) hb (fun _ => target_of_extern_zero hsym1 hsymNone hadd0) hpc hrun hnext

theorem fast_pairStep_extern_pos {A : Sort _} (prog : A → Program) (plOf : A → Placement)
    (lib : PlacedLib) (t : WordTree) (n : Nat) (rt : RelocTree)
    (hprog : ∀ a, prog a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes)
    (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rt.toList)
    (hwf : rt.wf = true)
    (off off4 off8 j j1 k : Nat) (r1 r2 : RelocEntry) (sym : String) (rd : BitVec 5)
    (b0 b1 b2 b3 c0 c1 c2 c3 : BitVec 8)
    (hoff : off = 4 * j) (hoff4 : off + 4 = off4) (hoff4j : off4 = 4 * j1) (hoff8 : off + 8 = off8)
    (hlt0 : decide (off < 4 * n) = true) (hlt4 : decide (off4 < 4 * n) = true)
    (hr1 : rt.lookup? off = some r1) (hr2 : rt.lookup? off4 = some r2)
    (hq0 : t.getQuad? j = some (b0, b1, b2, b3))
    (hq1 : t.getQuad? j1 = some (c0, c1, c2, c3))
    (hsym1 : r1.sym = sym) (hsymEq : r1.sym = r2.sym)
    (hsymNone : lookup sym lib.text.symbols = none)
    (haddPos : r1.addend = Int.ofNat k) (hk0 : (Int.ofNat k == 0) = false)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.addend == r2.addend &&
      isAdrpWord (wordOfBytesLE [b0, b1, b2, b3] 0) &&
      isAddImm64Word (wordOfBytesLE [c0, c1, c2, c3] 0) &&
      (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) == (wordOfBytesLE [c0, c1, c2, c3] 0 &&& 0x1f#32) &&
      ((wordOfBytesLE [c0, c1, c2, c3] 0 >>> 5) &&& 0x1f#32) == (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) &&
      (wordOfBytesLE [b0, b1, b2, b3] 0 &&& 0x1f#32) != 0x1f#32) = true)
    (hrd : (wordOfBytesLE [b0, b1, b2, b3] 0).extractLsb' 0 5 = rd)
    (hrd31 : decide (rd ≠ 31#5) = true)
    (a : A) (b : BitVec 64) (X : String → Option (State → State))
    (hb : b = (plOf a).base)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP ((prog a).rebase b X) tgt
      ((s.writeReg64 (.gpr rd) ((plOf a).ρ sym + BitVec.ofNat 64 k)).setPC
        (b + BitVec.ofNat 64 off8)) P post oom) :
    SepWP ((prog a).rebase b X) tgt s P post oom := by
  have hrel1 : lib.text.relocAt? off = some r1 := relocAt?_of_tree hrelocs hwf hr1
  have hrel2 : lib.text.relocAt? (off + 4) = some r2 := by
    rw [hoff4]; exact relocAt?_of_tree hrelocs hwf hr2
  have hw0 : lib.text.wordAt off = wordOfBytesLE [b0, b1, b2, b3] 0 := by
    rw [hoff]; exact wordAt_of_getQuad? hcode hsize hq0
  have hw1 : lib.text.wordAt (off + 4) = wordOfBytesLE [c0, c1, c2, c3] 0 := by
    rw [hoff4, hoff4j]; exact wordAt_of_getQuad? hcode hsize hq1
  have hrel : lib.text.relaxableAt off = true :=
    relaxableAt_of_words_eq hrel1 hrel2 hw0 hw1 hsymEq hchk
  have hrd' : (lib.text.wordAt off).extractLsb' 0 5 = rd := by rw [hw0]; exact hrd
  have hh0 : ((lib.program (plOf a)).rebase b X).hookAtOff? off = none :=
    hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (of_decide_eq_true hlt0)
  have hh4 : ((lib.program (plOf a)).rebase b X).hookAtOff? (off + 4) = none := by
    rw [hoff4]; exact hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (of_decide_eq_true hlt4)
  exact sepWP_rebase_relaxablePair (hprog a) hrel hrel1 hrd' (of_decide_eq_true hrd31) hoff8
    hh0 hh4 (hPOf a) hb (fun _ => target_of_extern_pos hsym1 hsymNone haddPos hk0) hpc hrun hnext

section MetaFastDecode

open Lean Meta Elab Term Command

private meta def hasRelocInSorted (offs : Array Nat) (lo hi : Nat) : Bool := Id.run do
  let mut l := 0
  let mut r := offs.size
  while l < r do
    let mid := (l + r) / 2
    if offs[mid]! < lo then
      l := mid + 1
    else
      r := mid
  return l < offs.size && offs[l]! ≤ hi

private meta def mkPrivChunkHelperName (progNs : Name) (pfxStr tag : String) : MetaM Name := do
  let env ← getEnv
  let mut idx := 0
  repeat do
    let s := if idx == 0 then s!"_{pfxStr}_{tag}" else s!"_{pfxStr}_{tag}_{idx}"
    let priv := mkPrivateName env (progNs ++ Name.mkSimple s)
    if !env.contains priv then
      return priv
    idx := idx + 1
  unreachable!

private meta def programE (lib pl : Expr) : MetaM Expr := do
  let mut e := mkApp2 (Lean.mkConst ``PlacedLib.program) lib pl
  let mut ty ← whnfD (← inferType e)
  while ty.isForall do
    let some v := ty.bindingDomain!.getOptParamDefault? | break
    e := mkApp e v
    ty ← whnfD (ty.bindingBody!.instantiate1 v)
  return e

private meta def ensureHProg
    (progName : Name) (paramTy : Expr) (libE plOfE : Expr) : MetaM Expr := do
  let env ← getEnv
  let modNm ← getMainModule
  let priv := mkPrivateName env (modNm ++ progName ++ `_gpf_hprog)
  if env.contains priv then
    return Lean.mkConst priv
  let (ty, val) ← withLocalDecl `a .default paramTy fun a => do
    let pl := mkApp plOfE a
    let progE := mkApp (Lean.mkConst progName) a
    let rhs ← programE libE pl
    let eqTy ← mkEq progE rhs
    let prf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Arm64.Program) progE
    return (← mkForallFVars #[a] eqTy, ← mkLambdaFVars #[a] prf)
  addDecl (.thmDecl { name := priv, levelParams := [], type := ty, value := val })
  return Lean.mkConst priv

private meta def ensureHWeakNil (progName : Name) (libE : Expr) : MetaM Expr := do
  let env ← getEnv
  let modNm ← getMainModule
  let priv := mkPrivateName env (modNm ++ progName ++ `_gfd_hweak_nil)
  if env.contains priv then
    return Lean.mkConst priv
  let strListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``String)
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``String)
  let lhs := mkApp (Lean.mkConst ``CodeBlock.weakRefs) (mkApp (Lean.mkConst ``PlacedLib.text) libE)
  let ty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy lhs nilE
  let val := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strListTy nilE
  addDecl (.thmDecl { name := priv, levelParams := [], type := ty, value := val })
  return Lean.mkConst priv

meta def mkFastWordDecodeProof (wNat : Nat) (wE inst rhs : Expr) : Expr :=
  let boolTy := Lean.mkConst ``Bool
  let reflTrue := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.true)
  let reflFalse := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
  let hbody := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr rhs

  if (wNat &&& 0x3f000000) == 0x39000000 && (wNat &&& 0xffc00000) != 0xf9800000 then
    mkAppN (Lean.mkConst ``fast_decode_br34) #[wE, inst, reflTrue, reflFalse, hbody]
  else if (wNat &&& 0x3e000000) == 0x28000000 && (wNat &&& 0x7f800000) != 0x28000000 then
    mkAppN (Lean.mkConst ``fast_decode_br28) #[wE, inst, reflTrue, reflFalse, hbody]
  else if (wNat &&& 0x1f800000) == 0x11000000 then
    mkAppN (Lean.mkConst ``fast_decode_br7) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0xff000010) == 0x54000000 then
    mkAppN (Lean.mkConst ``fast_decode_br15) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x7e000000) == 0x34000000 then
    mkAppN (Lean.mkConst ``fast_decode_br13) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x3f000000) == 0x38000000 && (wNat &&& 0xffe00c00) != 0xf8800000 && (wNat &&& 0xffe00c00) != 0xf8a00800 && (wNat &&& 0x3f200c00) != 0x38200000 then
    mkAppN (Lean.mkConst ``fast_decode_br35) #[wE, inst, reflTrue, reflFalse, reflFalse, reflFalse, hbody]
  else if (wNat &&& 0x3f000000) == 0x3d000000 then
    mkAppN (Lean.mkConst ``fast_decode_br49) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1f000000) == 0x0a000000 then
    mkAppN (Lean.mkConst ``fast_decode_br17) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x7c000000) == 0x14000000 then
    mkAppN (Lean.mkConst ``fast_decode_br12) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x3f000000) == 0x3c000000 then
    mkAppN (Lean.mkConst ``fast_decode_br50) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x3e000000) == 0x2c000000 && (wNat &&& 0x3f800000) != 0x2c000000 then
    mkAppN (Lean.mkConst ``fast_decode_br48) #[wE, inst, reflTrue, reflFalse, hbody]
  else if (wNat &&& 0x1f800000) == 0x12800000 then
    mkAppN (Lean.mkConst ``fast_decode_br9) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1f200000) == 0x0b000000 then
    mkAppN (Lean.mkConst ``fast_decode_br18) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1f800000) == 0x13000000 then
    mkAppN (Lean.mkConst ``fast_decode_br10) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x7e000000) == 0x36000000 then
    mkAppN (Lean.mkConst ``fast_decode_br14) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1f800000) == 0x12000000 then
    mkAppN (Lean.mkConst ``fast_decode_br8) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x3fe00800) == 0x1a800000 then
    mkAppN (Lean.mkConst ``fast_decode_br22) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x7f000000) == 0x1b000000 then
    mkAppN (Lean.mkConst ``fast_decode_br26) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x7fff0000) == 0x5ac00000 then
    mkAppN (Lean.mkConst ``fast_decode_br23) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1f000000) == 0x10000000 then
    mkAppN (Lean.mkConst ``fast_decode_br6) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x1fe00000) == 0x0b200000 then
    mkAppN (Lean.mkConst ``fast_decode_br19) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0x3fbffc00) == 0x089ffc00 then
    mkAppN (Lean.mkConst ``fast_decode_br38) #[wE, inst, reflTrue, hbody]
  else if (wNat &&& 0xff9ffc1f) == 0xd61f0000 then
    mkAppN (Lean.mkConst ``fast_decode_br16) #[wE, inst, reflTrue, hbody]
  else
    hbody

/-- Fast replacement for `gen_placed_fetches ... [0 → maxOff]`:
    proves extern `.call26`/`.jump26` fetches and relaxable `.adrpHi21`+`.addLo12` `pairStep`s
    directly without `mkDecideProof` or `CodeBlock` unfolding, delegates any rare intra-block
    relocations to `gen_placed_fetches`, and proves all non-relocation instruction fetches via
    64-instruction `RelocTree`-disjoint chunks, per-module deduplicated `_gfd_wdec_<wNat>`
    theorems, and pre-stepped `fast_decode_br*` lemmas. -/
meta def elabFastPlacedFetchesForBlock
    (progId libId treeId hcodeId hsizeId plOfId hPOfId : Ident)
    (nWords : Nat)
    (relocData : Array (Nat × Name × String × Int × Expr))
    (symSet : Std.HashSet String)
    (weakRefsEmpty : Bool) : CommandElabM Unit := do
  let sortedRelocOffs := (relocData.map fun (off, _, _, _, _) => off).qsort (· < ·)
  let mut relocWordSet : Std.HashSet Nat := {}
  let mut relocMap : Std.HashMap Nat (Name × String × Int × Expr) := {}
  for (off, kn, sym, addend, rE) in relocData do
    if !relocMap.contains off then
      relocMap := relocMap.insert off (kn, sym, addend, rE)
    if off % 4 == 0 && off + 4 ≤ 4 * nWords then
      relocWordSet := relocWordSet.insert off

  let relocWordOffs := (relocWordSet.toArray).qsort (· < ·)

  -- Partition aligned in-bounds relocations into direct fast-path vs rare fallback.
  let mut fastBranchOffs : Array (Nat × Bool × String × Expr) := #[]
  let mut fastPairOffs : Array (Nat × String × Int × Expr × Expr) := #[]
  let mut fallbackOffs : Array Nat := #[]
  for off in relocWordOffs do
    if let some (kn, sym, addend, rE) := relocMap.get? off then
      if kn == ``RelocKind.addLo12 || kn == ``RelocKind.ldst8Lo12 ||
          kn == ``RelocKind.ldst16Lo12 || kn == ``RelocKind.ldst32Lo12 ||
          kn == ``RelocKind.ldst64Lo12 then
        pure ()
      else if kn == ``RelocKind.call26 || kn == ``RelocKind.jump26 then
        if weakRefsEmpty && !symSet.contains sym && addend == 0 then
          fastBranchOffs := fastBranchOffs.push (off, kn == ``RelocKind.call26, sym, rE)
        else
          fallbackOffs := fallbackOffs.push off
      else if kn == ``RelocKind.adrpHi21 then
        match relocMap.get? (off + 4) with
        | some (kn2, sym2, add2, r2E) =>
          if kn2 == ``RelocKind.addLo12 && sym == sym2 && addend == add2 then
            if !symSet.contains sym && addend >= 0 && off + 8 ≤ 4 * nWords then
              fastPairOffs := fastPairOffs.push (off, sym, addend, rE, r2E)
            else
              fallbackOffs := fallbackOffs.push off
          else
            pure ()
        | none => pure ()
      else
        fallbackOffs := fallbackOffs.push off

  let mut chunks : Array (Nat × Nat) := #[]
  let mut offChunkIdx : Std.HashMap Nat Nat := {}
  let mut curChunk? : Option (Nat × Nat × Nat) := none
  for j in [0 : nWords] do
    let off := 4 * j
    if relocWordSet.contains off then
      if let some (lo, hi, _) := curChunk? then
        chunks := chunks.push (lo, hi)
        curChunk? := none
    else
      match curChunk? with
      | none =>
        offChunkIdx := offChunkIdx.insert off chunks.size
        curChunk? := some (off, off, 1)
      | some (lo, hi, cnt) =>
        if lo ≤ off && cnt < 64 && !hasRelocInSorted sortedRelocOffs lo off then
          offChunkIdx := offChunkIdx.insert off chunks.size
          curChunk? := some (lo, Nat.max hi off, cnt + 1)
        else
          chunks := chunks.push (lo, hi)
          offChunkIdx := offChunkIdx.insert off chunks.size
          curChunk? := some (off, off, 1)
  if let some (lo, hi, _) := curChunk? then
    chunks := chunks.push (lo, hi)

  let mut moreFallback : Array Nat := #[]
  if !chunks.isEmpty || !fastBranchOffs.isEmpty || !fastPairOffs.isEmpty then
    let attrStx ← `(Lean.Parser.Term.attrInstance| simp)
    let attrStx2 ← `(Lean.Parser.Term.attrInstance| arm64_norm)
    moreFallback ← liftTermElabM do
      let mut fb : Array Nat := #[]
      let attrs ← elabAttrs #[attrStx, attrStx2]
      let progName ← realizeGlobalConstNoOverloadWithInfo progId
      let libName ← realizeGlobalConstNoOverloadWithInfo libId
      let treeName ← realizeGlobalConstNoOverloadWithInfo treeId
      let hcodeName ← realizeGlobalConstNoOverloadWithInfo hcodeId
      let hsizeName ← realizeGlobalConstNoOverloadWithInfo hsizeId
      let plOfE := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo plOfId)
      let hPOfE := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo hPOfId)
      let libE := Lean.mkConst libName
      let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
      let treeE := Lean.mkConst treeName
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      let nE := mkNatLit nWords
      let hcodeE := Lean.mkConst hcodeName
      let hsizeE := Lean.mkConst hsizeName
      let progTy ← inferType (Lean.mkConst progName)
      let .forallE _ paramTy _ paramBi := progTy
        | throwError "elabFastPlacedFetchesForBlock: {progName} must take one parameter"
      let paramLvl ← getLevel paramTy
      let pfxStr := progName.getString!
      let progNs := progName.getPrefix
      let (shRtNm, shRtEqNm, shRtWfNm) := ProofLib.GenPlacedFetches.sharedRelocTreeNames progName
      let rtE := Lean.mkConst shRtNm
      let hrelocsE := Lean.mkConst shRtEqNm
      let hwfE := Lean.mkConst shRtWfNm
      let (shXsNm, shEncNm, shHtblNm, shHeqNm) := ProofLib.GenPlacedFetches.sharedSymEncNames progName
      let shXsE := Lean.mkConst shXsNm
      let shEncE := Lean.mkConst shEncNm
      let shHtblE := Lean.mkConst shHtblNm
      let shHeqE := Lean.mkConst shHeqNm
      let hprogE ← ensureHProg progName paramTy libE plOfE
      let plOfLam := Expr.lam `a paramTy (mkApp plOfE (.bvar 0)) .default
      let hPOfLam := Expr.lam `a paramTy (mkApp hPOfE (.bvar 0)) .default
      let boolTy := Lean.mkConst ``Bool
      let natTy := Lean.mkConst ``Nat
      let intTy := Lean.mkConst ``Int
      let strTy := Lean.mkConst ``String
      let reflBoolTrue := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.true)
      let reflBoolFalse := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy (Lean.mkConst ``Bool.false)
      let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
      let bv32Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
      let bv8Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
      let bv5Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 5)
      let bv8 (k : Nat) := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit k)
      let prodBv8Bv8 := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) bv8Ty bv8Ty
      let prodBv8P2 := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) bv8Ty prodBv8Bv8
      let quadInnerTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) bv8Ty prodBv8P2
      let quadTy := mkApp (Lean.mkConst ``Option [.zero]) quadInnerTy
      let mkSomeQuad (b0 b1 b2 b3 : Nat) : Expr :=
        let p3 := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) bv8Ty bv8Ty (bv8 b2) (bv8 b3)
        let p2 := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) bv8Ty prodBv8Bv8 (bv8 b1) p3
        let p1 := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) bv8Ty prodBv8P2 (bv8 b0) p2
        mkApp2 (Lean.mkConst ``Option.some [.zero]) quadInnerTy p1
      let hookTy ← mkArrow strTy
        (mkApp (Lean.mkConst ``Option [.zero])
          (← mkArrow (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State)))
      let (haddBv64, hsubBv64) ← withLocalDeclD `b bv64 fun b => do
        return ((← mkAppM ``HAdd.hAdd #[b, b]).appFn!.appFn!,
                (← mkAppM ``HSub.hSub #[b, b]).appFn!.appFn!)
      let noOvr ← withLocalDeclD `x strTy fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``Option.none
          #[← mkArrow (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State)])
      let modNm ← getMainModule
      let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) natTy
      let noneNatE := mkApp (Lean.mkConst ``Option.none [.zero]) natTy
      let natListTy := mkApp (Lean.mkConst ``List [.zero]) natTy
      let encKeyTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natListTy
      let tblE := mkApp (Lean.mkConst ``CodeBlock.symbols) textE
      let optRelTy := mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry)
      let relocKindTy := Lean.mkConst ``RelocKind
      let zeroIntE := toExpr (0 : Int)
      let haddZero := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy zeroIntE
      let symNoneCacheRef ← IO.mkRef ({} : Std.HashMap String Expr)

      let getSymNonePrf (sym : String) : TermElabM Expr := do
        let curCache ← symNoneCacheRef.get
        if let some p := curCache.get? sym then
          return p
        let env ← getEnv
        let thmNm := mkPrivateName env (modNm ++ libName ++ Name.mkSimple s!"_gfd_symnone_{sym.hash}_{curCache.size}")
        let symLit := mkStrLit sym
        let csList := sym.toList
        let csE := toExpr csList
        let ekE := toExpr (sym.length, csList.map (fun ch => ch.val.toNat))
        let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symLit
        let hek := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) encKeyTy ekE
        let hlookup := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optNatTy noneNatE
        let lhs ← mkAppM ``Arm64.Obj.lookup #[symLit, tblE]
        let ty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) optNatTy lhs noneNatE
        let val := mkAppN (Lean.mkConst ``lookup_of_enc)
          #[tblE, shXsE, shEncE, shHtblE, shHeqE, symLit, csE, ekE, noneNatE, hname, hek, hlookup]
        addDecl (.thmDecl { name := thmNm, levelParams := [], type := ty, value := val })
        let p := Lean.mkConst thmNm
        symNoneCacheRef.set (curCache.insert sym p)
        return p

      -- 1. Emit extern `.call26` / `.jump26` fetches directly.
      if !fastBranchOffs.isEmpty then
        let hweakNilE ← ensureHWeakNil progName libE
        let hkindCall := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) relocKindTy (Lean.mkConst ``RelocKind.call26)
        let hkindJump := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) relocKindTy (Lean.mkConst ``RelocKind.jump26)
        let hopCall := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty
          (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x94000000))
        let hopJump := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty
          (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit 0x14000000))
        for (off, isCall, sym, rE) in fastBranchOffs do
          let j := off / 4
          let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
          let wNat : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
          let expectedOp := if isCall then 0x94000000 else 0x14000000
          if (wNat &&& 0xfc000000) != expectedOp then
            fb := fb.push off
          else
            let offE := mkNatLit off
            let jE := mkNatLit j
            let symLit := mkStrLit sym
            let hoff4 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy offE
            let someRE := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE
            let hlookupR := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optRelTy someRE
            let hsymE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symLit
            let hsymNone ← getSymNonePrf sym
            let someQuad := mkSomeQuad b0 b1 b2 b3
            let hquad := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) quadTy someQuad
            let thmConst := if isCall then ``fast_fetch_extern_call26 else ``fast_fetch_extern_jump26
            let hkind := if isCall then hkindCall else hkindJump
            let hop := if isCall then hopCall else hopJump
            let corePrf := mkAppN (Lean.mkConst thmConst [paramLvl])
              #[paramTy, Lean.mkConst progName, plOfLam, libE, treeE, nE, rtE,
                hprogE, hPOfLam, hcodeE, hsizeE, hrelocsE, hwfE, hweakNilE, reflBoolTrue,
                offE, jE, rE, symLit, bv8 b0, bv8 b1, bv8 b2, bv8 b3,
                hoff4, reflBoolTrue, hlookupR, hoff4, hkind, haddZero, hsymE, hsymNone, hquad, hop]
            let rPrf :=
              if paramBi == .default then corePrf
              else Expr.lam `a paramTy (mkApp corePrf (.bvar 0)) paramBi
            let plApp := mkApp plOfE (.bvar 2)
            let rho := mkApp2 (Lean.mkConst ``Placement.ρ) plApp symLit
            let baseE := mkApp (Lean.mkConst ``Placement.base) plApp
            let stubE := mkApp2 hsubBv64 rho baseE
            let immE := mkApp2 hsubBv64 stubE (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) offE)
            let inst := mkApp (Lean.mkConst (if isCall then ``Arm64.Instr.bl else ``Arm64.Instr.b)) immE
            let rhs := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``Arm64.Instr) inst
            let pc := mkApp2 haddBv64 (.bvar 1) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) offE)
            let progR := mkApp4 (Lean.mkConst ``Program.rebase)
              (mkApp (Lean.mkConst progName) (.bvar 2)) (.bvar 1) (.bvar 0) noOvr
            let eqBody := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) ProofLib.GenDecodes.optInstr
              (mkApp2 (Lean.mkConst ``Program.fetch) progR pc) rhs
            let rTy := Expr.forallE `a paramTy
              (Expr.forallE `b bv64 (Expr.forallE `X hookTy eqBody .default) .default) paramBi
            let rName := progNs ++ ProofLib.GenPlacedFetches.hexName pfxStr "rebase_fetch" off
            ProofLib.GenDecodes.addThm rName rTy rPrf
            for a in attrs do Term.applyAttributes rName #[a]
            if off == 0 then
              let (bTy, bPrf) ←
                withLocalDecl `a paramBi paramTy fun a =>
                  withLocalDeclD `b bv64 fun b => withLocalDeclD `X hookTy fun X => do
                    let p ← mkAppM ``fetch_rebase_base_of_zero #[mkAppN (Lean.mkConst rName) #[a, b, X]]
                    return (← mkForallFVars #[a, b, X] (← inferType p), ← mkLambdaFVars #[a, b, X] p)
              let bName := progNs ++ Name.mkSimple s!"{pfxStr}_rebase_fetch_base"
              ProofLib.GenDecodes.addThm bName bTy bPrf
              for a in attrs do Term.applyAttributes bName #[a]

      -- 2. Emit extern relaxable `.adrpHi21`+`.addLo12` `pairStep`s directly.
      for (off, sym, addend, r1E, r2E) in fastPairOffs do
        let j := off / 4
        let j1 := j + 1
        let off4 := off + 4
        let off8 := off + 8
        let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
        let (c0, c1, c2, c3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off4
        let w0 : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
        let w1 : Nat := c0 ||| (c1 <<< 8) ||| (c2 <<< 16) ||| (c3 <<< 24)
        let rd := w0 % 32
        if !(w0 &&& 0x9f000000 == 0x90000000 && w1 &&& 0xffc00000 == 0x91000000 &&
            w1 % 32 == rd && (w1 >>> 5) % 32 == rd && rd != 31) then
          pure ()
        else
          let offE := mkNatLit off
          let off4E := mkNatLit off4
          let off8E := mkNatLit off8
          let jE := mkNatLit j
          let j1E := mkNatLit j1
          let symLit := mkStrLit sym
          let rdE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rd)
          let hoff := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy offE
          let hoff4 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy off4E
          let hoff8 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy off8E
          let someR1 := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) r1E
          let someR2 := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) r2E
          let hr1 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optRelTy someR1
          let hr2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optRelTy someR2
          let hq0 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) quadTy (mkSomeQuad b0 b1 b2 b3)
          let hq1 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) quadTy (mkSomeQuad c0 c1 c2 c3)
          let hsym1 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symLit
          let hsymNone ← getSymNonePrf sym
          let hrd := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv5Ty rdE
          let corePrf :=
            if addend == 0 then
              mkAppN (Lean.mkConst ``fast_pairStep_extern_zero [paramLvl])
                #[paramTy, Lean.mkConst progName, plOfLam, libE, treeE, nE, rtE,
                  hprogE, hPOfLam, hcodeE, hsizeE, hrelocsE, hwfE,
                  offE, off4E, off8E, jE, j1E, r1E, r2E, symLit, rdE,
                  bv8 b0, bv8 b1, bv8 b2, bv8 b3, bv8 c0, bv8 c1, bv8 c2, bv8 c3,
                  hoff, hoff4, hoff4, hoff8, reflBoolTrue, reflBoolTrue,
                  hr1, hr2, hq0, hq1, hsym1, hsym1, hsymNone, haddZero, reflBoolTrue, hrd, reflBoolTrue]
            else
              let kNat := addend.toNat
              let kE := mkNatLit kNat
              let haddPos := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy (toExpr addend)
              mkAppN (Lean.mkConst ``fast_pairStep_extern_pos [paramLvl])
                #[paramTy, Lean.mkConst progName, plOfLam, libE, treeE, nE, rtE,
                  hprogE, hPOfLam, hcodeE, hsizeE, hrelocsE, hwfE,
                  offE, off4E, off8E, jE, j1E, kE, r1E, r2E, symLit, rdE,
                  bv8 b0, bv8 b1, bv8 b2, bv8 b3, bv8 c0, bv8 c1, bv8 c2, bv8 c3,
                  hoff, hoff4, hoff4, hoff8, reflBoolTrue, reflBoolTrue,
                  hr1, hr2, hq0, hq1, hsym1, hsym1, hsymNone, haddPos, reflBoolFalse, reflBoolTrue, hrd, reflBoolTrue]
          let .forallE anm aty abody _ ← inferType corePrf
            | throwError "elabFastPlacedFetchesForBlock: unexpected pairStep type"
          let pTy := Expr.forallE anm aty abody paramBi
          let pPrf :=
            if paramBi == .default then corePrf
            else Expr.lam anm aty (mkApp corePrf (.bvar 0)) paramBi
          let pName := progNs ++ ProofLib.GenPlacedFetches.hexName pfxStr "pairStep" off
          ProofLib.GenDecodes.addThm pName pTy pPrf

      -- 3. Emit non-relocation instruction fetches via 64-instruction `RelocTree`-disjoint chunks.
      let mut chunkThms : Array Name := #[]
      for h : ci in [0 : chunks.size] do
        let (lo, hi) := chunks[ci]
        let chunkNm ← mkPrivChunkHelperName progNs pfxStr s!"chunk_{ci}"
        let chunkVal := mkAppN (Lean.mkConst ``fetch_rebase_of_chunk_placeable_tree [paramLvl])
          #[paramTy, Lean.mkConst progName, plOfLam, libE, treeE, nE, rtE,
            mkNatLit lo, mkNatLit hi, hprogE, hPOfLam, hcodeE, hsizeE, hrelocsE, hwfE,
            reflBoolTrue, reflBoolTrue]
        let chunkTy ← inferType chunkVal
        addDecl (.thmDecl { name := chunkNm, levelParams := [], type := chunkTy, value := chunkVal })
        chunkThms := chunkThms.push chunkNm

      let mut localWordCache : Std.HashMap Nat (Name × Expr) := {}
      for j in [0 : nWords] do
        let off := 4 * j
        if relocWordSet.contains off then
          continue
        let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
        let wNat : Nat := b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
        let wE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit wNat)
        let (wThmNm, rhs) ← match localWordCache.get? wNat with
          | some p => pure p
          | none =>
            let env ← getEnv
            let wNm := mkPrivateName env (modNm ++ Name.mkSimple s!"_gfd_wdec_{wNat}")
            match env.find? wNm with
            | some ci =>
              let rhs := ci.type.appArg!
              localWordCache := localWordCache.insert wNat (wNm, rhs)
              pure (wNm, rhs)
            | none =>
              let some instrVal := Arm64.decode (BitVec.ofNat 32 wNat)
                | pure (Name.anonymous, Expr.bvar 0)
              let rhs ← ProofLib.GenDecodes.formatInstrRhs instrVal false
              let inst := rhs.appArg!
              let wPrf := mkFastWordDecodeProof wNat wE inst rhs
              let wTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) ProofLib.GenDecodes.optInstr
                (mkApp (Lean.mkConst ``Arm64.decode) wE) rhs
              addDecl (.thmDecl { name := wNm, levelParams := [], type := wTy, value := wPrf })
              localWordCache := localWordCache.insert wNat (wNm, rhs)
              pure (wNm, rhs)
        if wThmNm.isAnonymous then
          continue
        let inst := rhs.appArg!
        let offE := mkNatLit off
        let hw := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty wE
        let hdecQuad := mkAppN (Lean.mkConst ``decode_quad_of_word)
          #[bv8 b0, bv8 b1, bv8 b2, bv8 b3, wE, inst, hw, Lean.mkConst wThmNm]
        let someQuad := mkSomeQuad b0 b1 b2 b3
        let hquad := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) quadTy someQuad
        let hoff := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy offE
        let hdec := mkAppN (Lean.mkConst ``fetchDecodeAt_of_quad_decode)
          #[treeE, offE, mkNatLit j, bv8 b0, bv8 b1, bv8 b2, bv8 b3, inst, hoff, hquad, hdecQuad]
        let chunkNm := chunkThms[offChunkIdx.get! off]!
        let corePrf := mkApp4 (Lean.mkConst chunkNm) offE inst reflBoolTrue hdec
        let rPrf :=
          if paramBi == .default then corePrf
          else Expr.lam `a paramTy (mkApp corePrf (.bvar 0)) paramBi
        let pc := mkApp2 haddBv64 (.bvar 1) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) offE)
        let progR := mkApp4 (Lean.mkConst ``Program.rebase)
          (mkApp (Lean.mkConst progName) (.bvar 2)) (.bvar 1) (.bvar 0) noOvr
        let eqBody := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) ProofLib.GenDecodes.optInstr
          (mkApp2 (Lean.mkConst ``Program.fetch) progR pc) rhs
        let rTy := Expr.forallE `a paramTy
          (Expr.forallE `b bv64 (Expr.forallE `X hookTy eqBody .default) .default) paramBi
        let rName := progNs ++ ProofLib.GenPlacedFetches.hexName pfxStr "rebase_fetch" off
        ProofLib.GenDecodes.addThm rName rTy rPrf
        for a in attrs do Term.applyAttributes rName #[a]
        if off == 0 then
          let (bTy, bPrf) ←
            withLocalDecl `a paramBi paramTy fun a =>
              withLocalDeclD `b bv64 fun b => withLocalDeclD `X hookTy fun X => do
                let p ← mkAppM ``fetch_rebase_base_of_zero #[mkAppN (Lean.mkConst rName) #[a, b, X]]
                return (← mkForallFVars #[a, b, X] (← inferType p), ← mkLambdaFVars #[a, b, X] p)
          let bName := progNs ++ Name.mkSimple s!"{pfxStr}_rebase_fetch_base"
          ProofLib.GenDecodes.addThm bName bTy bPrf
          for a in attrs do Term.applyAttributes bName #[a]
      return fb

  let allFallback := (fallbackOffs ++ moreFallback).qsort (· < ·)
  if !allFallback.isEmpty then
    let ranges ← allFallback.mapM fun off => do
      let lit := Syntax.mkNumLit (toString off)
      `(decodeRange| $lit:num)
    let rangesSep : Syntax.TSepArray `decodeRange "," := Syntax.TSepArray.ofElems ranges
    elabCommand (← `(command|
      gen_placed_fetches $progId:ident $libId:ident $treeId:ident $hcodeId:ident $hsizeId:ident
        via_placement $plOfId:ident $hPOfId:ident [$rangesSep,*]
    ))

end MetaFastDecode

end LibsignalBinary.Proofs.Placed.FastDecode
