/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
meta import ProofLib.StdStartup.StdDetect
import Arm64.Trusted.ISA.Eval
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Key-Schedule Helper Contracts (`Fixslice64.KsHelpers`)

Minimal-footprint `subroutine_ok` contracts for `libaes` (`aes::soft::fixslice64`) key-schedule
helpers:
- `memshift32` (`65` reachable instructions / `79` total words, `16` B stack): copies one 8-word
  `Model.FsState` slice block from `base + 8 * srcIdx` to `base + 8 * (srcIdx + 8)`.
- `xor_columns` (`175` reachable instructions / `200` total words, `16` B stack): updates the
  8-word `Model.FsState` slice block at `base + 8 * offset` in place to
  `Model.xorColumnsFs prev cur idxRor`, reading `prev` at `base + 8 * (offset - idxXor)`.

Both functions have **zero relocations** in their reachable prefixes (`0..64` and `0..174`),
with all `ADRP + ADD + BL` panic-handler relocations confined to unreachable tail blocks
(`65..78` and `175..199`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj adrpAddPair hasInstrs_prefix fsStateAt
   memRegion64_eq_exists_fsStateAt)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

/-! ## 1. `fixslice64::memshift32` Instruction Words & Template Equivalence -/

/-- Reachable 65-word prefix (`0x000..0x100`, ending at `ret`) of `fixslice64::memshift32`
    (zero relocations). -/
@[expose] def memshift32ReachableWords : List (BitVec 32) :=
  [0xa9bf7bfd#32, 0x910003fd#32, 0xb100205f#32, 0x54000822#32, 0x91001c49#32,
   0xeb01013f#32, 0x54000822#32, 0xaa0003e8#32, 0x9100204a#32, 0x91003c40#32,
   0xeb0a001f#32, 0x540006c3#32, 0xeb01001f#32, 0x540007e2#32, 0xf8697909#32,
   0xf8207909#32, 0x91003840#32, 0xeb0a001f#32, 0x540005e3#32, 0xeb01001f#32,
   0x54000702#32, 0x8b020d09#32, 0xf940192b#32, 0xf820790b#32, 0x91003440#32,
   0xeb0a001f#32, 0x540004e3#32, 0xeb01001f#32, 0x54000602#32, 0xf940152b#32,
   0xf820790b#32, 0x91003040#32, 0xeb0a001f#32, 0x54000403#32, 0xeb01001f#32,
   0x54000522#32, 0xf940112b#32, 0xf820790b#32, 0x91002c40#32, 0xeb0a001f#32,
   0x54000323#32, 0xeb01001f#32, 0x54000442#32, 0xf9400d2b#32, 0xf820790b#32,
   0x91002840#32, 0xeb0a001f#32, 0x54000243#32, 0xeb01001f#32, 0x54000362#32,
   0xf940092b#32, 0xf820790b#32, 0x91002440#32, 0xeb0a001f#32, 0x54000163#32,
   0xeb01001f#32, 0x54000282#32, 0xf9400529#32, 0xeb01015f#32, 0xf8207909#32,
   0x540001e2#32, 0xf8627909#32, 0xf82a7909#32, 0xa8c17bfd#32, 0xd65f03c0#32]

/-- Decoded 65-instruction reachable prefix of `fixslice64::memshift32`. -/
@[expose] def memshift32ReachableInstrs : List Instr :=
  decodeWords memshift32ReachableWords

/-- Complete 79-word unrelocated `.rlib` template of `fixslice64::memshift32` (`0x000..0x138`). -/
@[expose] def memshift32TemplateWords : List (BitVec 32) :=
  memshift32ReachableWords ++
  [0x90000000#32, 0x91000000#32, 0x94000000#32, 0x90000000#32, 0x91000000#32,
   0x94000000#32, 0x90000002#32, 0x91000042#32, 0xaa0903e0#32, 0x94000000#32,
   0xaa0a03e0#32, 0x90000002#32, 0x91000042#32, 0x94000000#32]

/-- Relocation parameters for the unreachable panic tail (`0x104..0x138`) of `memshift32`. -/
structure Memshift32PanicSyms where
  fnAddr : BitVec 64
  locAddOverflow3 : BitVec 64
  locAddOverflow1 : BitVec 64
  locBounds2 : BitVec 64
  locBounds4 : BitVec 64
  callAddOverflow3 : BitVec 64
  callAddOverflow1 : BitVec 64
  callBounds2 : BitVec 64
  callBounds4 : BitVec 64
  relaxAddOverflow3 : Bool := false
  relaxAddOverflow1 : Bool := false
  relaxBounds2 : Bool := false
  relaxBounds4 : Bool := false

/-- Construct `Memshift32PanicSyms` for a linked image where the two `panic_const_add_overflow`
    calls share one target and the two `panic_bounds_check` calls share one target. -/
@[expose] def Memshift32PanicSyms.linked
    (fnAddr loc3 loc1 loc2 loc4 panicAddOverflow panicBoundsCheck : BitVec 64)
    (relax3 relax1 relax2 relax4 : Bool := false) : Memshift32PanicSyms :=
  { fnAddr := fnAddr
    locAddOverflow3 := loc3
    locAddOverflow1 := loc1
    locBounds2 := loc2
    locBounds4 := loc4
    callAddOverflow3 := panicAddOverflow
    callAddOverflow1 := panicAddOverflow
    callBounds2 := panicBoundsCheck
    callBounds4 := panicBoundsCheck
    relaxAddOverflow3 := relax3
    relaxAddOverflow1 := relax1
    relaxBounds2 := relax2
    relaxBounds4 := relax4 }

/-- Zero-relocation `.rlib` template instance of `Memshift32PanicSyms` at `fnAddr`
    (with page-base `.rodata` targets and zero-displacement `BL` targets). -/
@[expose] def Memshift32PanicSyms.template (fnAddr : BitVec 64 := 0#64) : Memshift32PanicSyms :=
  let page := fnAddr &&& 0xfffffffffffff000#64
  { fnAddr := fnAddr
    locAddOverflow3 := page
    locAddOverflow1 := page
    locBounds2 := page
    locBounds4 := page
    callAddOverflow3 := fnAddr + 0x10c#64
    callAddOverflow1 := fnAddr + 0x118#64
    callBounds2 := fnAddr + 0x128#64
    callBounds4 := fnAddr + 0x138#64 }

/-- Unreachable 14-instruction panic tail (`0x104..0x138`) of `fixslice64::memshift32`. -/
@[expose] def memshift32PanicTail (p : Memshift32PanicSyms) : List Instr :=
  adrpAddPair (.gpr 0#5) (p.fnAddr + 0x104#64) p.locAddOverflow3 p.relaxAddOverflow3 ++
  [ .bl (p.callAddOverflow3 - (p.fnAddr + 0x10c#64)) ] ++
  adrpAddPair (.gpr 0#5) (p.fnAddr + 0x110#64) p.locAddOverflow1 p.relaxAddOverflow1 ++
  [ .bl (p.callAddOverflow1 - (p.fnAddr + 0x118#64)) ] ++
  adrpAddPair (.gpr 2#5) (p.fnAddr + 0x11c#64) p.locBounds2 p.relaxBounds2 ++
  [ decodeWord 0xaa0903e0#32,
    .bl (p.callBounds2 - (p.fnAddr + 0x128#64)),
    decodeWord 0xaa0a03e0#32 ] ++
  adrpAddPair (.gpr 2#5) (p.fnAddr + 0x130#64) p.locBounds4 p.relaxBounds4 ++
  [ .bl (p.callBounds4 - (p.fnAddr + 0x138#64)) ]

/-- Full 79-instruction list of `fixslice64::memshift32` (reachable prefix + panic tail). -/
@[expose] def memshift32FullInstrs (p : Memshift32PanicSyms) : List Instr :=
  memshift32ReachableInstrs ++ memshift32PanicTail p

private theorem map_decode_eq_map_some {ws : List (BitVec 32)}
    (h : (ws.all fun w => (Arm64.decode w).isSome) = true) :
    ws.map Arm64.decode = (decodeWords ws).map some := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, decodeWords, decodeWord]
    cases hd : Arm64.decode w with
    | none => simp [hd] at h
    | some i => exact congrArg (some i :: ·) (ih h.2)

/-- At `fnAddr = 0#64` with unpatched relocations, `memshift32FullInstrs` matches the exact 79
    words of `memshift32` in `libaes.rlib`. -/
theorem memshift32FullInstrs_template_eq :
    memshift32TemplateWords.map Arm64.decode =
      (memshift32FullInstrs (Memshift32PanicSyms.template 0#64)).map some := by
  simp only [memshift32TemplateWords, memshift32FullInstrs, memshift32ReachableInstrs,
    List.map_append]
  exact congrArg₂ (· ++ ·) (map_decode_eq_map_some (by decide)) (by decide)

/-! ## 2. `fixslice64::xor_columns` Instruction Words & Template Equivalence -/

/-- Reachable 175-word prefix (`0x000..0x2b8`, ending at `ret`) of `fixslice64::xor_columns`
    (zero relocations). -/
@[expose] def xorColumnsReachableWords : List (BitVec 32) :=
  [0xa9bf7bfd#32, 0x910003fd#32, 0xeb020028#32, 0x9a8833e9#32, 0xeb030048#32,
   0x54001743#32, 0xeb01011f#32, 0x54001502#32, 0xeb02003f#32, 0x54001749#32,
   0xf862780b#32, 0x2a0403ea#32, 0xf8687808#32, 0x9aca2d6b#32, 0x92008d6b#32,
   0xca08016c#32, 0x9100044b#32, 0xd37ced88#32, 0xd378dd8d#32, 0xd374cd8e#32,
   0x920cad0f#32, 0x92089dad#32, 0x92048dce#32, 0xcb030168#32, 0xca0f01ad#32,
   0xca0c01cc#32, 0xeb01011f#32, 0xca0c01ac#32, 0xf822780c#32, 0x54001242#32,
   0xf100053f#32, 0x54001280#32, 0xf86b780c#32, 0xf8687808#32, 0x9aca2d8c#32,
   0x92008d8c#32, 0xca08018d#32, 0x9100084c#32, 0xd37ceda8#32, 0xd378ddae#32,
   0xd374cdaf#32, 0x920cad10#32, 0x92089dce#32, 0x92048def#32, 0xcb030188#32,
   0xca1001ce#32, 0xca0d01ed#32, 0xeb01011f#32, 0xca0d01cd#32, 0xf82b780d#32,
   0x54000fa2#32, 0xf100093f#32, 0x540010a0#32, 0xf86c780b#32, 0xf8687808#32,
   0x9aca2d6b#32, 0x92008d6b#32, 0xca08016d#32, 0x91000c4b#32, 0xd37ceda8#32,
   0xd378ddae#32, 0xd374cdaf#32, 0x920cad10#32, 0x92089dce#32, 0x92048def#32,
   0xcb030168#32, 0xca1001ce#32, 0xca0d01ed#32, 0xeb01011f#32, 0xca0d01cd#32,
   0xf82c780d#32, 0x54000d02#32, 0xf1000d3f#32, 0x54000d40#32, 0xf86b780c#32,
   0xf8687808#32, 0x9aca2d8c#32, 0x92008d8c#32, 0xca08018d#32, 0x9100104c#32,
   0xd37ceda8#32, 0xd378ddae#32, 0xd374cdaf#32, 0x920cad10#32, 0x92089dce#32,
   0x92048def#32, 0xcb030188#32, 0xca1001ce#32, 0xca0d01ed#32, 0xeb01011f#32,
   0xca0d01cd#32, 0xf82b780d#32, 0x54000a62#32, 0xf100113f#32, 0x54000b60#32,
   0xf86c780b#32, 0xf8687808#32, 0x9aca2d6b#32, 0x92008d6b#32, 0xca08016d#32,
   0x9100144b#32, 0xd37ceda8#32, 0xd378ddae#32, 0xd374cdaf#32, 0x920cad10#32,
   0x92089dce#32, 0x92048def#32, 0xcb030168#32, 0xca1001ce#32, 0xca0d01ed#32,
   0xeb01011f#32, 0xca0d01cd#32, 0xf82c780d#32, 0x540007c2#32, 0xf100153f#32,
   0x54000800#32, 0xf86b780c#32, 0xf8687808#32, 0x9aca2d8c#32, 0x92008d8c#32,
   0xca08018d#32, 0x9100184c#32, 0xd37ceda8#32, 0xd378ddae#32, 0xd374cdaf#32,
   0x920cad10#32, 0x92089dce#32, 0x92048def#32, 0xcb030188#32, 0xca1001ce#32,
   0xca0d01ed#32, 0xeb01011f#32, 0xca0d01cd#32, 0xf82b780d#32, 0x54000522#32,
   0xf100193f#32, 0x54000740#32, 0xf86c780b#32, 0xf8687808#32, 0x91001c42#32,
   0x9aca2d6b#32, 0x92008d6b#32, 0xca08016b#32, 0xd37ced68#32, 0xd378dd6d#32,
   0xd374cd6e#32, 0x920cad0f#32, 0x92089dad#32, 0x92048dce#32, 0xcb030048#32,
   0xca0f01ad#32, 0xca0b01cb#32, 0xeb01011f#32, 0xca0b01ab#32, 0xf82c780b#32,
   0x54000282#32, 0xf1001d3f#32, 0x540004c0#32, 0xf8627809#32, 0xf8687808#32,
   0x9aca2d29#32, 0x92008d29#32, 0xca080128#32, 0xd37ced09#32, 0xd378dd0a#32,
   0xd374cd0b#32, 0x920cad29#32, 0x92089d4a#32, 0x92048d6b#32, 0xca090149#32,
   0xca080168#32, 0xca080128#32, 0xf8227808#32, 0xa8c17bfd#32, 0xd65f03c0#32]

/-- Decoded 175-instruction reachable prefix of `fixslice64::xor_columns`. -/
@[expose] def xorColumnsReachableInstrs : List Instr :=
  decodeWords xorColumnsReachableWords

/-- Complete 200-word unrelocated `.rlib` template of `fixslice64::xor_columns` (`0x000..0x31c`). -/
@[expose] def xorColumnsTemplateWords : List (BitVec 32) :=
  xorColumnsReachableWords ++
  [0x90000002#32, 0x91000042#32, 0xaa0803e0#32, 0x94000000#32, 0xaa0b03e2#32,
   0x90000008#32, 0x91000108#32, 0xaa0203e0#32, 0xaa0803e2#32, 0x94000000#32,
   0xaa0c03e2#32, 0x90000008#32, 0x91000108#32, 0xaa0203e0#32, 0xaa0803e2#32,
   0x94000000#32, 0x90000000#32, 0x91000000#32, 0x94000000#32, 0xaa0c03e2#32,
   0x90000008#32, 0x91000108#32, 0xaa0203e0#32, 0xaa0803e2#32, 0x94000000#32]

/-- Relocation parameters for the unreachable panic tail (`0x2bc..0x31c`) of `xor_columns`. -/
structure XorColumnsPanicSyms where
  fnAddr : BitVec 64
  locBounds6 : BitVec 64
  locBounds7a : BitVec 64
  locBounds7b : BitVec 64
  locSubOverflow5 : BitVec 64
  locBounds7c : BitVec 64
  callBounds6 : BitVec 64
  callBounds7a : BitVec 64
  callBounds7b : BitVec 64
  callSubOverflow5 : BitVec 64
  callBounds7c : BitVec 64
  relaxBounds6 : Bool := false
  relaxBounds7a : Bool := false
  relaxBounds7b : Bool := false
  relaxSubOverflow5 : Bool := false
  relaxBounds7c : Bool := false

/-- Construct `XorColumnsPanicSyms` for a linked image where the three `.Lanon...7` sites share
    `loc7` and the four `panic_bounds_check` calls share `panicBoundsCheck`. -/
@[expose] def XorColumnsPanicSyms.linked
    (fnAddr loc6 loc7 loc5 panicBoundsCheck panicSubOverflow : BitVec 64)
    (relax6 relax7a relax7b relax5 relax7c : Bool := false) : XorColumnsPanicSyms :=
  { fnAddr := fnAddr
    locBounds6 := loc6
    locBounds7a := loc7
    locBounds7b := loc7
    locSubOverflow5 := loc5
    locBounds7c := loc7
    callBounds6 := panicBoundsCheck
    callBounds7a := panicBoundsCheck
    callBounds7b := panicBoundsCheck
    callSubOverflow5 := panicSubOverflow
    callBounds7c := panicBoundsCheck
    relaxBounds6 := relax6
    relaxBounds7a := relax7a
    relaxBounds7b := relax7b
    relaxSubOverflow5 := relax5
    relaxBounds7c := relax7c }

/-- Zero-relocation `.rlib` template instance of `XorColumnsPanicSyms` at `fnAddr`. -/
@[expose] def XorColumnsPanicSyms.template (fnAddr : BitVec 64 := 0#64) : XorColumnsPanicSyms :=
  let page := fnAddr &&& 0xfffffffffffff000#64
  { fnAddr := fnAddr
    locBounds6 := page
    locBounds7a := page
    locBounds7b := page
    locSubOverflow5 := page
    locBounds7c := page
    callBounds6 := fnAddr + 0x2c8#64
    callBounds7a := fnAddr + 0x2e0#64
    callBounds7b := fnAddr + 0x2f8#64
    callSubOverflow5 := fnAddr + 0x304#64
    callBounds7c := fnAddr + 0x31c#64 }

/-- Unreachable 25-instruction panic tail (`0x2bc..0x31c`) of `fixslice64::xor_columns`. -/
@[expose] def xorColumnsPanicTail (p : XorColumnsPanicSyms) : List Instr :=
  adrpAddPair (.gpr 2#5) (p.fnAddr + 0x2bc#64) p.locBounds6 p.relaxBounds6 ++
  [ decodeWord 0xaa0803e0#32,
    .bl (p.callBounds6 - (p.fnAddr + 0x2c8#64)),
    decodeWord 0xaa0b03e2#32 ] ++
  adrpAddPair (.gpr 8#5) (p.fnAddr + 0x2d0#64) p.locBounds7a p.relaxBounds7a ++
  [ decodeWord 0xaa0203e0#32,
    decodeWord 0xaa0803e2#32,
    .bl (p.callBounds7a - (p.fnAddr + 0x2e0#64)),
    decodeWord 0xaa0c03e2#32 ] ++
  adrpAddPair (.gpr 8#5) (p.fnAddr + 0x2e8#64) p.locBounds7b p.relaxBounds7b ++
  [ decodeWord 0xaa0203e0#32,
    decodeWord 0xaa0803e2#32,
    .bl (p.callBounds7b - (p.fnAddr + 0x2f8#64)) ] ++
  adrpAddPair (.gpr 0#5) (p.fnAddr + 0x2fc#64) p.locSubOverflow5 p.relaxSubOverflow5 ++
  [ .bl (p.callSubOverflow5 - (p.fnAddr + 0x304#64)),
    decodeWord 0xaa0c03e2#32 ] ++
  adrpAddPair (.gpr 8#5) (p.fnAddr + 0x30c#64) p.locBounds7c p.relaxBounds7c ++
  [ decodeWord 0xaa0203e0#32,
    decodeWord 0xaa0803e2#32,
    .bl (p.callBounds7c - (p.fnAddr + 0x31c#64)) ]

/-- Full 200-instruction list of `fixslice64::xor_columns` (reachable prefix + panic tail). -/
@[expose] def xorColumnsFullInstrs (p : XorColumnsPanicSyms) : List Instr :=
  xorColumnsReachableInstrs ++ xorColumnsPanicTail p

/-- At `fnAddr = 0#64` with unpatched relocations, `xorColumnsFullInstrs` matches the exact 200
    words of `xor_columns` in `libaes.rlib`. -/
theorem xorColumnsFullInstrs_template_eq :
    xorColumnsTemplateWords.map Arm64.decode =
      (xorColumnsFullInstrs (XorColumnsPanicSyms.template 0#64)).map some := by
  simp only [xorColumnsTemplateWords, xorColumnsFullInstrs, xorColumnsReachableInstrs,
    List.map_append]
  exact congrArg₂ (· ++ ·) (map_decode_eq_map_some (by decide)) (by decide)

/-! ## 3. Minimal-Footprint Specifications -/

/-- Minimal 2-`fsStateAt`-footprint contract for `fixslice64::memshift32`:
    copies the 8-word `Model.FsState` at `base + 8 * srcIdx` to `base + 8 * (srcIdx + 8)`. -/
@[expose] def memshift32Spec : Spec (BitVec 64 × Nat × Nat × Model.FsState) where
  pre := fun (base, len, srcIdx, stSrc) s0 =>
    ⌜s0.readReg64 .x0 = base ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 len ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 srcIdx ∧
      srcIdx + 16 ≤ len ∧ 8 * (srcIdx + 16) < 2 ^ 64 ∧ len < 2 ^ 64⌝ ∗
      (fsStateAt (base + BitVec.ofNat 64 (8 * srcIdx)) stSrc ∗
       memRegion (base + BitVec.ofNat 64 (8 * (srcIdx + 8))) 64 ∗
       stackFrameAt s0.sp 16)
  post := fun (base, _len, srcIdx, stSrc) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
      (fsStateAt (base + BitVec.ofNat 64 (8 * srcIdx)) stSrc ∗
       fsStateAt (base + BitVec.ofNat 64 (8 * (srcIdx + 8))) stSrc ∗
       stackFrameAt s0.sp 16)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Minimal 2-`fsStateAt`-footprint contract for `fixslice64::xor_columns`:
    updates `cur` at `base + 8 * offset` in place to `Model.xorColumnsFs prev cur idxRor`,
    preserving `prev` at `base + 8 * (offset - idxXor)`. -/
@[expose] def xorColumnsSpec :
    Spec (BitVec 64 × Nat × Nat × Nat × Nat × Model.FsState × Model.FsState) where
  pre := fun (base, len, offset, idxXor, idxRor, prev, cur) s0 =>
    ⌜s0.readReg64 .x0 = base ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 len ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 offset ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 idxXor ∧
      s0.readReg32 .x4 = BitVec.ofNat 32 idxRor ∧
      8 ≤ idxXor ∧ idxXor ≤ offset ∧ offset + 8 ≤ len ∧
      8 * (offset + 8) < 2 ^ 64 ∧ len < 2 ^ 64 ∧ idxRor < 64⌝ ∗
      (fsStateAt (base + BitVec.ofNat 64 (8 * (offset - idxXor))) prev ∗
       fsStateAt (base + BitVec.ofNat 64 (8 * offset)) cur ∗
       stackFrameAt s0.sp 16)
  post := fun (base, _len, offset, idxXor, idxRor, prev, cur) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
      (fsStateAt (base + BitVec.ofNat 64 (8 * (offset - idxXor))) prev ∗
       fsStateAt (base + BitVec.ofNat 64 (8 * offset)) (Model.xorColumnsFs prev cur idxRor) ∗
       stackFrameAt s0.sp 16)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 4. Shared Arithmetic & Memory-Address Lemmas -/

private theorem fsStateAt_src_shift (ptr : BitVec 64) (srcIdx : Nat) (st : Model.FsState) :
    fsStateAt (ptr + BitVec.ofNat 64 (8 * srcIdx)) st =
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3)) ↦₆₄ st.s0) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 8#64) ↦₆₄ st.s1) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 16#64) ↦₆₄ st.s2) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 24#64) ↦₆₄ st.s3) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 32#64) ↦₆₄ st.s4) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 40#64) ↦₆₄ st.s5) ∗
      ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 48#64) ↦₆₄ st.s6) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 7#64) <<< 3)) ↦₆₄ st.s7) := by
  unfold fsStateAt
  rw [(show ptr + BitVec.ofNat 64 (8 * srcIdx) + 56#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 7#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * srcIdx) =
        ptr + (BitVec.ofNat 64 srcIdx <<< 3) by bv_lin)]

private theorem fsStateAt_dst_shift (ptr : BitVec 64) (srcIdx : Nat) (st : Model.FsState) :
    fsStateAt (ptr + BitVec.ofNat 64 (8 * (srcIdx + 8))) st =
      ((ptr + ((BitVec.ofNat 64 srcIdx + 8#64) <<< 3)) ↦₆₄ st.s0) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 9#64) <<< 3)) ↦₆₄ st.s1) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 10#64) <<< 3)) ↦₆₄ st.s2) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 11#64) <<< 3)) ↦₆₄ st.s3) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 12#64) <<< 3)) ↦₆₄ st.s4) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 13#64) <<< 3)) ↦₆₄ st.s5) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 14#64) <<< 3)) ↦₆₄ st.s6) ∗
      ((ptr + ((BitVec.ofNat 64 srcIdx + 15#64) <<< 3)) ↦₆₄ st.s7) := by
  unfold fsStateAt
  rw [(show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 8#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 9#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 16#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 10#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 24#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 11#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 32#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 12#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 40#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 13#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 48#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 14#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) + 56#64 =
        ptr + ((BitVec.ofNat 64 srcIdx + 15#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * (srcIdx + 8)) =
        ptr + ((BitVec.ofNat 64 srcIdx + 8#64) <<< 3) by bv_lin)]

private theorem stackFrameAt_16 (sp : BitVec 64) :
    stackFrameAt sp 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem post_two_fs_stack16 {A B : SepProp} (sp fp0 lr0 : BitVec 64) :
    A ∗ B ∗ (((sp - 16#64) ↦₆₄ fp0) ∗ ((sp - 8#64) ↦₆₄ lr0)) ⊢
      A ∗ B ∗ stackFrameAt sp 16 := by
  rw [stackFrameAt_16 sp]
  exact sepConj_mono_right (sepConj_mono_right
    (Entails.sepExists_right fp0 (Entails.sepExists_right lr0 (by sep_entail))))

private def Gpr19To28Preserved (s0 sf : State) : Prop :=
  sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) ∧
  sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) ∧
  sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  pureStepProj sf = pureStepProj s0 ∧
  sf.mem.perm = s0.mem.perm

private theorem Gpr19To28Preserved.trans {s0 s1 s2 : State}
    (h01 : Gpr19To28Preserved s0 s1) (h12 : Gpr19To28Preserved s1 s2) :
    Gpr19To28Preserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem Gpr19To28Preserved.calleeSaved {s0 sf : State}
    (h : Gpr19To28Preserved s0 sf) (hfp : sf.readReg64 Reg.fp = s0.readReg64 Reg.fp) :
    CalleeSavedPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   hfp, h.2.2.2.2.2.2.2.2.2.2.1⟩

private theorem Gpr19To28Preserved.pureStep {s0 sf : State} (h : Gpr19To28Preserved s0 sf) :
    PureStepPreserved s0 sf :=
  PureStepPreserved.of_proj_perm h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2

private theorem finish_sepwp_done {P : Program} {s0 s_mid sf : State} {Q R : SepProp}
    {Post : State → SepProp} {oom : State → SepProp}
    (hpc : sf.pc = s0.readReg64 .lr) (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp) (hfp : sf.readReg64 Reg.fp = s0.readReg64 Reg.fp)
    (hrel : Gpr19To28Preserved s0 s_mid) (hstep : Gpr19To28Preserved s_mid sf)
    (hpost : sf.mem ⊨ Q ∗ R → PureStepPreserved s0 sf → sf.mem ⊨ Post sf ∗ R) :
    SepWP P (s0.readReg64 .lr) sf Q
      (fun sf' Q' => (sf'.mem ⊨ Q' ∗ R → sf'.mem ⊨ Post sf' ∗ R) ∧
        sf'.sp = s0.sp ∧ CalleeSavedPreserved s0 sf') oom :=
  SepWP.done hpc hrun ⟨fun hm => hpost hm (hrel.trans hstep).pureStep,
    hsp, (hrel.trans hstep).calleeSaved hfp⟩

/-! ## 5. `fixslice64::memshift32` Verification -/

section
arm64_proof_prelude

private def MemshiftMidRegs (ptr : BitVec 64) (len srcIdx : Nat) (s : State) : Prop :=
  s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 len ∧
  s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 srcIdx ∧
  s.readReg64 (.gpr 8#5) = ptr ∧
  s.readReg64 (.gpr 9#5) = ptr + (BitVec.ofNat 64 srcIdx <<< 3) ∧
  s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 srcIdx + 8#64

private abbrev memshiftPre (ptr : BitVec 64) (srcIdx : Nat)
    (stSrc stDst : Model.FsState) (sp0 fp0 lr0 : BitVec 64) (R : SepProp) : SepProp :=
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3)) ↦₆₄ stSrc.s0) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 8#64) ↦₆₄ stSrc.s1) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 16#64) ↦₆₄ stSrc.s2) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 24#64) ↦₆₄ stSrc.s3) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 32#64) ↦₆₄ stSrc.s4) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 40#64) ↦₆₄ stSrc.s5) ∗
  ((ptr + (BitVec.ofNat 64 srcIdx <<< 3) + 48#64) ↦₆₄ stSrc.s6) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 7#64) <<< 3)) ↦₆₄ stSrc.s7) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 8#64) <<< 3)) ↦₆₄ stDst.s0) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 9#64) <<< 3)) ↦₆₄ stDst.s1) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 10#64) <<< 3)) ↦₆₄ stDst.s2) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 11#64) <<< 3)) ↦₆₄ stDst.s3) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 12#64) <<< 3)) ↦₆₄ stDst.s4) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 13#64) <<< 3)) ↦₆₄ stDst.s5) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 14#64) <<< 3)) ↦₆₄ stDst.s6) ∗
  ((ptr + ((BitVec.ofNat 64 srcIdx + 15#64) <<< 3)) ↦₆₄ stDst.s7) ∗
  ((sp0 - 16#64) ↦₆₄ fp0) ∗
  ((sp0 - 8#64) ↦₆₄ lr0) ∗ R

private theorem memshift_chunk1 {P : Program} {pc0 target_pc ptr w0 w1 : BitVec 64}
    {len srcIdx : Nat} {stSrc stDst : Model.FsState} {R : SepProp}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 memshift32ReachableInstrs)
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 (.gpr 0#5) = ptr)
    (hx1 : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 len)
    (hx2 : s0.readReg64 (.gpr 2#5) = BitVec.ofNat 64 srcIdx)
    (hbnd : srcIdx + 16 ≤ len) (hlen : len < 2 ^ 64)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 152#64 → s1.status = .Running → s1.sp = s0.sp - 16#64 →
      MemshiftMidRegs ptr len srcIdx s1 → Gpr19To28Preserved s0 s1 →
      SepWP P target_pc s1
        (memshiftPre ptr srcIdx stSrc
          { stDst with s4 := stSrc.s4, s5 := stSrc.s5, s6 := stSrc.s6, s7 := stSrc.s7 }
          s0.sp (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) R) post oom) :
    SepWP P target_pc s0 (memshiftPre ptr srcIdx stSrc stDst s0.sp w0 w1 R) post oom := by
  subst hx0
  have_instrs hc 0 38
  dsimp only [memshiftPre]
  wp_stp64 hf_0 m0 hm0
  wp_steps 3; wp_if h_cmn
  · exact absurd h_cmn (by bv_arith)
  · wp_steps 3; wp_if h_cmp7
    · exact absurd h_cmp7 (by bv_arith)
    · wp_steps 5; wp_if h_lo15
      · exact absurd h_lo15 (by bv_arith)
      · wp_steps 2; wp_if h_hi15
        · exact absurd h_hi15 (by bv_arith)
        · wp_step
          wp_str64 hf_15 m1 hm1
          wp_steps 3; wp_if h_lo14
          · exact absurd h_lo14 (by bv_arith)
          · wp_steps 2; wp_if h_hi14
            · exact absurd h_hi14 (by bv_arith)
            · wp_steps 2
              wp_str64 hf_23 m2 hm2
              wp_steps 3; wp_if h_lo13
              · exact absurd h_lo13 (by bv_arith)
              · wp_steps 2; wp_if h_hi13
                · exact absurd h_hi13 (by bv_arith)
                · wp_step
                  wp_str64 hf_30 m3 hm3
                  wp_steps 3; wp_if h_lo12
                  · exact absurd h_lo12 (by bv_arith)
                  · wp_steps 2; wp_if h_hi12
                    · exact absurd h_hi12 (by bv_arith)
                    · wp_step
                      wp_str64 hf_37 m4 hm4
                      refine hnext _ (by simp [wp_norm, arm64_norm])
                        (by simp [wp_norm, arm64_norm, hrun])
                        (by simp [wp_norm, arm64_norm, bv_lin_norm])
                        (by simp [MemshiftMidRegs, wp_norm, arm64_norm, hx1, hx2]) ?_
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
                      all_goals simp [wp_norm, arm64_norm, hm4, hm3, hm2, hm1, hm0]

private theorem memshift_chunk2 {P : Program} {pc0 ptr : BitVec 64}
    {len srcIdx : Nat} {stSrc stDst : Model.FsState} {R : SepProp}
    {s0 s1 : State} {oom : State → SepProp}
    (hc : hasInstrs P pc0 memshift32ReachableInstrs)
    (hpc : s1.pc = pc0 + 152#64) (hrun : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 16#64) (hsp0 : s0.spAligned = true)
    (hregs : MemshiftMidRegs ptr len srcIdx s1) (hrel : Gpr19To28Preserved s0 s1)
    (hbnd : srcIdx + 16 ≤ len) (hlen : len < 2 ^ 64) :
    SepWP P (s0.readReg64 .lr) s1
      (memshiftPre ptr srcIdx stSrc
        { stDst with s4 := stSrc.s4, s5 := stSrc.s5, s6 := stSrc.s6, s7 := stSrc.s7 }
        s0.sp (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) SepProp.emp)
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R → sf.mem ⊨ memshift32Spec.post (ptr, len, srcIdx, stSrc) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  rcases hregs with ⟨hx1, hx2, hx8, hx9, hx10⟩
  have hsp_align := sp_and_15_of_spAligned hsp0
  have_instrs hc 38 27
  dsimp only [memshiftPre]
  wp_steps 3; wp_if h_lo11
  · exact absurd h_lo11 (by bv_arith)
  · wp_steps 2; wp_if h_hi11
    · exact absurd h_hi11 (by bv_arith)
    · wp_step
      wp_str64 hf_44 m5 hm5
      wp_steps 3; wp_if h_lo10
      · exact absurd h_lo10 (by bv_arith)
      · wp_steps 2; wp_if h_hi10
        · exact absurd h_hi10 (by bv_arith)
        · wp_step
          wp_str64 hf_51 m6 hm6
          wp_steps 3; wp_if h_lo9
          · exact absurd h_lo9 (by bv_arith)
          · wp_steps 2; wp_if h_hi9
            · exact absurd h_hi9 (by bv_arith)
            · wp_steps 2
              wp_str64 hf_59 m7 hm7
              wp_step; wp_if h_hi8
              · exact absurd h_hi8 (by bv_arith)
              · wp_step
                wp_str64 hf_62 m8 hm8
                refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64)
                  (wb := some (.sp, s0.sp))
                  (by simp [wp_norm, arm64_norm, bv_lin_norm])
                  (by simp [wp_norm, arm64_norm, hrun]) hf_63
                  (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg,
                            wp_norm, arm64_norm, hsp1, hsp_align])
                  (by simp [evalAddrMode, wp_norm, arm64_norm, hsp1, bv_lin_norm]) (by bv_lin)
                  (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
                wp_step
                refine finish_sepwp_done
                  (Post := fun sf => memshift32Spec.post (ptr, len, srcIdx, stSrc) s0 sf)
                  (by simp [wp_norm, arm64_norm])
                  (by simp [wp_norm, arm64_norm, hrun])
                  (by simp [wp_norm, arm64_norm])
                  (by simp [wp_norm, arm64_norm])
                  hrel ?_ (fun hm hpure => ?_)
                · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
                  all_goals simp [wp_norm, arm64_norm, hm8, hm7, hm6, hm5]
                · dsimp only [memshift32Spec]
                  rw [sepConj_assoc, satisfies_pure_sepConj]
                  refine ⟨hpure, Satisfies.mono (sepConj_mono_left (Entails.trans ?_
                    (post_two_fs_stack16 s0.sp
                      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))))) hm⟩
                  rw [fsStateAt_src_shift ptr srcIdx stSrc,
                      fsStateAt_dst_shift ptr srcIdx stSrc]
                  sep_entail

/-- Minimal-footprint `subroutine_ok` contract for `fixslice64::memshift32` from its 65-instruction
    relocation-free reachable prefix. -/
theorem memshift32_ok (P : Program) (entry : BitVec 64)
    (hc : hasInstrs P entry memshift32ReachableInstrs) :
    subroutine_ok P entry memshift32Spec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, len, srcIdx, stSrc⟩ R s0 hpc hrun hpre hsp
  dsimp only [memshift32Spec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbnd, _hovf, hlen⟩, hpre⟩
  refine ⟨fsStateAt (ptr + BitVec.ofNat 64 (8 * srcIdx)) stSrc ∗
    memRegion (ptr + BitVec.ofNat 64 (8 * (srcIdx + 8))) 64 ∗
    stackFrameAt s0.sp 16, hpre, ?_⟩
  wp_conv_pre =>
    rw [memRegion64_eq_exists_fsStateAt, stackFrameAt_16 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro stDst
  wp_conv_pre =>
    rw [← sepConj_emp (fsStateAt _ _ ∗ _),
        fsStateAt_src_shift ptr srcIdx stSrc, fsStateAt_dst_shift ptr srcIdx stDst]
    simp only [sepConj_assoc]
  exact memshift_chunk1 hc hpc hrun hsp hx0 hx1 hx2 hbnd hlen
    fun s1 hpc1 hrun1 hsp1 hregs1 hrel1 =>
      memshift_chunk2 hc hpc1 hrun1 hsp1 hsp hregs1 hrel1 hbnd hlen

/-- Full 79-instruction `subroutine_ok` contract for `fixslice64::memshift32` (including its
    relocated panic tail). -/
theorem memshift32_full_ok (P : Program) (p : Memshift32PanicSyms)
    (hc : hasInstrs P p.fnAddr (memshift32FullInstrs p)) :
    subroutine_ok P p.fnAddr memshift32Spec :=
  memshift32_ok P p.fnAddr (hasInstrs_prefix hc)

end

/-! ## 6. `fixslice64::xor_columns` Verification -/

private abbrev fsPrevShifted (ptr : BitVec 64) (offset idxXor : Nat) (st : Model.FsState) :
    SepProp :=
  ((ptr + ((BitVec.ofNat 64 offset - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s0) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 1#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s1) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 2#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s2) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 3#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s3) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 4#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s4) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 5#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s5) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 6#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s6) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 7#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ st.s7)

private abbrev fsCurShifted (ptr : BitVec 64) (offset : Nat) (st : Model.FsState) : SepProp :=
  ((ptr + (BitVec.ofNat 64 offset <<< 3)) ↦₆₄ st.s0) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 1#64) <<< 3)) ↦₆₄ st.s1) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 2#64) <<< 3)) ↦₆₄ st.s2) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 3#64) <<< 3)) ↦₆₄ st.s3) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 4#64) <<< 3)) ↦₆₄ st.s4) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 5#64) <<< 3)) ↦₆₄ st.s5) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 6#64) <<< 3)) ↦₆₄ st.s6) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 7#64) <<< 3)) ↦₆₄ st.s7)

private theorem fsStateAt_cur_shift (ptr : BitVec 64) (offset : Nat) (st : Model.FsState) :
    fsStateAt (ptr + BitVec.ofNat 64 (8 * offset)) st = fsCurShifted ptr offset st := by
  unfold fsStateAt fsCurShifted
  rw [(show ptr + BitVec.ofNat 64 (8 * offset) + 8#64 =
        ptr + ((BitVec.ofNat 64 offset + 1#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 16#64 =
        ptr + ((BitVec.ofNat 64 offset + 2#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 24#64 =
        ptr + ((BitVec.ofNat 64 offset + 3#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 32#64 =
        ptr + ((BitVec.ofNat 64 offset + 4#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 40#64 =
        ptr + ((BitVec.ofNat 64 offset + 5#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 48#64 =
        ptr + ((BitVec.ofNat 64 offset + 6#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) + 56#64 =
        ptr + ((BitVec.ofNat 64 offset + 7#64) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * offset) =
        ptr + (BitVec.ofNat 64 offset <<< 3) by bv_lin)]

private theorem fsStateAt_prev_shift (ptr : BitVec 64) {offset idxXor : Nat}
    (hle : idxXor ≤ offset) (st : Model.FsState) :
    fsStateAt (ptr + BitVec.ofNat 64 (8 * (offset - idxXor))) st =
      fsPrevShifted ptr offset idxXor st := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  simp only [Nat.add_sub_cancel_left]
  unfold fsStateAt fsPrevShifted
  rw [(show ptr + BitVec.ofNat 64 (8 * d) + 8#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 1#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 16#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 2#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 24#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 3#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 32#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 4#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 40#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 5#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 48#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 6#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) + 56#64 =
        ptr + ((BitVec.ofNat 64 (idxXor + d) + 7#64 - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin),
      (show ptr + BitVec.ofNat 64 (8 * d) =
        ptr + ((BitVec.ofNat 64 (idxXor + d) - BitVec.ofNat 64 idxXor) <<< 3) by bv_lin)]

private theorem zext32_ofNat_lt64 {n : Nat} (h : n < 64) :
    (BitVec.ofNat 32 n).zeroExtend 64 = BitVec.ofNat 64 n := by
  bv_arith

private theorem xorColumnWord_hw_eq (p c : BitVec 64) {idxRor : Nat} (hror : idxRor < 64) :
    let rk := (c.rotateRight ((BitVec.ofNat 64 idxRor).toNat % 64) &&& 0x000f000f000f000f#64) ^^^ p
    (((rk <<< 8) &&& 0xff00ff00ff00ff00#64) ^^^ ((rk <<< 4) &&& 0xfff0fff0fff0fff0#64)) ^^^
      (((rk <<< 12) &&& 0xf000f000f000f000#64) ^^^ rk) =
      Model.xorColumnWord p c idxRor := by
  have hmod : (BitVec.ofNat 64 idxRor).toNat % 64 = idxRor := by
    rw [BitVec.toNat_ofNat]; omega
  have h_ac (a b4 b8 b12 : BitVec 64) :
      (b8 ^^^ b4) ^^^ (b12 ^^^ a) = ((a ^^^ b4) ^^^ b8) ^^^ b12 := by
    rw [BitVec.xor_comm b8 b4, BitVec.xor_comm b12 a,
        ← BitVec.xor_assoc (b4 ^^^ b8) a b12,
        BitVec.xor_comm (b4 ^^^ b8) a,
        ← BitVec.xor_assoc a b4 b8]
  dsimp only [Model.xorColumnWord, Model.ror64]
  simp only [hmod, BitVec.and_comm _ 0x000f000f000f000f#64,
    BitVec.and_comm _ 0xfff0fff0fff0fff0#64, BitVec.and_comm _ 0xff00ff00ff00ff00#64,
    BitVec.and_comm _ 0xf000f000f000f000#64]
  have hrk : (0x000f000f000f000f#64 &&& c.rotateRight idxRor) ^^^ p =
      p ^^^ (0x000f000f000f000f#64 &&& c.rotateRight idxRor) := BitVec.xor_comm _ _
  rw [hrk]
  exact h_ac _ _ _ _

private def XorBounds (len offset idxXor idxRor : Nat) : Prop :=
  8 ≤ idxXor ∧ idxXor ≤ offset ∧ offset + 8 ≤ len ∧ len < 2 ^ 64 ∧ idxRor < 64

private def XorEvenRegs (k : Nat) (ptr : BitVec 64) (len offset idxXor idxRor : Nat)
    (s : State) : Prop :=
  s.readReg64 (.gpr 0#5) = ptr ∧
  s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 len ∧
  s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 offset ∧
  s.readReg64 (.gpr 3#5) = BitVec.ofNat 64 idxXor ∧
  s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 offset + BitVec.ofNat 64 k - BitVec.ofNat 64 idxXor ∧
  s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 len - BitVec.ofNat 64 offset ∧
  s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 idxRor ∧
  s.readReg64 (.gpr 12#5) = BitVec.ofNat 64 offset + BitVec.ofNat 64 k

private abbrev xorPre (ptr : BitVec 64) (offset idxXor : Nat)
    (prev cur : Model.FsState) (sp0 fp0 lr0 : BitVec 64) (R : SepProp) : SepProp :=
  ((ptr + ((BitVec.ofNat 64 offset - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s0) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 1#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s1) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 2#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s2) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 3#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s3) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 4#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s4) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 5#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s5) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 6#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s6) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 7#64 - BitVec.ofNat 64 idxXor) <<< 3)) ↦₆₄ prev.s7) ∗
  ((ptr + (BitVec.ofNat 64 offset <<< 3)) ↦₆₄ cur.s0) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 1#64) <<< 3)) ↦₆₄ cur.s1) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 2#64) <<< 3)) ↦₆₄ cur.s2) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 3#64) <<< 3)) ↦₆₄ cur.s3) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 4#64) <<< 3)) ↦₆₄ cur.s4) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 5#64) <<< 3)) ↦₆₄ cur.s5) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 6#64) <<< 3)) ↦₆₄ cur.s6) ∗
  ((ptr + ((BitVec.ofNat 64 offset + 7#64) <<< 3)) ↦₆₄ cur.s7) ∗
  ((sp0 - 16#64) ↦₆₄ fp0) ∗
  ((sp0 - 8#64) ↦₆₄ lr0) ∗ R

section
arm64_proof_prelude

private theorem xor_chunk1 {P : Program} {pc0 target_pc ptr w0 w1 : BitVec 64}
    {len offset idxXor idxRor : Nat} {prev cur : Model.FsState} {R : SepProp}
    {s0 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 xorColumnsReachableInstrs)
    (hpc : s0.pc = pc0) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 (.gpr 0#5) = ptr)
    (hx1 : s0.readReg64 (.gpr 1#5) = BitVec.ofNat 64 len)
    (hx2 : s0.readReg64 (.gpr 2#5) = BitVec.ofNat 64 offset)
    (hx3 : s0.readReg64 (.gpr 3#5) = BitVec.ofNat 64 idxXor)
    (hx4 : s0.readReg32 (.gpr 4#5) = BitVec.ofNat 32 idxRor)
    (hb : XorBounds len offset idxXor idxRor)
    (hnext : ∀ s1 : State,
      s1.pc = pc0 + 212#64 → s1.status = .Running → s1.sp = s0.sp - 16#64 →
      XorEvenRegs 2 ptr len offset idxXor idxRor s1 → Gpr19To28Preserved s0 s1 →
      SepWP P target_pc s1
        (xorPre ptr offset idxXor prev
          { cur with
            s0 := Model.xorColumnWord prev.s0 cur.s0 idxRor
            s1 := Model.xorColumnWord prev.s1 cur.s1 idxRor }
          s0.sp (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) R) post oom) :
    SepWP P target_pc s0 (xorPre ptr offset idxXor prev cur s0.sp w0 w1 R) post oom := by
  rcases hb with ⟨hxor8, hle, hoff8, hlen, hror⟩
  subst hx0
  have h_ult12_bv : (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 offset) = false := by bv_arith
  have_instrs hc 0 53
  dsimp only [xorPre]
  wp_stp64 hf_0 m0 hm0
  wp_steps 5; wp_if h_lo0
  · exact absurd h_lo0 (by bv_arith)
  · wp_steps 2; wp_if h_hs0
    · exact absurd h_hs0 (by bv_arith)
    · wp_steps 2; wp_if h_ls0
      · exact absurd h_ls0 (by bv_arith)
      · wp_steps 18
        wp_str64 hf_28 m1 hm1
        wp_step; wp_if h_hs1
        · exact absurd h_hs1 (by bv_arith)
        · wp_steps 2; wp_if h_eq1
          · exact absurd h_eq1 (by bv_arith)
          · wp_steps 17
            wp_str64 hf_49 m2 hm2
            wp_step; wp_if h_hs2
            · exact absurd h_hs2 (by bv_arith)
            · wp_steps 2; wp_if h_eq2
              · exact absurd h_eq2 (by bv_arith)
              · have hx4_zext :
                    ((s0.readReg64 (.gpr 4#5)).truncate 32).zeroExtend 64 =
                      BitVec.ofNat 64 idxRor := by
                  change (s0.readReg32 (.gpr 4#5)).zeroExtend 64 = BitVec.ofNat 64 idxRor
                  rw [hx4, zext32_ofNat_lt64 hror]
                wp_conv_pre =>
                  simp only [hx4_zext,
                    xorColumnWord_hw_eq prev.s0 cur.s0 hror,
                    xorColumnWord_hw_eq prev.s1 cur.s1 hror]
                apply hnext
                · simp [wp_norm, arm64_norm]
                · simp [wp_norm, arm64_norm, hrun]
                · simp [wp_norm, arm64_norm, bv_lin_norm]
                · simp [XorEvenRegs, wp_norm, arm64_norm, hx1, hx2, hx3, hx4_zext]
                · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
                  all_goals simp [wp_norm, arm64_norm, hm2, hm1, hm0]

private theorem xor_chunk2 {P : Program} {pc0 target_pc ptr sp0 fp0 lr0 : BitVec 64}
    {len offset idxXor idxRor : Nat} {prev cur : Model.FsState} {R : SepProp}
    {s1 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 xorColumnsReachableInstrs)
    (hpc : s1.pc = pc0 + 212#64) (hrun : s1.status = .Running)
    (hregs : XorEvenRegs 2 ptr len offset idxXor idxRor s1)
    (hb : XorBounds len offset idxXor idxRor)
    (hnext : ∀ s2 : State,
      s2.pc = pc0 + 380#64 → s2.status = .Running → s2.sp = s1.sp →
      XorEvenRegs 4 ptr len offset idxXor idxRor s2 → Gpr19To28Preserved s1 s2 →
      SepWP P target_pc s2
        (xorPre ptr offset idxXor prev
          { cur with
            s2 := Model.xorColumnWord prev.s2 cur.s2 idxRor
            s3 := Model.xorColumnWord prev.s3 cur.s3 idxRor }
          sp0 fp0 lr0 R) post oom) :
    SepWP P target_pc s1 (xorPre ptr offset idxXor prev cur sp0 fp0 lr0 R) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx8, hx9, hx10, hx12⟩
  rcases hb with ⟨hxor8, hle, hoff8, hlen, hror⟩
  subst hx0
  have_instrs hc 53 42
  dsimp only [xorPre]
  wp_steps 17
  wp_str64 hf_70 m1 hm1
  wp_step; wp_if h_hs3
  · exact absurd h_hs3 (by bv_arith)
  · wp_steps 2; wp_if h_eq3
    · exact absurd h_eq3 (by bv_arith)
    · wp_steps 17
      wp_str64 hf_91 m2 hm2
      wp_step; wp_if h_hs4
      · exact absurd h_hs4 (by bv_arith)
      · wp_steps 2; wp_if h_eq4
        · exact absurd h_eq4 (by bv_arith)
        · wp_conv_pre =>
            simp only [xorColumnWord_hw_eq prev.s2 cur.s2 hror,
              xorColumnWord_hw_eq prev.s3 cur.s3 hror]
          apply hnext
          · simp [wp_norm, arm64_norm, bv_lin_norm]
          · simp [wp_norm, arm64_norm, hrun]
          · simp [wp_norm, arm64_norm]
          · simp [XorEvenRegs, wp_norm, arm64_norm, hx1, hx2, hx3, hx9, hx10]
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
            all_goals simp [wp_norm, arm64_norm, hm2, hm1]

private theorem xor_chunk3 {P : Program} {pc0 target_pc ptr sp0 fp0 lr0 : BitVec 64}
    {len offset idxXor idxRor : Nat} {prev cur : Model.FsState} {R : SepProp}
    {s2 : State} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hc : hasInstrs P pc0 xorColumnsReachableInstrs)
    (hpc : s2.pc = pc0 + 380#64) (hrun : s2.status = .Running)
    (hregs : XorEvenRegs 4 ptr len offset idxXor idxRor s2)
    (hb : XorBounds len offset idxXor idxRor)
    (hnext : ∀ s3 : State,
      s3.pc = pc0 + 548#64 → s3.status = .Running → s3.sp = s2.sp →
      XorEvenRegs 6 ptr len offset idxXor idxRor s3 → Gpr19To28Preserved s2 s3 →
      SepWP P target_pc s3
        (xorPre ptr offset idxXor prev
          { cur with
            s4 := Model.xorColumnWord prev.s4 cur.s4 idxRor
            s5 := Model.xorColumnWord prev.s5 cur.s5 idxRor }
          sp0 fp0 lr0 R) post oom) :
    SepWP P target_pc s2 (xorPre ptr offset idxXor prev cur sp0 fp0 lr0 R) post oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx8, hx9, hx10, hx12⟩
  rcases hb with ⟨hxor8, hle, hoff8, hlen, hror⟩
  subst hx0
  have_instrs hc 95 42
  dsimp only [xorPre]
  wp_steps 17
  wp_str64 hf_112 m1 hm1
  wp_step; wp_if h_hs5
  · exact absurd h_hs5 (by bv_arith)
  · wp_steps 2; wp_if h_eq5
    · exact absurd h_eq5 (by bv_arith)
    · wp_steps 17
      wp_str64 hf_133 m2 hm2
      wp_step; wp_if h_hs6
      · exact absurd h_hs6 (by bv_arith)
      · wp_steps 2; wp_if h_eq6
        · exact absurd h_eq6 (by bv_arith)
        · wp_conv_pre =>
            simp only [xorColumnWord_hw_eq prev.s4 cur.s4 hror,
              xorColumnWord_hw_eq prev.s5 cur.s5 hror]
          apply hnext
          · simp [wp_norm, arm64_norm, bv_lin_norm]
          · simp [wp_norm, arm64_norm, hrun]
          · simp [wp_norm, arm64_norm]
          · simp [XorEvenRegs, wp_norm, arm64_norm, hx1, hx2, hx3, hx9, hx10]
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
            all_goals simp [wp_norm, arm64_norm, hm2, hm1]

private theorem xor_chunk4 {P : Program} {pc0 ptr : BitVec 64}
    {len offset idxXor idxRor : Nat} {prev cur0 : Model.FsState} {R : SepProp}
    {s0 s3 : State} {oom : State → SepProp}
    (hc : hasInstrs P pc0 xorColumnsReachableInstrs)
    (hpc : s3.pc = pc0 + 548#64) (hrun : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 16#64) (hsp0 : s0.spAligned = true)
    (hregs : XorEvenRegs 6 ptr len offset idxXor idxRor s3)
    (hrel : Gpr19To28Preserved s0 s3)
    (hb : XorBounds len offset idxXor idxRor) :
    SepWP P (s0.readReg64 .lr) s3
      (xorPre ptr offset idxXor prev
        { cur0 with
          s0 := Model.xorColumnWord prev.s0 cur0.s0 idxRor
          s1 := Model.xorColumnWord prev.s1 cur0.s1 idxRor
          s2 := Model.xorColumnWord prev.s2 cur0.s2 idxRor
          s3 := Model.xorColumnWord prev.s3 cur0.s3 idxRor
          s4 := Model.xorColumnWord prev.s4 cur0.s4 idxRor
          s5 := Model.xorColumnWord prev.s5 cur0.s5 idxRor }
        s0.sp (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) SepProp.emp)
      (fun sf Q =>
        (sf.mem ⊨ Q ∗ R →
          sf.mem ⊨ xorColumnsSpec.post (ptr, len, offset, idxXor, idxRor, prev, cur0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  rcases hregs with ⟨hx0, hx1, hx2, hx3, hx8, hx9, hx10, hx12⟩
  rcases hb with ⟨hxor8, hle, hoff8, hlen, hror⟩
  subst hx0
  have hsp_align := sp_and_15_of_spAligned hsp0
  have_instrs hc 137 38
  dsimp only [xorPre]
  wp_steps 17
  wp_str64 hf_154 m1 hm1
  wp_step; wp_if h_hs7
  · exact absurd h_hs7 (by bv_arith)
  · wp_steps 2; wp_if h_eq7
    · exact absurd h_eq7 (by bv_arith)
    · wp_steps 14
      wp_str64 hf_172 m2 hm2
      refine SepWP.step_ldp64 (ea := s0.sp - 16#64) (ea2 := s0.sp - 8#64)
        (wb := some (.sp, s0.sp))
        (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun]) hf_173
        (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg,
                  wp_norm, arm64_norm, hsp3, hsp_align])
        (by simp [evalAddrMode, wp_norm, arm64_norm, hsp3, bv_lin_norm]) (by bv_lin)
        (by wp_sep_access) (by wp_sep_access) (by wp_norm_lhs) ?_
      wp_step
      wp_conv_pre =>
        simp only [xorColumnWord_hw_eq prev.s6 cur0.s6 hror,
          xorColumnWord_hw_eq prev.s7 cur0.s7 hror]
      refine finish_sepwp_done
        (Post := fun sf =>
          xorColumnsSpec.post (s3.readReg64 (.gpr 0#5), len, offset, idxXor, idxRor, prev, cur0)
            s0 sf)
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm])
        hrel ?_ (fun hm hpure => ?_)
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
        all_goals simp [wp_norm, arm64_norm, hm2, hm1]
      · dsimp only [xorColumnsSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨hpure, Satisfies.mono (sepConj_mono_left (Entails.trans ?_
          (post_two_fs_stack16 s0.sp
            (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))))) hm⟩
        rw [fsStateAt_prev_shift (s3.readReg64 (.gpr 0#5)) hle prev,
            fsStateAt_cur_shift (s3.readReg64 (.gpr 0#5)) offset
              (Model.xorColumnsFs prev cur0 idxRor)]
        dsimp only [Model.xorColumnsFs, Model.FsState.zipWith, fsPrevShifted, fsCurShifted]
        sep_entail

/-- Minimal-footprint `subroutine_ok` contract for `fixslice64::xor_columns` from its
    175-instruction relocation-free reachable prefix. -/
theorem xorColumns_ok (P : Program) (entry : BitVec 64)
    (hc : hasInstrs P entry xorColumnsReachableInstrs) :
    subroutine_ok P entry xorColumnsSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ptr, len, offset, idxXor, idxRor, prev, cur⟩ R s0 hpc hrun hpre hsp
  dsimp only [xorColumnsSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hxor8, hle, hoff8, _hovf, hlen, hror⟩, hpre⟩
  refine ⟨fsStateAt (ptr + BitVec.ofNat 64 (8 * (offset - idxXor))) prev ∗
    fsStateAt (ptr + BitVec.ofNat 64 (8 * offset)) cur ∗
    stackFrameAt s0.sp 16, hpre, ?_⟩
  wp_conv_pre =>
    rw [stackFrameAt_16 s0.sp]
    simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  wp_conv_pre =>
    rw [← sepConj_emp (fsStateAt _ _ ∗ _),
        fsStateAt_prev_shift ptr hle prev, fsStateAt_cur_shift ptr offset cur]
    simp only [fsPrevShifted, fsCurShifted, sepConj_assoc]
  have hb : XorBounds len offset idxXor idxRor := ⟨hxor8, hle, hoff8, hlen, hror⟩
  exact xor_chunk1 hc hpc hrun hsp hx0 hx1 hx2 hx3 hx4 hb
    fun s1 hpc1 hrun1 hsp1 hregs1 hrel1 =>
      xor_chunk2 hc hpc1 hrun1 hregs1 hb
        fun s2 hpc2 hrun2 hsp2 hregs2 hrel2 =>
          xor_chunk3 hc hpc2 hrun2 hregs2 hb
            fun s3 hpc3 hrun3 hsp3 hregs3 hrel3 =>
              xor_chunk4 hc hpc3 hrun3 (hsp3.trans (hsp2.trans hsp1)) hsp hregs3
                (hrel1.trans (hrel2.trans hrel3)) hb

/-- Full 200-instruction `subroutine_ok` contract for `fixslice64::xor_columns` (including its
    relocated panic tail). -/
theorem xorColumns_full_ok (P : Program) (p : XorColumnsPanicSyms)
    (hc : hasInstrs P p.fnAddr (xorColumnsFullInstrs p)) :
    subroutine_ok P p.fnAddr xorColumnsSpec :=
  xorColumns_ok P p.fnAddr (hasInstrs_prefix hc)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KsHelpers
