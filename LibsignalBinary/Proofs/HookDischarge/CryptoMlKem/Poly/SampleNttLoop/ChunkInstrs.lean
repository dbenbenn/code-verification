/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import

/-!
# Instruction block builders and register state for `rej_sample`

Register parameterization (`isVarA : Bool`), PC-offset helpers, `FetchesInstrsAt` fetch slicing,
instruction block builders for all 3 variants (`A`, `B`, `C`) of the 193-instruction `rej_sample`
inner chunk loop, and scratch-register preservation invariants (`B03`–`B07`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  parseRej12Triple
)

/-! ## 1. Register Assignment, PC Indexing, & Fetch Slicing -/

@[expose] def rSampled (isVarA : Bool) : Reg := if isVarA then .x12 else .x11
@[expose] def rSlotBase (isVarA : Bool) : Reg := if isVarA then .x13 else .x12
@[expose] def rBuf (isVarA : Bool) : Reg := if isVarA then .x14 else .x13
@[expose] def rRem (isVarA : Bool) : Reg := if isVarA then .x15 else .x14
@[expose] def rOut (isVarA : Bool) : Reg := if isVarA then .x16 else .x15
@[expose] def rCnt (isVarA : Bool) : Reg := if isVarA then .x17 else .x16
@[expose] def rB1 (isVarA : Bool) : Reg := if isVarA then .x18 else .x17
@[expose] def rS0 (isVarA : Bool) : Reg := if isVarA then .x0 else .x18
@[expose] def rS1 (isVarA : Bool) : Reg := if isVarA then .x1 else .x0

/-- Scratch registers overwritten inside a single 24-byte chunk body (`[17..203]`). -/
@[expose] def rejScratchRegs (isVarA : Bool) : List Reg :=
  [rOut isVarA, rCnt isVarA, rB1 isVarA, rS0 isVarA, rS1 isVarA]

/-- Registers modified across the entire inner chunk loop (`[11..203]`). -/
@[expose] def rejClobberedRegs (isVarA : Bool) : List Reg :=
  [rSampled isVarA, rBuf isVarA, rRem isVarA,
   rOut isVarA, rCnt isVarA, rB1 isVarA, rS0 isVarA, rS1 isVarA]

@[expose] def pcAt (pcBase : BitVec 64) (idx : Nat) : BitVec 64 :=
  pcBase + BitVec.ofNat 64 (4 * idx)

@[expose] def brDisp (srcIdx dstIdx : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (4 * dstIdx) - BitVec.ofNat 64 (4 * srcIdx)

theorem pcAt_succ (pcBase : BitVec 64) (idx : Nat) :
    pcAt pcBase idx + 4#64 = pcAt pcBase (idx + 1) := by
  unfold pcAt; bv_omega

theorem pcAt_brDisp (pcBase : BitVec 64) (srcIdx dstIdx : Nat) :
    pcAt pcBase srcIdx + brDisp srcIdx dstIdx = pcAt pcBase dstIdx := by
  unfold pcAt brDisp; bv_omega

@[expose] def FetchesInstrsAt (prog : Program) (pcBase : BitVec 64)
    (baseIdx : Nat) (instrs : List Instr) : Prop :=
  ∀ k inst, instrs[k]? = some inst → prog.fetch (pcAt pcBase (baseIdx + k)) = some inst

theorem FetchesInstrsAt.append_iff {prog : Program} {pcBase : BitVec 64}
    {baseIdx : Nat} {xs ys : List Instr} :
    FetchesInstrsAt prog pcBase baseIdx (xs ++ ys) ↔
      FetchesInstrsAt prog pcBase baseIdx xs ∧
      FetchesInstrsAt prog pcBase (baseIdx + xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun k inst hk => h k inst (by
        rw [List.getElem?_append_left (by
          by_contra hge; simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hk)]
        exact hk),
      fun k inst hk => ?_⟩
    have hxy : (xs ++ ys)[xs.length + k]? = some inst := by
      rw [List.getElem?_append_right (by omega)]; simpa using hk
    simpa [Nat.add_assoc] using h (xs.length + k) inst hxy
  · rintro ⟨hx, hy⟩ k inst hk
    by_cases hlt : k < xs.length
    · rw [List.getElem?_append_left hlt] at hk; exact hx k inst hk
    · rw [List.getElem?_append_right (by omega)] at hk
      have := hy (k - xs.length) inst hk
      rwa [show baseIdx + xs.length + (k - xs.length) = baseIdx + k by omega] at this

theorem FetchesInstrsAt.get {prog : Program} {pcBase : BitVec 64}
    {baseIdx idx : Nat} {instrs : List Instr} {inst : Instr}
    (hf : FetchesInstrsAt prog pcBase baseIdx instrs) (k : Nat)
    (hget : instrs[k]? = some inst := by rfl) (hidx : baseIdx + k = idx := by omega) :
    prog.fetch (pcAt pcBase idx) = some inst :=
  hidx ▸ hf k inst hget

/-! ## 2. Parametric Instruction Block Builders (`[11..203]`) -/

@[expose] def rejByteAddr (rb : Reg) (j : Nat) : AddrMode :=
  if j < 11 then .UnscaledOffset rb (BitVec.ofNat 64 j - 11#64)
  else .Offset rb (BitVec.ofNat 64 (j - 11))

@[expose] def rejLoadByte (isVarA : Bool) (rt : Reg) (j : Nat) : Instr :=
  .ldr .W32 .B8 false rt (rejByteAddr (rBuf isVarA) j)

@[expose] def rejStoreRegOff (isVarA : Bool) (rt : Reg) : Instr :=
  .str .H16 rt (.RegOffset (rOut isVarA) (rCnt isVarA) .UXTX 1)

@[expose] def rejHeadLatchInstrs (isVarA : Bool) : List Instr :=
  [.addSubShift .W64 .ADD (rSampled isVarA) (rCnt isVarA) (rSampled isVarA) .LSL 0,
   .addSubImm .W64 .SUBS (rRem isVarA) (rRem isVarA) 1#12 false,
   .addSubImm .W64 .ADD (rBuf isVarA) (rBuf isVarA) 24#12 false,
   .bCond .EQ (brDisp 14 0),
   .addSubImm .W64 .SUBS .xzr (rSampled isVarA) 256#12 false,
   .bCond .CS (brDisp 16 12)]

@[expose] def rejTriple0ABInstrs (isVarA : Bool) : List Instr :=
  [rejLoadByte isVarA (rCnt isVarA) 0,
   rejLoadByte isVarA (rB1 isVarA) 1,
   .addSubShift .W64 .ADD (rOut isVarA) (rSlotBase isVarA) (rSampled isVarA) .LSL 1,
   .bitfield .W32 .BFM (rCnt isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rCnt isVarA) 3329#12 false,
   .bCond .CS (brDisp 22 31),
   .str .H16 (rCnt isVarA) (.Offset (rOut isVarA) 0#64),
   .moveWide .W32 .MOVZ (rCnt isVarA) 1#16 0,
   rejLoadByte isVarA (rS0 isVarA) 2,
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3329#12 false,
   .bCond .CC (brDisp 29 37),
   .b (brDisp 30 39),
   .logicalShift .W64 .ORR (rCnt isVarA) .xzr .xzr .LSL 0,
   rejLoadByte isVarA (rS0 isVarA) 2,
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3329#12 false,
   .bCond .CS (brDisp 36 39),
   rejStoreRegOff isVarA (rB1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false]

@[expose] def rejTriple0CFastInstrs : List Instr :=
  [rejLoadByte false (rCnt false) 0,
   rejLoadByte false (rB1 false) 1,
   .addSubShift .W64 .ADD (rOut false) (rSlotBase false) (rSampled false) .LSL 1,
   .bitfield .W32 .BFM (rCnt false) (rB1 false) 24 3,
   .addSubImm .W32 .SUBS .xzr (rCnt false) 3329#12 false,
   .bCond .CS (brDisp 22 103),
   .str .H16 (rCnt false) (.Offset (rOut false) 0#64),
   .moveWide .W32 .MOVZ (rCnt false) 1#16 0,
   rejLoadByte false (rS0 false) 2,
   .bitfield .W32 .UBFM (rB1 false) (rB1 false) 4 31,
   .logicalShift .W32 .ORR (rB1 false) (rB1 false) (rS0 false) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 false) 3329#12 false,
   .bCond .CS (brDisp 29 32),
   rejStoreRegOff false (rB1 false),
   .addSubImm .W64 .ADD (rCnt false) (rCnt false) 1#12 false]

@[expose] def rejTriple0CSlowInstrs : List Instr :=
  [.logicalShift .W64 .ORR (rCnt false) .xzr .xzr .LSL 0,
   rejLoadByte false (rS0 false) 2,
   .bitfield .W32 .UBFM (rB1 false) (rB1 false) 4 31,
   .logicalShift .W32 .ORR (rB1 false) (rB1 false) (rS0 false) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 false) 3329#12 false,
   .bCond .CC (brDisp 108 30),
   .b (brDisp 109 32)]

@[expose] def rejSpine14Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let spIdx := 39 - spShift + 10 * (t - 1)
  let store1Idx := 110 + 14 * (t - 1)
  [rejLoadByte isVarA (rS0 isVarA) (3 * t),
   rejLoadByte isVarA (rB1 isVarA) (3 * t + 1),
   .bitfield .W32 .BFM (rS0 isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rS0 isVarA) 3328#12 false,
   .bCond .LS (brDisp (spIdx + 4) store1Idx),
   rejLoadByte isVarA (rS0 isVarA) (3 * t + 2),
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .LS (brDisp (spIdx + 9) (store1Idx + 7))]

@[expose] def rejSpine56Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let spIdx := 39 - spShift + 10 * (t - 1)
  let store1Idx := 167 + 14 * (t - 5)
  [rejLoadByte isVarA (rS1 isVarA) (3 * t),
   rejLoadByte isVarA (rB1 isVarA) (3 * t + 1),
   rejLoadByte isVarA (rS0 isVarA) (3 * t + 2),
   .bitfield .W32 .BFM (rS1 isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rS1 isVarA) 3328#12 false,
   .bCond .LS (brDisp (spIdx + 5) store1Idx),
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .LS (brDisp (spIdx + 9) (store1Idx + 6))]

@[expose] def rejSpine7Instrs (isVarA : Bool) (spShift : Nat) : List Instr :=
  let spIdx := 99 - spShift
  [rejLoadByte isVarA (rS1 isVarA) 21,
   rejLoadByte isVarA (rB1 isVarA) 22,
   rejLoadByte isVarA (rS0 isVarA) 23,
   .bitfield .W32 .BFM (rS1 isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rS1 isVarA) 3328#12 false,
   .bCond .LS (brDisp (spIdx + 5) 195),
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .HI (brDisp (spIdx + 9) 11),
   .b (brDisp (spIdx + 10) 201)]

@[expose] def rejOutPre24Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let outIdx := 105 + 14 * (t - 1)
  let spIdx := 39 - spShift + 10 * (t - 1)
  [rejLoadByte isVarA (rS0 isVarA) (3 * t),
   rejLoadByte isVarA (rB1 isVarA) (3 * t + 1),
   .bitfield .W32 .BFM (rS0 isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rS0 isVarA) 3328#12 false,
   .bCond .HI (brDisp (outIdx + 4) (spIdx + 5))]

@[expose] def rejStore14Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let store1Idx := 110 + 14 * (t - 1)
  let nextSpIdx := 39 - spShift + 10 * t
  [rejStoreRegOff isVarA (rS0 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false,
   rejLoadByte isVarA (rS0 isVarA) (3 * t + 2),
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .HI (brDisp (store1Idx + 6) nextSpIdx),
   rejStoreRegOff isVarA (rB1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false]

@[expose] def rejOutPre57Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let outIdx := 105 + 14 * (t - 1)
  let spIdx := 39 - spShift + 10 * (t - 1)
  [rejLoadByte isVarA (rS1 isVarA) (3 * t),
   rejLoadByte isVarA (rB1 isVarA) (3 * t + 1),
   rejLoadByte isVarA (rS0 isVarA) (3 * t + 2),
   .bitfield .W32 .BFM (rS1 isVarA) (rB1 isVarA) 24 3,
   .addSubImm .W32 .SUBS .xzr (rS1 isVarA) 3328#12 false,
   .bCond .HI (brDisp (outIdx + 5) (spIdx + 6))]

@[expose] def rejStore56Instrs (isVarA : Bool) (spShift t : Nat) : List Instr :=
  let store1Idx := 167 + 14 * (t - 5)
  let nextSpIdx := 39 - spShift + 10 * t
  [rejStoreRegOff isVarA (rS1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false,
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .HI (brDisp (store1Idx + 5) nextSpIdx),
   rejStoreRegOff isVarA (rB1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false]

@[expose] def rejStore7Instrs (isVarA : Bool) : List Instr :=
  [rejStoreRegOff isVarA (rS1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false,
   .bitfield .W32 .UBFM (rB1 isVarA) (rB1 isVarA) 4 31,
   .logicalShift .W32 .ORR (rB1 isVarA) (rB1 isVarA) (rS0 isVarA) .LSL 4,
   .addSubImm .W32 .SUBS .xzr (rB1 isVarA) 3328#12 false,
   .bCond .HI (brDisp 200 11),
   rejStoreRegOff isVarA (rB1 isVarA),
   .addSubImm .W64 .ADD (rCnt isVarA) (rCnt isVarA) 1#12 false,
   .b (brDisp 203 11)]

/-! ## 3. Register-Preservation & Triple-State Invariants -/

@[expose] def parseRej12TripleAt (chunk : List (BitVec 8)) (t : Nat) : List Nat :=
  parseRej12Triple (chunk.getD (3 * t) 0#8) (chunk.getD (3 * t + 1) 0#8)
    (chunk.getD (3 * t + 2) 0#8)

@[expose] def ScratchPreserved (isVarA : Bool) (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp ∧
  s.vregs = s0.vregs ∧
  ∀ r : Reg, r ∉ rejScratchRegs isVarA → s.readReg64 r = s0.readReg64 r

@[expose] def RejTripleState (isVarA : Bool) (s0 : State) (slotBase : BitVec 64)
    (sampled cnt : Nat) (s : State) : Prop :=
  ScratchPreserved isVarA s0 s ∧
  s.readReg64 (rOut isVarA) = slotBase + (BitVec.ofNat 64 sampled <<< 1) ∧
  s.readReg64 (rCnt isVarA) = BitVec.ofNat 64 cnt

theorem ScratchPreserved.refl {isVarA : Bool} {s0 : State} (hrun : s0.status = .Running) :
    ScratchPreserved isVarA s0 s0 := ⟨hrun, rfl, rfl, fun _ _ => rfl⟩

theorem ScratchPreserved.setPC {isVarA : Bool} {s0 s : State} (h : ScratchPreserved isVarA s0 s)
    (pc : BitVec 64) : ScratchPreserved isVarA s0 (s.setPC pc) := by
  rcases h with ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem ScratchPreserved.setPState {isVarA : Bool} {s0 s : State} (h : ScratchPreserved isVarA s0 s)
    (ps : PState) : ScratchPreserved isVarA s0 (s.setPState ps) := by
  rcases h with ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem ScratchPreserved.setMem {isVarA : Bool} {s0 s : State} (h : ScratchPreserved isVarA s0 s)
    (m : Memory) : ScratchPreserved isVarA s0 (s.setMem m) := by
  rcases h with ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem readReg64_writeReg64_ne_of (s : State) {r1 r2 : Reg} {val : BitVec 64} (hne : r1 ≠ r2) :
    (s.writeReg64 r2 val).readReg64 r1 = s.readReg64 r1 :=
  State.readReg64_writeReg64_ne s r2 r1 val hne

theorem ScratchPreserved.writeScratch {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) {w : Width} {rt : Reg}
    (hrt : rt ∈ rejScratchRegs isVarA) (val : BitVec 64) :
    ScratchPreserved isVarA s0 (s.writeReg w rt val) := by
  rcases h with ⟨hrun, hsp, hv, hregs⟩
  have hnotsp : rt ≠ .sp := by
    cases isVarA <;> simp [rejScratchRegs, rOut, rCnt, rB1, rS0, rS1] at hrt <;>
      rcases hrt with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨by cases w <;> simp [State.writeReg, State.writeReg64, hrun],
    by cases w <;> cases rt <;> simp_all [State.writeReg, State.writeReg64],
    by cases w <;> cases rt <;> simp_all [State.writeReg, State.writeReg64],
    fun r hr => ?_⟩
  have hne : r ≠ rt := fun heq => hr (heq ▸ hrt)
  cases w <;> simp [State.writeReg, readReg64_writeReg64_ne_of s hne, hregs r hr]

theorem ScratchPreserved.readBuf {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) :
    s.readReg64 (rBuf isVarA) = s0.readReg64 (rBuf isVarA) :=
  h.2.2.2 (rBuf isVarA) (by cases isVarA <;> simp [rejScratchRegs, rBuf, rOut, rCnt, rB1, rS0, rS1])

theorem ScratchPreserved.readSlotBase {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) :
    s.readReg64 (rSlotBase isVarA) = s0.readReg64 (rSlotBase isVarA) :=
  h.2.2.2 (rSlotBase isVarA) (by
    cases isVarA <;> simp [rejScratchRegs, rSlotBase, rOut, rCnt, rB1, rS0, rS1])

theorem ScratchPreserved.readSampled {isVarA : Bool} {s0 s : State}
    (h : ScratchPreserved isVarA s0 s) :
    s.readReg64 (rSampled isVarA) = s0.readReg64 (rSampled isVarA) :=
  h.2.2.2 (rSampled isVarA) (by
    cases isVarA <;> simp [rejScratchRegs, rSampled, rOut, rCnt, rB1, rS0, rS1])

theorem read_writeScratch_self {isVarA : Bool} (s : State) {rt : Reg}
    (hrt : rt ∈ rejScratchRegs isVarA) (v : BitVec 64) :
    (s.writeReg64 rt v).readReg64 rt = v := by
  cases isVarA <;> simp [rejScratchRegs, rOut, rCnt, rB1, rS0, rS1] at hrt <;>
    rcases hrt with rfl | rfl | rfl | rfl | rfl <;> simp

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
