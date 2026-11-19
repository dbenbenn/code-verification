/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTop -- proof-setup: allow-public-import

/-!
# Frame and Loop-Head Definitions for Seed `SessionRecord::deserialize`

Defines the stack-frame layout (`deserLocals` at `L = s0.sp - 0x770`), field-loop head invariant
(`DeserLoop` and `DeserLoopPlaced` at `+0x254`), raw output layout (`deserOutRecord`, `deserOutRaw`),
and segment-chaining helpers (`DeserStep`, `DeserStepPlaced`) for `SessionRecord::deserialize`
(`0x16ed4`, block `46`) on `seedRecord f`:
* `[s0.sp - 0x60, s0.sp)`: callee-saved registers `x29, x30, x28 .. x19` at `fp = L + 0x710`.
* `[L, fp)`: slice cursor `(ptr, len)` at `L + 0x3f8`, `previous_sessions` `{0, 8, 0}` at
  `L + 0x408`, prost `SessionStructure` at `L + 0x420` (`prostSSAt`), and `bufRef` pointer
  `L + 0x3f8` at `fp - 0x28`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record

abbrev deserSpL (sp0 : BitVec 64) : BitVec 64 := sp0 - 0x770#64

abbrev deserCalleeStack : Nat := recDeserializeStack - 0x770

/-- Callee-saved registers of `s0` stored at `fp = s0.sp - 0x60`. -/
@[expose] def deserSaved (s0 : State) : SepProp :=
  let fp := s0.sp - 0x60#64
  (fp ↦₆₄ s0.readReg64 .x29) ∗ ((fp + 8#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((fp + 0x10#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fp + 0x18#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((fp + 0x20#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fp + 0x28#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((fp + 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fp + 0x38#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((fp + 0x40#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fp + 0x48#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((fp + 0x50#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fp + 0x58#64) ↦₆₄ s0.readReg64 .x19)

/-- Stack-frame locals of `SessionRecord::deserialize` in the field loop at `L`: slice cursor
advanced to `rest`, empty `previous_sessions`, `prostSSAt` holding `v`, and `bufRef` at `fp - 0x28`. -/
@[expose] def deserLocals (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSV) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSAt A0 (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

/-- Raw `RecordStructure` layout at `out`: empty `previous_sessions` `{0, 8, 0}` at `out` and
`prostSSAt` holding all decoded fields of `seedFields f` at `out + 0x18`. -/
@[expose] def deserOutRecord (out : BitVec 64) (f : List (BitVec 8)) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSAt A0 (out + 0x18#64) (ssvAfter f (seedFields f).length)

@[expose] def deserOutRaw (x : DeserializeSeedGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ x.bs) ∗ deserOutRecord x.out x.f ∗
    stackAt s0.sp recDeserializeStack

@[expose] def DeserRet (x : DeserializeSeedGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRaw x s0 sf ∗ R)

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

noncomputable abbrev recordPlacedProg [LibsignalPlacement]
    (H : String → Option (State → State)) : Program :=
  lsProg_46 H

abbrev deserPlacedPC [LibsignalPlacement] (off : BitVec 64) : BitVec 64 :=
  (blkPl_46).base + off

/-- One segment step of relocatable `SessionRecord::deserialize` (`lsProg_46 H`) reaching `Q` or
panicking with `deserializeSeedRawSpec.onPanic`. -/
@[expose] def DeserStepPlaced [LibsignalPlacement] (x : DeserializeSeedGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop)
    (H : String → Option (State → State)) : Prop :=
  (lsProg_46 H).CodeLoaded s.mem →
    ∃ s', Steps (lsProg_46 H) s s' ∧
      (Q s' ∨ (s'.status = .Panicked ∧ (s'.mem ⊨ deserializeSeedRawSpec.onPanic x s0 s' ∗ R)))

/-- Relocatable loop-head invariant at `(blkPl_46).base + 0x254` after decoding `k` fields of
`seedFields f` under `[LibsignalPlacement]`, carrying `LibsignalCodeRoLoaded lsmpl s.mem`. -/
@[expose] def DeserLoopPlaced [LibsignalPlacement] (x : DeserializeSeedGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPlacedPC 0x254#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocals (deserSpL s0.sp) x.p x.bs
        (((seedFields x.f).drop k).flatMap SeedField.enc) (ssvAfter x.f k) ∗
      memRegion x.out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

theorem deserStepPlaced_then [LibsignalPlacement] {H : String → Option (State → State)}
    {x : DeserializeSeedGhost} {R : SepProp} {s0 s : State} {Q : State → Prop}
    (h : DeserStepPlaced x R s0 s Q H)
    (k : ∀ s', Q s' → reaches_outcome (lsProg_46 H) deserializeSeedPlacedSpec x R s0 s') :
    reaches_outcome (lsProg_46 H) deserializeSeedPlacedSpec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s', hst, hq | ⟨hpan, hmem⟩⟩ := h hL
  · exact reaches_outcome_steps hst (k s' hq)
  · exact reaches_outcome_steps hst (reaches_outcome_refl_panic hpan hmem)

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
