/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs

/-!
# Frame and Loop-Head Definitions for PQXDH-Scope `SessionRecord::deserialize`

Extends `DeserializeGeneral/BodyDefs.lean` to PQXDH-scope records (`DeserializeScopeP`), replacing
`prostSSGAt` with `prostSSGXAt` (`SSGX`) and stepping over `recFieldsX r` at field-loop head `+0x254`.
-/

public section

namespace CryptoVerification.E2E.Record.L1GX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

/-- Stack-frame locals of `SessionRecord::deserialize` in the field loop at `L`, with
`SessionStructure` holding `v : SSGX`. -/
@[expose] def deserLocalsX (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGX) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGXAt A0 (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

theorem deserLocalsX_base (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) :
    deserLocalsX L p bs rest ⟨v, ExtraG.empty⟩ = deserLocalsG L p bs rest v := by
  unfold deserLocalsX deserLocalsG
  rw [prostSSGXAt_empty]

/-- Raw `RecordStructure` output at `out` with `prostSSGXAt` holding all decoded fields of
`recFieldsX r` at `out + 0x18`. -/
@[expose] def deserOutRecordX (out : BitVec 64) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSGXAt A0 (out + 0x18#64) (ssgxAfter r (recFieldsX r).length)

@[expose] def deserOutRawX (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗ deserOutRecordX x.out x.r ∗
    stackAt s0.sp recDeserializeStack

@[expose] def DeserRetX (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawX x s0 sf ∗ R)

end CryptoVerification.E2E.Record.L1GX
