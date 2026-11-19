/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs

/-!
# Frame and Loop-Head Definitions for General `SessionRecord::deserialize`

Defines the stack-frame layout (`deserLocalsG`), field-loop head invariant (`DeserLoopG` at
`+0x254`), raw output layout (`deserOutRecordG`, `deserOutRawG`), and return postcondition
(`DeserRetG`) for `SessionRecord::deserialize` (`0x16ed4`) on an in-scope `SessionRecord`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

/-- Stack-frame locals of `SessionRecord::deserialize` in the field loop at `L`, with the
`SessionStructure` holding `v : SSG`. -/
@[expose] def deserLocalsG (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGAt A0 (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

/-- The `Ok(record)` bytes deserialize leaves at `out`, in `RecordStructure` form:
`previous_sessions` `{cap 0, ptr 8, len 0}` at `out`, the SS with all the record's fields at
`out + 0x18`. -/
@[expose] def deserOutRecordG (out : BitVec 64) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSGAt A0 (out + 0x18#64) (ssgAfter r (recFields r).length)

@[expose] def deserOutRawG (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗ deserOutRecordG x.out x.r ∗
    stackAt s0.sp recDeserializeStack

end CryptoVerification.E2E.Record.DeserializeGeneral
