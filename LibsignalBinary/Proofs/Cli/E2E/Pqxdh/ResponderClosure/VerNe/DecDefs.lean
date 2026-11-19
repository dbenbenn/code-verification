/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Defs

/-!
# Inlined `SessionStructure::decode` Seam Definitions

Stack budget (`overDecStackX`), `previous_sessions` element buffer layout (`overPrevElemAt`),
closure stack scratch predicates (`overDecScratchPre`, `overDecScratchPost`), and seam statements
(`OverPrevDecodeCliStmtGenExt`) for the inlined `SessionStructure::decode` block
(`+0x1ee8 → +0x2620`) in the CLI PQXDH responder closure.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (prostSSGQAt ssgqOf)

/-- Callee stack budget (64 KiB) below closure `sp` during inlined `SessionStructure::decode`. -/
abbrev overDecStackX : Nat := 65536

/-- Buffer half of `prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`:
for `prevCap ≠ 0#64`, `prevVecAt A r prevCap prevPtr [enc]` equals
`HdrP r prevCap prevPtr 1#64 ∗ overPrevElemAt A prevCap prevPtr enc`. -/
@[expose] def overPrevElemAt (A : RustAlloc) (prevCap prevPtr : BitVec 64) (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    (A.live prevPtr (prevCap.toNat * 24) 8 ∗ vecU8 A prevPtr enc ∗
      memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24))

theorem prevVecAt_one_eq_elemAt (A : RustAlloc) (r prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A r prevCap prevPtr [enc] =
      HdrP r prevCap prevPtr 1#64 ∗ overPrevElemAt A prevCap prevPtr enc :=
  prevVecAt_one_eq A r prevCap prevPtr enc hcap

/-- Stack scratch region touched by inlined `SessionStructure::decode` (`+0x1ee8 → +0x2620`):
- `sp + 0x920` (16B): `prost` `&[u8]` slice cursor `{ptr, end}`;
- `sp + 0x930` (344B): destination `SessionStructure` (`x21`);
- `sp + 0xa88` (8B): `merge_varint` cursor pointer scratch;
- `sp + 0xa90` (344B): nested field `merge` scratch (`x28`);
- `sp + 0xbe8` (136B): `DecodeError` return / `be8` cursor pointer scratch. -/
@[expose] def overDecScratchPre (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x920#64) 16 ∗
  memRegion (sp + 0x930#64) 344 ∗
  memRegion (sp + 0xa88#64) 8 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  memRegion (sp + 0xbe8#64) 136

/-- Stack scratch region returned intact after `+0x1ee8 → +0x2620` (all slots except `sp + 0x930`,
which now holds `prostSSGQAt A0 (sp + 0x930#64) (ssgqOf sess)`). -/
@[expose] def overDecScratchPost (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x920#64) 16 ∗
  memRegion (sp + 0xa88#64) 8 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  memRegion (sp + 0xbe8#64) 136

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
