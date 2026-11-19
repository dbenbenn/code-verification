/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.PrevEncOK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Inlined `SessionStructure::decode` Loop Definitions

Loop-state invariants (`OverDecG`, `OverDecRegs`, `overDecHeap`), field-group predicates, and
per-step contracts (`OverPrevDecodeStmt`, `OverDecEntryStmt`, `OverDecHeadConsStmt`,
`OverDecHeadNilStmt`, `OverDecKeyStmt`, `OverDecArmStmtTR`) for the inlined
`SessionStructure::decode` range (`+0x1ee8..+0x2620`) in `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)

/-- Callee stack budget below closure frame `q` during inlined `SessionStructure::decode` (`64 KiB`). -/
abbrev overDecStackX : Nat := 65536

/-- The archived element of `previous_sessions` at `prevPtr` (`{encCap, encPtr, enc.length}`), its
buffer's allocation token and bytes, and the spare `(prevCap - 1) · 24` bytes with the outer token
(parameterized over `A : RustAlloc`). -/
@[expose] def overPrevElemAtExt (A : RustAlloc) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    A.live prevPtr (prevCap.toNat * 24) 8 ∗
    vecU8At A prevPtr encCap encPtr enc ∗
    memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24)

abbrev overPrevElemAt (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    SepProp :=
  overPrevElemAtExt CryptoVerification.E2E.Record.A0 prevCap prevPtr encCap encPtr enc

/-- Closure scratch owned by the decode before `+0x1ee8` (closure frame `q`). -/
@[expose] def overDecScratchPre (q : BitVec 64) : SepProp :=
  memRegion (q + 0x920#64) 112 ∗ memRegion (q + 0x990#64) 256 ∗
    memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbe8#64) 136

/-- Closure scratch after the decode at `+0x2620` (closure frame `q`, decoded value `v`,
allocator `A : RustAlloc`). -/
@[expose] def overDecScratchPostExt (A : RustAlloc) (q : BitVec 64) (v : SSGQ) : SepProp :=
  memRegion (q + 0x920#64) 16 ∗ prostSSGQAt A (q + 0x930#64) v ∗
    memRegion (q + 0xa88#64) 8 ∗ memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbe8#64) 136

abbrev overDecScratchPost (q : BitVec 64) (v : SSGQ) : SepProp :=
  overDecScratchPostExt CryptoVerification.E2E.Record.A0 q v

/-- Ghost bundle of the inlined `SessionStructure::decode` loop in `decryptPrekeyClosureName`. -/
structure OverDecG where
  q : BitVec 64
  r19 : BitVec 64
  r20 : BitVec 64
  r26 : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  encCap : BitVec 64
  encPtr : BitVec 64
  enc : List (BitVec 8)
  sv : State

/-- `overPrevElemAtExt A` without `encPtr ↦ₛ enc` (lent to the slice cursor during the decode loop). -/
@[expose] def overPrevElemRestExt (A : RustAlloc) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    A.live prevPtr (prevCap.toNat * 24) 8 ∗
    (vecHeader prevPtr encCap encPtr (BitVec.ofNat 64 enc.length) ∗
      ⌜enc.length ≤ encCap.toNat ∧ encCap.toNat < 2 ^ 63 ∧ encPtr ≠ 0⌝ ∗
      (A.live encPtr encCap.toNat 1 ∗
        memRegion (encPtr + BitVec.ofNat 64 enc.length) (encCap.toNat - enc.length))) ∗
    memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24)

abbrev overPrevElemRest (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    SepProp :=
  overPrevElemRestExt CryptoVerification.E2E.Record.A0 prevCap prevPtr encCap encPtr enc

/-- Spatial invariant of the decode loop at undecoded suffix `rest` and partial `SSGQ` value `v`
(allocator `A : RustAlloc`). -/
@[expose] def overDecHeapExt (A : RustAlloc) (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr
      g.enc rest ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool

abbrev overDecHeap (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overDecHeapExt CryptoVerification.E2E.Record.A0 g rest v

/-! ## Step Statements -/

/-- Varint arms: tags 1 (`session_version`), 5 (`previous_counter`), 10, 11 (registration ids). -/
@[expose] def OverDecVarintField : GenFieldQ → Prop
  | .base (.version _) | .base (.prevCounter _) | .remReg _ | .locReg _ => True
  | _ => False

/-- `bytes::merge` arms: tags 2, 3, 4 (identity keys, root key), 13 (`alice_base_key`),
15 (`pq_ratchet_state`). -/
@[expose] def OverDecBytesField : GenFieldQ → Prop
  | .base (.lik _) | .base (.rik _) | .base (.root _) | .abk _ | .pq _ => True
  | _ => False

/-- Tag 6 (`sender_chain`, `merge<Chain>` in place into `Option<Chain>`). -/
@[expose] def OverDecSenderField : GenFieldQ → Prop
  | .base (.sender _) => True
  | _ => False

/-- Tag 7 (`receiver_chains`, `merge<Chain>` into a temporary, then the push). -/
@[expose] def OverDecRecvField : GenFieldQ → Prop
  | .base (.recv _) => True
  | _ => False

/-- The fields of a session with neither pending pre-key are in one of the four groups. -/
@[expose] def OverDecAnyField (fl : GenFieldQ) : Prop :=
  OverDecVarintField fl ∨ OverDecBytesField fl ∨ OverDecSenderField fl ∨ OverDecRecvField fl

/-! ## Key and Arm Split of `OverDecFieldStmt` -/

/-- Jump-table target (closure offset) of a field's tag in `decryptPrekeyClosureName`. -/
@[expose] def overDecArmOff : GenFieldQ → BitVec 64
  | .base (.version _) => 0x21bc#64
  | .base (.lik _) => 0x22cc#64
  | .base (.rik _) => 0x22b8#64
  | .base (.root _) => 0x2290#64
  | .base (.prevCounter _) => 0x21e8#64
  | .base (.sender _) => 0x2214#64
  | .base (.recv _) => 0x22e0#64
  | .base (.pending _) | .pendingId _ _ | .pendingSpk _ _ _ => 0x2350#64
  | .remReg _ => 0x23a8#64
  | .locReg _ => 0x2390#64
  | .abk _ => 0x21d4#64
  | .kyber _ _ => 0x2258#64
  | .pq _ => 0x2200#64

/-- Wire type held in `x0` on entry to a field arm (`0` varint, `2` length-delimited). -/
@[expose] def overDecWt (fl : GenFieldQ) : BitVec 64 :=
  if fl.wt = .varint then 0#64 else 2#64

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
