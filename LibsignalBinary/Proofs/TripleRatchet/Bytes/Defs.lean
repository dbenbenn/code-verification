/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import ProofLib.GenDecodes

/-!
# `bytes::Bytes` Representation and Function Specifications

Defines the 32-byte `bytes::Bytes` memory layout and separation-logic contracts for
`<Bytes as From<Vec<u8>>>::from` (`0x423cc`), `promotable_even_drop` (`0x41098`),
`promotable_odd_drop` (`0x40fac`), `static_drop` (`0x40950`), `static_clone`, and unified `.rodata`
vtable `drop` dispatch (`[vtable + 0x20]`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## 1. Symbol Names, Vtable Addresses, and Kernel-Checked Guards -/

/-- `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from` at `.text` offset `0x423cc` (`271308`). -/
abbrev bytesFromVecName : String :=
  "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from"

/-- `bytes::bytes::promotable_even_drop` at `.text` offset `0x41098` (`266392`). -/
abbrev promotableEvenDropName : String :=
  "bytes::bytes::promotable_even_drop"

/-- `bytes::bytes::promotable_odd_drop` at `.text` offset `0x40fac` (`266156`). -/
abbrev promotableOddDropName : String :=
  "bytes::bytes::promotable_odd_drop"

/-- `bytes::bytes::static_drop` at `.text` offset `0x40950` (`264528`). -/
abbrev bytesStaticDropName : String :=
  "bytes::bytes::static_drop"

/-- `bytes::bytes::PROMOTABLE_EVEN_VTABLE` at `.rodata` offset `0x50820` (`329760`, 40 bytes). -/
abbrev promotableEvenVtableName : String :=
  "bytes::bytes::PROMOTABLE_EVEN_VTABLE"

/-- `bytes::bytes::PROMOTABLE_ODD_VTABLE` at `.rodata` offset `0x507f8` (`329720`, 40 bytes). -/
abbrev promotableOddVtableName : String :=
  "bytes::bytes::PROMOTABLE_ODD_VTABLE"

/-- Stack frame of `<Bytes as From<Vec<u8>>>::from` (`0x423cc`):
    `stp x29, x30, [sp, #-0x30]!` allocates 48 bytes; leaf on the `cap = len` path. -/
abbrev bytesFromVecStack : Nat := 48

/-- Stack budget of `bytes::bytes::promotable_even_drop` (`0x41098`):
    48-byte frame (`stp x29, x30, [sp, #-0x30]!`), popped at `+0x84` before tail-calling
    `__rust_dealloc` (`allocHookStack`). -/
abbrev promotableEvenDropStack : Nat := allocHookStack + 48

/-- Stack budget of `bytes::bytes::promotable_odd_drop` (`0x40fac`):
    48-byte frame (`stp x29, x30, [sp, #-0x30]!`), popped at `+0x80` before tail-calling
    `__rust_dealloc` (`allocHookStack`). -/
abbrev promotableOddDropStack : Nat := allocHookStack + 48

/-- Stack budget of `bytes::bytes::static_drop` (`0x40950`):
    single `ret` instruction, 0 bytes. -/
abbrev bytesStaticDropStack : Nat := 0

/-- Stack budget of the unified `bytesVtableDropSpec`: `allocHookStack + 48`. -/
abbrev bytesVtableDropStack : Nat := allocHookStack + 48

/-! ## 3. `bytes::Bytes` Layout and Representation Predicates

In `bytes 1.x` on 64-bit targets, `Bytes` is 32 bytes (`repr(C)`):
- `+0x00`: `vtable : &'static Vtable` (`0x42418`, `0x42484`, `0x424a8`: `str x8, [x19]`)
- `+0x08`: `ptr : *const u8` (`0x4240c`, `0x42470`, `0x424a0`: `str/stp` to `[x19, #8]`)
- `+0x10`: `len : usize` (`0x4240c`, `0x42474`, `0x424a0`: `stp` to `[x19, #16]`)
- `+0x18`: `data : AtomicPtr<()>` (`0x42410`, `0x42474`, `0x424a4`: `str/stp` to `[x19, #24]`)

When `<Bytes as From<Vec<u8>>>::from` (`0x423cc`) is called on a `Vec<u8>` with `cap = len`
(`0x423ec: subs xzr, x21, x22; 0x423f0: b.ne +0x38` not taken):
- **Case `len = 0`** (`0x423f4: cbz x21, +0x7c` → `0x42470..0x42494`):
  writes `vtable = staticVtableAddr b`, `ptr = 1`, `len = 0`, `data = 0`.
- **Case `len > 0` and `ptr &&& 1 = 0`** (`0x423fc: tbnz w9, #0, +0x9c` not taken → `0x42400..0x42424`):
  writes `vtable = promotableEvenVtableAddr b`, `ptr = ptr`, `len = len`, `data = ptr ||| 1`
  (`KIND_VEC = 0x1` tag in bit 0).
- **Case `len > 0` and `ptr &&& 1 ≠ 0`** (`0x423fc: tbnz w9, #0, +0x9c` taken → `0x42498..0x424b8`):
  writes `vtable = promotableOddVtableAddr b`, `ptr = ptr`, `len = len`, `data = ptr`
  (bit 0 of `ptr` is already `1`).
-/

/-- The `ptr` field stored at `Bytes + 0x08` by `Bytes::from(Vec<u8>)` when `cap = len`. -/
@[expose] def bytesPtr (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then 1#64 else ptr

/-- The `data` field stored at `Bytes + 0x18` by `Bytes::from(Vec<u8>)` when `cap = len`. -/
@[expose] def bytesData (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then 0#64
  else if ptr &&& 1#64 = 0#64 then ptr ||| 1#64
  else ptr

/-- Boxed byte-slice buffer predicate (`ptr ↦ₛ bs` with live heap ownership when non-empty,
matching `boxU8Buf` and `vecU8At` when `cap.toNat = bs.length`). -/
@[expose] def bytesBoxU8Buf (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

/-- The 32-byte `Bytes` header in memory at `p`: `{vtable @ +0, ptr @ +8, len @ +16, data @ +24}`. -/
@[expose] def bytesHeader (p vtable ptr len data : BitVec 64) : SepProp :=
  (p ↦₆₄ vtable) ∗ ((p + 8#64) ↦₆₄ ptr) ∗
    ((p + 16#64) ↦₆₄ len) ∗ ((p + 24#64) ↦₆₄ data)

/-- Ghost state for `<Bytes as From<Vec<u8>>>::from`:
    `(v, out, cap, ptr, bs)` where `v` is the input `&Vec<u8>` header address (`x0`),
    `out` is the 32-byte `Bytes` sret address (`x8`), `cap` is the capacity word (`cap.toNat = bs.length`),
    `ptr` is the `Vec`'s buffer pointer, and `bs` is the byte list. -/
abbrev BytesFromVecGhost := BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)

/-- Ghost state for `promotable_even_drop` and `promotable_odd_drop`:
    `(ptr, bs, off)` where `ptr` is the backing buffer base pointer, `bs` is the buffer byte list
    (`cap = bs.length`), and `off ≤ bs.length` is the current cursor offset within the buffer. -/
abbrev BytesDropGhost := BitVec 64 × List (BitVec 8) × Nat

/-- Specification of `bytes::bytes::promotable_even_drop` (`0x41098`) on an unpromoted even-pointer
    `Bytes` buffer (`(ptr &&& 1#64) = 0#64`, `data = ptr ||| 1#64`, `bs ≠ []`):
    - `x0 = ptr ||| 1#64` (`data` value with `KIND_VEC = 1` tag in bit 0)
    - `x1 = ptr + BitVec.ofNat 64 off` (current slice cursor within `[ptr, ptr + bs.length]`)
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (remaining slice length, for any `off ≤ bs.length`)
    Reconstructs `buf_ptr = data &&& ~1 = ptr` and `cap = (x1 - ptr) + x2 = bs.length`, pops its
    48B frame, and tail-calls `__rust_dealloc(ptr, bs.length, 1)` (`0x47f30`), freeing the heap allocation. -/
@[expose] def promotableEvenDropSpec (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableEvenDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableEvenDropStack

/-- Specification of `bytes::bytes::promotable_odd_drop` (`0x40fac`) on an unpromoted odd-pointer
    `Bytes` buffer (`(ptr &&& 1#64) ≠ 0#64`, `data = ptr`, `bs ≠ []`):
    - `x0 = ptr` (`data` value, which already has bit 0 set)
    - `x1 = ptr + BitVec.ofNat 64 off` (current slice cursor within `[ptr, ptr + bs.length]`)
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (remaining slice length, for any `off ≤ bs.length`)
    Reconstructs `cap = (x1 - ptr) + x2 = bs.length`, pops its 48B frame, and tail-calls
    `__rust_dealloc(ptr, bs.length, 1)` (`0x47f30`), freeing the heap allocation. -/
@[expose] def promotableOddDropSpec (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableOddDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableOddDropStack

/-- Specification of `bytes::bytes::static_drop` (`0x40950`):
    single `ret` instruction (`0xd65f03c0`), no-op. -/
@[expose] def bytesStaticDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- Unified specification for dropping a `Bytes` via its vtable `drop` slot
    (`entry_pc = bytesDropFnAddr b ptr bs.length`, loaded from `[bytesVtable b ptr bs.length + 0x20#64]`):
    Whether `bs = []` (`STATIC_VTABLE` → `static_drop`), `bs ≠ []` with even `ptr`
    (`PROMOTABLE_EVEN_VTABLE` → `promotable_even_drop`), or `bs ≠ []` with odd `ptr`
    (`PROMOTABLE_ODD_VTABLE` → `promotable_odd_drop`), calling `bytesDropFnAddr b ptr bs.length` with:
    - `x0 = bytesData ptr bs.length`
    - `x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off`
    - `x2 = BitVec.ofNat 64 (bs.length - off)` (for any `off ≤ bs.length`, e.g. `off = bs.length`
      in `prost::encoding::bytes::merge` after `copy_to_slice` or `off = 0` for direct drop)
    consumes `bytesBoxU8Buf A ptr bs` and returns to `X30`. -/
@[expose] def bytesVtableDropSpec (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStack

/-! ## 5. Subroutine Contract Targets on `tripleRatchetProgAt` -/

/-- Stack budget of `bytes::bytes::promotable_even_drop` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev promotableEvenDropStackX : Nat := extHookStack + 48

/-- Stack budget of `bytes::bytes::promotable_odd_drop` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev promotableOddDropStackX : Nat := extHookStack + 48

/-- Stack budget of the unified `bytesVtableDropSpecX` under `AllocContractsX`: `extHookStack + 48`. -/
abbrev bytesVtableDropStackX : Nat := extHookStack + 48

/-- `promotableEvenDropSpec A` at `promotableEvenDropStackX` (`= extHookStack + 48`). -/
@[expose] def promotableEvenDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableEvenDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableEvenDropStackX

/-- `promotableOddDropSpec A` at `promotableOddDropStackX` (`= extHookStack + 48`). -/
@[expose] def promotableOddDropSpecX (A : RustAlloc) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp promotableOddDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp promotableOddDropStackX

/-- `bytesVtableDropSpec A ptr bs off` at `bytesVtableDropStackX` (`= extHookStack + 48`). -/
@[expose] def bytesVtableDropSpecX (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp bytesVtableDropStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp bytesVtableDropStackX

/-- Symbol name of `STATIC_VTABLE` in `libsignalSessionData` (`bytes:.rodata..Lanon.3`). -/
abbrev staticVtableSym : String := "bytes:.rodata..Lanon.3"

/-- Symbol name of `bytes::bytes::static_clone` (Block `226`). -/
abbrev bytesStaticCloneName : String := "bytes::bytes::static_clone"

/-- Relocatable address of `STATIC_VTABLE` under `[LibsignalPlacement]`. -/
abbrev staticVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ staticVtableSym

/-- Relocatable address of `bytes::bytes::PROMOTABLE_ODD_VTABLE` under `[LibsignalPlacement]`. -/
abbrev promotableOddVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ promotableOddVtableName

/-- Relocatable address of `bytes::bytes::PROMOTABLE_EVEN_VTABLE` under `[LibsignalPlacement]`. -/
abbrev promotableEvenVtablePlacedAddr [LibsignalPlacement] : BitVec 64 :=
  lsρ promotableEvenVtableName

/-- The `vtable` pointer stored at `Bytes + 0x00` by `Bytes::from(Vec<u8>)` under `[LibsignalPlacement]`. -/
@[expose] def bytesPlacedVtable [LibsignalPlacement] (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then staticVtablePlacedAddr
  else if ptr &&& 1#64 = 0#64 then promotableEvenVtablePlacedAddr
  else promotableOddVtablePlacedAddr

/-- The target `drop` function address stored at `[bytesPlacedVtable ptr len + 0x20#64]` in `.rodata`
    under `[LibsignalPlacement]`:
    - `len = 0`: `lsmpl.base 224` (`bytes::bytes::static_drop`)
    - `len > 0` and `ptr &&& 1#64 = 0#64`: `lsmpl.base 237` (`bytes::bytes::promotable_even_drop`)
    - `len > 0` and `ptr &&& 1#64 ≠ 0#64`: `lsmpl.base 236` (`bytes::bytes::promotable_odd_drop`) -/
@[expose] def bytesPlacedDropFnAddr [LibsignalPlacement] (ptr : BitVec 64) (len : Nat) : BitVec 64 :=
  if len = 0 then lsmpl.base 224
  else if ptr &&& 1#64 = 0#64 then lsmpl.base 237
  else lsmpl.base 236

/-- Full ownership of a `Bytes` at `p` constructed from a `Vec<u8>` with `cap.toNat = bs.length` and
    buffer pointer `ptr` under `[LibsignalPlacement]`. -/
@[expose] def bytesPlacedAt [LibsignalPlacement] (A : RustAlloc) (p ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  bytesHeader p (bytesPlacedVtable ptr bs.length) (bytesPtr ptr bs.length)
    (BitVec.ofNat 64 bs.length) (bytesData ptr bs.length) ∗
  bytesBoxU8Buf A ptr bs

/-- Relocatable specification of `<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from`
    (Block `250`) when `cap.toNat = bs.length`. -/
@[expose] def bytesFromVecPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec BytesFromVecGhost where
  pre := fun (v, out, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x8 = out ∧ cap.toNat = bs.length⌝ ∗
    vecU8At A v cap ptr bs ∗
    memRegion out 32 ∗
    stackAt s.sp bytesFromVecStack
  post := fun (v, out, cap, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
    bytesPlacedAt A out ptr bs ∗
    stackAt s0.sp bytesFromVecStack

/-- Relocatable specification of `bytes::bytes::static_clone` (Block `226`):
    writes `{vtable = staticVtablePlacedAddr, ptr = x1, len = x2, data = 0}` to `sret` (`x8`). -/
@[expose] def bytesStaticClonePlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (out, ptr, len) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x1 = ptr ∧ s.readReg64 .x2 = len⌝ ∗
    memRegion out 32
  post := fun (out, ptr, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    bytesHeader out staticVtablePlacedAddr ptr len 0#64

end CryptoVerification.LibsignalTripleRatchet
