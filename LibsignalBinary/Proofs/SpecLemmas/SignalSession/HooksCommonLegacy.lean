/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.UnmappedDecidable -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# Legacy Fixed-Image / Bump-Allocator Hook Helpers (`HooksCommonLegacy`)

**Checked by Lean.** Untrusted proof-side external-call hooks for the legacy `[2^60, 2^61)` bump
allocator, `String` cloning (`stringCloneHook0`), `SystemTime` addition (`timeAddHook`), and
fixed-image panic symbol helpers (`withImagePanics`), moved out of
`LibsignalBinary/Specifications/LibsignalE2E/HooksCommon.lean` (bump-allocator AES-256-CBC
`aesEncHook0` / `aesDecHook0` live in `LibsignalBinary/Proofs/E2E/AesHooks0.lean`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open LibsignalBinary.Proofs.Common.UnmappedDecidable (findIdxFrom findIdxFrom_isSome_iff)
open scoped LibsignalBinary.Proofs.Common.UnmappedDecidable

/-! ## The heap region and the lowest-fit bump -/

/-- Base of the heap region, `2^60`: far above the CLI's image (at `0x400000`), its
`mmap` slots (from `0x6000_0000_0000`) and its stack (top `0x7fff_ffff_0000`) (DEV-M6,
`SignalSession/CliBinaryPq.lean`). -/
@[expose] def heapBase : BitVec 64 := BitVec.ofNat 64 (2 ^ 60)

/-- Size of the heap region: `2^60` bytes, so the region is `[2^60, 2^61)` (no wrap-around). -/
@[expose] def heapSize : Nat := 2 ^ 60

/-- Offset `k` fits a block of `size` bytes with alignment `align` in `m`: `heapBase + k` is
`align`-aligned, the block lies inside the heap region, and every byte of it is unmapped. -/
@[expose] def HeapBlockFitsAt (m : Memory) (size align k : Nat) : Prop :=
  0 < align ∧ (heapBase + BitVec.ofNat 64 k).toNat % align = 0 ∧ k + size ≤ heapSize ∧
    Unmapped m (heapBase + BitVec.ofNat 64 k) size

@[expose] def decExistsLt (N : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∃ k < N, P k) :=
  decidable_of_iff ((findIdxFrom (fun k => decide (P k)) N 0).isSome = true)
    (by
      rw [findIdxFrom_isSome_iff]
      simp only [Nat.zero_le, Nat.zero_add, true_and, decide_eq_true_eq])

local instance instDecidableHeapBlockFitsAt (m : Memory) (size align k : Nat) :
    Decidable (HeapBlockFitsAt m size align k) :=
  inferInstanceAs (Decidable
    (0 < align ∧ (heapBase + BitVec.ofNat 64 k).toNat % align = 0 ∧ k + size ≤ heapSize ∧
      Unmapped m (heapBase + BitVec.ofNat 64 k) size))

theorem exists_heapBlockFitsAt_iff (m : Memory) (size align : Nat) :
    (∃ k, HeapBlockFitsAt m size align k) ↔
      ∃ k < heapSize + 1, HeapBlockFitsAt m size align k :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by have := hk.2.2.1; omega, hk⟩, fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

local instance instDecidableExistsHeapBlockFitsAt (m : Memory) (size align : Nat) :
    Decidable (∃ k, HeapBlockFitsAt m size align k) :=
  letI : Decidable (∃ k < heapSize + 1, HeapBlockFitsAt m size align k) :=
    decExistsLt (heapSize + 1) (HeapBlockFitsAt m size align)
  decidable_of_iff (∃ k < heapSize + 1, HeapBlockFitsAt m size align k)
    (exists_heapBlockFitsAt_iff m size align).symm

/-- **The lowest fit**: the block at the smallest offset that fits (`HeapBlockFitsAt`), `none` if no
offset does. It depends on `m` only through which bytes are mapped. -/
@[expose] def bumpAddr? (m : Memory) (size align : Nat) : Option (BitVec 64) :=
  if h : ∃ k, HeapBlockFitsAt m size align k then some (heapBase + BitVec.ofNat 64 (Nat.find h))
  else none

/-- `bumpAddr?` agrees pointwise with the `Classical.propDecidable` definition. -/
theorem bumpAddr?_eq_classical (m : Memory) (size align : Nat) :
    bumpAddr? m size align =
      @dite _ (∃ k, HeapBlockFitsAt m size align k) (Classical.propDecidable _)
        (fun h => some (heapBase + BitVec.ofNat 64
          (@Nat.find _ (fun k => Classical.propDecidable (HeapBlockFitsAt m size align k)) h)))
        (fun _ => none) := by
  unfold bumpAddr?
  by_cases h : ∃ k, HeapBlockFitsAt m size align k
  · simp only [h, ↓reduceDIte]
    exact congrArg (fun dec => some (heapBase + BitVec.ofNat 64 (@Nat.find _ dec h)))
      (funext fun _ => Subsingleton.elim _ _)
  · simp only [h, ↓reduceDIte]

example : (bumpAddr? Memory.empty 16 8).isSome = true := by decide

/-- Map a fresh block of `size` bytes (alignment `align`) at the lowest fit and continue with
`ok` on the state with the block mapped read-write and the block's address; `fail s` if nothing
fits. -/
@[expose] def bumpThen (size align : Nat) (ok : State → BitVec 64 → State)
    (fail : State → State) (s : State) : State :=
  match bumpAddr? s.mem size align with
  | some p => ok (s.setMem (s.mem.mapFresh p size Perm.rw)) p
  | none => fail s

/-! ## The allocator -/

/-- The failure of `__rust_alloc` / `__rust_realloc` / `__rust_alloc_zeroed` (their contracts'
`x0 = 0` branch): one `allocFailedEvent`, `x0 = 0`, return. -/
@[expose] def allocFail : State → State :=
  retHook fun s => (s.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64

/-- A stub that panics after a failed allocation: appends `allocFailedEvent`, status `Panicked`,
memory and registers unchanged. -/
@[expose] def allocPanicHook (s : State) : State :=
  (s.appendTrace [allocFailedEvent]).setStatus .Panicked

/-- The request of `__rust_alloc(size = x0, align = x1)` (and `__rust_alloc_zeroed`). -/
@[expose] def allocReq (s : State) : Nat × Nat := ((s.readReg64 .x0).toNat, (s.readReg64 .x1).toNat)

/-- `__rust_alloc`: the lowest-fit block of `x0` bytes, alignment `x1`, its address in `x0`. -/
@[expose] def allocHook0 (s : State) : State :=
  bumpThen (allocReq s).1 (allocReq s).2 (fun s p => retHook (fun s => s.writeReg64 .x0 p) s)
    allocFail s

/-- The request of `__rust_realloc(ptr = x0, old = x1, align = x2, new = x3)`. -/
@[expose] def reallocReq (s : State) : Nat × Nat := ((s.readReg64 .x3).toNat, (s.readReg64 .x2).toNat)

/-- `__rust_realloc`: a lowest-fit block of `new` bytes, the first `min old new` bytes of the old
block copied in, its address in `x0`; the old block is leaked (stays mapped). -/
@[expose] def reallocHook0 (s : State) : State :=
  let bs := s.mem.readBytes (s.readReg64 .x0) (min (s.readReg64 .x1).toNat (s.readReg64 .x3).toNat)
  bumpThen (reallocReq s).1 (reallocReq s).2
    (fun s q => retHook (fun s => (s.setMem (s.mem.writeBytes q bs)).writeReg64 .x0 q) s)
    allocFail s

/-- `__rust_alloc_zeroed`: as `allocHook0`, the block filled with `x0` zero bytes. -/
@[expose] def allocZeroedHook0 (s : State) : State :=
  bumpThen (allocReq s).1 (allocReq s).2
    (fun s p => retHook (fun s =>
      (s.setMem (s.mem.writeBytes p (List.replicate (allocReq s).1 0#8))).writeReg64 .x0 p) s)
    allocFail s

/-- `__rust_dealloc`: returns at once. Memory is never unmapped or reused.

**DEV-E6 (machine model): `__rust_dealloc` frees nothing.** The real allocator may hand a freed
block, with its old bytes, out again; here no block is reused within a call. A fresh block holds
the bytes its addresses held before it was mapped (`Memory.mapFresh`). Why: a simpler allocator.
Effect: w.l.o.g., argued: a reused block's old bytes are one more kind of residue, and outputs must
not depend on uninitialised bytes. No theorem checks this (no CLI theorem varies the initial
memory), so it rests on this argument alone. -/
@[expose] def deallocHook : State → State := hookNoop

/-! ## Hooks returning a fresh `Vec<u8>` -/

/-- A hook returning a fresh `Vec<u8>` holding `bs` in the sret `x8`: a lowest-fit block of
`bs.length` bytes (alignment 1; for empty `bs` the block is empty and its address, non-null, is the
dangling pointer of a capacity-0 `Vec`), `bs` copied in, the header `{len, block, len}`. If nothing
fits: `allocPanicHook` (one `allocFailedEvent`, then a panic, as the contracts allow). -/
@[expose] def returnFreshVecU8 (bs : List (BitVec 8)) : State → State :=
  bumpThen bs.length 1
    (fun s p => retHook (fun s =>
      let n := BitVec.ofNat 64 bs.length
      s.setMem (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8) n p n)) s)
    allocPanicHook

/-- The bytes of the `String` at `x0` (its header's `ptr` @8 and `len` @16). -/
@[expose] def cloneSrc (s : State) : List (BitVec 8) :=
  let v := s.readReg64 .x0
  s.mem.readBytes (s.mem.read64 (v + 8#64)) (s.mem.read64 (v + 16#64)).toNat

/-- `<String as Clone>::clone`: the bytes of `x0`'s `String` in a fresh `Vec<u8>` at the sret. -/
@[expose] def stringCloneHook0 (s : State) : State := returnFreshVecU8 (cloneSrc s) s

/-! ## `SystemTime` addition and fixed-image panic symbols -/

/-- `<SystemTime as Add<Duration>>::add(self = (x0 = tv_sec, w1 = tv_nsec), dur = (x2 = secs,
w3 = nanos))`: adds `secs` (unsigned) to signed `tv_sec` and `nanos` to `tv_nsec` (`u32`), carrying
`1` second when `nsec ≥ 10^9`; panics (`Rust.panicked`) if the resulting `sec` exceeds `i64::MAX`,
and otherwise writes `(sec, nsec)` to `(x0, x1)` and returns to `lr`. Matches `std`'s
`Timespec::checked_add_duration` followed by `expect`, and agrees with
`SystemTime.checkedAddSecs` when `nanos = 0`. -/
@[expose] def timeAddHook (s : State) : State :=
  let sec := (s.readReg64 .x0).toInt + ((s.readReg64 .x2).toNat : Int)
  let ns : BitVec 32 := (s.readReg64 .x3).setWidth 32 + (s.readReg64 .x1).setWidth 32
  let carry : Bool := decide (1000000000 ≤ ns.toNat)
  let sec' := if carry then sec + 1 else sec
  let ns' := if carry then ns - 1000000000#32 else ns
  if sec' ≤ 2 ^ 63 - 1 then
    ((s.writeReg64 .x0 (BitVec.ofInt 64 sec')).writeReg64 .x1 (ns'.setWidth 64)).setPC
      (s.readReg64 .lr)
  else Rust.panicked s

/-- Out-of-line panic stub `<alloc::vec::Vec<_, _>>::remove::assert_failed` not listed in
`Rust.isPanicSymbol`. -/
@[expose] def extraImagePanicNames : List String :=
  ["<alloc::vec::Vec<_, _>>::remove::assert_failed"]

/-- Whether `s` is an engine or image-local Rust panic symbol. -/
@[expose] def isImagePanicSymbol (s : String) : Bool :=
  Rust.isPanicSymbol s || extraImagePanicNames.contains s

/-- Extends `hooks` by mapping every symbol satisfying `isImagePanicSymbol` to `Rust.panicked`. -/
@[expose] def withImagePanics (hooks : String → Option (State → State)) : String → Option (State → State) :=
  fun s => if isImagePanicSymbol s then some Rust.panicked else hooks s

end CryptoVerification.E2E
