/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Kits
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
import LibsignalBinary.Proofs.SpecLemmas.FsFold
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeySpec
public import LibsignalBinary.Specifications.SignalSession.Process
public import ProofLib
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRunProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun -- proof-setup: allow-public-import

set_option warningAsError false

/-!
# Callee Contracts for `signal-session` `main`

Callee contracts (`strlen`, `from_utf8`, `address`, `do_reserve_and_handle`, `try_allocate_in`)
and hook-shaped I/O contracts (`write_file`, `write_stdout`, and `IoModel` ghost records) used by
the `main` hop proofs.
-/

public section

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Adds `sf.fs = s0.fs` to `spec`'s normal-return postcondition (panic, exit, and OOM unchanged). -/
@[expose] def _root_.Arm64.Spec.keepsFs {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.fs = s0.fs⌝ ∗ spec.post x s0 sf }

/-- Mangled symbol name for `do_reserve_and_handle` (`Vec<&str>` growth in M2, `path_of` pushes in M5). -/
abbrev reserve11Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

/-- Mangled symbol name for `try_allocate_in` (`bundle.to_owned()` in `init`). -/
abbrev tryAllocateIn3Name : String := "<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]"

abbrev addressName : String := "libsignal_cli::address"

abbrev runName : String := "libsignal_cli::run"

abbrev mainReadStdinName : String := CryptoVerification.SignalSession.readStdinName

abbrev mainWriteFileName : String := CryptoVerification.SignalSession.writeFileName

abbrev mainWriteStdoutName : String := CryptoVerification.SignalSession.writeStdoutName

/-! ## In-image callees -/

/-- Contract of `strlen(p)` on a NUL-terminated byte slice `s` containing no interior NULs. -/
@[expose] def strlenSpec (hookStack : Nat) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, s) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ ∀ b ∈ s, b ≠ 0#8⌝ ∗ cStrAt p s ∗ stackAt s0.sp hookStack
  post := fun (p, s) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAt p s ∗
      stackAt s0.sp hookStack

/-- Contract of `core::str::from_utf8(bytes)` on ASCII bytes, writing `Ok(&bytes)` (`tag = 0` @0,
pointer @8, length @16) into the 24-byte `sret` slot at `x8`. -/
@[expose] def fromUtf8AsciiSpec (hookStack : Nat) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (r, p, bs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 (.gpr 8#5) = r ∧ ∀ b ∈ bs, b.toNat < 128⌝ ∗
      (p ↦ₛ bs) ∗ memRegion r 24 ∗ stackAt s0.sp hookStack
  post := fun (r, p, bs) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (p ↦ₛ bs) ∗ (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ p) ∗
      ((r + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ stackAt s0.sp hookStack

structure AddressCall where
  out : BitVec 64
  p : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `signal_session::address(text)`: writes `Option<ProtocolAddress>` (32 bytes) at `x0`
(`None` iff word 0 is `-1`; `Some` is `protocolAddressAt` with an owned copy of `addrParse`'s name). -/
@[expose] def addressSpec (A : RustAlloc) (uuidParse : UuidParser) (resStack : Nat) : Spec AddressCall where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.out ∧ s0.readReg64 .x1 = x.p ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 x.bs.length⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 32 ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗ (x.p ↦ₛ x.bs) ∗ A.pool ∗ stackAt s0.sp resStack ∗
      (match addrParse uuidParse x.bs with
       | none => (x.out ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.out + 8#64) 24
       | some a => ∃∗ g : AddrGhost,
           ⌜g.name.bytes = a.name ∧ g.name.cap = BitVec.ofNat 64 a.name.length ∧
             g.device = a.device⌝ ∗ protocolAddressAt A g x.out)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

structure Reserve16Call where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- A `Vec` of 16-byte elements at `v`, represented by its raw byte payload across reallocations. -/
@[expose] def vec16At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 (bs.length / 16)) ∗
    ⌜bs.length % 16 = 0 ∧ bs.length ≤ 16 * cap.toNat ∧ 16 * cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr (16 * cap.toNat) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (16 * cap.toNat - bs.length))

/-- Contract of `do_reserve_and_handle` with `additional = 1`, align 8, and stride 16 (`M+0x180`),
requiring `16 * x.cap.toNat < 2 ^ 62` so amortized doubling cannot trigger capacity-overflow panic. -/
@[expose] def reserve16Spec (A : RustAlloc) (resStack : Nat) : Spec Reserve16Call where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.v ∧ s0.readReg64 .x1 = BitVec.ofNat 64 (x.bs.length / 16) ∧
      s0.readReg64 .x2 = 1#64 ∧ s0.readReg64 .x3 = 8#64 ∧ s0.readReg64 .x4 = 16#64 ∧
      16 * (x.bs.length / 16 + 1) < 2 ^ 62 ∧ 16 * x.cap.toNat < 2 ^ 62⌝ ∗
      vec16At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp resStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜x.bs.length / 16 + 1 ≤ cap'.toNat⌝ ∗ vec16At A x.v cap' p' x.bs) ∗
      A.pool ∗ stackAt s0.sp resStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

open CryptoVerification.E2E.Pqxdh.Shared in
/-- Contract of `try_allocate_in` parameterized by an explicit stack budget `resStack`. -/
@[expose] def tryAllocateInSpecOf (resStack : Nat) (A : RustAlloc) : Spec TryAllocateInCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗
      (if tag = 1#64 then
        ((x.out + 8#64) ↦₆₄ x.align) ∗
        ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
        ⌜p' = 0#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ((x.out + 8#64) ↦₆₄ x.new) ∗
        ((x.out + 16#64) ↦₆₄ p') ∗
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
          memRegion p' (x.new.toNat * x.stride.toNat)) ∗
      A.pool ∗ stackAt s0.sp resStack

/-! ## I/O Callees -/

/-- Abstract I/O model parameterizing `main`'s file and stdio contracts. -/
structure IoModel where
  /-- Read rule for `read_file`. -/
  rd : ReadRule
  /-- Write rule for `write_file`: `some F'` on `Ok`, `none` on `Err`. -/
  wr : WriteRule
  /-- Remaining stdin bytes on `FsState` (`none` if fd 0 is outside the model). -/
  stdin : FsState → Option (List (BitVec 8))
  /-- Modelled file-system paths. -/
  pathOk : List (BitVec 8) → Prop

structure ReadStdinGhost where
  ret : BitVec 64
  bs : List (BitVec 8)

structure ReadFileLitGhost where
  pathA : BitVec 64
  path : List (BitVec 8)
  ret : BitVec 64

structure WriteFileGhost where
  pathA : BitVec 64
  path : List (BitVec 8)
  buf : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `write_file(path, bytes)` (`Result<(), IoError>` in `x0`: `0` Ok, `1` Err):
updates `fs.files` via `io.wr` with stdout unchanged. -/
@[expose] def writeFileSpec (io : IoModel) (stk : Nat) : Spec WriteFileGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜(match io.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
      s0.trace <+: sf.trace ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk

structure WriteStdoutGhost where
  buf : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `write_stdout(bytes)`: appends `bs` to stdout with `fs.files` unchanged and returns `0`. -/
@[expose] def writeStdoutSpec (stk : Nat) : Spec WriteStdoutGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
      ProcessOutcome.traceStreamBytes .stdout sf.trace =
        ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk

/-! ## `run` -/

structure RunCall where
  i : Inputs
  c : CallV
  a : RunAnswer
  res : BitVec 64
  call : BitVec 64
  stores : BitVec 64
  inp : BitVec 64
  coins : BitVec 64

end CryptoVerification.SignalSession.Cli.MainHops
