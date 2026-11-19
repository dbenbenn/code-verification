/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.IoHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.AesHooks0

public section

set_option autoImplicit false

/-!
# Fixed-Image Hook Table, Extern Map, and Load Base

**Checked by Lean.** Fixed-image extern definitions for the `libsignal-cli` CLI: demangled I/O
stub names (`readFileName`, `writeFileName`, `readStdinName`, `writeStdoutName`), hook table
`cliHookTable`, panic-wrapped extern map `cliExterns`, and fixed load base `cliBase = 0x400000`.

**DEV-E1 (machine model): hooks write only their outputs (legacy `cliHookTable` only; the ELF
headlines in `CliBinaryPq.lean` run `Program.pureMem` with zero hooks or overrides).**
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib

/-- Demangled extern stub name for `libsignal_cli_io::read_file`. -/
@[expose] def readFileName : String := "libsignal_cli_io::read_file"

@[expose] def writeFileName : String := "libsignal_cli_io::write_file"

@[expose] def readStdinName : String := "libsignal_cli_io::read_stdin"

@[expose] def writeStdoutName : String := "libsignal_cli_io::write_stdout"

/-- Canonical byte-slice equality comparator replacing the retired `CliHooks.bcmp` field. -/
@[expose] def cliDefaultBcmp (a b : List (BitVec 8)) : BitVec 64 :=
  if a == b then 0#64 else 1#64

theorem cliDefaultBcmp_ok (a b : List (BitVec 8)) (_hlen : a.length = b.length) :
    (cliDefaultBcmp a b).setWidth 32 = 0#32 ↔ a = b := by
  unfold cliDefaultBcmp
  by_cases h : a = b
  · simp [h]
  · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-- Canonical invalid-UTF-8 error witness replacing the retired `CliHooks.utf8Err` field. -/
@[expose] def cliDefaultUtf8Err : List (BitVec 8) → BitVec 64 × BitVec 16 :=
  fun _ => (0#64, 0#16)

/-! ## Legacy Read and Linked CLI Extern Contracts -/

/-- `Err(IoError)` of a `Result<Vec<u8>, IoError>` at sret `x8` (capacity niche
`0xFFFF_FFFF_FFFF_FFFF` at `[x8]`, then return; legacy read-hook helper). -/
@[expose] def vecErr : State → State :=
  retHook fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) 0xFFFFFFFFFFFFFFFF#64)

/-- `Ok(Vec::new())` at sret `x8` (`{cap = 0, ptr = 1, len = 0}` via `E2E.writeVecHeader`, then
return; legacy read-hook helper). -/
@[expose] def vecEmptyOk : State → State :=
  retHook fun s => s.setMem (E2E.writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)

/-- `Ok(bs)` at the sret (legacy read-hook model, outside the `Computational/Theorems/` headline
closure because `read_file` and `read_stdin` are linked directly in `cliDehookedSymsPlaced`; kept
for fixed-image/legacy proofs): `vecEmptyOk` for empty `bs`; otherwise a lowest-fit heap block of
`bs.length` bytes (`E2E.bumpThen`, the allocator hooks' block), `bs` copied in, the header
`{len, block, len}`. If no block fits: `E2E.allocPanicHook` (log `allocFailedEvent`, then
`.Panicked`), as for every other failed allocation of the legacy hook-allocator CLI. -/
@[expose] def vecOk (bs : List (BitVec 8)) : State → State :=
  if bs.isEmpty then vecEmptyOk
  else
    E2E.bumpThen bs.length 1
      (fun s p => retHook (fun s =>
        let n := BitVec.ofNat 64 bs.length
        s.setMem (E2E.writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8) n p n)) s)
      E2E.allocPanicHook

/-- Legacy hook contract for `libsignal_cli_io::read_file(path: &str = (x0, x1)) -> Result<Vec<u8>, IoError>`
(sret `x8`); `lsReadFileSym` is linked directly in `cliDehookedSymsPlaced` (outside the headline
closure). -/
@[expose] def readFileHook (s : State) : State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  if !(s.mem.canRead ptr len.toNat && s.mem.canWrite (s.readReg64 .x8) 24) then
    unmodelled "read_file: unreadable path or unwritable result" s
  else
    let raw := s.mem.readBytes ptr len.toNat
    if cliPathMaxBytes ≤ len.toNat || raw.contains 0#8 then
      vecErr s
    else
      let p := readPath s.mem ptr len
      if !PathOk p then unmodelled "read_file: path outside the model" s
      else
        match blockingAncestor? s.fs p with
        | some (some _) => vecErr s
        | some none => vecEmptyOk s
        | none =>
          match s.fs.files p with
          | some (.file bs) =>
            if bs.length ≤ fileCapBytes then vecOk bs s else vecErr s
          | some .dir => vecErr s
          | none => vecEmptyOk s

/-- Legacy hook contract for `libsignal_cli_io::read_stdin() -> Result<Vec<u8>, IoError>` (sret
`x8`); `lsReadStdinSym` is linked directly in `cliDehookedSymsPlaced` (outside the headline
closure). -/
@[expose] def readStdinHook (s : State) : State :=
  if !s.mem.canWrite (s.readReg64 .x8) 24 then unmodelled "read_stdin: unwritable result" s
  else
    match s.fs.fds 0#64 with
    | some e =>
      if e.kind == .stdio && e.accMode.canRead then
        let rest := s.fs.stdin.drop e.offset
        if rest.length ≤ stdinCapBytes then
          vecOk rest (s.setFs (s.fs.setFd 0#64 (some { e with offset := e.offset + rest.length })))
        else
          vecErr (s.setFs (s.fs.setFd 0#64 (some { e with offset := e.offset + (stdinCapBytes + 1) })))
      else unmodelled "read_stdin: file descriptor 0 is not readable standard input" s
    | none => unmodelled "read_stdin: file descriptor 0 is closed" s

theorem allPerm_mono_len (m : Memory) (pred : Option Perm → Bool) :
    ∀ {k₁ k₂ : Nat} (p : BitVec 64), k₁ ≤ k₂ → m.allPerm pred p k₂ = true →
      m.allPerm pred p k₁ = true
  | 0, _, _, _, _ => rfl
  | k₁ + 1, 0, _, hle, _ => absurd hle (Nat.not_le_of_gt (Nat.succ_pos _))
  | k₁ + 1, k₂ + 1, p, hle, h => by
    simp only [Memory.allPerm, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, allPerm_mono_len m pred (p + 1#64) (Nat.le_of_succ_le_succ hle) h.2⟩

theorem allNoLazyFree_mono_len (m : Memory) :
    ∀ {k₁ k₂ : Nat} (p : BitVec 64), k₁ ≤ k₂ → m.allNoLazyFree p k₂ = true →
      m.allNoLazyFree p k₁ = true
  | 0, _, _, _, _ => rfl
  | k₁ + 1, 0, _, hle, _ => absurd hle (Nat.not_le_of_gt (Nat.succ_pos _))
  | k₁ + 1, k₂ + 1, p, hle, h => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, allNoLazyFree_mono_len m (p + 1#64) (Nat.le_of_succ_le_succ hle) h.2⟩

theorem canRead_mono_len (m : Memory) {k₁ k₂ : Nat} (p : BitVec 64) (hle : k₁ ≤ k₂)
    (h : m.canRead p k₂ = true) : m.canRead p k₁ = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h ⊢
  exact ⟨allPerm_mono_len m _ p hle h.1, allNoLazyFree_mono_len m p hle h.2⟩

theorem exists_strlenNul_iff (m : Memory) (p : BitVec 64) :
    (∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8) ↔
      ∃ n < 2 ^ 64, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8 := by
  constructor
  · rintro ⟨n, hcr, hr8⟩
    refine ⟨n % 2 ^ 64, Nat.mod_lt n (by positivity),
      canRead_mono_len m p (Nat.add_le_add_right (Nat.mod_le n (2 ^ 64)) 1) hcr, ?_⟩
    have hbv : BitVec.ofNat 64 (n % 2 ^ 64) = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp
    rw [hbv]; exact hr8
  · rintro ⟨n, _, h⟩
    exact ⟨n, h⟩

/-- Constructively decides existence of a readable NUL byte starting at `p` by bounding `n < 2 ^ 64`.
Note: evaluates quickly when a short NUL-terminated string is present, but scans up to `2 ^ 64`
offsets if every address were readable and non-zero. -/
local instance instDecidableExistsStrlenNul (m : Memory) (p : BitVec 64) :
    Decidable (∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8) :=
  letI : Decidable (∃ n < 2 ^ 64, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8) :=
    E2E.decExistsLt (2 ^ 64)
      (fun n => m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8)
  decidable_of_iff
    (∃ n < 2 ^ 64, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8)
    (exists_strlenNul_iff m p).symm

/-- `strlen(s = x0) -> size_t` (`x0`): the least `n` such that the bytes `[s, s + n]` are readable
and byte `s + n` is `0`; `.Exception` if there is none. -/
@[expose] def strlenHook (s : State) : State :=
  let p := s.readReg64 .x0
  if h : ∃ n, s.mem.canRead p (n + 1) = true ∧ s.mem.read8 (p + BitVec.ofNat 64 n) = 0#8 then
    retHook (fun s => s.writeReg64 .x0 (BitVec.ofNat 64 (Nat.find h))) s
  else unmodelled "strlen: no readable NUL" s

/-- `strlenHook` agrees pointwise with the `Classical.propDecidable` definition. -/
theorem strlenHook_eq_classical (s : State) :
    strlenHook s =
      (let p := s.readReg64 .x0
       @dite _ (∃ n, s.mem.canRead p (n + 1) = true ∧ s.mem.read8 (p + BitVec.ofNat 64 n) = 0#8)
         (Classical.propDecidable _)
         (fun h => retHook (fun s' => s'.writeReg64 .x0 (BitVec.ofNat 64
           (@Nat.find _ (fun n => Classical.propDecidable
             (s.mem.canRead p (n + 1) = true ∧ s.mem.read8 (p + BitVec.ofNat 64 n) = 0#8)) h))) s)
         (fun _ => unmodelled "strlen: no readable NUL" s)) := by
  unfold strlenHook
  dsimp only
  by_cases h : ∃ n, s.mem.canRead (s.readReg64 .x0) (n + 1) = true ∧
      s.mem.read8 (s.readReg64 .x0 + BitVec.ofNat 64 n) = 0#8
  · simp only [h, ↓reduceDIte]
    exact congrArg (fun dec => retHook (fun s' => s'.writeReg64 .x0 (BitVec.ofNat 64 (@Nat.find _ dec h))) s)
      (funext fun _ => Subsingleton.elim _ _)
  · simp only [h, ↓reduceDIte]

/-- `core::slice::memchr::memrchr(x: u8 = w0, text: &[u8] = (x1, x2)) -> Option<usize>`
(`x0` = tag, `x1` = value). -/
@[expose] def memrchrHook (s : State) : State :=
  let x := (s.readReg64 .x0).setWidth 8
  let ptr := s.readReg64 .x1
  let len := s.readReg64 .x2
  if !s.mem.canRead ptr len.toNat then unmodelled "memrchr: unreadable bytes" s
  else
    let bs := s.mem.readBytes ptr len.toNat
    match ((List.range bs.length).filter fun i => bs[i]? == some x).getLast? with
    | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
    | none => retHook (fun s => s.writeReg64 .x0 0#64) s

/-- **`bs` is well-formed UTF-8**: the UTF-8 encoding (`String.utf8EncodeChar`, shortest form) of
some list of Unicode scalar values (`Char`: no surrogates, at most U+10FFFF). -/
@[expose] def Utf8Ok (bs : List (BitVec 8)) : Prop :=
  ∃ cs : List Char, (cs.flatMap String.utf8EncodeChar).map UInt8.toBitVec = bs

private theorem toByteArray_loop_toList :
    ∀ (xs : List UInt8) (acc : ByteArray),
      (List.toByteArray.loop xs acc).data.toList = acc.data.toList ++ xs
  | [], acc => by simp [List.toByteArray.loop]
  | x :: xs, acc => by
    rw [List.toByteArray.loop, toByteArray_loop_toList]
    simp [ByteArray.push]

theorem utf8Ok_iff_isValidUTF8 (bs : List (BitVec 8)) :
    Utf8Ok bs ↔ (ByteArray.mk (bs.map UInt8.ofBitVec).toArray).IsValidUTF8 := by
  constructor
  · rintro ⟨cs, h⟩
    refine ⟨cs, ?_⟩
    apply ByteArray.ext
    apply Array.ext'
    have h1 := congrArg (List.map UInt8.ofBitVec) h.symm
    simpa [List.utf8Encode, List.toByteArray, toByteArray_loop_toList, Function.comp_def] using h1
  · rintro ⟨cs, h⟩
    refine ⟨cs, ?_⟩
    have h1 := congrArg (fun ba : ByteArray => ba.data.toList.map UInt8.toBitVec) h
    simpa [List.utf8Encode, List.toByteArray, toByteArray_loop_toList, Function.comp_def] using h1.symm

local instance instDecidableUtf8Ok (bs : List (BitVec 8)) : Decidable (Utf8Ok bs) :=
  decidable_of_iff (ByteArray.mk (bs.map UInt8.ofBitVec).toArray).IsValidUTF8
    (utf8Ok_iff_isValidUTF8 bs).symm

example : decide (Utf8Ok [0x68#8, 0x69#8]) = true := by decide
example : decide (Utf8Ok [0xff#8]) = false := by decide

/-- `core::str::converts::from_utf8(v: &[u8] = (x0, x1)) -> Result<&str, Utf8Error>` (sret `x8`,
24 bytes). -/
@[expose] def fromUtf8Hook (err : List (BitVec 8) → BitVec 64 × BitVec 16) (s : State) :
    State :=
  let ptr := s.readReg64 .x0
  let len := s.readReg64 .x1
  let r := s.readReg64 .x8
  if !(s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) then
    unmodelled "from_utf8: unreadable bytes or unwritable result" s
  else
    let bs := s.mem.readBytes ptr len.toNat
    if Utf8Ok bs then
      retHook (fun s => s.setMem (((s.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64
        (r + 16#64) len)) s
    else
      retHook (fun s => s.setMem (((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).write16
        (r + 16#64) (err bs).2)) s

/-- `fromUtf8Hook` agrees pointwise with the `Classical.propDecidable` definition. -/
theorem fromUtf8Hook_eq_classical (err : List (BitVec 8) → BitVec 64 × BitVec 16) (s : State) :
    fromUtf8Hook err s =
      (let ptr := s.readReg64 .x0
       let len := s.readReg64 .x1
       let r := s.readReg64 .x8
       if !(s.mem.canRead ptr len.toNat && s.mem.canWrite r 24) then
         unmodelled "from_utf8: unreadable bytes or unwritable result" s
       else
         let bs := s.mem.readBytes ptr len.toNat
         @ite _ (Utf8Ok bs) (Classical.propDecidable (Utf8Ok bs))
           (retHook (fun s => s.setMem (((s.mem.write64 r 0#64).write64 (r + 8#64) ptr).write64
             (r + 16#64) len)) s)
           (retHook (fun s => s.setMem (((s.mem.write64 r 1#64).write64 (r + 8#64) (err bs).1).write16
             (r + 16#64) (err bs).2)) s)) := by
  unfold fromUtf8Hook
  dsimp only
  split
  · rfl
  · exact congrArg (fun dec =>
      @ite _ (Utf8Ok (s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat)) dec _ _)
      (Subsingleton.elim _ _)

/-- `<SystemTime>::duration_since(&self = x0, earlier = (x1 = tv_sec, w2 = tv_nsec))
-> Result<Duration, SystemTimeError>` (sret `x8`), matching `std`'s `Timespec::sub_timespec`. -/
@[expose] def durationSinceExactHook (s : State) : State :=
  let a := s.readReg64 .x0
  let r := s.readReg64 .x8
  if !(s.mem.canRead a 12 && s.mem.canWrite r 24) then
    unmodelled "duration_since: unreadable self or unwritable result" s
  else
    let ns1 := (s.mem.read32 (a + 8#64)).toNat
    let ns2 := ((s.readReg64 .x2).setWidth 32).toNat
    if ns1 < 1000000000 ∧ ns2 < 1000000000 then
      let t1 : Int := (s.mem.read64 a).toInt * 1000000000 + ns1
      let t2 : Int := (s.readReg64 .x1).toInt * 1000000000 + ns2
      let d := (t1 - t2).natAbs
      let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
      retHook (fun s => s.setMem (((s.mem.write64 r tag).write64 (r + 8#64)
        (BitVec.ofNat 64 (d / 1000000000))).write32 (r + 16#64)
        (BitVec.ofNat 32 (d % 1000000000)))) s
    else unmodelled "duration_since: tv_nsec out of range" s

/-- `bcmp(a = x0, b = x1, n = x2) -> int`: `x0 := bcmp (n bytes at a) (n bytes at b)`, return. -/
@[expose] def cliBcmpHook (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) : State → State :=
  retHook fun s =>
    let n := (s.readReg64 .x2).toNat
    s.writeReg64 .x0 (bcmp (s.mem.readBytes (s.readReg64 .x0) n)
      (s.mem.readBytes (s.readReg64 .x1) n))

/-- Fixed-image `(stubName, hook)` table combining the 18 PQXDH/SPQR hooks of
`E2E.pqxdhHookTable W.C W.Q` with the 28 allocator, libc, I/O, `core`/`std`, and session-crypto
hooks. -/
@[expose] def cliHookTable (W : CliHooks) : List (String × (State → State)) :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.pqxdhHookTable W.C W.Q ++ [
  -- Allocator (`__rust_dealloc` is a no-op, DEV-E6).
  ("__rustc::__rust_no_alloc_shim_is_unstable_v2", hookNoop),
  ("__rustc::__rust_alloc", E2E.allocHook0),
  ("__rustc::__rust_dealloc", E2E.deallocHook),
  ("__rustc::__rust_realloc", E2E.reallocHook0),
  ("__rustc::__rust_alloc_zeroed", E2E.allocZeroedHook0),
  -- libc.
  ("memset", hookMemset),
  ("memmove", hookMemmove),
  ("memcpy", hookMemcpy),
  ("bcmp", cliBcmpHook cliDefaultBcmp),
  ("strlen", strlenHook),
  -- I/O crate.
  (readFileName, readFileHook),
  (writeFileName, writeFileHook),
  (readStdinName, readStdinHook),
  (writeStdoutName, writeStdoutHook),
  -- `core` / `std`.
  ("core::slice::memchr::memrchr", memrchrHook),
  ("core::str::converts::from_utf8", fromUtf8Hook cliDefaultUtf8Err),
  ("core::fmt::write", E2E.fmtWriteHook0),
  ("alloc::fmt::format::format_inner", E2E.formatInnerHook0),
  ("<std::time::SystemTime>::duration_since", durationSinceExactHook),
  ("<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add",
    E2E.timeAddHook),
  -- `subtle::black_box`: identity on the low byte.
  ("subtle::black_box::<u8>", LibsignalSession.blackBoxHook),
  -- Session crypto primitives `W.C`.
  ("sha2::sha256::compress256", LibsignalHmac.compress256Hook W.C.F),
  ("signal_crypto::aes_cbc::aes_256_cbc_encrypt", E2E.aesEncHook0 W.C.E),
  ("signal_crypto::aes_cbc::aes_256_cbc_decrypt", E2E.aesDecHook0 W.C.D),
  ("<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from",
    LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey),
  ("<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
    LibsignalTripleRatchet.diffieHellmanHook W.C.X),
  -- Secret zeroization on drop.
  ("<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop",
    LibsignalTripleRatchet.zeroizeSecretHook),
  ("<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop",
    LibsignalTripleRatchet.zeroizeSecretHook)]

/-- Unreached `InMem*Store` hashbrown `Fallibility` `#1` panic stubs (`0x488548`, `0x488550`),
left as zero (`udf #0`) words in the CLI ELF and excluded from `isCliPanicSymbol`. -/
@[expose] def deadCliHashbrownPanicNames : List String :=
  ["<hashbrown::raw::Fallibility>::capacity_overflow#1",
   "<hashbrown::raw::Fallibility>::alloc_err#1"]

/-- Fixed-image CLI panic predicate: `E2E.isImagePanicSymbol` excluding
`deadCliHashbrownPanicNames`. -/
@[expose] def isCliPanicSymbol (s : String) : Bool :=
  E2E.isImagePanicSymbol s && !(deadCliHashbrownPanicNames.contains s)

/-- Overrides `hooks` with `some Rust.panicked` on every `isCliPanicSymbol`. -/
@[expose] def withCliPanics (hooks : String → Option (State → State)) :
    String → Option (State → State) :=
  fun s => if isCliPanicSymbol s then some Rust.panicked else hooks s

private theorem not_isPanicSymbol_capacityOverflow1 :
    Rust.isPanicSymbol "<hashbrown::raw::Fallibility>::capacity_overflow#1" = false := by
  simp [Rust.isPanicSymbol]

private theorem not_isPanicSymbol_allocErr1 :
    Rust.isPanicSymbol "<hashbrown::raw::Fallibility>::alloc_err#1" = false := by
  simp [Rust.isPanicSymbol]

theorem isCliPanicSymbol_of_isPanicSymbol {s : String} (h : Rust.isPanicSymbol s = true) :
    isCliPanicSymbol s = true := by
  have hc : s ≠ "<hashbrown::raw::Fallibility>::capacity_overflow#1" := by
    rintro rfl
    rw [not_isPanicSymbol_capacityOverflow1] at h
    cases h
  have ha : s ≠ "<hashbrown::raw::Fallibility>::alloc_err#1" := by
    rintro rfl
    rw [not_isPanicSymbol_allocErr1] at h
    cases h
  simp [isCliPanicSymbol, E2E.isImagePanicSymbol, deadCliHashbrownPanicNames, h, hc, ha]

theorem isCliPanicSymbol_eq_false_of_isImagePanicSymbol_false {s : String}
    (h : E2E.isImagePanicSymbol s = false) : isCliPanicSymbol s = false := by
  simp [isCliPanicSymbol, h]

theorem withPanics_withCliPanics (X : String → Option (State → State)) :
    Rust.withPanics (withCliPanics X) = withCliPanics X := by
  funext s
  by_cases h : Rust.isPanicSymbol s = true
  · simp [Rust.withPanics, withCliPanics, h, isCliPanicSymbol_of_isPanicSymbol h]
  · simp [Rust.withPanics, h]

@[simp] theorem withCliPanics_of_isImagePanicSymbol_false
    (hooks : String → Option (State → State)) {s : String}
    (h : E2E.isImagePanicSymbol s = false) :
    withCliPanics hooks s = hooks s := by
  simp [withCliPanics, isCliPanicSymbol, h]

@[simp] theorem withCliPanics_of_isCliPanicSymbol_false
    (hooks : String → Option (State → State)) {s : String}
    (h : isCliPanicSymbol s = false) :
    withCliPanics hooks s = hooks s := by
  simp [withCliPanics, h]

@[simp] theorem withCliPanics_of_isCliPanicSymbol_true
    (hooks : String → Option (State → State)) {s : String}
    (h : isCliPanicSymbol s = true) :
    withCliPanics hooks s = some Rust.panicked := by
  simp [withCliPanics, h]

@[simp] theorem withCliPanics_of_isPanicSymbol_true
    (hooks : String → Option (State → State)) {s : String}
    (h : Rust.isPanicSymbol s = true) :
    withCliPanics hooks s = some Rust.panicked := by
  simp [withCliPanics, isCliPanicSymbol_of_isPanicSymbol h]

/-- Fixed-image extern map combining `withCliPanics` over `cliHookTable W` (`none` elsewhere). -/
@[expose] def cliExterns (W : CliHooks) : String → Option (State → State) :=
  withCliPanics fun name => (cliHookTable W).lookup name

/-- Fixed load base address `0x400000` (`snapshot-link --base`). -/
@[expose] def cliBase : BitVec 64 := 0x400000#64

end CryptoVerification.SignalSession
