/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Overrides
public import LibsignalBinary.Specifications.CryptoGames.AEAD.Aes256
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519
public import LibsignalBinary.Specifications.CryptoGames.Hash.Sha512
public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch

@[expose] public section

set_option autoImplicit false

/-!
# Whole-process correctness of the `libsignal-cli` ELF (PQXDH mode)

**Trusted: the statement.** Read it in full (see `Computational/docs/TRUSTED_BASE.md`).
`CliPqxdhBinaryCorrect bytes` states that `bytes` parses as an `ElfImage` (`ElfImage.parse`),
all 23 `.symtab` addresses resolve via `resolveCliElfAddrs` (`Arm64.Process.parseSymtabFull` and
`Arm64.Process.resolveSym`: 18 Rust panic entry points and 5 `libcrux_ml_kem` `SampleNTT` entry
points), and for all model extras `X : UnreachedPqxdhPrimitives`, the ELF-direct process
`cliRunElf elf addrs` (starting directly from plain `elf.loadState (cliProcessInputs i)` with zero
initial memory patches) is total except on `.OutOfMemory` (`CliReachesOOMElf elf addrs`, DEV-CLI15)
or `SampleNTT` seed divergence (`CliReachesSampleNttStuckElf elf addrs`, DEV-CLI22) and satisfies
`CliSpecPqxdh` (`PqDir.lean`) and `CliSpecPqxdhNoMatch` (`PqDirNoMatch.lean`, DEV-CLI11) at the
closed primitive bundle `realPEParams` (`realCrypto`, `realPqxdhPrims`: FIPS 180-4 SHA-256 /
SHA-512 compression, FIPS 197 AES-256, RFC 7748 X25519, round-3 Kyber-1024, and FIPS 203 ML-KEM-768
incremental).

The run uses no library placement (`Obj.MultiPlacement` / `libsignalSessionLib`) and no initial
memory patches: every instruction except the 18 Rust panic entry points (`cliPanicSymbolsPlaced`,
DEV-E7)—including `aes` and SPQR's CPU feature probes on the pinned auxv (`AT_HWCAP = 0x1b`,
`AT_HWCAP2 = 0`, `AT_RANDOM = 0^16`), all cryptographic primitives (including ARMv8 hardware AES
and SPQR `PMULL` GF(2¹⁶)), allocator, libc, and I/O routines—is fetched from plain loaded ELF
memory. The 23 addresses (18 panic entry points and 5 `SampleNTT` entries) are read directly from
the ELF's `.symtab`.

## Scope exclusions

* `keygen` (`PqDir.lean`) and usage-error paths (`CliRejectsMalformedCommandLine`).
* Party states outside `PqxdhPartyInSpecDomain`; `init` when a session already exists (DEV-C-PREV);
  non-canonical pre-key messages (DEV-CLI3); inputs of `2^32` bytes or more (`2^32 - 2048` for a
  pre-key message's inner message).
* After an accepted pre-key `recv` over a non-matching session: the written session file bytes and
  all subsequent calls on that directory (DEV-CLI11).
* Outputs and files on runs that reach `.OutOfMemory` (DEV-CLI15).
* Termination, outputs, and files on runs that reach one of the 5 `libcrux_ml_kem` `SampleNTT` entry
  points with a non-terminating SHAKE-128 matrix seed (`CliReachesSampleNttStuckElf`, DEV-CLI22).
* CPUs with ATOMICS/LSE (`AT_HWCAP = 0x1b`, `AT_HWCAP2 = 0` in `cliProcessInputs`: FP, ASIMD, AES,
  and PMULL enabled while LSE bit 8 is `0`, so `.init_array` `RUST_LSE_INIT` leaves outline atomics
  on the LL/SC path rather than ARMv8.1+ LSE; DEV-CLI10).

## Deviations of a run of the ELF

**DEV-M6 (machine model): fixed stack, heap, and `mmap` layout.** The ELF image `elf` is loaded
at its static segment addresses (for the pinned non-PIE ELF `cliElfBytes`, linked with stock
`ld.lld` under `cli-elf/stock/stock_c2.ld` at load base `0x400000`). The process gets an 8 MiB
stack with its top at `0x7fff_ffff_0000` (DEV-CLI7), the auxiliary vector of
`SignalSession/Process.lean` (`AT_RANDOM` = 16 zero bytes, `AT_HWCAP` = `0x1b` enabling FP, ASIMD,
AES, and PMULL while keeping LSE bit 8 `= 0`, `AT_HWCAP2` = `0`), empty initial signal mask and
pending set with default dispositions (launch assumption E1), `mmap` slots from `0x6000_0000_0000`,
and `brk` starting at `elf.brkStart`. A real kernel places the
stack, `brk`, and the `mmap` area at random addresses. Effect: out of scope: no claim for another
stack/`mmap`/`brk` layout.

**DEV-M7 (machine model): this ELF and its build.** The closed headline claims are about the ELF
pinned by SHA-256 in `CliElf.lean` (`cliElfBytes`): libsignal v0.105.4's `libsignal-cli` CLI built
from source by `scripts/cli-elf-stock --stdbin --build` from
`third_party/libsignal/libsignal-session/cli-elf/stock/inputs_stock_stdbin.lock` (rustc 1.98.1 and
its `aarch64-unknown-linux-musl` `self-contained/` CRT objects and `libc.a`, stock LLVM `ld.lld`
22.1.8 `--no-relax` under `cli-elf/stock/stock_c2.ld`, zig 0.16.0 for `rdl_shim.S` including
abort-only `rust_begin_unwind`/`__rust_alloc_error_handler` shims `b abort`, `std-main`, and
`libsignal-session/translation.toml` plus `cli/io/translation.toml`, with ARMv8 hardware AES and
SPQR `PMULL` autodetection and the software SHA-2 backend). Effect: out of scope: production builds,
other compilers and other flags are not covered.

**DEV-M11 (machine model): each call is a fresh process.** Each `init` / `send` / `recv` in
`cliRunElf elf addrs` runs from plain `elf.loadState (cliProcessInputs i)` under `cliProgElf addrs`
to `exit_group` or `SIGABRT`, with constant clock `UNIX_EPOCH`. Effect: out of scope for long-lived
processes.

**DEV-E7 (machine model): Rust panic entry points intercepted as `SIGABRT`.** Calls to the 18
crate-referenced Rust panic entry points (`cliPanicSymbolsPlaced`, resolved from `.symtab` into
`addrs.panicAddrs`) are intercepted by `cliProgElf addrs` (`abortOnPanic Rust.panicked`) and
reported as `ExecStatus.Signaled 6#7` (`SIGABRT`, exit 134) without executing the linked panic
handler body (in the pinned ELF, the linked bodies reach musl `abort` only via the abort-only
`rdl_shim.S` handlers `rust_begin_unwind` from `panic_fmt` and `__rust_alloc_error_handler` from
`handle_alloc_error`; the real ELF writes no stderr panic message either, so this is not a
modelling gap, and `Outcome` checks only signal 6 / exit 134).

**DEV-CLI10 (machine model): pinned auxiliary vector (`AT_HWCAP = 0x1b`, `AT_HWCAP2 = 0`).**
`CliRunsToElf` starts from plain `elf.loadState (cliProcessInputs i)` with no initial `.data`
patch, and both `aes` 0.9.1 and SPQR's `Once::call` probe execute `getauxval(AT_HWCAP)` against the
initial stack auxiliary vector (running ARMv8 hardware AES and SPQR `PMULL` GF(2¹⁶), while
`ATOMICS/LSE = 0` keeps outline atomics on LL/SC). Effect: out of scope for ARMv8.1+ LSE or other
`AT_HWCAP` values (also covers DEV-M17).

**DEV-CLI22 (machine model): unbounded `SampleNTT` rejection loop in `libcrux_ml_kem`.** With all
non-panic code executing from loaded ELF memory (`cliProgElf addrs`), the 5 matrix-sampling entry
points in `libcrux_ml_kem` (Kyber-1024 `encapsulate` / `decapsulate` and incremental ML-KEM-768
`from_seed` / `encapsulate1` / `decapsulate_compressed_key`) execute `sampling::sample_from_xof`
(`while !done` over SHAKE-128 12-bit candidates `< 3329`). Runs whose deterministic trajectory
reaches one of these 5 entry points in `.Running` status with a matrix seed that never yields 256
coefficients (`MlKemSampleNttStuckAtElf`, `CliReachesSampleNttStuckElf`) are excused from
termination in `CliPqxdhElfCorrect` and `CliElfProgress` (`ElfBinding.lean`), and counted via
`exc? := some (CliReachesSampleNttStuckElf elf addrs)` in `CliPqxdhElfSecure`
(`StatementPqElf.lean`). Effect: availability only; the headline security bound gains a
`2·CliPqxdhFlagProb` SampleNTT-divergence term.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.E2E

/-! ## Closed Cryptographic Primitive Bundle -/

/-- Closed `Crypto` primitives executed by the linked `libsignal-cli` ELF: FIPS 180-4 SHA-256
compression, FIPS 197 AES-256, and RFC 7748 X25519. -/
def realCrypto : Crypto where
  F := CryptoVerification.LibsignalSpqrV1.sha256Compress
  E := CryptoGames.AES256.aes256Enc
  D := CryptoGames.AES256.aes256Dec
  X := CryptoGames.RFC7748.x25519Ref
  pubKey := CryptoGames.RFC7748.x25519PubFromSecretRef

/-- Closed `PqxdhPrims` primitives executed by the linked `libsignal-cli` ELF: FIPS 180-4 SHA-512
compression, `libcrux` Kyber-1024 (round 3), and FIPS 203 ML-KEM-768 incremental. -/
noncomputable def realPqxdhPrims : PqxdhPrims where
  F512 := CryptoGames.SHA512.sha512CompressState
  encaps := CryptoGames.MLKEM.kyber1024EncapsVec
  decaps := CryptoGames.MLKEM.kyber1024DecapsVec
  K := CryptoGames.MLKEM.mlkem768Incremental

/-- Closed `PEParams` primitive bundle (`⟨realCrypto, realPqxdhPrims⟩`) executed by the linked
`libsignal-cli` ELF. -/
noncomputable def realPEParams : PEParams := ⟨realCrypto, realPqxdhPrims⟩

/-! ## Mangled ELF `.symtab` Symbol Names -/

/-- The `18` mangled Rust panic entry-point symbols intercepted as `SIGABRT` (DEV-E7). -/
def cliPanicSymbolsPlaced : List String :=
  ["_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_",
   "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_",
   "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error",
   "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error",
   "_RNvNtCskxtBwYRO61I_4core6option13expect_failed",
   "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed",
   "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check",
   "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner",
   "_RNvNtCskxtBwYRO61I_4core9panicking5panic",
   "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt",
   "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow",
   "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed",
   "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"]

/-- Mangled `.symtab` name of `libcrux_ml_kem` Kyber-1024 `encapsulate` (`SampleNTT` entry). -/
abbrev kyberEncapsElfSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"

/-- Mangled `.symtab` name of `libcrux_ml_kem` Kyber-1024 `decapsulate` (`SampleNTT` entry). -/
abbrev kyberDecapsElfSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"

/-- Mangled `.symtab` name of `libcrux_ml_kem` ML-KEM-768 incremental `from_seed` (`SampleNTT`). -/
abbrev mlkemFromSeedElfSym : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"

/-- Mangled `.symtab` name of `libcrux_ml_kem` ML-KEM-768 incremental `encapsulate1` (`SampleNTT`). -/
abbrev mlkemEncaps1ElfSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"

/-- Mangled `.symtab` name of `libcrux_ml_kem` ML-KEM-768 incremental `decapsulate_compressed_key`. -/
abbrev mlkemDecapsElfSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"

/-! ## Fail-Closed `.symtab` Resolution -/

/-- Resolved ELF `.symtab` addresses for the `libsignal-cli` ELF run: the `18` Rust panic entry
points (DEV-E7) and the `5` `libcrux_ml_kem` `SampleNTT` entry points (DEV-CLI22). -/
structure CliElfAddrs where
  panicAddrs : List Nat
  kyberEncapsVa : BitVec 64
  kyberDecapsVa : BitVec 64
  mlkemFromSeedVa : BitVec 64
  mlkemEncaps1Va : BitVec 64
  mlkemDecapsVa : BitVec 64
  deriving DecidableEq, Repr

/-- Fail-closed resolution of all 23 `.symtab` function addresses used by the `libsignal-cli` ELF
run specification from raw ELF `bytes` and parsed `elf` (with pairwise distinctness across the 18
panic sites and the 5 `SampleNTT` entry points). -/
def resolveCliElfAddrs (bytes : List (BitVec 8)) (elf : ElfImage) :
    Except String CliElfAddrs := do
  let (syms, shdrs) ← parseSymtabFull bytes
  let panicAddrs ← cliPanicSymbolsPlaced.mapM (resolveSym elf syms shdrs)
  let kyberEncaps ← resolveSym elf syms shdrs kyberEncapsElfSym
  let kyberDecaps ← resolveSym elf syms shdrs kyberDecapsElfSym
  let mlkemFromSeed ← resolveSym elf syms shdrs mlkemFromSeedElfSym
  let mlkemEncaps1 ← resolveSym elf syms shdrs mlkemEncaps1ElfSym
  let mlkemDecaps ← resolveSym elf syms shdrs mlkemDecapsElfSym
  if !(cliPanicSymbolsPlaced.Nodup ∧
      (panicAddrs ++ [kyberEncaps, kyberDecaps, mlkemFromSeed, mlkemEncaps1, mlkemDecaps]).Nodup) then
    .error "cli: duplicate panic symbol or function address"
  return {
    panicAddrs
    kyberEncapsVa := BitVec.ofNat 64 kyberEncaps
    kyberDecapsVa := BitVec.ofNat 64 kyberDecaps
    mlkemFromSeedVa := BitVec.ofNat 64 mlkemFromSeed
    mlkemEncaps1Va := BitVec.ofNat 64 mlkemEncaps1
    mlkemDecapsVa := BitVec.ofNat 64 mlkemDecaps
  }

/-! ## ELF-Direct Execution Model -/

/-- The 18 Rust panic overrides mapping each panic entry point to `SIGABRT` (`abortOnPanic`). -/
def cliPanicOverrides : List (String × (State → State)) :=
  cliPanicSymbolsPlaced.map (fun s => (s, abortOnPanic Rust.panicked))

/-- ELF-direct program: supervisor calls go to `execSyscall`, the 18 resolved Rust panic entry
points abort with `SIGABRT`, and every other instruction is fetched from loaded ELF memory. -/
def cliProgElf (addrs : CliElfAddrs) : Program :=
  overrideProgram execSyscall cliPanicOverrides addrs.panicAddrs

/-- ELF-direct process run relation for `elf` at resolved `.symtab` addresses `addrs` from plain
`elf.loadState (cliProcessInputs i)` (no initial `.data` patch). -/
def CliRunsToElf (elf : ElfImage) (addrs : CliElfAddrs) (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    ProcessRunsTo (cliProgElf addrs) s0 (OutcomeMatchesProcess o)

open Classical in
/-- ELF-direct deterministic process runner for `elf` at resolved `.symtab` addresses `addrs`. -/
noncomputable def cliRunElf (elf : ElfImage) (addrs : CliElfAddrs) : CliRun := fun i =>
  if h : ∃ o, CliRunsToElf elf addrs i o then some (Classical.choose h) else none

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec

/-! ## The PQXDH-mode input domain, `.OutOfMemory`, and `SampleNTT` divergence -/

/-- **The inputs of the PQXDH-mode specs at model primitives `W`**: the inputs of the calls of
`CliSpecPqxdh`'s five clauses and of `CliSpecPqxdhNoMatch`, for a party state `st` in the domain
(`PqxdhPartyInSpecDomain W st`):
1. `init <peer> bundle` with no session, any typed bundle `b` and the 192 coin bytes `t`;
2. `send <peer>` of a plaintext `m` below `2^32` bytes with the 64 coin bytes `r`;
3. `recv <peer>` of `2 ‖ c` with `c` below `2^32` bytes;
4. `recv <peer>` of `3 ‖ m.bytes` for a typed pre-key message `m` whose inner message is below
   `2^32 - 2048` bytes, at any session state (no session, a matching one: `CliSpecPqxdh`; one that
   does not match: `CliSpecPqxdhNoMatch`);
5. `recv <peer>` of any input `c` below `2^32` bytes whose first byte is neither `2` nor `3`, or of
   nothing.
In 2–5 the receive coins `rc` are any 32 bytes. -/
def CliPqxdhInputs (W : PEParams) (i : Inputs) : Prop :=
  ∃ st : PqParty, PqxdhPartyInSpecDomain W st ∧
    ((st.session = none ∧
        ∃ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), i = pqInitInputs W st b t) ∨
      (∃ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64),
        m.length < 2 ^ 32 ∧ i = pqSendInputs W st m r) ∨
      (∃ (c : List (BitVec 8)) (rc : BitVec 256),
        c.length < 2 ^ 32 ∧ i = pqRecvInputs W st (wireWhisper :: c) rc) ∨
      (∃ (m : PreKeyMessageFields) (rc : BitVec 256),
        m.inner.length + 2048 < 2 ^ 32 ∧ i = pqRecvInputs W st (wirePrekey :: m.bytes) rc) ∨
      (∃ (c : List (BitVec 8)) (rc : BitVec 256),
        c.length < 2 ^ 32 ∧ c.head? ≠ some wireWhisper ∧ c.head? ≠ some wirePrekey ∧
        i = pqRecvInputs W st c rc))

/-- Run on `i` reaches `s.status = .OutOfMemory` (`brk` / `mmap` / `mprotect` / `mremap`
exhaustion) from plain `s0` (DEV-CLI15). By determinism of `Step`, reaching `.OutOfMemory` forces
`cliRunElf elf addrs i = none` and excludes `.Exception`, `.Halted`, and divergence. -/
def CliReachesOOMElf (elf : ElfImage) (addrs : CliElfAddrs) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgElf addrs) s0 s ∧
    s.status = .OutOfMemory

/-- The 5 `libcrux_ml_kem` entry points that run `SampleNTT` (`sample_from_xof`), addressed directly
from `.symtab` (`addrs`). At entry `u` (AAPCS64 `x0`, and `x1` for `encapsulate1`'s length),
`MlKemSampleNttStuckAtElf addrs u` says the call's `SHAKE-128` matrix seed never yields 256
coefficients `< 3329`. -/
def MlKemSampleNttStuckAtElf (addrs : CliElfAddrs) (u : State) : Prop :=
  (u.pc = addrs.kyberEncapsVa ∧
    ¬ CryptoGames.MLKEM.Kyber1024EncapsTerminates (u.mem.readBytes (u.readReg64 .x0) 1568)) ∨
  (u.pc = addrs.kyberDecapsVa ∧
    ¬ CryptoGames.MLKEM.Kyber1024DecapsTerminates (u.mem.readBytes (u.readReg64 .x0) 3168)) ∨
  (u.pc = addrs.mlkemFromSeedVa ∧
    ¬ CryptoGames.MLKEM.Mlkem768FromSeedTerminates
        ⟨u.mem.readBytes (u.readReg64 .x0) 64, Memory.readBytes_length _ _ _⟩) ∨
  (u.pc = addrs.mlkemEncaps1Va ∧
    ¬ CryptoGames.MLKEM.Mlkem768Encaps1Terminates
        (u.mem.readBytes (u.readReg64 .x0) (u.readReg64 .x1).toNat)) ∨
  (u.pc = addrs.mlkemDecapsVa ∧
    ¬ CryptoGames.MLKEM.Mlkem768DecapsTerminates
        ⟨u.mem.readBytes (u.readReg64 .x0) 2400, Memory.readBytes_length _ _ _⟩)

/-- Run on `i` reaches a running state at one of the 5 `SampleNTT` entry points whose matrix seed
never terminates (DEV-CLI22). -/
def CliReachesSampleNttStuckElf (elf : ElfImage) (addrs : CliElfAddrs) (i : Inputs) : Prop :=
  ∃ s0 u, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgElf addrs) s0 u ∧
    u.status = .Running ∧ MlKemSampleNttStuckAtElf addrs u

/-- Excused abort / divergence predicate for PQXDH-mode correctness: `.OutOfMemory` (DEV-CLI15) or
non-terminating `SampleNTT` seed (DEV-CLI22). -/
def cliExcusedElf (elf : ElfImage) (addrs : CliElfAddrs) (i : Inputs) : Prop :=
  CliReachesOOMElf elf addrs i ∨ CliReachesSampleNttStuckElf elf addrs i

/-! ## Specs total except `.OutOfMemory` (DEV-CLI15) or `SampleNTT` seed divergence (DEV-CLI22) -/

/-- **The outcome of `run` on `i` meets `P`, or `run` has no outcome on an excused input**
(DEV-CLI15, DEV-CLI22: total except `.OutOfMemory` or `SampleNTT` seed divergence): either
`run i = some o` with `P o`, or `run i = none` and `exc i`. With `exc := fun _ => False` it is
equivalent to `∃ o, run i = some o ∧ P o`, and with `P := (· = e)` it is equivalent to
`run i = some e`. -/
def OutcomeOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (i : Inputs) (P : Outcome → Prop) : Prop :=
  (∃ o, run i = some o ∧ P o) ∨ (run i = none ∧ exc i)

/-- **`CliSpecPqxdh` total except `.OutOfMemory` or `SampleNTT` seed divergence (DEV-CLI15,
DEV-CLI22).** `CliSpecPqxdh run X W` (`PqDir.lean`) with each clause's conclusion `run i = some e`
replaced by `OutcomeOrExcusedAbort exc run i (· = e)`: on the clause's input `i` the run is total
with exactly the clause's outcome, except when `run i = none` and `i` is excused (`exc i`). The five
clauses are `CliSpecPqxdh`'s (1. `init`, 2. `send`, 3. `recv` of `2 ‖ c`, 4. `recv` of a typed
pre-key message with no session or a matching one, 5. `recv` of any other first byte or of nothing),
in the same order, with the same binders, hypotheses and outcomes, including the `stdinCapBytes` /
`maxPlaintextBytes` rejections (DEV-CLI21). With `exc := fun _ => False` it is equivalent to
`CliSpecPqxdh run X W`. -/
def CliSpecPqxdhOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) : Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
      OutcomeOrExcusedAbort exc run (pqInitInputs W st b t)
        (· = pqxdhExpectedOutcome W (pqInitInputs W st b t) (pqInitModel X W st b t))) ∧
    (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
      OutcomeOrExcusedAbort exc run (pqSendInputs W st m r)
        (· = if m.length > stdinCapBytes then
              .exited 2 [] (filesOf (pqSendInputs W st m r).files)
            else if m.length > maxPlaintextBytes then
              .exited 1 [] (filesOf (pqSendInputs W st m r).files)
            else
              pqxdhExpectedOutcome W (pqSendInputs W st m r) (pqSendModel W st m r.toList))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wireWhisper :: c) rc)
        (· = if (wireWhisper :: c).length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st (wireWhisper :: c) rc).files)
            else
              pqxdhExpectedOutcome W (pqRecvInputs W st (wireWhisper :: c) rc)
                (pqRecvWhisperModel W st c rc))) ∧
    (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
        (· = if (wirePrekey :: m.bytes).length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files)
            else
              pqxdhExpectedOutcome W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X W st m rc))) ∧
    (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
      c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st c rc)
        (· = if c.length > stdinCapBytes then
              .exited 2 [] (filesOf (pqRecvInputs W st c rc).files)
            else
              .exited 1 [] (filesOf (pqRecvInputs W st c rc).files)))

/-- **`CliSpecPqxdhNoMatch` total except `.OutOfMemory` or `SampleNTT` seed divergence (DEV-CLI15,
DEV-CLI22).** `CliSpecPqxdhNoMatch run X W` (`PqDirNoMatch.lean`) with its conclusion
`∃ o, run i = some o ∧ OutcomeMatchesModelExceptPath …` replaced by `OutcomeOrExcusedAbort exc run i …`,
with the same binders, hypotheses and outcomes, including the `stdinCapBytes` rejection (DEV-CLI21).
With `exc := fun _ => False` it is equivalent to `CliSpecPqxdhNoMatch run X W`. -/
def CliSpecPqxdhNoMatchOrExcusedAbort (exc : Inputs → Prop) (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain W st →
    ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
    ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      ¬ PqSessionMatches x g m →
      OutcomeOrExcusedAbort exc run (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
        (fun o => if (wirePrekey :: m.bytes).length > stdinCapBytes then
            o = .exited 2 [] (filesOf (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files)
          else
            OutcomeMatchesModelExceptPath W (pqRecvInputs W st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X W { st with session := none } m rc) o)

/-- **ELF-direct PQXDH-mode correctness** for `elf` at resolved `.symtab` addresses `addrs`, total
except `.OutOfMemory` (DEV-CLI15) or `SampleNTT` seed divergence (DEV-CLI22). -/
def CliPqxdhElfCorrect (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort (cliExcusedElf elf addrs) (cliRunElf elf addrs) X realPEParams ∧
    CliSpecPqxdhNoMatchOrExcusedAbort (cliExcusedElf elf addrs) (cliRunElf elf addrs) X realPEParams

/-- **ELF-direct PQXDH-mode correctness of raw ELF `bytes`:** `bytes` parses as `elf`, the 23
`.symtab` addresses resolve via `resolveCliElfAddrs`, and `CliPqxdhElfCorrect elf addrs` holds. -/
def CliPqxdhBinaryCorrect (bytes : List (BitVec 8)) : Prop :=
  ∃ elf addrs, ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliPqxdhElfCorrect elf addrs

end CryptoVerification.SignalSession
