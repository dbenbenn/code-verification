/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.TokenNames
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.IoHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Mallocng.Spec

set_option autoImplicit false

/-!
# Relocatable CLI Correctness Proof-Internal Compatibility Definitions

**Checked by Lean (untrusted proof-internal layer).** Hosts the retired zero-row hook table
(`cliHookTablePlaced`), the 73-symbol list of directly linked external symbols
(`cliDehookedSymsPlaced`, including the 18 crate-referenced Rust panic entry points and
2 CPU-probe symbols), the symbol
name abbreviations (`ls*Sym`), the two-placement `(mpl, mmpl)` proof-internal shapes
(`CliElfCodeMatchesPlaced`, `CliPqxdhElfCorrectPlaced`, `CliPqxdhBinaryCorrectPlacedAt`,
`CliPqxdhBinaryCorrectPlaced`), and the equality bridges to the single-placement trusted
definitions in `LibsignalBinary.Specifications.SignalSession.CliBinaryPq`.
-/

public section

namespace LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced

open Arm64 ProofLib
open CryptoVerification.SignalSession (CliHooks)

abbrev cliHookTablePlaced (_mmpl : Obj.MultiPlacement) (_W : CliHooks) :
    List (String × (State → State)) :=
  []

end LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoVerification.E2E (PqxdhPrims UnreachedPqxdhPrimitives)

/-- The multi-block placed library `libsignalSessionMultiLib` (624 code blocks, 1,248 data objects,
4 exports) extracted from the `.rlib`/`.o` archives in `GeneratedLean.LibsignalSessionPlacedObj`. -/
abbrev libsignalSessionLib : Obj.MultiPlacedLib := CryptoVerification.libsignalSessionMultiLib

/-- Proof-side list of the `19` linked Rust panic entry-point symbols (`18` crate-referenced
entries in `cliPanicSymbolsPlaced` plus internal `liballoc` callee `capacity_overflow`). -/
@[expose] def cliPanicSymbolsLinked : List String :=
  ["_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_",
   "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_",
   "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error",
   "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error",
   "_RNvNtCs69KKACWg7bl_5alloc7raw_vec17capacity_overflow",
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

/-- Compatibility alias for the `18` crate-referenced Rust panic entry points in
`cliPanicSymbolsPlaced`. -/
abbrev cliCratePanicSyms : List String := cliPanicSymbolsPlaced

/-- Placed panic-symbol predicate matching `cliPanicSymbolsPlaced` plus `Rust.isPanicSymbol`. -/
@[expose] def isCliPanicSymbolPlaced (name : String) : Bool :=
  cliPanicSymbolsPlaced.contains name || Rust.isPanicSymbol name

/-- Linked-panic symbol predicate for ghost-hook `P_ghost` execution (matches the `19` linked
`core`/`alloc` panic entry points in `cliPanicSymbolsLinked` plus `Rust.isPanicSymbol`). -/
@[expose] def isCliPanicSymbolLinked (name : String) : Bool :=
  cliPanicSymbolsLinked.contains name || Rust.isPanicSymbol name

/-- Panic-free placed CLI extern map (zero overrides on all mangled symbols of `libsignalSessionLib`,
matching `Program.pureMem`). -/
@[expose] noncomputable def cliExternsPlacedSig : String → Option (State → State) :=
  fun name =>
    if isCliPanicSymbolPlaced name then some (abortOnPanic Rust.panicked) else none

/-- Ghost-base CLI extern map intercepting `cliPanicSymbolsLinked` as `some Rust.panicked` for
`CliPanicHooksPlaced` during `b2MainSpecTightNeedLocksFineAt` proofs. -/
@[expose] noncomputable def cliExternsPlacedWithPanics : String → Option (State → State) :=
  fun name =>
    if isCliPanicSymbolLinked name then some Rust.panicked else none

namespace Placed

/-- Relocatable program of a CLI run: block `617` of `libsignalSessionLib` under `mpl` with
`cliExternsPlacedSig`. -/
@[expose] noncomputable def cliProgPlacedSig (mpl : Obj.MultiPlacement) : Program :=
  libsignalSessionLib.blockProgram mpl 617 cliExternsPlacedSig

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Kernel-checked guard that block `617` of `libsignalSessionLib` exists and shares the exact
`externs` list of `main`'s block (with `main` at offset `0`). -/
theorem libsignalSessionLib_main_block :
    decide (617 < libsignalSessionLib.blocks.length) = true ∧
    ((Obj.lookupBlockSym "main" libsignalSessionLib.blocks).map (·.2)) = some 0 ∧
    ((Obj.lookupBlockSym "main" libsignalSessionLib.blocks).map
        (fun p => (libsignalSessionLib.blocks.getD p.1 { code := [] }).externs)) =
      some (libsignalSessionLib.blocks.getD 617 { code := [] }).externs :=
  ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

/-- Relocatable SPQR CPU-probe patch (`STORAGE.0 := 0` at `mpl.ρ tokenStorageName`,
`TOKEN.state := 0` at `mpl.ρ tokenName + 8`; see `cliTokenPatch`, DEV-CLI10). -/
@[expose] def cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) : State :=
  s.setMem ((s.mem.writeBytes (mpl.ρ LibsignalSpqrV1.tokenStorageName) [0#8]).writeBytes
    (mpl.ρ LibsignalSpqrV1.tokenName + 8#64) [0#8, 0#8, 0#8, 0#8])

/-- Relocatable `CliRunsTo` under `libsignalSessionLib` placement `mpl`. -/
@[expose] def CliRunsToPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage) (i : Inputs)
    (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgPlacedSig mpl) (cliTokenPatchPlaced mpl s0)
      (OutcomeMatchesProcess o)

open Classical in
/-- Relocatable `cliRunAbortOnPanic` under `libsignalSessionLib` placement `mpl`. -/
@[expose] noncomputable def cliRunPlacedSig (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    CliRun := fun i =>
  if h : ∃ o, CliRunsToPlaced mpl elf i o then some (Classical.choose h) else none

/-- External resolution `stubVa = mpl.ρ sym` reaches `.symtab` definition `targetVa` in `elf`:
directly or via a 4-byte-aligned executable (`Perm.rx`) unconditional branch `B targetVa`. -/
@[expose] def DirectOrBranchStub (elf : ElfImage) (stubVa targetVa : BitVec 64) : Prop :=
  stubVa = targetVa ∨
    (stubVa.toNat % 4 = 0 ∧
      Obj.BranchInRange stubVa targetVa ∧
      Obj.ElfMaps elf stubVa (Obj.bytesOfWordLE (Obj.branchWord 0x14000000#32 stubVa targetVa))
        (· == Perm.rx))

/-- Relocatable `CliElfCodeMatches` under `libsignalSessionLib` placement `mpl`. -/
@[expose] def CliElfCodeMatchesPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  libsignalSessionLib.DataDisjoint mpl ∧
  ∀ a : BitVec 64,
    (cliProgPlacedSig mpl).externAt? a ≠ none →
      ∃ sym targetVa,
        isCliPanicSymbolPlaced sym = true ∧
        Obj.lookupUnique sym elf.symbols = some targetVa ∧
        DirectOrBranchStub elf a targetVa

end Placed

/-- Run on `i` under `mpl` reaches `s.status = .OutOfMemory`. -/
@[expose] def CliReachesOOMPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (Placed.cliProgPlacedSig mpl) (Placed.cliTokenPatchPlaced mpl s0) s ∧
      s.status = .OutOfMemory

/-- The 5 `libcrux_ml_kem` entry points that run `SampleNTT` (`sample_from_xof`) under `mpl`. -/
@[expose] def MlKemSampleNttStuckAt (mpl : Obj.MultiPlacement) (u : State) : Prop :=
  (u.pc = mpl.ρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate" ∧
    ¬ CryptoGames.MLKEM.Kyber1024EncapsTerminates (u.mem.readBytes (u.readReg64 .x0) 1568)) ∨
  (u.pc = mpl.ρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate" ∧
    ¬ CryptoGames.MLKEM.Kyber1024DecapsTerminates (u.mem.readBytes (u.readReg64 .x0) 3168)) ∨
  (u.pc = mpl.ρ "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed" ∧
    ¬ CryptoGames.MLKEM.Mlkem768FromSeedTerminates
        ⟨u.mem.readBytes (u.readReg64 .x0) 64, Memory.readBytes_length _ _ _⟩) ∨
  (u.pc = mpl.ρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1" ∧
    ¬ CryptoGames.MLKEM.Mlkem768Encaps1Terminates
        (u.mem.readBytes (u.readReg64 .x0) (u.readReg64 .x1).toNat)) ∨
  (u.pc = mpl.ρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key" ∧
    ¬ CryptoGames.MLKEM.Mlkem768DecapsTerminates
        ⟨u.mem.readBytes (u.readReg64 .x0) 2400, Memory.readBytes_length _ _ _⟩)

/-- Run on `i` reaches a running state at one of the 5 `SampleNTT` entry points under `mpl`. -/
@[expose] def CliReachesSampleNttStuckPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (i : Inputs) : Prop :=
  ∃ s0 u, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (Placed.cliProgPlacedSig mpl) (Placed.cliTokenPatchPlaced mpl s0) u ∧
    u.status = .Running ∧ MlKemSampleNttStuckAt mpl u

/-- Relocatable `CliPqxdhElfCorrect` under placement `mpl`. -/
@[expose] def CliPqxdhElfCorrectPlaced (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  Placed.CliElfCodeMatchesPlaced mpl elf ∧
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort
      (fun i => CliReachesOOMPlaced mpl elf i ∨ CliReachesSampleNttStuckPlaced mpl elf i)
      (Placed.cliRunPlacedSig mpl elf) X realPEParams ∧
    CliSpecPqxdhNoMatchOrExcusedAbort
      (fun i => CliReachesOOMPlaced mpl elf i ∨ CliReachesSampleNttStuckPlaced mpl elf i)
      (Placed.cliRunPlacedSig mpl elf) X realPEParams

/-- Relocatable `CliPqxdhBinaryCorrect` at specific placement `mpl`. -/
@[expose] def CliPqxdhBinaryCorrectPlacedAt (mpl : Obj.MultiPlacement) (bytes : List (BitVec 8)) :
    Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectPlaced mpl elf

/-- Relocatable `CliPqxdhBinaryCorrect` quantified over placements `mpl` of `libsignalSessionLib`. -/
@[expose] def CliPqxdhBinaryCorrectPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    CliPqxdhBinaryCorrectPlacedAt mpl bytes

abbrev lsRustNoAllocShimSymCli : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
abbrev lsRustAllocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
abbrev lsRustDeallocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
abbrev lsRustReallocSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"
abbrev lsRustAllocZeroedSymCli : String := "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"

abbrev lsReadFileSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io9read_file"
abbrev lsWriteFileSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10write_file"
abbrev lsReadStdinSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io10read_stdin"
abbrev lsWriteStdoutSym : String := "_RNvCs9Xul1Kjr0QF_16libsignal_cli_io12write_stdout"

abbrev lsMemrchrSym : String := "_RNvNtNtCskxtBwYRO61I_4core5slice6memchr7memrchr"
abbrev lsFromUtf8Sym : String := "_RNvNtNtCskxtBwYRO61I_4core3str8converts9from_utf8"
abbrev lsFmtWriteSym : String := "_RNvNtCskxtBwYRO61I_4core3fmt5write"
abbrev lsFormatInnerSym : String := "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"
abbrev lsDurationSinceSym : String :=
  "_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since"
abbrev lsTimeAddSym : String :=
  "_RNvXs6_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTimeINtNtNtCskxtBwYRO61I_4core3ops5arith3AddNtNtBR_4time8DurationE3add"
abbrev lsBlackBoxSym : String :=
  "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek"
abbrev lsCompress256Sym : String := "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"
abbrev lsLibcruxHmacSym : String := "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"
abbrev lsAesEncSym : String := "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_encrypt"
abbrev lsAesDecSym : String := "_RNvNtCsbKnPy0UR4Ui_13signal_crypto7aes_cbc19aes_256_cbc_decrypt"
abbrev lsGetauxvalHwcapSym : String := "_RNvNtCslWItzXo2NmA_11cpufeatures7aarch6415getauxval_hwcap"
abbrev lsPubFromSecretSym : String :=
  "_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from"
abbrev lsDiffieHellmanSym : String :=
  "_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman"
abbrev lsStaticSecretDropSym : String :=
  "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"
abbrev lsSharedSecretDropSym : String :=
  "_RNvXse_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12SharedSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"

/-- Proof-side record of the `73` `libsignalSessionLib` external symbols verified directly
against linked ELF code (`53` allocator/libc/I/O/fmt/crypto/std + `2` CPU-probe + `18`
crate-referenced Rust panic entry points; `alloc::raw_vec::capacity_overflow` is an internal
`liballoc` callee also linked and verified in `cliPanicSymbolsLinked`). -/
@[expose] def cliDehookedSymsPlaced : List String :=
  [lsRustNoAllocShimSymCli,
   lsRustAllocSymCli,
   lsRustDeallocSymCli,
   lsRustReallocSymCli,
   lsRustAllocZeroedSymCli,
   lsReadFileSym,
   lsReadStdinSym,
   "memcpy",
   "memset",
   "memmove",
   "bcmp",
   "strlen",
   lsMemrchrSym,
   lsFromUtf8Sym,
   lsDurationSinceSym,
   lsTimeAddSym,
   lsBlackBoxSym,
   lsStaticSecretDropSym,
   lsSharedSecretDropSym,
   "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
   "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
   "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
   "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
   "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
   lsCompress256Sym,
   lsLibcruxHmacSym,
   lsAesEncSym,
   lsAesDecSym,
   "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
   lsWriteFileSym,
   lsWriteStdoutSym,
   lsFmtWriteSym,
   lsFormatInnerSym,
   lsPubFromSecretSym,
   lsDiffieHellmanSym,
   "_RNvMsa_NtCskxtBwYRO61I_4core3fmtNtB5_9Formatter9write_str",
   "_RNvMsa_NtCskxtBwYRO61I_4core3fmtNtB5_9Formatter3pad",
   "_RNvXsi_NtCskxtBwYRO61I_4core3fmteNtB5_7Display3fmt",
   "_RNvXNtNtNtCskxtBwYRO61I_4core3fmt3num3imphNtB6_7Display3fmt",
   "_RNvXs8_NtNtNtCskxtBwYRO61I_4core3fmt3num3impmNtB9_7Display3fmt",
   "_RNvXsd_NtNtNtCskxtBwYRO61I_4core3fmt3num3impyNtB9_7Display3fmt",
   "_RNvXsi_NtNtNtCskxtBwYRO61I_4core3fmt3num3impjNtB9_7Display3fmt",
   "_RNvMs0_NtNtNtNtCsfr5T3GFabw_3std3sys4sync4once5futexNtB5_4Once4call",
   lsGetauxvalHwcapSym]

/-- The `55` non-panic external symbols of `libsignalSessionLib` verified directly against linked
ELF code (`53` allocator/libc/I/O/fmt/crypto/std + `2` CPU-probe; `externAt? = none` in `P_pan`). -/
@[expose] def cliNonPanicDehookedSyms : List String :=
  cliDehookedSymsPlaced

/-- Proof-side compatibility stub for the retired hook table (`0` rows). -/
@[expose] def cliHookTablePlaced : List (String × (State → State)) := []

/-- Proof-side compatibility stub for the retired PQXDH hook table (empty at zero hooks). -/
@[expose] noncomputable def cliPqxdhHookTablePlaced (_Q : PqxdhPrims) :
    List (String × (State → State)) :=
  []

/-- Proof-side compatibility wrapper for `cliExternsPlaced` (ignores `mmpl` and `W` at zero hooks). -/
@[expose] noncomputable def cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name =>
    if isCliPanicSymbolPlaced name then some Rust.panicked
    else (LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.cliHookTablePlaced mmpl W).lookup name

end CryptoVerification.SignalSession

namespace LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced

open Arm64 ProofLib
open Arm64.Process (ElfImage)
open CryptoVerification.E2E (PqxdhPrims UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession
  (CliHooks Inputs Outcome OutcomeMatchesProcess CliRun abortOnPanic cliProcessInputs
   cliDehookedSymsPlaced realCrypto realPqxdhPrims realPEParams
   CliSpecPqxdhOrExcusedAbort CliSpecPqxdhNoMatchOrExcusedAbort)
open CryptoVerification.SignalSession.Placed (DirectOrBranchStub)

abbrev libsignalSessionLib : Obj.MultiPlacedLib := CryptoVerification.SignalSession.libsignalSessionLib

abbrev lsRustNoAllocShimSymCli : String := CryptoVerification.SignalSession.lsRustNoAllocShimSymCli
abbrev lsRustAllocSymCli : String := CryptoVerification.SignalSession.lsRustAllocSymCli
abbrev lsRustDeallocSymCli : String := CryptoVerification.SignalSession.lsRustDeallocSymCli
abbrev lsRustReallocSymCli : String := CryptoVerification.SignalSession.lsRustReallocSymCli
abbrev lsRustAllocZeroedSymCli : String := CryptoVerification.SignalSession.lsRustAllocZeroedSymCli

abbrev lsReadFileSym : String := CryptoVerification.SignalSession.lsReadFileSym
abbrev lsWriteFileSym : String := CryptoVerification.SignalSession.lsWriteFileSym
abbrev lsReadStdinSym : String := CryptoVerification.SignalSession.lsReadStdinSym
abbrev lsWriteStdoutSym : String := CryptoVerification.SignalSession.lsWriteStdoutSym

abbrev lsMemrchrSym : String := CryptoVerification.SignalSession.lsMemrchrSym
abbrev lsFromUtf8Sym : String := CryptoVerification.SignalSession.lsFromUtf8Sym
abbrev lsFmtWriteSym : String := CryptoVerification.SignalSession.lsFmtWriteSym
abbrev lsFormatInnerSym : String := CryptoVerification.SignalSession.lsFormatInnerSym
abbrev lsDurationSinceSym : String := CryptoVerification.SignalSession.lsDurationSinceSym
abbrev lsTimeAddSym : String := CryptoVerification.SignalSession.lsTimeAddSym
abbrev lsBlackBoxSym : String := CryptoVerification.SignalSession.lsBlackBoxSym
abbrev lsCompress256Sym : String := CryptoVerification.SignalSession.lsCompress256Sym
abbrev lsAesEncSym : String := CryptoVerification.SignalSession.lsAesEncSym
abbrev lsAesDecSym : String := CryptoVerification.SignalSession.lsAesDecSym
abbrev lsGetauxvalHwcapSym : String := CryptoVerification.SignalSession.lsGetauxvalHwcapSym
abbrev lsPubFromSecretSym : String := CryptoVerification.SignalSession.lsPubFromSecretSym
abbrev lsDiffieHellmanSym : String := CryptoVerification.SignalSession.lsDiffieHellmanSym
abbrev lsStaticSecretDropSym : String := CryptoVerification.SignalSession.lsStaticSecretDropSym
abbrev lsSharedSecretDropSym : String := CryptoVerification.SignalSession.lsSharedSecretDropSym

noncomputable abbrev cliPqxdhHookTablePlaced (Q : PqxdhPrims) :
    List (String × (State → State)) :=
  CryptoVerification.SignalSession.cliPqxdhHookTablePlaced Q

abbrev cliPanicSymbolsPlaced : List String :=
  CryptoVerification.SignalSession.cliPanicSymbolsPlaced

abbrev cliCratePanicSyms : List String :=
  CryptoVerification.SignalSession.cliCratePanicSyms

abbrev cliNonPanicDehookedSyms : List String :=
  CryptoVerification.SignalSession.cliNonPanicDehookedSyms

abbrev isCliPanicSymbolPlaced (name : String) : Bool :=
  CryptoVerification.SignalSession.isCliPanicSymbolPlaced name

noncomputable abbrev cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  CryptoVerification.SignalSession.cliExternsPlaced mmpl W

noncomputable abbrev cliExternsPlacedSig (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name => (CryptoVerification.SignalSession.cliExternsPlaced mmpl W name).map abortOnPanic

section
set_option linter.dupNamespace false

namespace Placed

noncomputable abbrev cliProgPlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl 617 (cliExternsPlacedSig mmpl W)

abbrev cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) : State :=
  CryptoVerification.SignalSession.Placed.cliTokenPatchPlaced mpl s

abbrev CliRunsToPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks)
    (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgPlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0)
      (OutcomeMatchesProcess o)

open Classical in
noncomputable abbrev cliRunPlacedSig (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : CliRun := fun i =>
  if h : ∃ o, CliRunsToPlaced mpl mmpl elf W i o then some (Classical.choose h) else none

/-- Proof-internal two-placement `(mpl, mmpl)` code-matching invariant (retained inside `Proofs/`
so internal proof files do not need rewriting after `mmpl` left the trusted statements). -/
@[expose] def CliElfCodeMatchesPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  libsignalSessionLib.Placeable mpl ∧
    libsignalSessionLib.InElf elf mpl ∧
    libsignalSessionLib.DataDisjoint mpl ∧
    VerifiedLibraries.mallocngLib.Placeable mmpl ∧
    VerifiedLibraries.mallocngLib.InElf elf mmpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl ∧
    (∀ (i : Nat) (hi : i < libsignalSessionLib.blocks.length)
       (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length) (a : BitVec 64),
      ProofLib.InRegion (mpl.base i) libsignalSessionLib.blocks[i].code.length a →
        ¬ ProofLib.InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a) ∧
    (∀ d₁ ∈ libsignalSessionLib.data, ∀ d₂ ∈ VerifiedLibraries.mallocngLib.data,
      (d₁.readOnly = true ∧ d₂.readOnly = true) ∨
        ∀ a : BitVec 64,
          ProofLib.InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a →
            ¬ ProofLib.InRegion (mmpl.ρ d₂.sym) (VerifiedLibraries.mallocngLib.patchedData mmpl d₂).length a) ∧
    (∀ (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length) (a : BitVec 64),
      ProofLib.InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a →
        (cliProgPlacedSig mpl mmpl ⟨realCrypto, realPqxdhPrims⟩).externAt? a = none) ∧
    (∀ sym ∈ cliNonPanicDehookedSyms,
      (cliProgPlacedSig mpl mmpl ⟨realCrypto, realPqxdhPrims⟩).externAt? (mpl.ρ sym) = none ∧
      ∃ targetVa : BitVec 64,
        Obj.lookupUnique sym elf.symbols = some targetVa ∧
        DirectOrBranchStub elf (mpl.ρ sym) targetVa ∧
        (cliProgPlacedSig mpl mmpl ⟨realCrypto, realPqxdhPrims⟩).externAt? targetVa = none)

end Placed

end

noncomputable abbrev cliProgPlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) : Program :=
  Placed.cliProgPlacedSig mpl mmpl W

abbrev cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) : State :=
  Placed.cliTokenPatchPlaced mpl s

abbrev CliRunsToPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks)
    (i : Inputs) (o : Outcome) : Prop :=
  Placed.CliRunsToPlaced mpl mmpl elf W i o

noncomputable abbrev cliRunPlacedSig (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) : CliRun :=
  Placed.cliRunPlacedSig mpl mmpl elf W

abbrev CliReachesOOMPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks)
    (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (Placed.cliProgPlacedSig mpl mmpl W) (Placed.cliTokenPatchPlaced mpl s0) s ∧
      s.status = .OutOfMemory

abbrev MlKemSampleNttStuckAt (mpl : Obj.MultiPlacement) (u : State) : Prop :=
  CryptoVerification.SignalSession.MlKemSampleNttStuckAt mpl u

abbrev CliReachesSampleNttStuckPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 u, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (Placed.cliProgPlacedSig mpl mmpl W) (Placed.cliTokenPatchPlaced mpl s0) u ∧
    u.status = .Running ∧ CryptoVerification.SignalSession.MlKemSampleNttStuckAt mpl u

abbrev CliElfCodeMatchesPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  Placed.CliElfCodeMatchesPlaced mpl mmpl elf

theorem cliExternsPlacedSig_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlacedSig mmpl W = CryptoVerification.SignalSession.cliExternsPlacedSig := by
  funext name
  unfold cliExternsPlacedSig CryptoVerification.SignalSession.cliExternsPlaced
    CryptoVerification.SignalSession.cliExternsPlacedSig
  cases h : isCliPanicSymbolPlaced name <;> simp [h, cliHookTablePlaced]

theorem cliProgPlacedSig_eq (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Placed.cliProgPlacedSig mpl mmpl W =
      CryptoVerification.SignalSession.Placed.cliProgPlacedSig mpl := by
  unfold Placed.cliProgPlacedSig CryptoVerification.SignalSession.Placed.cliProgPlacedSig
  rw [cliExternsPlacedSig_eq]

theorem cliRunsToPlaced_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    Placed.CliRunsToPlaced mpl mmpl elf W =
      CryptoVerification.SignalSession.Placed.CliRunsToPlaced mpl elf := by
  funext i o
  unfold Placed.CliRunsToPlaced CryptoVerification.SignalSession.Placed.CliRunsToPlaced
  rw [cliProgPlacedSig_eq]

theorem cliRunPlacedSig_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    Placed.cliRunPlacedSig mpl mmpl elf W =
      CryptoVerification.SignalSession.Placed.cliRunPlacedSig mpl elf := by
  funext i
  unfold Placed.cliRunPlacedSig CryptoVerification.SignalSession.Placed.cliRunPlacedSig
  rw [cliRunsToPlaced_eq]

theorem cliReachesOOMPlaced_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    CliReachesOOMPlaced mpl mmpl elf W =
      CryptoVerification.SignalSession.CliReachesOOMPlaced mpl elf := by
  funext i
  unfold CliReachesOOMPlaced CryptoVerification.SignalSession.CliReachesOOMPlaced
  rw [cliProgPlacedSig_eq]

theorem cliReachesSampleNttStuckPlaced_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    CliReachesSampleNttStuckPlaced mpl mmpl elf W =
      CryptoVerification.SignalSession.CliReachesSampleNttStuckPlaced mpl elf := by
  funext i
  unfold CliReachesSampleNttStuckPlaced
    CryptoVerification.SignalSession.CliReachesSampleNttStuckPlaced
  rw [cliProgPlacedSig_eq]

/-- Proof-internal two-placement `(mpl, mmpl)` `CliPqxdhElfCorrectPlaced`. -/
@[expose] def CliPqxdhElfCorrectPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  Placed.CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort
      (fun i => CliReachesOOMPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i ∨
        CliReachesSampleNttStuckPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i)
      (Placed.cliRunPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams ∧
    CliSpecPqxdhNoMatchOrExcusedAbort
      (fun i => CliReachesOOMPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i ∨
        CliReachesSampleNttStuckPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i)
      (Placed.cliRunPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams

/-- Proof-internal two-placement `(mpl, mmpl)` `CliPqxdhBinaryCorrectPlacedAt`. -/
@[expose] def CliPqxdhBinaryCorrectPlacedAt (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectPlaced mpl mmpl elf

/-- Proof-internal two-placement `CliPqxdhBinaryCorrectPlaced`. -/
@[expose] def CliPqxdhBinaryCorrectPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes

/-- Bridge from the proof-internal two-placement `CliPqxdhElfCorrectPlaced` (plus the shrunk
trusted `CliElfCodeMatchesPlaced mpl elf`) to the trusted single-placement
`CryptoVerification.SignalSession.CliPqxdhElfCorrectPlaced mpl elf`. -/
theorem cliPqxdhElfCorrectPlaced_to_trusted {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hcm : CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf)
    (h : CliPqxdhElfCorrectPlaced mpl mmpl elf) :
    CryptoVerification.SignalSession.CliPqxdhElfCorrectPlaced mpl elf := by
  refine ⟨hcm, fun X => ?_⟩
  have hX := h.2 X
  rw [cliReachesOOMPlaced_eq, cliReachesSampleNttStuckPlaced_eq, cliRunPlacedSig_eq] at hX
  exact hX

end LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
