/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion
public meta import ProofLib.ProgramReflection
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclBytes -- proof-setup: allow-public-import

/-!
# Relocatable `Obj.MultiPlacedLib` Model of `libcrux_sha2::hacl` and `libcrux_hmac::hmac`

Packages the 7 code blocks (`0..6`, `3,153` words = `12,612` B, no `GeneratedLean` imports):

- `[0]` `sha256_init` (`78` words)
- `[1]` `sha256_update` (`2,074` words)
- `[2]` `sha256_update_nblocks` (`35` words)
- `[3]` `sha256_update_last` (`74` words)
- `[4]` `sha256_finish` (`79` words)
- `[5]` `hash_256` (`101` words)
- `[6]` `libcrux_hmac::hmac` (`712` words)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (svcAnyPat svcAnyPat_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclBytes
  (sha256InitBytes sha256UpdateBytes sha256UpdateNblocksBytes sha256UpdateLastBytes sha256FinishBytes hash256Bytes libcruxHmacBytes)

/-! ## 1. Symbol Names & Shared Extern List -/

@[expose] def sha256InitSym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl11sha256_init"
@[expose] def sha256UpdateSym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha256_update"
@[expose] def sha256UpdateNblocksSym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha256_update_nblocks"
@[expose] def sha256UpdateLastSym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha256_update_last"
@[expose] def sha256FinishSym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha256_finish"
@[expose] def hash256Sym : String := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl8hash_256"
@[expose] def libcruxHmacSym : String := "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"
@[expose] def memcpySym : String := "memcpy"
@[expose] def rustAllocShimSym : String := "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"
@[expose] def rustAllocSym : String := "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"
@[expose] def rustAllocZeroedSym : String := "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"
@[expose] def rustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
@[expose] def rustHandleErrorSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"
@[expose] def rustUnwrapFailedSym : String := "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed"
@[expose] def rustPanicBoundsCheckSym : String := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check"
@[expose] def rustPanicFmtSym : String := "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt"
@[expose] def rustSliceIndexFailSym : String := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail"

@[expose] def libcruxHmacExterns : List String := [
  rustAllocSym,
  rustDeallocSym,
  rustAllocZeroedSym,
  rustAllocShimSym,
  rustHandleErrorSym,
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl11sha384_init",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl11sha512_init",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha384_finish",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha512_finish",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha384_update_last",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha512_update_last",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha384_update_nblocks",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha512_update_nblocks",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl8hash_384",
  "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl8hash_512",
  rustUnwrapFailedSym,
  rustPanicBoundsCheckSym,
  rustPanicFmtSym,
  rustSliceIndexFailSym,
  memcpySym]

/-! ## 2. Relocatable Code Blocks (`0..6`) & `libcruxHmacLib` -/

@[expose] def sha256InitBlock : Obj.CodeBlock where
  code := sha256InitBytes
  align := 4
  symbols := [(sha256InitSym, 0)]
  relocs := [
    { off := 0xac, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xb0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xb8, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xbc, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xc0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xc8, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xcc, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xd0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xdc, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xe0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xe4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xec, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xf0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0xf4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x100, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x104, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x108, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x110, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x114, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x118, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x124, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x128, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x12c, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.13", addend := 0 },
    { off := 0x134, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def sha256UpdateBlock : Obj.CodeBlock where
  code := sha256UpdateBytes
  align := 4
  symbols := [(sha256UpdateSym, 0)]
  relocs := [
    { off := 0x1ecc, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.19", addend := 0 },
    { off := 0x1ed0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.19", addend := 0 },
    { off := 0x1ee4, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1ee8, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1eec, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1efc, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f04, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f08, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f14, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f1c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f20, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f2c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f34, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f38, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f44, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f4c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f50, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f5c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f64, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f68, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f74, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f7c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f80, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f8c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1f94, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1f98, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fa4, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1fac, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fb0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fbc, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1fc4, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fc8, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fd4, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1fdc, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fe0, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1fec, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x1ff4, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x1ff8, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2004, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x200c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2010, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x201c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x2024, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2028, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2034, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x203c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2040, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x204c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x2054, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2058, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.58", addend := 0 },
    { off := 0x2064, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def sha256UpdateNblocksBlock : Obj.CodeBlock where
  code := sha256UpdateNblocksBytes
  align := 4
  symbols := [(sha256UpdateNblocksSym, 0)]
  relocs := [
    { off := 0x48, kind := .call26, sym := sha256UpdateSym, addend := 0 },
    { off := 0x74, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x78, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x7c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.51", addend := 0 },
    { off := 0x80, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.51", addend := 0 },
    { off := 0x88, kind := .call26, sym := rustPanicFmtSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def sha256UpdateLastBlock : Obj.CodeBlock where
  code := sha256UpdateLastBytes
  align := 4
  symbols := [(sha256UpdateLastSym, 0)]
  relocs := [
    { off := 0x60, kind := .call26, sym := memcpySym, addend := 0 },
    { off := 0xa4, kind := .call26, sym := sha256UpdateSym, addend := 0 },
    { off := 0xc4, kind := .call26, sym := sha256UpdateSym, addend := 0 },
    { off := 0xe0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.47", addend := 0 },
    { off := 0xe4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.47", addend := 0 },
    { off := 0xf4, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0xf8, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.45", addend := 0 },
    { off := 0xfc, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.45", addend := 0 },
    { off := 0x110, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0x114, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.46", addend := 0 },
    { off := 0x118, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.46", addend := 0 },
    { off := 0x124, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def sha256FinishBlock : Obj.CodeBlock where
  code := sha256FinishBytes
  align := 4
  symbols := [(sha256FinishSym, 0)]
  relocs := [
    { off := 0x94, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.18", addend := 0 },
    { off := 0x98, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.18", addend := 0 },
    { off := 0xac, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0xb0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xb4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xbc, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xc0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xc4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xcc, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xd0, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xd4, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xe0, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xe4, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xe8, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xf0, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0xf4, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0xf8, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x104, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x108, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x10c, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x114, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x118, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x11c, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x128, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 },
    { off := 0x12c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x130, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.17", addend := 0 },
    { off := 0x138, kind := .call26, sym := rustPanicBoundsCheckSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def hash256Block : Obj.CodeBlock where
  code := hash256Bytes
  align := 4
  symbols := [(hash256Sym, 0)]
  relocs := [
    { off := 0xa8, kind := .call26, sym := sha256UpdateSym, addend := 0 },
    { off := 0xe0, kind := .call26, sym := sha256UpdateLastSym, addend := 0 },
    { off := 0x14c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x150, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x154, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.51", addend := 0 },
    { off := 0x158, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.51", addend := 0 },
    { off := 0x160, kind := .call26, sym := rustPanicFmtSym, addend := 0 },
    { off := 0x164, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x168, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.0", addend := 0 },
    { off := 0x16c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.54", addend := 0 },
    { off := 0x170, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.54", addend := 0 },
    { off := 0x178, kind := .call26, sym := rustPanicFmtSym, addend := 0 },
    { off := 0x17c, kind := .adrpHi21, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.18", addend := 0 },
    { off := 0x180, kind := .addLo12, sym := "libcrux_sha2:.rodata..Lanon.33fc5f1067cfecbfbf8c1b4906a2e850.18", addend := 0 },
    { off := 0x190, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def libcruxHmacBlock : Obj.CodeBlock where
  code := libcruxHmacBytes
  align := 4
  symbols := [(libcruxHmacSym, 0)]
  relocs := [
    { off := 0x90, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x9c, kind := .call26, sym := rustAllocZeroedSym, addend := 0 },
    { off := 0xc8, kind := .call26, sym := memcpySym, addend := 0 },
    { off := 0xfc, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x108, kind := .call26, sym := rustAllocZeroedSym, addend := 0 },
    { off := 0x134, kind := .call26, sym := memcpySym, addend := 0 },
    { off := 0x16c, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x178, kind := .call26, sym := rustAllocZeroedSym, addend := 0 },
    { off := 0x1a4, kind := .call26, sym := memcpySym, addend := 0 },
    { off := 0x1bc, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl8hash_384", addend := 0 },
    { off := 0x1c0, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x1cc, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x214, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x220, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x340, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha384_update_nblocks", addend := 0 },
    { off := 0x358, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha384_update_nblocks", addend := 0 },
    { off := 0x38c, kind := .call26, sym := hash256Sym, addend := 0 },
    { off := 0x390, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x39c, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x3dc, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x3e8, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x4b8, kind := .call26, sym := sha256UpdateNblocksSym, addend := 0 },
    { off := 0x4d0, kind := .call26, sym := sha256UpdateNblocksSym, addend := 0 },
    { off := 0x500, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl8hash_512", addend := 0 },
    { off := 0x504, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x510, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x558, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x564, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x684, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha512_update_nblocks", addend := 0 },
    { off := 0x69c, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha512_update_nblocks", addend := 0 },
    { off := 0x6dc, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha384_update_last", addend := 0 },
    { off := 0x6f0, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha384_finish", addend := 0 },
    { off := 0x6fc, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl11sha384_init", addend := 0 },
    { off := 0x714, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha384_update_nblocks", addend := 0 },
    { off := 0x72c, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha384_update_nblocks", addend := 0 },
    { off := 0x74c, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha384_update_last", addend := 0 },
    { off := 0x760, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha384_finish", addend := 0 },
    { off := 0x770, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x780, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x790, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x794, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x7a0, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x7d8, kind := .call26, sym := sha256UpdateLastSym, addend := 0 },
    { off := 0x7ec, kind := .call26, sym := sha256FinishSym, addend := 0 },
    { off := 0x7f8, kind := .call26, sym := sha256InitSym, addend := 0 },
    { off := 0x810, kind := .call26, sym := sha256UpdateNblocksSym, addend := 0 },
    { off := 0x828, kind := .call26, sym := sha256UpdateNblocksSym, addend := 0 },
    { off := 0x844, kind := .call26, sym := sha256UpdateLastSym, addend := 0 },
    { off := 0x858, kind := .call26, sym := sha256FinishSym, addend := 0 },
    { off := 0x868, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x878, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x888, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x88c, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x898, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x8cc, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha512_update_last", addend := 0 },
    { off := 0x8e0, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha512_finish", addend := 0 },
    { off := 0x8ec, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl11sha512_init", addend := 0 },
    { off := 0x904, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha512_update_nblocks", addend := 0 },
    { off := 0x91c, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl21sha512_update_nblocks", addend := 0 },
    { off := 0x93c, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl18sha512_update_last", addend := 0 },
    { off := 0x950, kind := .call26, sym := "_RNvNtCsfbAkLoxnnbA_12libcrux_sha24hacl13sha512_finish", addend := 0 },
    { off := 0x960, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x970, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x980, kind := .call26, sym := rustDeallocSym, addend := 0 },
    { off := 0x984, kind := .call26, sym := rustAllocShimSym, addend := 0 },
    { off := 0x990, kind := .call26, sym := rustAllocSym, addend := 0 },
    { off := 0x9e4, kind := .call26, sym := rustHandleErrorSym, addend := 0 },
    { off := 0x9f0, kind := .call26, sym := rustHandleErrorSym, addend := 0 },
    { off := 0x9f8, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0x9fc, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0xa04, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa08, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa0c, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.5", addend := 0 },
    { off := 0xa10, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.5", addend := 0 },
    { off := 0xa1c, kind := .call26, sym := rustUnwrapFailedSym, addend := 0 },
    { off := 0xa24, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0xa28, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0xa2c, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa30, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa34, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.4", addend := 0 },
    { off := 0xa38, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.4", addend := 0 },
    { off := 0xa48, kind := .call26, sym := rustUnwrapFailedSym, addend := 0 },
    { off := 0xa50, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0xa54, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.2", addend := 0 },
    { off := 0xa5c, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa60, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.1", addend := 0 },
    { off := 0xa64, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.6", addend := 0 },
    { off := 0xa68, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.6", addend := 0 },
    { off := 0xa74, kind := .call26, sym := rustUnwrapFailedSym, addend := 0 },
    { off := 0xa80, kind := .call26, sym := rustHandleErrorSym, addend := 0 },
    { off := 0xa8c, kind := .call26, sym := rustHandleErrorSym, addend := 0 },
    { off := 0xa90, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xa94, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xa98, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.11", addend := 0 },
    { off := 0xa9c, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.11", addend := 0 },
    { off := 0xaa4, kind := .call26, sym := rustPanicFmtSym, addend := 0 },
    { off := 0xaa8, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xaac, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xab0, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.9", addend := 0 },
    { off := 0xab4, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.9", addend := 0 },
    { off := 0xabc, kind := .call26, sym := rustPanicFmtSym, addend := 0 },
    { off := 0xac0, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xac4, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.0", addend := 0 },
    { off := 0xac8, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.13", addend := 0 },
    { off := 0xacc, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.13", addend := 0 },
    { off := 0xad4, kind := .call26, sym := rustPanicFmtSym, addend := 0 },
    { off := 0xad8, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.10", addend := 0 },
    { off := 0xadc, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.10", addend := 0 },
    { off := 0xaec, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0xaf0, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.8", addend := 0 },
    { off := 0xaf4, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.8", addend := 0 },
    { off := 0xb04, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 },
    { off := 0xb08, kind := .adrpHi21, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.12", addend := 0 },
    { off := 0xb0c, kind := .addLo12, sym := "libcrux_hmac:.rodata..Lanon.4433146ba9efa48bc0981118e6275d7e.12", addend := 0 },
    { off := 0xb1c, kind := .call26, sym := rustSliceIndexFailSym, addend := 0 }]
  externs := libcruxHmacExterns
  weakRefs := []

@[expose] def libcruxHmacLib : Obj.MultiPlacedLib where
  name := "libcrux_sha2_hmac"
  blocks := [
    sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, libcruxHmacBlock]
  data := []
  exports := [
    sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym,
    sha256UpdateLastSym, sha256FinishSym, hash256Sym, libcruxHmacSym]

/-- Ambient `Placeable` placement of `libcruxHmacLib`. -/
class HaclPlacement where
  mpl : Obj.MultiPlacement
  placeable : libcruxHmacLib.Placeable mpl

abbrev haclMpl [HaclPlacement] : Obj.MultiPlacement := HaclPlacement.mpl

/-! ## 3. Symbol Uniqueness, `fnAddr` Equations, and Opcode Exclusion -/

theorem libcruxHmacLib_symbols_nodup :
    ((libcruxHmacLib.blocks.flatMap (·.symbols)).map (·.1)).Nodup := by
  decide

@[simp] theorem fnAddr_sha256Init (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl sha256InitSym = mpl.base 0 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock]

@[simp] theorem fnAddr_sha256Update (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl sha256UpdateSym = mpl.base 1 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256InitSym, sha256UpdateSym]

@[simp] theorem fnAddr_sha256UpdateNblocks (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl sha256UpdateNblocksSym = mpl.base 2 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym]

@[simp] theorem fnAddr_sha256UpdateLast (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl sha256UpdateLastSym = mpl.base 3 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym,
    sha256UpdateLastSym]

@[simp] theorem fnAddr_sha256Finish (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl sha256FinishSym = mpl.base 4 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, sha256InitSym, sha256UpdateSym,
    sha256UpdateNblocksSym, sha256UpdateLastSym, sha256FinishSym]

@[simp] theorem fnAddr_hash256 (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl hash256Sym = mpl.base 5 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, sha256InitSym, sha256UpdateSym,
    sha256UpdateNblocksSym, sha256UpdateLastSym, sha256FinishSym, hash256Sym]

@[simp] theorem fnAddr_libcruxHmac (mpl : Obj.MultiPlacement) :
    libcruxHmacLib.fnAddr mpl libcruxHmacSym = mpl.base 6 := by
  simp [Obj.MultiPlacedLib.fnAddr, Obj.lookupBlockSym, Obj.lookupBlockSymAux, Obj.lookup,
    libcruxHmacLib, sha256InitBlock, sha256UpdateBlock, sha256UpdateNblocksBlock,
    sha256UpdateLastBlock, sha256FinishBlock, hash256Block, libcruxHmacBlock,
    sha256InitSym, sha256UpdateSym, sha256UpdateNblocksSym, sha256UpdateLastSym,
    sha256FinishSym, hash256Sym, libcruxHmacSym]

set_option maxRecDepth 400000 in
theorem hacl_patchSafe_noSvc :
    Obj.CodeBlock.patchSafe svcAnyPat sha256InitBlock = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat sha256UpdateBlock = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat sha256UpdateNblocksBlock = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat sha256UpdateLastBlock = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat sha256FinishBlock = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat hash256Block = true ∧
    Obj.CodeBlock.patchSafe svcAnyPat libcruxHmacBlock = true :=
  ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel,
   by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

set_option maxRecDepth 400000 in
theorem hacl_patchSafe_noMsrTpidrEl0 :
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat sha256InitBlock = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat sha256UpdateBlock = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat sha256UpdateNblocksBlock = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat sha256UpdateLastBlock = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat sha256FinishBlock = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat hash256Block = true ∧
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat libcruxHmacBlock = true :=
  ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel,
   by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

private theorem hacl_blockLib_text_patchSafe_noSvc {i : Nat} (hi : i < 7) :
    Obj.CodeBlock.patchSafe svcAnyPat (libcruxHmacLib.blockLib i).text = true := by
  have hi' : i < libcruxHmacLib.blocks.length := hi
  rw [libcruxHmacLib.blockLib_text hi']
  rcases hacl_patchSafe_noSvc with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6

private theorem hacl_blockLib_text_patchSafe_noMsr {i : Nat} (hi : i < 7) :
    Obj.CodeBlock.patchSafe Obj.msrTpidrEl0Pat (libcruxHmacLib.blockLib i).text = true := by
  have hi' : i < libcruxHmacLib.blocks.length := hi
  rw [libcruxHmacLib.blockLib_text hi']
  rcases hacl_patchSafe_noMsrTpidrEl0 with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6

theorem hacl_blockProgram_noSvc (mpl : Obj.MultiPlacement) {i : Nat} (hi : i < 7)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (libcruxHmacLib.blockProgram mpl i externs overrides svc).allInstrs (fun ins => !ins.isSvc) = true :=
  Obj.PlacedLib.program_allInstrs_of_patchSafe (lib := libcruxHmacLib.blockLib i)
    (fun w _ hd hw => decode_not_isSvc hd (by rw [← svcAnyPat_matches]; exact hw))
    (hacl_blockLib_text_patchSafe_noSvc hi) (libcruxHmacLib.blockPlacement mpl i)
    externs overrides svc

theorem hacl_blockProgram_noMsrTpidrEl0 (mpl : Obj.MultiPlacement) {i : Nat} (hi : i < 7)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    (libcruxHmacLib.blockProgram mpl i externs overrides svc).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true :=
  Obj.PlacedLib.program_noMsrTpidrEl0_of_patchSafe (lib := libcruxHmacLib.blockLib i)
    (hacl_blockLib_text_patchSafe_noMsr hi) (libcruxHmacLib.blockPlacement mpl i)
    externs overrides svc

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
