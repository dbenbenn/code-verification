/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib.Placed.Multi
public import ProofLib.Placed.OpcodeExclusion

/-!
# Multi-block placed object definitions for `x25519-dalek`

Object bundle checked against the linked ELF by `MultiPlacedLib.checkInElf`:

- 19 `rustc 1.98.1` (`aarch64-unknown-linux-musl`) `.text.<fn>` `CodeBlock`s
  (`x25519CliBlk00`..`x25519CliBlk18`, `2,127` words = `8,508` bytes) forming the transitive
  call-graph closure of `<x25519_dalek::PublicKey as From<&StaticSecret>>::from`
  (`lsPubFromSecretSym`) and `<x25519_dalek::StaticSecret>::diffie_hellman` (`lsDiffieHellmanSym`).
- 3 `.rodata` sections (`x25519CliData00`..`x25519CliData02`, `30,800` bytes).
- `x25519CliMultiLib : Obj.MultiPlacedLib` and `patchSafe` opcode-exclusion theorems
  (`svc0Pat` and `msrTpidrEl0Pat`).
-/

set_option autoImplicit false
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs

open Arm64 Arm64.Obj

/-! ## 1. Per-Section Code Blocks (`x25519CliBlk00`..`x25519CliBlk18`) -/

/-- Block `00` (`5` words): `subtle::black_box::<u8>`. -/
@[expose] def x25519CliBlk00Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 0 20

@[expose] def x25519CliBlk00 : CodeBlock where
  code := x25519CliBlk00Bytes
  align := 4
  symbols := [("subtle::black_box::<u8>", 0)]
  relocs := []

/-- Block `01` (`166` words): `<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul`. -/
@[expose] def x25519CliBlk01Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 20 664

@[expose] def x25519CliBlk01 : CodeBlock where
  code := x25519CliBlk01Bytes
  align := 4
  symbols := [("<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul", 0)]
  relocs := []

/-- Block `02` (`100` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k`. -/
@[expose] def x25519CliBlk02Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 684 400

@[expose] def x25519CliBlk02 : CodeBlock where
  code := x25519CliBlk02Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k", 0)]
  relocs := []

/-- Block `03` (`173` words): `<curve25519_dalek::scalar::Scalar>::as_radix_16`. -/
@[expose] def x25519CliBlk03Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 1084 692

@[expose] def x25519CliBlk03 : CodeBlock where
  code := x25519CliBlk03Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar>::as_radix_16", 0)]
  relocs := []

/-- Block `04` (`41` words): `<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth`. -/
@[expose] def x25519CliBlk04Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 1776 164

@[expose] def x25519CliBlk04 : CodeBlock where
  code := x25519CliBlk04Bytes
  align := 4
  symbols := [("<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth", 0)]
  relocs := [
    { off := 128, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 132, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 140, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 144, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 148, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 160, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `05` (`101` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501`. -/
@[expose] def x25519CliBlk05Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 1940 404

@[expose] def x25519CliBlk05 : CodeBlock where
  code := x25519CliBlk05Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 56, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 72, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 88, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 104, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 120, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 136, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 152, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 168, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 184, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 200, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 216, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 232, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 248, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 264, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 280, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 296, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 312, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 328, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 344, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 360, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `06` (`191` words): `<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select`. -/
@[expose] def x25519CliBlk06Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 2344 764

@[expose] def x25519CliBlk06 : CodeBlock where
  code := x25519CliBlk06Bytes
  align := 4
  symbols := [("<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select", 0)]
  relocs := [
    { off := 132, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 432, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `07` (`144` words): `<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double`. -/
@[expose] def x25519CliBlk07Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 3108 576

@[expose] def x25519CliBlk07 : CodeBlock where
  code := x25519CliBlk07Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double", 0)]
  relocs := [
    { off := 48, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 64, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 80, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 176, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" }]

/-- Block `08` (`152` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add`. -/
@[expose] def x25519CliBlk08Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 3684 608

@[expose] def x25519CliBlk08 : CodeBlock where
  code := x25519CliBlk08Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add", 0)]
  relocs := [
    { off := 224, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `09` (`79` words): `<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2`. -/
@[expose] def x25519CliBlk09Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 4292 316

@[expose] def x25519CliBlk09 : CodeBlock where
  code := x25519CliBlk09Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2", 0)]
  relocs := [
    { off := 112, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 128, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 144, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 160, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 224, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 272, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 288, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `10` (`171` words): `<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery`. -/
@[expose] def x25519CliBlk10Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 4608 684

@[expose] def x25519CliBlk10 : CodeBlock where
  code := x25519CliBlk10Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery", 0)]
  relocs := [
    { off := 204, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" },
    { off := 260, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 276, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 292, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `11` (`130` words): `<curve25519_dalek::montgomery::ProjectivePoint>::as_affine`. -/
@[expose] def x25519CliBlk11Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 5292 520

@[expose] def x25519CliBlk11 : CodeBlock where
  code := x25519CliBlk11Bytes
  align := 4
  symbols := [("<curve25519_dalek::montgomery::ProjectivePoint>::as_affine", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" },
    { off := 92, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 108, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 124, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `12` (`238` words): `curve25519_dalek::montgomery::differential_add_and_double`. -/
@[expose] def x25519CliBlk12Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 5812 952

@[expose] def x25519CliBlk12 : CodeBlock where
  code := x25519CliBlk12Bytes
  align := 4
  symbols := [("curve25519_dalek::montgomery::differential_add_and_double", 0)]
  relocs := [
    { off := 364, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 380, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 512, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 528, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 696, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 712, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 716, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.35" },
    { off := 720, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.35" },
    { off := 732, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 748, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 808, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 824, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `13` (`167` words): `<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base`. -/
@[expose] def x25519CliBlk13Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 6764 668

@[expose] def x25519CliBlk13 : CodeBlock where
  code := x25519CliBlk13Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base", 0)]
  relocs := [
    { off := 56, kind := .call26, sym := "<curve25519_dalek::scalar::Scalar>::as_radix_16" },
    { off := 64, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 68, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 180, kind := .call26, sym := "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select" },
    { off := 196, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add" },
    { off := 212, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 228, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 244, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 260, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 332, kind := .call26, sym := "<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2" },
    { off := 444, kind := .call26, sym := "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select" },
    { off := 460, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add" },
    { off := 476, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 492, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 508, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 524, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 652, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.65" },
    { off := 656, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.65" },
    { off := 664, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `14` (`11` words): `<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped`. -/
@[expose] def x25519CliBlk14Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 7432 44

@[expose] def x25519CliBlk14 : CodeBlock where
  code := x25519CliBlk14Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped", 0)]
  relocs := [
    { off := 16, kind := .adrpHi21, sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" },
    { off := 20, kind := .addLo12, sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" },
    { off := 40, kind := .jump26, sym := "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base" }]

/-- Block `15` (`211` words): `<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul`. -/
@[expose] def x25519CliBlk15Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 7476 844

@[expose] def x25519CliBlk15 : CodeBlock where
  code := x25519CliBlk15Bytes
  align := 4
  symbols := [("<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul", 0)]
  relocs := [
    { off := 120, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 124, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 252, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 512, kind := .call26, sym := "curve25519_dalek::montgomery::differential_add_and_double" },
    { off := 544, kind := .call26, sym := "<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth" },
    { off := 576, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 788, kind := .call26, sym := "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine" },
    { off := 824, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 828, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.5" },
    { off := 840, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `16` (`17` words): `<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped`. -/
@[expose] def x25519CliBlk16Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8320 68

@[expose] def x25519CliBlk16 : CodeBlock where
  code := x25519CliBlk16Bytes
  align := 4
  symbols := [("<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped", 0)]
  relocs := [
    { off := 52, kind := .call26, sym := "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul" }]

/-- Block `17` (`13` words): `<x25519_dalek::x25519::StaticSecret>::diffie_hellman`. -/
@[expose] def x25519CliBlk17Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8388 52

@[expose] def x25519CliBlk17 : CodeBlock where
  code := x25519CliBlk17Bytes
  align := 4
  symbols := [("<x25519_dalek::x25519::StaticSecret>::diffie_hellman", 0)]
  relocs := [
    { off := 36, kind := .call26, sym := "<curve25519_dalek::montgomery::MontgomeryPoint>::mul_clamped" }]

/-- Block `18` (`17` words): `<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from`. -/
@[expose] def x25519CliBlk18Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8440 68

@[expose] def x25519CliBlk18 : CodeBlock where
  code := x25519CliBlk18Bytes
  align := 4
  symbols := [("<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from", 0)]
  relocs := [
    { off := 36, kind := .call26, sym := "<curve25519_dalek::edwards::EdwardsPoint>::mul_base_clamped" },
    { off := 48, kind := .call26, sym := "<curve25519_dalek::edwards::EdwardsPoint>::to_montgomery" }]

/-! ## 2. Active `.rodata` Sections (`x25519CliData00`..`x25519CliData02`) -/

/-- Data `00` (`40` bytes, align `8`): `curve25519_dalek:.rodata..Lanon.0`. -/
@[expose] def x25519CliData00Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8508 40

@[expose] def x25519CliData00 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.0"
  align := 8
  readOnly := true
  bytes := x25519CliData00Bytes
  relocs := []

/-- Data `01` (`40` bytes, align `8`): `curve25519_dalek:.rodata..Lanon.35`. -/
@[expose] def x25519CliData01Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8548 40

@[expose] def x25519CliData01 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.35"
  align := 8
  readOnly := true
  bytes := x25519CliData01Bytes
  relocs := []

/-- Data `02` (`30720` bytes, align `8`): `curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`. -/
@[expose] def x25519CliData02Bytes : List (BitVec 8) :=
  include_bytes% "CryptoX25519PlacedObj.bin" 8588 30720

@[expose] def x25519CliData02 : SymDataInfo where
  sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"
  align := 8
  readOnly := true
  bytes := x25519CliData02Bytes
  relocs := []

/-! ## 3. Multi-Block Library Bundle & Static Opcode-Exclusion Checks -/

@[expose] def x25519CliBlocks : List CodeBlock :=
  [x25519CliBlk00, x25519CliBlk01, x25519CliBlk02, x25519CliBlk03, x25519CliBlk04, x25519CliBlk05, x25519CliBlk06, x25519CliBlk07, x25519CliBlk08, x25519CliBlk09, x25519CliBlk10, x25519CliBlk11, x25519CliBlk12, x25519CliBlk13, x25519CliBlk14, x25519CliBlk15, x25519CliBlk16, x25519CliBlk17, x25519CliBlk18]

@[expose] def x25519CliData : List SymDataInfo :=
  [x25519CliData00, x25519CliData01, x25519CliData02]

@[expose] def x25519CliExports : List String := [
  "<x25519_dalek::x25519::StaticSecret>::diffie_hellman",
  "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"]

@[expose] def x25519CliExportSyms : List (String × String) := [
  ("<x25519_dalek::x25519::StaticSecret>::diffie_hellman", "_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman"),
  ("<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from", "_RNvXs8_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_9PublicKeyINtNtCskxtBwYRO61I_4core7convert4FromRNtB5_12StaticSecretE4from")]

/-- Multi-block placed library for `x25519-dalek` `3.0.0` `StaticSecret::diffie_hellman`
    (`lsDiffieHellmanSym`) and `<PublicKey as From<&StaticSecret>>::from` (`lsPubFromSecretSym`)
    together with their complete `curve25519-dalek` `5.0.0` `.text` and `.rodata` closure. -/
@[expose] def x25519CliMultiLib : MultiPlacedLib where
  name := "x25519_cli"
  blocks := x25519CliBlocks
  data := x25519CliData
  exports := x25519CliExports
  exportSyms := x25519CliExportSyms

set_option maxHeartbeats 10000000 in
/-- Every block of `x25519CliMultiLib` is statically free of `SVC #0` under arbitrary
    relocation patching. -/
theorem x25519CliMultiLib_blocks_all_svc0 :
    (x25519CliMultiLib.blocks.all fun b => b.patchSafe svc0Pat) = true := by
  decide +kernel

theorem x25519CliMultiLib_patchSafe_svc0 :
    ∀ k (hk : k < x25519CliMultiLib.blocks.length),
      x25519CliMultiLib.blocks[k].patchSafe svc0Pat = true := by
  intro k hk
  exact List.all_eq_true.mp x25519CliMultiLib_blocks_all_svc0 x25519CliMultiLib.blocks[k]
    (List.getElem_mem hk)

set_option maxHeartbeats 10000000 in
/-- Every block of `x25519CliMultiLib` is statically free of `MSR TPIDR_EL0, Xt` under
    arbitrary relocation patching. -/
theorem x25519CliMultiLib_blocks_all_msr :
    (x25519CliMultiLib.blocks.all fun b => b.patchSafe msrTpidrEl0Pat) = true := by
  decide +kernel

theorem x25519CliMultiLib_patchSafe_msr :
    ∀ k (hk : k < x25519CliMultiLib.blocks.length),
      x25519CliMultiLib.blocks[k].patchSafe msrTpidrEl0Pat = true := by
  intro k hk
  exact List.all_eq_true.mp x25519CliMultiLib_blocks_all_msr x25519CliMultiLib.blocks[k]
    (List.getElem_mem hk)

theorem x25519CliMultiLib_blocks_all_externs_empty :
    (x25519CliMultiLib.blocks.all fun b => b.externs.isEmpty) = true := by
  decide +kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.PlacedObjDefs
