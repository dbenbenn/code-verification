/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.Surface.IncludeBytes

/-!
# Multi-Block Placed Object Definitions

Object bundle for `dalekCliMultiLib : Obj.MultiPlacedLib` (checked against the linked ELF by
`MultiPlacedLib.checkInElf`): 36 `curve25519-dalek` `5.0.0` (`rustc 1.98.1`,
`aarch64-unknown-linux-musl`) `.text.<fn>` `CodeBlock`s (`dalekCliBlk00`..`dalekCliBlk35`),
stock `musl` `1.2.5` `memcpy` (`dalekCliBlk36`), and 11 `.rodata` / `.data.rel.ro` sections
(`dalekCliData00`..`dalekCliData10`).
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs

open Arm64 Arm64.Obj

/-! ## 1. Per-Section Code Blocks (`dalekCliBlk00`..`dalekCliBlk36`) -/

/-- Block `00` (`5` words): `subtle::black_box::<u8>`. -/
@[expose] def dalekCliBlk00Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 0 20

@[expose] def dalekCliBlk00 : CodeBlock where
  code := dalekCliBlk00Bytes
  align := 4
  symbols := [("subtle::black_box::<u8>", 0)]
  relocs := []

/-- Block `01` (`3` words): `<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order`. -/
@[expose] def dalekCliBlk01Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 20 12

@[expose] def dalekCliBlk01 : CodeBlock where
  code := dalekCliBlk01Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order", 0)]
  relocs := [
    { off := 8, kind := .jump26, sym := "<curve25519_dalek::scalar::Scalar>::reduce" }]

/-- Block `02` (`277` words): `<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide`. -/
@[expose] def dalekCliBlk02Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 32 1108

@[expose] def dalekCliBlk02 : CodeBlock where
  code := dalekCliBlk02Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide", 0)]
  relocs := [
    { off := 472, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.17" },
    { off := 476, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.17" },
    { off := 496, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::montgomery_mul" },
    { off := 508, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.16" },
    { off := 512, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.16" },
    { off := 536, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::montgomery_mul" },
    { off := 732, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `03` (`653` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::sqrt_ratio_i`. -/
@[expose] def dalekCliBlk03Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 1140 2612

@[expose] def dalekCliBlk03 : CodeBlock where
  code := dalekCliBlk03Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::field::FieldElement51>::sqrt_ratio_i", 0)]
  relocs := [
    { off := 56, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 72, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 88, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 104, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 120, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 136, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 148, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" },
    { off := 184, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 200, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 216, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 232, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 248, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 700, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::to_bytes" },
    { off := 712, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 1380, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 1388, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.8" },
    { off := 1392, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.8" },
    { off := 1420, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 2180, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 2200, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 2208, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 2380, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 2548, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `04` (`101` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501`. -/
@[expose] def dalekCliBlk04Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 3752 404

@[expose] def dalekCliBlk04 : CodeBlock where
  code := dalekCliBlk04Bytes
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

/-- Block `05` (`176` words): `<curve25519_dalek::edwards::CompressedEdwardsY>::decompress`. -/
@[expose] def dalekCliBlk05Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 4156 704

@[expose] def dalekCliBlk05 : CodeBlock where
  code := dalekCliBlk05Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::CompressedEdwardsY>::decompress", 0)]
  relocs := [
    { off := 112, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 136, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.6" },
    { off := 140, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.6" },
    { off := 232, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 276, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::sqrt_ratio_i" },
    { off := 368, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 564, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `06` (`329` words): `<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::montgomery_mul`. -/
@[expose] def dalekCliBlk06Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 4860 1316

@[expose] def dalekCliBlk06 : CodeBlock where
  code := dalekCliBlk06Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::montgomery_mul", 0)]
  relocs := [
    { off := 1188, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `07` (`662` words): `<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::mul`. -/
@[expose] def dalekCliBlk07Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 6176 2648

@[expose] def dalekCliBlk07 : CodeBlock where
  code := dalekCliBlk07Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::mul", 0)]
  relocs := [
    { off := 1168, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 2524, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `08` (`267` words): `<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards`. -/
@[expose] def dalekCliBlk08Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 8824 1068

@[expose] def dalekCliBlk08 : CodeBlock where
  code := dalekCliBlk08Bytes
  align := 4
  symbols := [("<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards", 0)]
  relocs := [
    { off := 92, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.7" },
    { off := 96, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.7" },
    { off := 408, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::to_bytes" },
    { off := 420, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 560, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" },
    { off := 616, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 632, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 648, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1032, kind := .call26, sym := "<curve25519_dalek::edwards::CompressedEdwardsY>::decompress" }]

/-- Block `09` (`191` words): `<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select`. -/
@[expose] def dalekCliBlk09Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 9892 764

@[expose] def dalekCliBlk09 : CodeBlock where
  code := dalekCliBlk09Bytes
  align := 4
  symbols := [("<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select", 0)]
  relocs := [
    { off := 132, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 432, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `10` (`229` words): `<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select`. -/
@[expose] def dalekCliBlk10Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 10656 916

@[expose] def dalekCliBlk10 : CodeBlock where
  code := dalekCliBlk10Bytes
  align := 4
  symbols := [("<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select", 0)]
  relocs := [
    { off := 152, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 560, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `11` (`100` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k`. -/
@[expose] def dalekCliBlk11Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 11572 400

@[expose] def dalekCliBlk11 : CodeBlock where
  code := dalekCliBlk11Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k", 0)]
  relocs := []

/-- Block `12` (`94` words): `<curve25519_dalek::backend::serial::u64::field::FieldElement51>::to_bytes`. -/
@[expose] def dalekCliBlk12Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 11972 376

@[expose] def dalekCliBlk12 : CodeBlock where
  code := dalekCliBlk12Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::u64::field::FieldElement51>::to_bytes", 0)]
  relocs := []

/-- Block `13` (`144` words): `<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double`. -/
@[expose] def dalekCliBlk13Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 12348 576

@[expose] def dalekCliBlk13 : CodeBlock where
  code := dalekCliBlk13Bytes
  align := 4
  symbols := [("<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double", 0)]
  relocs := [
    { off := 48, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 64, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 80, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 176, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" }]

/-- Block `14` (`204` words): `<curve25519_dalek::edwards::EdwardsPoint>::compress`. -/
@[expose] def dalekCliBlk14Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 12924 816

@[expose] def dalekCliBlk14 : CodeBlock where
  code := dalekCliBlk14Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::compress", 0)]
  relocs := [
    { off := 52, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow22501" },
    { off := 104, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 120, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 136, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 152, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 560, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `15` (`173` words): `<curve25519_dalek::scalar::Scalar>::as_radix_16`. -/
@[expose] def dalekCliBlk15Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 13740 692

@[expose] def dalekCliBlk15 : CodeBlock where
  code := dalekCliBlk15Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar>::as_radix_16", 0)]
  relocs := []

/-- Block `16` (`427` words): `<curve25519_dalek::scalar::Scalar>::reduce`. -/
@[expose] def dalekCliBlk16Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 14432 1708

@[expose] def dalekCliBlk16 : CodeBlock where
  code := dalekCliBlk16Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar>::reduce", 0)]
  relocs := [
    { off := 1364, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `17` (`316` words): `<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint`. -/
@[expose] def dalekCliBlk17Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 16140 1264

@[expose] def dalekCliBlk17 : CodeBlock where
  code := dalekCliBlk17Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint", 0)]
  relocs := [
    { off := 440, kind := .call26, sym := "<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from" },
    { off := 448, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 452, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 472, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.36" },
    { off := 476, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.36" },
    { off := 536, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 584, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 600, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 616, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 632, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 660, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" },
    { off := 704, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 720, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 736, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 752, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 792, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::sub" },
    { off := 840, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 856, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 872, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 888, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 912, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add" },
    { off := 932, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 948, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 964, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 980, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1012, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::sub" },
    { off := 1028, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1044, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1060, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1148, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1164, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1180, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" },
    { off := 1196, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1232, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.38" },
    { off := 1236, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.38" },
    { off := 1244, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1248, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.37" },
    { off := 1252, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.c6ce7f773b28f90d27bc9bfaab0b7cc0.37" },
    { off := 1260, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `18` (`79` words): `<curve25519_dalek::edwards::EdwardsPoint>::mul_by_pow_2`. -/
@[expose] def dalekCliBlk18Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 17404 316

@[expose] def dalekCliBlk18 : CodeBlock where
  code := dalekCliBlk18Bytes
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

/-- Block `19` (`32` words): `<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free`. -/
@[expose] def dalekCliBlk19Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 17720 128

@[expose] def dalekCliBlk19 : CodeBlock where
  code := dalekCliBlk19Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free", 0)]
  relocs := [
    { off := 16, kind := .adrpHi21, sym := "curve25519_dalek:.rodata.cst32+0x0" },
    { off := 20, kind := .addLo12, sym := "curve25519_dalek:.rodata.cst32+0x0" },
    { off := 32, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul" },
    { off := 40, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 44, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 100, kind := .call26, sym := "<curve25519_dalek::edwards::EdwardsPoint as subtle::ConstantTimeEq>::ct_eq" }]

/-- Block `20` (`317` words): `<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from`. -/
@[expose] def dalekCliBlk20Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 17848 1268

@[expose] def dalekCliBlk20 : CodeBlock where
  code := dalekCliBlk20Bytes
  align := 4
  symbols := [("<curve25519_dalek::window::NafLookupTable5<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from", 0)]
  relocs := [
    { off := 72, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 76, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 716, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 736, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 752, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 768, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 784, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 812, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" },
    { off := 832, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 852, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 868, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 884, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1072, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 1076, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 1100, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1232, kind := .call26, sym := "memcpy" }]

/-- Block `21` (`147` words): `<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul`. -/
@[expose] def dalekCliBlk21Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 19116 588

@[expose] def dalekCliBlk21 : CodeBlock where
  code := dalekCliBlk21Bytes
  align := 4
  symbols := [("<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul", 0)]
  relocs := [
    { off := 304, kind := .call26, sym := "<curve25519_dalek::backend::serial::u64::scalar::Scalar52>::mul" }]

/-- Block `22` (`166` words): `<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul`. -/
@[expose] def dalekCliBlk22Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 19704 664

@[expose] def dalekCliBlk22 : CodeBlock where
  code := dalekCliBlk22Bytes
  align := 4
  symbols := [("<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul", 0)]
  relocs := []

/-- Block `23` (`197` words): `<&curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add`. -/
@[expose] def dalekCliBlk23Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 20368 788

@[expose] def dalekCliBlk23 : CodeBlock where
  code := dalekCliBlk23Bytes
  align := 4
  symbols := [("<&curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add", 0)]
  relocs := [
    { off := 416, kind := .call26, sym := "subtle::black_box::<u8>" }]

/-- Block `24` (`210` words): `<[u8] as subtle::ConstantTimeEq>::ct_eq`. -/
@[expose] def dalekCliBlk24Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 21156 840

@[expose] def dalekCliBlk24 : CodeBlock where
  code := dalekCliBlk24Bytes
  align := 4
  symbols := [("<[u8] as subtle::ConstantTimeEq>::ct_eq", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 64, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 88, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 112, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 140, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 164, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 188, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 216, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 240, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 264, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 288, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 316, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 340, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 364, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 388, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 412, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 440, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 464, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 488, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 512, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 536, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 560, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 588, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 612, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 636, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 660, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 684, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 708, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 732, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 760, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 784, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 808, kind := .call26, sym := "subtle::black_box::<u8>" },
    { off := 836, kind := .jump26, sym := "subtle::black_box::<u8>" }]

/-- Block `25` (`323` words): `<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from`. -/
@[expose] def dalekCliBlk25Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 21996 1292

@[expose] def dalekCliBlk25 : CodeBlock where
  code := dalekCliBlk25Bytes
  align := 4
  symbols := [("<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from", 0)]
  relocs := [
    { off := 184, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 188, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 228, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 800, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" },
    { off := 820, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 840, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 856, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 872, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1056, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 1060, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.22" },
    { off := 1084, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1256, kind := .call26, sym := "memcpy" }]

/-- Block `26` (`167` words): `<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base`. -/
@[expose] def dalekCliBlk26Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 23288 668

@[expose] def dalekCliBlk26 : CodeBlock where
  code := dalekCliBlk26Bytes
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

/-- Block `27` (`4` words): `<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul`. -/
@[expose] def dalekCliBlk27Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 23956 16

@[expose] def dalekCliBlk27 : CodeBlock where
  code := dalekCliBlk27Bytes
  align := 4
  symbols := [("<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul", 0)]
  relocs := [
    { off := 12, kind := .jump26, sym := "<curve25519_dalek::edwards::EdwardsBasepointTable as curve25519_dalek::traits::BasepointTable>::mul_base" }]

/-- Block `28` (`156` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add`. -/
@[expose] def dalekCliBlk28Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 23972 624

@[expose] def dalekCliBlk28 : CodeBlock where
  code := dalekCliBlk28Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add", 0)]
  relocs := [
    { off := 224, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 272, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `29` (`156` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::sub`. -/
@[expose] def dalekCliBlk29Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 24596 624

@[expose] def dalekCliBlk29 : CodeBlock where
  code := dalekCliBlk29Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::sub", 0)]
  relocs := [
    { off := 224, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 272, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `30` (`408` words): `<curve25519_dalek::edwards::EdwardsPoint as subtle::ConstantTimeEq>::ct_eq`. -/
@[expose] def dalekCliBlk30Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 25220 1632

@[expose] def dalekCliBlk30 : CodeBlock where
  code := dalekCliBlk30Bytes
  align := 4
  symbols := [("<curve25519_dalek::edwards::EdwardsPoint as subtle::ConstantTimeEq>::ct_eq", 0)]
  relocs := [
    { off := 40, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 56, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 812, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 832, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 848, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 1600, kind := .call26, sym := "<[u8] as subtle::ConstantTimeEq>::ct_eq" },
    { off := 1628, kind := .jump26, sym := "subtle::black_box::<u8>" }]

/-- Block `31` (`152` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add`. -/
@[expose] def dalekCliBlk31Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 26852 608

@[expose] def dalekCliBlk31 : CodeBlock where
  code := dalekCliBlk31Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::add", 0)]
  relocs := [
    { off := 224, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `32` (`152` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::sub`. -/
@[expose] def dalekCliBlk32Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 27460 608

@[expose] def dalekCliBlk32 : CodeBlock where
  code := dalekCliBlk32Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Sub<&curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::sub", 0)]
  relocs := [
    { off := 224, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 240, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 256, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `33` (`219` words): `<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul`. -/
@[expose] def dalekCliBlk33Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 28068 876

@[expose] def dalekCliBlk33 : CodeBlock where
  code := dalekCliBlk33Bytes
  align := 4
  symbols := [("<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul", 0)]
  relocs := [
    { off := 44, kind := .call26, sym := "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> as core::convert::From<&curve25519_dalek::edwards::EdwardsPoint>>::from" },
    { off := 60, kind := .call26, sym := "<curve25519_dalek::scalar::Scalar>::as_radix_16" },
    { off := 68, kind := .adrpHi21, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 72, kind := .addLo12, sym := "curve25519_dalek:.rodata..Lanon.0" },
    { off := 144, kind := .call26, sym := "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select" },
    { off := 164, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" },
    { off := 184, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 200, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 216, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 280, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 296, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 312, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 328, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 392, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 408, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 424, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 440, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 504, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 520, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 536, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 552, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 616, kind := .call26, sym := "<curve25519_dalek::backend::serial::curve_models::ProjectivePoint>::double" },
    { off := 632, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 648, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 664, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 680, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 756, kind := .call26, sym := "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::select" },
    { off := 772, kind := .call26, sym := "<&curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Add<&curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint>>::add" },
    { off := 800, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 816, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 832, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" },
    { off := 848, kind := .call26, sym := "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" }]

/-- Block `34` (`1` words): `<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul`. -/
@[expose] def dalekCliBlk34Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 28944 4

@[expose] def dalekCliBlk34 : CodeBlock where
  code := dalekCliBlk34Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul" }]

/-- Block `35` (`1` words): `<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add`. -/
@[expose] def dalekCliBlk35Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 28948 4

@[expose] def dalekCliBlk35 : CodeBlock where
  code := dalekCliBlk35Bytes
  align := 4
  symbols := [("<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add" }]

/-- Block `36` (`99` words): `memcpy`. -/
@[expose] def dalekCliBlk36Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 28952 396

@[expose] def dalekCliBlk36 : CodeBlock where
  code := dalekCliBlk36Bytes
  align := 4
  symbols := [("memcpy", 0)]
  relocs := []

/-! ## 2. Mathematical `.rodata` & `.data.rel.ro` Objects (`dalekCliData00`..`dalekCliData10`) -/

/-- Data `00` (`D[1]`, `8` bytes): `curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE`. -/
@[expose] def dalekCliData00Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29348 8

@[expose] def dalekCliData00 : SymDataInfo where
  sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE"
  align := 8
  readOnly := true
  bytes := dalekCliData00Bytes
  relocs := [
    { off := 0, kind := .abs64, sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN" }]

/-- Data `01` (`D[2]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.0`. -/
@[expose] def dalekCliData01Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29356 40

@[expose] def dalekCliData01 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.0"
  align := 8
  readOnly := true
  bytes := dalekCliData01Bytes
  relocs := []

/-- Data `02` (`D[8]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.6`. -/
@[expose] def dalekCliData02Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29396 40

@[expose] def dalekCliData02 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.6"
  align := 8
  readOnly := true
  bytes := dalekCliData02Bytes
  relocs := []

/-- Data `03` (`D[9]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.7`. -/
@[expose] def dalekCliData03Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29436 40

@[expose] def dalekCliData03 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.7"
  align := 8
  readOnly := true
  bytes := dalekCliData03Bytes
  relocs := []

/-- Data `04` (`D[10]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.8`. -/
@[expose] def dalekCliData04Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29476 40

@[expose] def dalekCliData04 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.8"
  align := 8
  readOnly := true
  bytes := dalekCliData04Bytes
  relocs := []

/-- Data `05` (`D[17]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.16`. -/
@[expose] def dalekCliData05Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29516 40

@[expose] def dalekCliData05 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.16"
  align := 8
  readOnly := true
  bytes := dalekCliData05Bytes
  relocs := []

/-- Data `06` (`D[18]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.17`. -/
@[expose] def dalekCliData06Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29556 40

@[expose] def dalekCliData06 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.17"
  align := 8
  readOnly := true
  bytes := dalekCliData06Bytes
  relocs := []

/-- Data `07` (`D[22]`, `40` bytes): `curve25519_dalek:.rodata..Lanon.22`. -/
@[expose] def dalekCliData07Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29596 40

@[expose] def dalekCliData07 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.22"
  align := 8
  readOnly := true
  bytes := dalekCliData07Bytes
  relocs := []

/-- Data `08` (`D[31]`, `32` bytes): `curve25519_dalek:.rodata.cst32+0x0`. -/
@[expose] def dalekCliData08Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29636 32

@[expose] def dalekCliData08 : SymDataInfo where
  sym := "curve25519_dalek:.rodata.cst32+0x0"
  align := 1
  readOnly := true
  bytes := dalekCliData08Bytes
  relocs := []

/-- Data `09` (`D[37]`, `7680` bytes): `curve25519_dalek:.rodata..Lanon.36`. -/
@[expose] def dalekCliData09Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 29668 7680

@[expose] def dalekCliData09 : SymDataInfo where
  sym := "curve25519_dalek:.rodata..Lanon.36"
  align := 8
  readOnly := true
  bytes := dalekCliData09Bytes
  relocs := []

/-- Data `10` (`D[40]`, `30720` bytes): `curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`. -/
@[expose] def dalekCliData10Bytes : List (BitVec 8) :=
  include_bytes% "DalekCliPlacedObj.bin" 37348 30720

@[expose] def dalekCliData10 : SymDataInfo where
  sym := "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"
  align := 8
  readOnly := true
  bytes := dalekCliData10Bytes
  relocs := []

@[expose] def dalekCliBlocks : List CodeBlock :=
  [dalekCliBlk00, dalekCliBlk01, dalekCliBlk02, dalekCliBlk03, dalekCliBlk04, dalekCliBlk05, dalekCliBlk06, dalekCliBlk07, dalekCliBlk08, dalekCliBlk09, dalekCliBlk10, dalekCliBlk11, dalekCliBlk12, dalekCliBlk13, dalekCliBlk14, dalekCliBlk15, dalekCliBlk16, dalekCliBlk17, dalekCliBlk18, dalekCliBlk19, dalekCliBlk20, dalekCliBlk21, dalekCliBlk22, dalekCliBlk23, dalekCliBlk24, dalekCliBlk25, dalekCliBlk26, dalekCliBlk27, dalekCliBlk28, dalekCliBlk29, dalekCliBlk30, dalekCliBlk31, dalekCliBlk32, dalekCliBlk33, dalekCliBlk34, dalekCliBlk35, dalekCliBlk36]

@[expose] def dalekCliData : List SymDataInfo :=
  [dalekCliData00, dalekCliData01, dalekCliData02, dalekCliData03, dalekCliData04, dalekCliData05, dalekCliData06, dalekCliData07, dalekCliData08, dalekCliData09, dalekCliData10]

@[expose] def dalekCliExports : List String := [
  "subtle::black_box::<u8>",
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order",
  "<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide",
  "<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards",
  "<curve25519_dalek::edwards::EdwardsPoint>::compress",
  "<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint",
  "<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free",
  "<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul",
  "<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul",
  "<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add",
  "memcpy"]

@[expose] def dalekCliExportSyms : List (String × String) := [
  ("subtle::black_box::<u8>", "_RINvCsdqpLrhraQXi_6subtle9black_boxhECs2wR8L9wiBdT_16curve25519_dalek"),
  ("<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order", "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order"),
  ("<curve25519_dalek::scalar::Scalar>::from_bytes_mod_order_wide", "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide"),
  ("<curve25519_dalek::montgomery::MontgomeryPoint>::to_edwards", "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"),
  ("<curve25519_dalek::edwards::EdwardsPoint>::compress", "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress"),
  ("<curve25519_dalek::edwards::EdwardsPoint>::vartime_double_scalar_mul_basepoint", "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint"),
  ("<curve25519_dalek::edwards::EdwardsPoint>::is_torsion_free", "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free"),
  ("<&curve25519_dalek::scalar::Scalar as core::ops::arith::Mul<&curve25519_dalek::edwards::EdwardsBasepointTable>>::mul", "_RNvXsX_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsRNtNtB7_6scalar6ScalarINtNtNtCskxtBwYRO61I_4core3ops5arith3MulRNtB5_21EdwardsBasepointTableE3mul"),
  ("<curve25519_dalek::scalar::Scalar as core::ops::arith::Mul>::mul", "_RNvXsv_NtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB5_6ScalarNtNtNtCskxtBwYRO61I_4core3ops5arith3Mul3mul"),
  ("<curve25519_dalek::scalar::Scalar as core::ops::arith::Add>::add", "_RNvXsz_NtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB5_6ScalarNtNtNtCskxtBwYRO61I_4core3ops5arith3Add3add")]

/-- Multi-block placed library for all active `libsignal-cli` `curve25519-dalek` `5.0.0`
    `EdwardsPoint` / `MontgomeryPoint::to_edwards` / `Scalar` functions + `musl` `memcpy`. -/
@[expose] def dalekCliMultiLib : MultiPlacedLib where
  name := "dalek_cli_edwards"
  blocks := dalekCliBlocks
  data := dalekCliData
  exports := dalekCliExports
  exportSyms := dalekCliExportSyms

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs
