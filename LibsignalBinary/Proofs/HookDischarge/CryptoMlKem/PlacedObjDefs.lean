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
# Multi-block placed object definitions

Library object bundle checked against the linked ELF by `MultiPlacedLib.checkInElf`:
28 `libcrux_ml_kem` `0.0.10` and `libcrux_sha3` (`rustc 1.98.1`, `aarch64-unknown-linux-musl`)
`.text.<fn>` `CodeBlock`s (`mlkemBlk00`..`mlkemBlk27`), 4 stock `musl` `1.2.5` blocks
(`mlkemBlk28`..`mlkemBlk31` for `memcpy`, `memset`, `bcmp`, `memcmp`), 11 read-only `.rodata`
constants (`mlkemData00`..`mlkemData10`), and `mlkemMultiLib : Obj.MultiPlacedLib`.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs

open Arm64 Arm64.Obj

/-! ## 1. Per-Section Code Blocks (`mlkemBlk00`..`mlkemBlk31`) -/

/-- Block `00` (`713` words): `libcrux_ml_kem` `libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>`. -/
@[expose] def mlkemBlk00Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 0 2852

@[expose] def mlkemBlk00 : CodeBlock where
  code := mlkemBlk00Bytes
  align := 4
  symbols := [("libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>", 0)]
  relocs := [
    { off := 188, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 192, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 1460, kind := .call26, sym := "memcpy" },
    { off := 1532, kind := .call26, sym := "memcpy" },
    { off := 2664, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2668, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2676, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2688, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2692, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2696, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2708, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2712, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2720, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2732, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2736, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2740, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2752, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2756, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 2764, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2776, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2780, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 2784, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2788, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.9" },
    { off := 2792, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.9" },
    { off := 2808, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2812, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.8" },
    { off := 2816, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.8" },
    { off := 2828, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 2832, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2836, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2848, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `01` (`601` words): `libcrux_ml_kem` `libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>`. -/
@[expose] def mlkemBlk01Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 2852 2404

@[expose] def mlkemBlk01 : CodeBlock where
  code := mlkemBlk01Bytes
  align := 4
  symbols := [("libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>", 0)]
  relocs := [
    { off := 88, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 92, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 180, kind := .call26, sym := "<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Absorb<2>>::load_block::<136>" },
    { off := 1132, kind := .call26, sym := "memcpy" },
    { off := 1212, kind := .call26, sym := "memcpy" },
    { off := 2332, kind := .call26, sym := "<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t>>::squeeze2::<136>" },
    { off := 2384, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2388, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2400, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `02` (`595` words): `libcrux_ml_kem` `libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>`. -/
@[expose] def mlkemBlk02Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 5256 2380

@[expose] def mlkemBlk02 : CodeBlock where
  code := mlkemBlk02Bytes
  align := 4
  symbols := [("libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>", 0)]
  relocs := [
    { off := 84, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 88, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 172, kind := .call26, sym := "<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Absorb<2>>::load_block::<136>" },
    { off := 1124, kind := .call26, sym := "memcpy" },
    { off := 1204, kind := .call26, sym := "memcpy" },
    { off := 2360, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2364, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" },
    { off := 2376, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `03` (`7114` words): `libcrux_ml_kem` `libcrux_ml_kem::ind_cca::incremental::neon::encapsulate1_serialized::<3, 1088, 960, 10, 320, 2, 128, 2, 128>`. -/
@[expose] def mlkemBlk03Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 7636 28456

@[expose] def mlkemBlk03 : CodeBlock where
  code := mlkemBlk03Bytes
  align := 4
  symbols := [("libcrux_ml_kem::ind_cca::incremental::neon::encapsulate1_serialized::<3, 1088, 960, 10, 320, 2, 128, 2, 128>", 0)]
  relocs := [
    { off := 248, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" },
    { off := 432, kind := .call26, sym := "memset" },
    { off := 456, kind := .call26, sym := "memcpy" },
    { off := 476, kind := .call26, sym := "memcpy" },
    { off := 496, kind := .call26, sym := "memcpy" },
    { off := 528, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 544, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 552, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 556, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 588, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 592, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 600, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 608, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 1316, kind := .call26, sym := "memset" },
    { off := 12948, kind := .call26, sym := "memset" },
    { off := 13008, kind := .call26, sym := "memset" },
    { off := 13248, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 13300, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 13576, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 13580, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 13636, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 13640, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 18240, kind := .call26, sym := "memset" },
    { off := 18484, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 18536, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 19372, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 20020, kind := .call26, sym := "memset" },
    { off := 20072, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 20076, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 20988, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 20992, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 21152, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 21156, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 27284, kind := .call26, sym := "memcpy" },
    { off := 27392, kind := .call26, sym := "memcpy" },
    { off := 27412, kind := .call26, sym := "memcpy" },
    { off := 27428, kind := .call26, sym := "memcpy" },
    { off := 27832, kind := .call26, sym := "memcpy" },
    { off := 27852, kind := .call26, sym := "memcpy" },
    { off := 27888, kind := .call26, sym := "memcpy" },
    { off := 27928, kind := .call26, sym := "memcpy" },
    { off := 27968, kind := .call26, sym := "memcpy" },
    { off := 27984, kind := .call26, sym := "memcpy" },
    { off := 28252, kind := .call26, sym := "<libcrux_ml_kem::ind_cca::incremental::types::EncapsState<3, libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector>>::to_bytes" },
    { off := 28320, kind := .call26, sym := "memcpy" },
    { off := 28380, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 28384, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 28388, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28392, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 28396, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 28400, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28404, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 28408, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 28412, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28416, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 28420, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 28424, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28432, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 28436, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 28452, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `04` (`13411` words): `libcrux_ml_kem` `libcrux_ml_kem::ind_cca::incremental::neon::decapsulate_compressed_key::<3, 1152, 2400, 1152, 1184, 1088, 1152, 960, 128, 10, 4, 320, 2, 128, 2, 128, 1120>`. -/
@[expose] def mlkemBlk04Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 36092 53644

@[expose] def mlkemBlk04 : CodeBlock where
  code := mlkemBlk04Bytes
  align := 4
  symbols := [("libcrux_ml_kem::ind_cca::incremental::neon::decapsulate_compressed_key::<3, 1152, 2400, 1152, 1184, 1088, 1152, 960, 128, 10, 4, 320, 2, 128, 2, 128, 1120>", 0)]
  relocs := [
    { off := 132, kind := .call26, sym := "memcpy" },
    { off := 196, kind := .call26, sym := "memcpy" },
    { off := 228, kind := .call26, sym := "memset" },
    { off := 236, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 244, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 500, kind := .call26, sym := "memcpy" },
    { off := 752, kind := .call26, sym := "memcpy" },
    { off := 1012, kind := .call26, sym := "memcpy" },
    { off := 1032, kind := .call26, sym := "memset" },
    { off := 1840, kind := .call26, sym := "memcpy" },
    { off := 5216, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 5220, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 5432, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 5436, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 6272, kind := .call26, sym := "memcpy" },
    { off := 6448, kind := .call26, sym := "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_4" },
    { off := 6584, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 6588, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 7868, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 7872, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 8080, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 8084, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 14432, kind := .call26, sym := "memcpy" },
    { off := 14636, kind := .call26, sym := "memcpy" },
    { off := 14660, kind := .call26, sym := "memcpy" },
    { off := 14676, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.4" },
    { off := 14680, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.5" },
    { off := 14692, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.4" },
    { off := 14696, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.5" },
    { off := 15400, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" },
    { off := 15448, kind := .call26, sym := "memset" },
    { off := 15488, kind := .call26, sym := "memcpy" },
    { off := 15556, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 15592, kind := .call26, sym := "memset" },
    { off := 15884, kind := .call26, sym := "memcpy" },
    { off := 16172, kind := .call26, sym := "memcpy" },
    { off := 16456, kind := .call26, sym := "memcpy" },
    { off := 16476, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 16480, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 16556, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 16560, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 16568, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 16572, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 16580, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 16588, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 17292, kind := .call26, sym := "memset" },
    { off := 28976, kind := .call26, sym := "memcpy" },
    { off := 28996, kind := .call26, sym := "memset" },
    { off := 29056, kind := .call26, sym := "memset" },
    { off := 29288, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 29348, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 29624, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 29628, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 29684, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 29688, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 34288, kind := .call26, sym := "memset" },
    { off := 34532, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 34592, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 35432, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 36092, kind := .call26, sym := "memset" },
    { off := 36144, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 36148, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 37056, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 37060, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 37220, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 37224, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 43364, kind := .call26, sym := "memcpy" },
    { off := 43480, kind := .call26, sym := "memcpy" },
    { off := 43504, kind := .call26, sym := "memcpy" },
    { off := 43524, kind := .call26, sym := "memcpy" },
    { off := 43928, kind := .call26, sym := "memcpy" },
    { off := 43948, kind := .call26, sym := "memcpy" },
    { off := 43988, kind := .call26, sym := "memcpy" },
    { off := 44044, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 44064, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 45080, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 45084, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 46412, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 46416, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 46620, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 46624, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 52972, kind := .call26, sym := "memcpy" },
    { off := 53212, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.7" },
    { off := 53224, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.7" },
    { off := 53472, kind := .call26, sym := "memcpy" },
    { off := 53512, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time" },
    { off := 53568, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 53572, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 53576, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 53580, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 53584, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 53588, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 53592, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 53596, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 53600, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 53604, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 53608, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 53612, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 53620, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 53624, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 53640, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `05` (`7112` words): `libcrux_ml_kem` `libcrux_ml_kem::ind_cca::incremental::neon::generate_keypair_compressed::<3, 1152, 1152, 2400, 1184, 1152, 2, 128, 2400>`. -/
@[expose] def mlkemBlk05Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 89736 28448

@[expose] def mlkemBlk05 : CodeBlock where
  code := mlkemBlk05Bytes
  align := 4
  symbols := [("libcrux_ml_kem::ind_cca::incremental::neon::generate_keypair_compressed::<3, 1152, 1152, 2400, 1184, 1152, 2, 128, 2400>", 0)]
  relocs := [
    { off := 264, kind := .call26, sym := "memset" },
    { off := 300, kind := .call26, sym := "memcpy" },
    { off := 340, kind := .call26, sym := "memset" },
    { off := 368, kind := .call26, sym := "memcpy" },
    { off := 400, kind := .call26, sym := "memcpy" },
    { off := 420, kind := .call26, sym := "memcpy" },
    { off := 528, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" },
    { off := 600, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 620, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 624, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 628, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 644, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 648, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 660, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 668, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 728, kind := .call26, sym := "memset" },
    { off := 13188, kind := .call26, sym := "memcpy" },
    { off := 13212, kind := .call26, sym := "memcpy" },
    { off := 13236, kind := .call26, sym := "memcpy" },
    { off := 13284, kind := .call26, sym := "memcpy" },
    { off := 13308, kind := .call26, sym := "memcpy" },
    { off := 13332, kind := .call26, sym := "memcpy" },
    { off := 13380, kind := .call26, sym := "memcpy" },
    { off := 13404, kind := .call26, sym := "memcpy" },
    { off := 13428, kind := .call26, sym := "memcpy" },
    { off := 13668, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 13728, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 13868, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 13872, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 13976, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 13980, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 18660, kind := .call26, sym := "memset" },
    { off := 18884, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 18944, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 19084, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 19088, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 19112, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 19116, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 23680, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 23684, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 24880, kind := .call26, sym := "memcpy" },
    { off := 24896, kind := .call26, sym := "memcpy" },
    { off := 24916, kind := .call26, sym := "memcpy" },
    { off := 24932, kind := .call26, sym := "memcpy" },
    { off := 24948, kind := .call26, sym := "memcpy" },
    { off := 24968, kind := .call26, sym := "memcpy" },
    { off := 24984, kind := .call26, sym := "memcpy" },
    { off := 25000, kind := .call26, sym := "memcpy" },
    { off := 25020, kind := .call26, sym := "memcpy" },
    { off := 25040, kind := .call26, sym := "memcpy" },
    { off := 25064, kind := .call26, sym := "memset" },
    { off := 25372, kind := .call26, sym := "memcpy" },
    { off := 25396, kind := .call26, sym := "memcpy" },
    { off := 25692, kind := .call26, sym := "memcpy" },
    { off := 25720, kind := .call26, sym := "memcpy" },
    { off := 25984, kind := .call26, sym := "memcpy" },
    { off := 26012, kind := .call26, sym := "memcpy" },
    { off := 26060, kind := .call26, sym := "memcpy" },
    { off := 26108, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 26164, kind := .call26, sym := "memcpy" },
    { off := 26216, kind := .call26, sym := "memset" },
    { off := 26524, kind := .call26, sym := "memcpy" },
    { off := 26548, kind := .call26, sym := "memcpy" },
    { off := 26860, kind := .call26, sym := "memcpy" },
    { off := 26888, kind := .call26, sym := "memcpy" },
    { off := 27196, kind := .call26, sym := "memcpy" },
    { off := 27224, kind := .call26, sym := "memcpy" },
    { off := 27252, kind := .call26, sym := "memcpy" },
    { off := 27604, kind := .call26, sym := "memcpy" },
    { off := 27624, kind := .call26, sym := "memcpy" },
    { off := 27936, kind := .call26, sym := "memcpy" },
    { off := 27956, kind := .call26, sym := "memcpy" },
    { off := 28260, kind := .call26, sym := "memcpy" },
    { off := 28280, kind := .call26, sym := "memcpy" },
    { off := 28300, kind := .call26, sym := "memcpy" },
    { off := 28400, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 28404, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 28408, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28412, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 28416, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 28420, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28424, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 28428, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 28432, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 28436, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 28440, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 28444, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" }]

/-- Block `06` (`13979` words): `libcrux_ml_kem` `libcrux_ml_kem::ind_cca::instantiations::neon::kyber_decapsulate::<4, 3168, 1536, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128, 1600>`. -/
@[expose] def mlkemBlk06Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 118184 55916

@[expose] def mlkemBlk06 : CodeBlock where
  code := mlkemBlk06Bytes
  align := 4
  symbols := [("libcrux_ml_kem::ind_cca::instantiations::neon::kyber_decapsulate::<4, 3168, 1536, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128, 1600>", 0)]
  relocs := [
    { off := 148, kind := .call26, sym := "memset" },
    { off := 156, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 164, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 420, kind := .call26, sym := "memcpy" },
    { off := 672, kind := .call26, sym := "memcpy" },
    { off := 932, kind := .call26, sym := "memcpy" },
    { off := 1192, kind := .call26, sym := "memcpy" },
    { off := 1212, kind := .call26, sym := "memset" },
    { off := 1668, kind := .call26, sym := "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_11" },
    { off := 1796, kind := .call26, sym := "memcpy" },
    { off := 5172, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 5176, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 5392, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 5396, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 6228, kind := .call26, sym := "memcpy" },
    { off := 6404, kind := .call26, sym := "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_5" },
    { off := 6536, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 6540, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 7820, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 7824, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 8032, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 8036, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 14384, kind := .call26, sym := "memcpy" },
    { off := 14588, kind := .call26, sym := "memcpy" },
    { off := 14612, kind := .call26, sym := "memcpy" },
    { off := 14628, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.4" },
    { off := 14632, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.5" },
    { off := 14644, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.4" },
    { off := 14648, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.5" },
    { off := 15220, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" },
    { off := 15268, kind := .call26, sym := "memset" },
    { off := 15304, kind := .call26, sym := "memcpy" },
    { off := 15380, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 15412, kind := .call26, sym := "memset" },
    { off := 15704, kind := .call26, sym := "memcpy" },
    { off := 15996, kind := .call26, sym := "memcpy" },
    { off := 16288, kind := .call26, sym := "memcpy" },
    { off := 16576, kind := .call26, sym := "memcpy" },
    { off := 16624, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 16640, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 16648, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 16652, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 16684, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 16688, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 16696, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 16700, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.8" },
    { off := 16708, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 16716, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.8" },
    { off := 16784, kind := .call26, sym := "memset" },
    { off := 18752, kind := .call26, sym := "memset" },
    { off := 30040, kind := .call26, sym := "memcpy" },
    { off := 30064, kind := .call26, sym := "memcpy" },
    { off := 30088, kind := .call26, sym := "memcpy" },
    { off := 30132, kind := .call26, sym := "memcpy" },
    { off := 30156, kind := .call26, sym := "memcpy" },
    { off := 30180, kind := .call26, sym := "memcpy" },
    { off := 30232, kind := .call26, sym := "memcpy" },
    { off := 30256, kind := .call26, sym := "memcpy" },
    { off := 30280, kind := .call26, sym := "memcpy" },
    { off := 30316, kind := .call26, sym := "memcpy" },
    { off := 30340, kind := .call26, sym := "memcpy" },
    { off := 30364, kind := .call26, sym := "memcpy" },
    { off := 30408, kind := .call26, sym := "memcpy" },
    { off := 30428, kind := .call26, sym := "memset" },
    { off := 30484, kind := .call26, sym := "memset" },
    { off := 30760, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 30820, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 31096, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 31100, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 31156, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 31160, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 35824, kind := .call26, sym := "memset" },
    { off := 36112, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 36180, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 37100, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 37756, kind := .call26, sym := "memset" },
    { off := 37808, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 37812, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 38724, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 38728, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 38888, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 38892, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 45028, kind := .call26, sym := "memcpy" },
    { off := 45140, kind := .call26, sym := "memcpy" },
    { off := 45164, kind := .call26, sym := "memcpy" },
    { off := 45192, kind := .call26, sym := "memcpy" },
    { off := 45768, kind := .call26, sym := "memcpy" },
    { off := 45788, kind := .call26, sym := "memcpy" },
    { off := 45828, kind := .call26, sym := "memcpy" },
    { off := 45884, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 45904, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 46896, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 46900, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 48248, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 48252, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 48456, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 48460, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 54808, kind := .call26, sym := "memcpy" },
    { off := 55448, kind := .call26, sym := "memcpy" },
    { off := 55512, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 55600, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 55664, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 55740, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 55784, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time" },
    { off := 55840, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 55844, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 55848, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 55852, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 55856, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 55860, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 55864, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 55868, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 55872, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 55876, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 55880, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 55884, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 55892, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 55896, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 55912, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `07` (`10252` words): `libcrux_ml_kem` `libcrux_ml_kem::ind_cca::instantiations::neon::kyber_encapsulate::<4, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128>`. -/
@[expose] def mlkemBlk07Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 174100 41008

@[expose] def mlkemBlk07 : CodeBlock where
  code := mlkemBlk07Bytes
  align := 4
  symbols := [("libcrux_ml_kem::ind_cca::instantiations::neon::kyber_encapsulate::<4, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128>", 0)]
  relocs := [
    { off := 168, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 548, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 636, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" },
    { off := 700, kind := .call26, sym := "memset" },
    { off := 848, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 852, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 984, kind := .call26, sym := "memcpy" },
    { off := 1268, kind := .call26, sym := "memcpy" },
    { off := 1552, kind := .call26, sym := "memcpy" },
    { off := 1832, kind := .call26, sym := "memcpy" },
    { off := 1880, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 1888, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 1912, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 1916, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" },
    { off := 1936, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.0" },
    { off := 1940, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 1952, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.1" },
    { off := 1956, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.8" },
    { off := 1964, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.2" },
    { off := 1972, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.8" },
    { off := 2036, kind := .call26, sym := "memset" },
    { off := 4004, kind := .call26, sym := "memset" },
    { off := 15292, kind := .call26, sym := "memcpy" },
    { off := 15316, kind := .call26, sym := "memcpy" },
    { off := 15340, kind := .call26, sym := "memcpy" },
    { off := 15384, kind := .call26, sym := "memcpy" },
    { off := 15408, kind := .call26, sym := "memcpy" },
    { off := 15432, kind := .call26, sym := "memcpy" },
    { off := 15484, kind := .call26, sym := "memcpy" },
    { off := 15508, kind := .call26, sym := "memcpy" },
    { off := 15532, kind := .call26, sym := "memcpy" },
    { off := 15568, kind := .call26, sym := "memcpy" },
    { off := 15592, kind := .call26, sym := "memcpy" },
    { off := 15616, kind := .call26, sym := "memcpy" },
    { off := 15656, kind := .call26, sym := "memcpy" },
    { off := 15676, kind := .call26, sym := "memset" },
    { off := 15732, kind := .call26, sym := "memset" },
    { off := 16008, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 16068, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 16344, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 16348, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 66 },
    { off := 16404, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 16408, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 21072, kind := .call26, sym := "memset" },
    { off := 21360, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 21428, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 22332, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 22988, kind := .call26, sym := "memset" },
    { off := 23036, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 23040, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 23952, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 23956, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 24116, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 24120, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 30256, kind := .call26, sym := "memcpy" },
    { off := 30368, kind := .call26, sym := "memcpy" },
    { off := 30392, kind := .call26, sym := "memcpy" },
    { off := 30420, kind := .call26, sym := "memcpy" },
    { off := 30996, kind := .call26, sym := "memcpy" },
    { off := 31016, kind := .call26, sym := "memcpy" },
    { off := 31056, kind := .call26, sym := "memcpy" },
    { off := 31112, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 31132, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 32152, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 32156, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 33484, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 33488, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 33692, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 33696, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 40044, kind := .call26, sym := "memcpy" },
    { off := 40692, kind := .call26, sym := "memcpy" },
    { off := 40716, kind := .call26, sym := "memcpy" },
    { off := 40776, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 40860, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" },
    { off := 40932, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 40936, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 40940, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 40944, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 40948, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 40952, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 40956, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 40960, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 40964, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 40968, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 40972, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 40976, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 40984, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 40988, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" },
    { off := 41004, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `08` (`264` words): `libcrux_ml_kem` `<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t>>::squeeze2::<136>`. -/
@[expose] def mlkemBlk08Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 215108 1056

@[expose] def mlkemBlk08 : CodeBlock where
  code := mlkemBlk08Bytes
  align := 4
  symbols := [("<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t>>::squeeze2::<136>", 0)]
  relocs := [
    { off := 476, kind := .call26, sym := "memcpy" },
    { off := 572, kind := .call26, sym := "memcpy" },
    { off := 596, kind := .call26, sym := "memcpy" },
    { off := 632, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 636, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 648, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 660, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 664, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 676, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 688, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 692, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 696, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 700, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.15" },
    { off := 704, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.15" },
    { off := 716, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 720, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.14" },
    { off := 724, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.14" },
    { off := 740, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 744, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.13" },
    { off := 748, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.13" },
    { off := 760, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 764, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.12" },
    { off := 768, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.12" },
    { off := 784, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 796, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 800, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 812, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 824, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 828, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 832, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 844, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 848, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 860, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 872, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 876, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 880, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 892, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 896, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 908, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 920, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 924, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 928, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 940, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 944, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 956, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 968, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 972, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 976, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 988, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 992, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 1004, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 1016, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 1020, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" },
    { off := 1024, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 1036, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 1040, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" },
    { off := 1052, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `09` (`179` words): `libcrux_ml_kem` `<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Absorb<2>>::load_block::<136>`. -/
@[expose] def mlkemBlk09Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 216164 716

@[expose] def mlkemBlk09 : CodeBlock where
  code := mlkemBlk09Bytes
  align := 4
  symbols := [("<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Absorb<2>>::load_block::<136>", 0)]
  relocs := [
    { off := 528, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 532, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 544, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 552, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 556, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 568, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 580, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 584, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 596, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 608, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 612, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 624, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 632, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 636, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" },
    { off := 648, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 656, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 660, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" },
    { off := 672, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 676, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.9" },
    { off := 680, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.9" },
    { off := 692, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 696, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.8" },
    { off := 700, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.8" },
    { off := 712, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `10` (`24` words): `libcrux_ml_kem` `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed`. -/
@[expose] def mlkemBlk10Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 216880 96

@[expose] def mlkemBlk10 : CodeBlock where
  code := mlkemBlk10Bytes
  align := 4
  symbols := [("<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed", 0)]
  relocs := [
    { off := 44, kind := .call26, sym := "memset" },
    { off := 56, kind := .call26, sym := "libcrux_ml_kem::ind_cca::incremental::neon::generate_keypair_compressed::<3, 1152, 1152, 2400, 1184, 1152, 2, 128, 2400>" },
    { off := 72, kind := .call26, sym := "memcpy" }]

/-- Block `11` (`202` words): `libcrux_ml_kem` `<libcrux_ml_kem::ind_cca::incremental::types::EncapsState<3, libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector>>::to_bytes`. -/
@[expose] def mlkemBlk11Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 216976 808

@[expose] def mlkemBlk11 : CodeBlock where
  code := mlkemBlk11Bytes
  align := 4
  symbols := [("<libcrux_ml_kem::ind_cca::incremental::types::EncapsState<3, libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector>>::to_bytes", 0)]
  relocs := []

/-- Block `12` (`11` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::is_non_zero`. -/
@[expose] def mlkemBlk12Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 217784 44

@[expose] def mlkemBlk12 : CodeBlock where
  code := mlkemBlk12Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::is_non_zero", 0)]
  relocs := [
    { off := 12, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::inz" }]

/-- Block `13` (`10` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::compare_ciphertexts_in_constant_time`. -/
@[expose] def mlkemBlk13Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 217828 40

@[expose] def mlkemBlk13 : CodeBlock where
  code := mlkemBlk13Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::compare_ciphertexts_in_constant_time", 0)]
  relocs := [
    { off := 12, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::compare" }]

/-- Block `14` (`8` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::select_shared_secret_in_constant_time`. -/
@[expose] def mlkemBlk14Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 217868 32

@[expose] def mlkemBlk14 : CodeBlock where
  code := mlkemBlk14Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::select_shared_secret_in_constant_time", 0)]
  relocs := [
    { off := 16, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::select_ct" }]

/-- Block `15` (`4` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::inz`. -/
@[expose] def mlkemBlk15Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 217900 16

@[expose] def mlkemBlk15 : CodeBlock where
  code := mlkemBlk15Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::inz", 0)]
  relocs := []

/-- Block `16` (`21` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time`. -/
@[expose] def mlkemBlk16Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 217916 84

@[expose] def mlkemBlk16 : CodeBlock where
  code := mlkemBlk16Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time", 0)]
  relocs := [
    { off := 44, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::compare_ciphertexts_in_constant_time" },
    { off := 80, kind := .jump26, sym := "libcrux_ml_kem::constant_time_ops::select_shared_secret_in_constant_time" }]

/-- Block `17` (`20` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::compare`. -/
@[expose] def mlkemBlk17Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 218000 80

@[expose] def mlkemBlk17 : CodeBlock where
  code := mlkemBlk17Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::compare", 0)]
  relocs := [
    { off := 56, kind := .jump26, sym := "libcrux_ml_kem::constant_time_ops::is_non_zero" },
    { off := 60, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.32" },
    { off := 64, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.32" },
    { off := 76, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `18` (`433` words): `libcrux_ml_kem` `libcrux_ml_kem::constant_time_ops::select_ct`. -/
@[expose] def mlkemBlk18Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 218080 1732

@[expose] def mlkemBlk18 : CodeBlock where
  code := mlkemBlk18Bytes
  align := 4
  symbols := [("libcrux_ml_kem::constant_time_ops::select_ct", 0)]
  relocs := [
    { off := 36, kind := .call26, sym := "libcrux_ml_kem::constant_time_ops::is_non_zero" },
    { off := 1096, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1100, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1108, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1116, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1120, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1128, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1136, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1140, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1148, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1156, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1160, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1168, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1176, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1180, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1188, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1196, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1200, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1208, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1216, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1220, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1228, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1236, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1240, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1248, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1256, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1260, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1268, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1276, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1280, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1288, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1296, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1300, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1308, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1316, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1320, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1328, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1336, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1340, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1348, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1356, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1360, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1368, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1376, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1380, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1388, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1396, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1400, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1408, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1416, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1420, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1428, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1436, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1440, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1448, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1456, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1460, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1468, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1476, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1480, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1488, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1496, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1500, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1508, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1516, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1520, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1528, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1536, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1540, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1548, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1556, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1560, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1568, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1576, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1580, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1588, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1596, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1600, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1608, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1616, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1620, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1628, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1636, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1640, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1648, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1656, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1660, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1668, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1676, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1680, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1688, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1696, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1700, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1708, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" },
    { off := 1716, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1720, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" },
    { off := 1728, kind := .call26, sym := "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" }]

/-- Block `19` (`28` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem768::incremental::encapsulate1`. -/
@[expose] def mlkemBlk19Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 219812 112

@[expose] def mlkemBlk19 : CodeBlock where
  code := mlkemBlk19Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem768::incremental::encapsulate1", 0)]
  relocs := [
    { off := 96, kind := .call26, sym := "libcrux_ml_kem::ind_cca::incremental::neon::encapsulate1_serialized::<3, 1088, 960, 10, 320, 2, 128, 2, 128>" }]

/-- Block `20` (`2769` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem768::incremental::encapsulate2`. -/
@[expose] def mlkemBlk20Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 219924 11076

@[expose] def mlkemBlk20 : CodeBlock where
  code := mlkemBlk20Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem768::incremental::encapsulate2", 0)]
  relocs := [
    { off := 52, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 68, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 1308, kind := .call26, sym := "memcpy" },
    { off := 1552, kind := .call26, sym := "memcpy" },
    { off := 1804, kind := .call26, sym := "memcpy" },
    { off := 1816, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 1820, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.6" },
    { off := 2560, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 2564, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 134 },
    { off := 3936, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 3940, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 254 },
    { off := 4144, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 4148, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0", addend := 126 },
    { off := 10472, kind := .call26, sym := "memcpy" },
    { off := 10708, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.7" },
    { off := 10716, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.7" },
    { off := 11028, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 11032, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" },
    { off := 11036, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 11040, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 11044, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" },
    { off := 11048, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 11052, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 11056, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" },
    { off := 11060, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" },
    { off := 11064, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 11068, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" },
    { off := 11072, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" }]

/-- Block `21` (`530` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`. -/
@[expose] def mlkemBlk21Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 231000 2120

@[expose] def mlkemBlk21 : CodeBlock where
  code := mlkemBlk21Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes", 0)]
  relocs := [
    { off := 72, kind := .call26, sym := "memcpy" },
    { off := 136, kind := .call26, sym := "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" },
    { off := 184, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 196, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" },
    { off := 588, kind := .call26, sym := "memcpy" },
    { off := 864, kind := .call26, sym := "memcpy" },
    { off := 1076, kind := .call26, sym := "memcpy" },
    { off := 1096, kind := .call26, sym := "memset" },
    { off := 1400, kind := .call26, sym := "memcpy" },
    { off := 1416, kind := .call26, sym := "memcpy" },
    { off := 1716, kind := .call26, sym := "memcpy" },
    { off := 1732, kind := .call26, sym := "memcpy" },
    { off := 2024, kind := .call26, sym := "memcpy" },
    { off := 2044, kind := .call26, sym := "memcpy" },
    { off := 2072, kind := .call26, sym := "bcmp" }]

/-- Block `22` (`5` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`. -/
@[expose] def mlkemBlk22Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233120 20

@[expose] def mlkemBlk22 : CodeBlock where
  code := mlkemBlk22Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key", 0)]
  relocs := [
    { off := 16, kind := .jump26, sym := "libcrux_ml_kem::ind_cca::incremental::neon::decapsulate_compressed_key::<3, 1152, 2400, 1152, 1184, 1088, 1152, 960, 128, 10, 4, 320, 2, 128, 2, 128, 1120>" }]

/-- Block `23` (`4` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem1024::kyber::decapsulate`. -/
@[expose] def mlkemBlk23Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233140 16

@[expose] def mlkemBlk23 : CodeBlock where
  code := mlkemBlk23Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem1024::kyber::decapsulate", 0)]
  relocs := [
    { off := 12, kind := .jump26, sym := "libcrux_ml_kem::ind_cca::instantiations::neon::kyber_decapsulate::<4, 3168, 1536, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128, 1600>" }]

/-- Block `24` (`4` words): `libcrux_ml_kem` `libcrux_ml_kem::mlkem1024::kyber::encapsulate`. -/
@[expose] def mlkemBlk24Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233156 16

@[expose] def mlkemBlk24 : CodeBlock where
  code := mlkemBlk24Bytes
  align := 4
  symbols := [("libcrux_ml_kem::mlkem1024::kyber::encapsulate", 0)]
  relocs := [
    { off := 12, kind := .jump26, sym := "libcrux_ml_kem::ind_cca::instantiations::neon::kyber_encapsulate::<4, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128>" }]

/-- Block `25` (`59` words): `libcrux_ml_kem` `<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_4`. -/
@[expose] def mlkemBlk25Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233172 236

@[expose] def mlkemBlk25 : CodeBlock where
  code := mlkemBlk25Bytes
  align := 4
  symbols := [("<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_4", 0)]
  relocs := [
    { off := 196, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.87" },
    { off := 200, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.87" },
    { off := 212, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 216, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.88" },
    { off := 220, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.88" },
    { off := 232, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `26` (`69` words): `libcrux_ml_kem` `<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_5`. -/
@[expose] def mlkemBlk26Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233408 276

@[expose] def mlkemBlk26 : CodeBlock where
  code := mlkemBlk26Bytes
  align := 4
  symbols := [("<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_5", 0)]
  relocs := [
    { off := 236, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.89" },
    { off := 240, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.89" },
    { off := 252, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 256, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.90" },
    { off := 260, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.90" },
    { off := 272, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `27` (`91` words): `libcrux_ml_kem` `<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_11`. -/
@[expose] def mlkemBlk27Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 233684 364

@[expose] def mlkemBlk27 : CodeBlock where
  code := mlkemBlk27Bytes
  align := 4
  symbols := [("<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_11", 0)]
  relocs := [
    { off := 324, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.93" },
    { off := 328, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.93" },
    { off := 340, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" },
    { off := 344, kind := .adrpHi21, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.94" },
    { off := 348, kind := .addLo12, sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.94" },
    { off := 360, kind := .call26, sym := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" }]

/-- Block `28` (`99` words): stock `musl` `1.2.5` `memcpy`. -/
@[expose] def mlkemBlk28Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 234048 396

@[expose] def mlkemBlk28 : CodeBlock where
  code := mlkemBlk28Bytes
  align := 4
  symbols := [("memcpy", 0)]
  relocs := []

/-- Block `29` (`65` words): stock `musl` `1.2.5` `memset`. -/
@[expose] def mlkemBlk29Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 234444 260

@[expose] def mlkemBlk29 : CodeBlock where
  code := mlkemBlk29Bytes
  align := 4
  symbols := [("memset", 0)]
  relocs := []

/-- Block `30` (`1` word): stock `musl` `1.2.5` `bcmp` tail-call wrapper. -/
@[expose] def mlkemBlk30Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 234704 4

@[expose] def mlkemBlk30 : CodeBlock where
  code := mlkemBlk30Bytes
  align := 4
  symbols := [("bcmp", 0)]
  relocs := [
    { off := 0, kind := .jump26, sym := "memcmp" }]

/-- Block `31` (`13` words): stock `musl` `1.2.5` `memcmp`. -/
@[expose] def mlkemBlk31Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 234708 52

@[expose] def mlkemBlk31 : CodeBlock where
  code := mlkemBlk31Bytes
  align := 4
  symbols := [("memcmp", 0)]
  relocs := []

/-! ## 2. Read-Only `.rodata` Constants (`mlkemData00`..`mlkemData10`) -/

/-- Data `00` (`256` bytes, align `2`): `ZETA_TABLE` (128 little-endian `i16` Montgomery-form powers of `ζ = 17` mod `3329`). -/
@[expose] def mlkemData00Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 234760 256

@[expose] def mlkemData00 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"
  align := 2
  readOnly := true
  bytes := mlkemData00Bytes
  relocs := []

/-- Data `01` (`192` bytes, align `8`): `KECCAK_RC` (24 little-endian `u64` Keccak-f[1600] round constants). -/
@[expose] def mlkemData01Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235016 192

@[expose] def mlkemData01 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29"
  align := 8
  readOnly := true
  bytes := mlkemData01Bytes
  relocs := []

/-- Data `02` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #0 (`0xff0000ffffffffffffffffffffffffff`). -/
@[expose] def mlkemData02Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235208 16

@[expose] def mlkemData02 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.0"
  align := 16
  readOnly := true
  bytes := mlkemData02Bytes
  relocs := []

/-- Data `03` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #1 (`0x00011f00000000000000000000000000`). -/
@[expose] def mlkemData03Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235224 16

@[expose] def mlkemData03 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.1"
  align := 16
  readOnly := true
  bytes := mlkemData03Bytes
  relocs := []

/-- Data `04` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #2 (`0x00021f00000000000000000000000000`). -/
@[expose] def mlkemData04Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235240 16

@[expose] def mlkemData04 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.2"
  align := 16
  readOnly := true
  bytes := mlkemData04Bytes
  relocs := []

/-- Data `05` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #3 (`0x000101020304040506070708090a0a0b`). -/
@[expose] def mlkemData05Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235256 16

@[expose] def mlkemData05 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.3"
  align := 16
  readOnly := true
  bytes := mlkemData05Bytes
  relocs := []

/-- Data `06` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #4 (`0xf1fff2fff3fff4fff5fff6fff7fff8ff`). -/
@[expose] def mlkemData06Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235272 16

@[expose] def mlkemData06 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.4"
  align := 16
  readOnly := true
  bytes := mlkemData06Bytes
  relocs := []

/-- Data `07` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #5 (`0x01000200040008001000200040008000`). -/
@[expose] def mlkemData07Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235288 16

@[expose] def mlkemData07 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.5"
  align := 16
  readOnly := true
  bytes := mlkemData07Bytes
  relocs := []

/-- Data `08` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #6 (`0x0000ff00fefffdfffcfffbfffafff9ff`). -/
@[expose] def mlkemData08Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235304 16

@[expose] def mlkemData08 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.6"
  align := 16
  readOnly := true
  bytes := mlkemData08Bytes
  relocs := []

/-- Data `09` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #7 (`0x0000040008000c000000040008000c00`). -/
@[expose] def mlkemData09Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235320 16

@[expose] def mlkemData09 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.7"
  align := 16
  readOnly := true
  bytes := mlkemData09Bytes
  relocs := []

/-- Data `10` (`16` bytes, align `16`): 16-byte SIMD `.rodata.cst16` constant #8 (`0x00031f00000000000000000000000000`). -/
@[expose] def mlkemData10Bytes : List (BitVec 8) :=
  include_bytes% "MlKemPlacedObj.bin" 235336 16

@[expose] def mlkemData10 : SymDataInfo where
  sym := "libcrux_ml_kem:.rodata.cst16.8"
  align := 16
  readOnly := true
  bytes := mlkemData10Bytes
  relocs := []

@[expose] def mlkemBlocks : List CodeBlock :=
  [mlkemBlk00, mlkemBlk01, mlkemBlk02, mlkemBlk03, mlkemBlk04, mlkemBlk05, mlkemBlk06, mlkemBlk07, mlkemBlk08, mlkemBlk09, mlkemBlk10, mlkemBlk11, mlkemBlk12, mlkemBlk13, mlkemBlk14, mlkemBlk15, mlkemBlk16, mlkemBlk17, mlkemBlk18, mlkemBlk19, mlkemBlk20, mlkemBlk21, mlkemBlk22, mlkemBlk23, mlkemBlk24, mlkemBlk25, mlkemBlk26, mlkemBlk27, mlkemBlk28, mlkemBlk29, mlkemBlk30, mlkemBlk31]

@[expose] def mlkemData : List SymDataInfo :=
  [mlkemData00, mlkemData01, mlkemData02, mlkemData03, mlkemData04, mlkemData05, mlkemData06, mlkemData07, mlkemData08, mlkemData09, mlkemData10]

@[expose] def mlkemExports : List String := [
  "libcrux_ml_kem::mlkem1024::kyber::encapsulate",
  "libcrux_ml_kem::mlkem1024::kyber::decapsulate",
  "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed",
  "libcrux_ml_kem::mlkem768::incremental::encapsulate1",
  "libcrux_ml_kem::mlkem768::incremental::encapsulate2",
  "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key",
  "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes",
  "memcpy",
  "memset",
  "bcmp",
  "memcmp"]

@[expose] def mlkemExportSyms : List (String × String) := [
  ("libcrux_ml_kem::mlkem1024::kyber::encapsulate", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"),
  ("libcrux_ml_kem::mlkem1024::kyber::decapsulate", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"),
  ("<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed", "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"),
  ("libcrux_ml_kem::mlkem768::incremental::encapsulate1", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"),
  ("libcrux_ml_kem::mlkem768::incremental::encapsulate2", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2"),
  ("libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"),
  ("libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes", "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes")]

/-- Multi-block placed library for all 7 `libcrux_ml_kem` `0.0.10` CLI hooks
    (PQXDH Round-3 CRYSTALS-Kyber-1024 + SPQR V1 incremental ML-KEM-768)
    together with stock `musl` `1.2.5` `memcpy`, `memset`, `bcmp`, and `memcmp`. -/
@[expose] def mlkemMultiLib : MultiPlacedLib where
  name := "libcrux_ml_kem_cli"
  blocks := mlkemBlocks
  data := mlkemData
  exports := mlkemExports
  exportSyms := mlkemExportSyms

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
