/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# `mlkemMultiLib` Placement, `Placeable`, Symbol Resolution, and Hull Facts

Defines the concrete zero-hook stock-ELF `Obj.MultiPlacement` (`c2MlkemMpl`) for the 32 code blocks
(28 `libcrux_ml_kem`/`libcrux_sha3` blocks in `.text.lib2` and 4 `musl`
`memcpy`/`memset`/`bcmp`/`memcmp` blocks in `.text.b_pre`) and 11 `.rodata` tables of
`mlkemMultiLib`, together with `Placeable`, symbol-resolution equalities for all 7 entry points,
and `.text.b_pre ∪ .text.lib2` hull / `LsRetAddr624` exclusion lemmas.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt c2_keepTextBPre_of_sub_lt c2_noPanic_of_band_sub_lt
   isLinkedPanicAddr_false_of_keepTextBPre)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr keepLib2Text keepLib2Text_sub_rxProg
   keepTextBPre keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BcmpAddr c2Compress256Addr c2Compress256K32Addr c2DurationSinceCst16Addr
   c2FirstExternStubAddr c2Lib2TextHi c2Lib2TextLo c2MemcmpAddr c2StaticSecretDropAddr
   c2TextBPreHi c2TextBPreLo wp4HandleErrorAddr wp4MemcpyRealAddr wp4MemsetRealAddr)

/-! ## 1. Mangled Entrypoint Symbol Constants (7 ML-KEM / Kyber Exports) -/

abbrev lsKyber1024EncapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"

abbrev lsKyber1024DecapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"

abbrev lsMlkem768FromSeedSym : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"

abbrev lsMlkem768Encaps1Sym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"

abbrev lsMlkem768Encaps2Sym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2"

abbrev lsMlkem768DecapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"

abbrev lsMlkem768ValidatePkSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"

/-! ## 2. Entrypoint Addresses and `c2MlkemMpl` (32 Blocks, 11 `.rodata` Tables) -/

@[expose] def c2Mlkem768FromSeedAddr   : BitVec 64 := c2Compress256Addr - 17168#64 -- 0x4b6e34 (B10)
@[expose] def c2Mlkem768Encaps1Addr    : BitVec 64 := c2Compress256Addr - 14236#64 -- 0x4b79a8 (B19)
@[expose] def c2Mlkem768Encaps2Addr    : BitVec 64 := c2Compress256Addr - 14124#64 -- 0x4b7a18 (B20)
@[expose] def c2Mlkem768ValidatePkAddr : BitVec 64 := c2Compress256Addr - 3048#64  -- 0x4ba55c (B21)
@[expose] def c2Mlkem768DecapsAddr     : BitVec 64 := c2Compress256Addr - 928#64   -- 0x4bada4 (B22)
@[expose] def c2Kyber1024DecapsAddr    : BitVec 64 := c2Compress256Addr - 908#64   -- 0x4badb8 (B23)
@[expose] def c2Kyber1024EncapsAddr    : BitVec 64 := c2Compress256Addr - 892#64   -- 0x4badc8 (B24)

/-- Concrete zero-hook stock-ELF `Obj.MultiPlacement` for the 32 blocks and 11 `.rodata` tables of
    `mlkemMultiLib`. -/
@[expose] def c2MlkemMpl : Obj.MultiPlacement where
  base i :=
    match i with
    |  0 => c2StaticSecretDropAddr + 252#64
    |  1 => c2StaticSecretDropAddr + 3104#64
    |  2 => c2StaticSecretDropAddr + 5508#64
    |  3 => c2StaticSecretDropAddr + 7888#64
    |  4 => c2StaticSecretDropAddr + 36344#64
    |  5 => c2StaticSecretDropAddr + 89988#64
    |  6 => c2Compress256Addr - 115880#64
    |  7 => c2Compress256Addr - 59964#64
    |  8 => c2Compress256Addr - 18956#64
    |  9 => c2Compress256Addr - 17900#64
    | 10 => c2Compress256Addr - 17168#64
    | 11 => c2Compress256Addr - 17072#64
    | 12 => c2Compress256Addr - 16264#64
    | 13 => c2Compress256Addr - 16220#64
    | 14 => c2Compress256Addr - 16180#64
    | 15 => c2Compress256Addr - 16148#64
    | 16 => c2Compress256Addr - 16132#64
    | 17 => c2Compress256Addr - 16048#64
    | 18 => c2Compress256Addr - 15968#64
    | 19 => c2Compress256Addr - 14236#64
    | 20 => c2Compress256Addr - 14124#64
    | 21 => c2Compress256Addr - 3048#64
    | 22 => c2Compress256Addr - 928#64
    | 23 => c2Compress256Addr - 908#64
    | 24 => c2Compress256Addr - 892#64
    | 25 => c2Compress256Addr - 876#64
    | 26 => c2Compress256Addr - 640#64
    | 27 => c2Compress256Addr - 364#64
    | 28 => wp4MemcpyRealAddr
    | 29 => wp4MemsetRealAddr
    | 30 => c2BcmpAddr
    | 31 => c2MemcmpAddr
    | _  => 0#64
  ρ sym :=
    if sym == "libcrux_ml_kem:.rodata.cst16.6" then
      c2DurationSinceCst16Addr - 80#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.4" then
      c2DurationSinceCst16Addr - 64#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.1" then
      c2DurationSinceCst16Addr - 48#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.8" then
      c2DurationSinceCst16Addr - 32#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.7" then
      c2DurationSinceCst16Addr - 16#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.3" then
      c2DurationSinceCst16Addr + 16#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.5" then
      c2DurationSinceCst16Addr + 32#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.0" then
      c2DurationSinceCst16Addr + 64#64
    else if sym == "libcrux_ml_kem:.rodata.cst16.2" then
      c2DurationSinceCst16Addr + 80#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0" then
      c2Compress256K32Addr - 1024#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" then
      c2Compress256K32Addr - 480#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.5" then
      c2Compress256K32Addr - 768#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.8" then
      c2Compress256K32Addr - 744#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.9" then
      c2Compress256K32Addr - 720#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.10" then
      c2Compress256K32Addr - 696#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.11" then
      c2Compress256K32Addr - 672#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.12" then
      c2Compress256K32Addr - 648#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.13" then
      c2Compress256K32Addr - 624#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.14" then
      c2Compress256K32Addr - 600#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.15" then
      c2Compress256K32Addr - 576#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.16" then
      c2Compress256K32Addr - 552#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.17" then
      c2Compress256K32Addr - 528#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.18" then
      c2Compress256K32Addr - 504#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.32" then
      c2Compress256K32Addr - 288#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.33" then
      c2Compress256K32Addr - 264#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.47" then
      c2Compress256K32Addr - 240#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.48" then
      c2Compress256K32Addr - 216#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.49" then
      c2Compress256K32Addr - 192#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.50" then
      c2Compress256K32Addr - 168#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.87" then
      c2Compress256K32Addr - 144#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.88" then
      c2Compress256K32Addr - 120#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.89" then
      c2Compress256K32Addr - 96#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.90" then
      c2Compress256K32Addr - 72#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.93" then
      c2Compress256K32Addr - 48#64
    else if sym == "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.94" then
      c2Compress256K32Addr - 24#64
    else if sym == "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" then
      0x47a2a4#64
    else if sym == "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" then
      0x47a9c4#64
    else if sym == "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_neg_overflow" then
      0x473a4c#64
    else 0#64

set_option maxRecDepth 8000000 in
/-- Full `Placeable` witness for `mlkemMultiLib` at `c2MlkemMpl`. -/
theorem c2_mlkem_placeable : mlkemMultiLib.Placeable c2MlkemMpl :=
  mlkemMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

/-! ## 3. Entrypoint Symbol Resolution (7 ML-KEM / Kyber Exports) -/

theorem c2_resolve_kyber1024Encaps_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsKyber1024EncapsSym = c2MlkemMpl.base 24 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsKyber1024EncapsSym).trans (by rfl_kernel)

theorem c2_resolve_kyber1024Decaps_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsKyber1024DecapsSym = c2MlkemMpl.base 23 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsKyber1024DecapsSym).trans (by rfl_kernel)

theorem c2_resolve_mlkem768FromSeed_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym = c2MlkemMpl.base 10 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsMlkem768FromSeedSym).trans (by rfl_kernel)

theorem c2_resolve_mlkem768Encaps1_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym = c2MlkemMpl.base 19 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsMlkem768Encaps1Sym).trans (by rfl_kernel)

theorem c2_resolve_mlkem768Encaps2_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkem768Encaps2Sym = c2MlkemMpl.base 20 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsMlkem768Encaps2Sym).trans (by rfl_kernel)

theorem c2_resolve_mlkem768Decaps_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkem768DecapsSym = c2MlkemMpl.base 22 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsMlkem768DecapsSym).trans (by rfl_kernel)

theorem c2_resolve_mlkem768ValidatePk_eq {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsMlkem768ValidatePkSym = c2MlkemMpl.base 21 :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsMlkem768ValidatePkSym).trans (by rfl_kernel)

/-! ## 4. `c2MlkemKeep`, Hull Inclusions (`⊆ keepTextBPre ∪ keepLib2Text`), and `LsRetAddr624` Guard -/

/-- Exposed execute-keep mask covering all 32 blocks of `mlkemMultiLib` under `mpl`
    (transparent companion to `NoSvcLiftBase.mlkemKeep`, which lacks `@[expose]` under `module`). -/
@[expose] def c2MlkemKeep (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  (List.range mlkemMultiLib.blocks.length).any fun k =>
    progKeep (mlkemMultiLib.blockProgram mpl k) a

theorem strip_codeLoaded_c2MlkemKeep {mpl : MultiPlacement} {m : Memory}
    (hcl : mlkemMultiLib.CodeLoaded mpl m) :
    mlkemMultiLib.CodeLoaded mpl (stripExecOutside (c2MlkemKeep mpl) m) := by
  intro k hk
  have hL := hcl k hk
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  let Pk := mlkemMultiLib.blockProgram mpl k
  have hno := hL.no_wrap
  have hsub : Pk.base + BitVec.ofNat 64 i - Pk.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (Pk.base + BitVec.ofNat 64 i - Pk.base).toNat < Pk.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  have hmk : c2MlkemKeep mpl (Pk.base + BitVec.ofNat 64 i) = true := by
    unfold c2MlkemKeep
    rw [List.any_eq_true]
    exact ⟨k, List.mem_range.mpr hk, decide_eq_true hin⟩
  rw [strip_read8, strip_perm_of_keep hmk, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

set_option maxRecDepth 2000000 in
private theorem c2_mlkem_blocks_in_rxRegions :
    ((List.range mlkemMultiLib.blocks.length).all fun j =>
      let b := (c2MlkemMpl.base j).toNat
      let len := (mlkemMultiLib.blockLib j).text.code.length
      Nat.beq (len % 4) 0 &&
      ((Nat.ble c2TextBPreLo.toNat b && Nat.ble (b + len) c2TextBPreHi.toNat) ||
       (Nat.ble 0x47ac2c b && Nat.ble (b + len) 0x4cb070))) = true := by
  rfl_kernel

theorem c2_mlkemKeep_sub_rxRegion {pc : BitVec 64}
    (hk : c2MlkemKeep c2MlkemMpl pc = true) :
    keepTextBPre pc = true ∨ keepLib2Text pc = true := by
  unfold c2MlkemKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hbnd := List.all_eq_true.mp c2_mlkem_blocks_in_rxRegions j hj_mem
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  rcases hbnd with ⟨hal, ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩⟩
  · refine Or.inl ?_
    unfold progKeep at hkp
    rw [decide_eq_true_eq] at hkp
    have hplen : (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length =
        (mlkemMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ hal
    have hbase : (mlkemMultiLib.blockProgram c2MlkemMpl j).base = c2MlkemMpl.base j := rfl
    rw [hbase, hplen] at hkp
    exact c2_keepTextBPre_of_sub_lt hkp hlo hhi
  · refine Or.inr ?_
    unfold progKeep at hkp
    rw [decide_eq_true_eq] at hkp
    have hplen : (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length =
        (mlkemMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ hal
    have hbase : (mlkemMultiLib.blockProgram c2MlkemMpl j).base = c2MlkemMpl.base j := rfl
    rw [hbase, hplen] at hkp
    have hlo' : c2Lib2TextLo.toNat ≤ (c2MlkemMpl.base j).toNat :=
      Nat.le_trans (by decide : c2Lib2TextLo.toNat ≤ 0x47ac2c) hlo
    have hhi' : (c2MlkemMpl.base j).toNat + (mlkemMultiLib.blockLib j).text.code.length ≤
        c2Lib2TextHi.toNat :=
      Nat.le_trans hhi (by decide : 0x4cb070 ≤ c2Lib2TextHi.toNat)
    exact c2_keepLib2Text_of_sub_lt hkp hlo' hhi'

theorem c2_mlkemKeep_noPanic {pc : BitVec 64}
    (hk : c2MlkemKeep c2MlkemMpl pc = true) :
    isLinkedPanicAddr pc = false := by
  unfold c2MlkemKeep at hk
  rw [List.any_eq_true] at hk
  obtain ⟨j, hj_mem, hkp⟩ := hk
  have hbnd := List.all_eq_true.mp c2_mlkem_blocks_in_rxRegions j hj_mem
  dsimp only at hbnd
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hbnd
  unfold progKeep at hkp
  rw [decide_eq_true_eq] at hkp
  rcases hbnd with ⟨hal, ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩⟩
  · have hplen : (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length =
        (mlkemMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ hal
    have hbase : (mlkemMultiLib.blockProgram c2MlkemMpl j).base = c2MlkemMpl.base j := rfl
    rw [hbase, hplen] at hkp
    exact isLinkedPanicAddr_false_of_keepTextBPre (c2_keepTextBPre_of_sub_lt hkp hlo hhi)
  · have hplen : (mlkemMultiLib.blockProgram c2MlkemMpl j).code.length =
        (mlkemMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ hal
    have hbase : (mlkemMultiLib.blockProgram c2MlkemMpl j).base = c2MlkemMpl.base j := rfl
    rw [hbase, hplen] at hkp
    exact c2_noPanic_of_band_sub_lt hkp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlo, hhi⟩)))))
      (Nat.lt_of_le_of_lt hhi (by decide))

theorem c2_mlkemKeep_sub_rxProg {pc : BitVec 64}
    (hk : c2MlkemKeep c2MlkemMpl pc = true) :
    progKeep f3TrialRxProg pc = true := by
  rcases c2_mlkemKeep_sub_rxRegion hk with hpre | hlib2
  · exact keepTextBPre_sub_rxProg hpre
  · exact keepLib2Text_sub_rxProg hlib2

theorem c2_mlkemKeep_lr_false [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    c2MlkemKeep c2MlkemMpl lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  cases hk : c2MlkemKeep c2MlkemMpl lr
  · rfl
  · rcases c2_mlkemKeep_sub_rxRegion hk with hb | hl
    · unfold keepTextBPre at hb
      rw [decide_eq_true_eq] at hb
      have hlo : c2FirstExternStubAddr.toNat ≤ c2TextBPreLo.toNat := by decide
      omega
    · unfold keepLib2Text at hl
      rw [decide_eq_true_eq] at hl
      have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
      omega

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
