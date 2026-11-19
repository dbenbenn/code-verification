/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
public import LibsignalBinary.Proofs.TripleRatchet.Hooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
public import LibsignalBinary.Proofs.SessionRecordMin.Deserialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.Deps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.AesCbc.Bytes
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Relocatable `cliExternsPlaced` and `cliGhostExterns` Contracts

`HookSat` contracts for `cliGhostExterns g (cliExternsPlaced mmpl W)` and the 18 panic symbols of
`cliCratePanicSyms` under `[LibsignalPlacement]`, together with `CliGhostA0Hooks`, `a0Ghost`, and
placed allocator/codec hook bundles.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.CliExt (dhSpec pureByteFunctionSpec)
open CryptoVerification.E2E.Pqxdh.Shared
  (compressInPlaceStubSpecPlaced sha512CompressOutBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowOk ExtraSpecOk GhostRowSpecOk WriteFileRowOk hookOk_congr
   hookSatCompress256_cliGhostExterns_of_extraOk
   hookSatCompress256_cliGhostExterns_of_extraOk_eq
   hookSat_cliGhostExterns_congr_extra
   hookSat_cliGhostExterns_of_extraOk
   hookSat_cliGhostExterns_of_extraRowOk
   hookSat_cliGhostExterns_of_extra_lookup)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet hookSat_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
  (kemDecapsAtSpec kemEncapsAtSpec kemEncapsPreservedAtSpec mlkemDecapsAtSpec
   mlkemEncaps1AtSpec mlkemEncaps2AtSpec mlkemFromSeedAtSpec mlkemValidatePkAtSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
  (kyber1024DecapsVec kyber1024EncapsVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512
  (compress512StackedMasterSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (x25519PubFromSecretRef x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (dalekHookStack)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
  (dalekCompressExtSpec dalekDsmbExtSpec dalekEdNegExtSpec dalekScalarModExtSpec
   dalekScalarWideExtSpec edwardsPointNegUnstackedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (masterEdNegSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemHookStack mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat hookSatCompress256_of_eq hookSatCompress256_of_sym_eq)

/-! ## 1. Mangled symbol abbreviations for `cliPqxdhHookTablePlaced` -/

abbrev lsCompress512SymCli : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512"
abbrev lsToEdwardsSymCli : String :=
  "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"
abbrev lsCompressSymCli : String :=
  "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress"
abbrev lsEdNegSymCli : String :=
  "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg"
abbrev lsTorsionFreeSymCli : String :=
  "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free"
abbrev lsDsmbSymCli : String :=
  "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint"
abbrev lsScalarModSymCli : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order"
abbrev lsScalarWideSymCli : String :=
  "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide"
abbrev lsKemEncapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate"
abbrev lsKemDecapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"
abbrev lsMlkemFromSeedSymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"
abbrev lsMlkemPk1SymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1"
abbrev lsMlkemPk2SymCli : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2"
abbrev lsMlkemEncaps1SymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"
abbrev lsMlkemEncaps2SymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2"
abbrev lsMlkemDecapsSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key"
abbrev lsMlkemValidatePkSymCli : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"
abbrev lsLibcruxHmacSymCli : String :=
  "_RNvCs65XVORQObL2_12libcrux_hmac4hmac"
abbrev lsGrowOneU8SymCli : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVechE8grow_oneB7_"
abbrev lsGrowOneVecU8SymCli : String :=
  "_RNvMs4_NtCs69KKACWg7bl_5alloc7raw_vecINtB5_6RawVecINtNtB7_3vec3VechEE8grow_oneCsfr5T3GFabw_3std"

/-! ## 2. Panic symbols of `cliCratePanicSyms` -/

theorem cliExternsPlaced_panic_all (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ sym ∈ cliCratePanicSyms, cliExternsPlaced mmpl W sym = some Rust.panicked :=
  fun _ hmem => cliExternsPlaced_panic_of_mem mmpl W hmem

theorem cliGhostExterns_panic_all (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    ∀ sym ∈ cliCratePanicSyms,
      cliGhostExterns g (cliExternsPlaced mmpl W) sym = some Rust.panicked :=
  fun _ hmem => cliGhostExterns_panic_of_mem mmpl g W hmem

theorem cliExternsPlaced_panic_assert_jj (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_assert_yy (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_handle_alloc_error (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_handle_error (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_option_expect_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6option13expect_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_option_unwrap_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6option13unwrap_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_result_unwrap_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_bounds_check (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_assert_failed_inner (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking19assert_failed_inner" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_panic (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking5panic" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_panic_fmt (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtCskxtBwYRO61I_4core9panicking9panic_fmt" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_slice_index_fail (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_add_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_mul_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_mul_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_shl_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_shl_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_sub_overflow (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_async_fn_resumed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const28panic_const_async_fn_resumed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)
theorem cliExternsPlaced_panic_vec_remove_assert_failed (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed" =
      some Rust.panicked :=
  cliExternsPlaced_panic_of_mem mmpl W (by decide)

theorem cliGhostExterns_panic_handle_alloc_error (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)
theorem cliGhostExterns_panic_handle_error (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)
theorem cliGhostExterns_panic_option_expect_failed (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) :
    cliGhostExterns g (cliExternsPlaced mmpl W)
      "_RNvNtCskxtBwYRO61I_4core6option13expect_failed" = some Rust.panicked :=
  cliGhostExterns_panic_of_mem mmpl g W (by decide)

/-! ## 3. `A0` ghost-hook bundle and `HookSat` contracts -/

/-- `RustAlloc` ghost-hook hypothesis bundle on `g : CliGhostHooks`, including `memset`, `memcpy`, and `extra` consumer contracts. -/
structure CliGhostA0Hooks (A : RustAlloc) (g : CliGhostHooks) : Prop where
  alloc : HookOk g.alloc (rustAllocSpec A)
  allocNW : HookOk g.alloc (E2E.HooksE.rustAllocNWSpec A)
  dealloc : HookOk g.dealloc (rustDeallocSpec A)
  realloc : HookOk g.realloc (rustReallocSpec A)
  allocZeroed : HookOk g.allocZeroed (rustAllocZeroedSpec A)
  alloc_fs : ∀ s : State, (g.alloc s).fs = s.fs
  dealloc_fs : ∀ s : State, (g.dealloc s).fs = s.fs
  realloc_fs : ∀ s : State, (g.realloc s).fs = s.fs
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed
  shim_eq : g.shim = hookNoop := by rfl
  memset : ∃ f, g.memset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy : ∃ f, g.memcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec ∧
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy_exact : ∀ f, g.memcpy = some f → HookExactMemcpy f
  fmtWrite : ∃ f, g.extra.lookup lsFmtWriteSym = some f ∧ HookOk f (fmtWriteSpec A)
  formatInner : ∃ f, g.extra.lookup lsFormatInnerSym = some f ∧ HookOk f (formatInnerSpec A)
  extraOk :
    ∀ [LibsignalPlacement],
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.ExtraSpecOk g

/-- Canonical `E2E.HooksE.A0` instantiation of `CliGhostHooks` (no replay obligation). -/
@[expose] noncomputable def a0Ghost : CliGhostHooks where
  alloc := E2E.allocHook0
  dealloc := E2E.deallocHook
  realloc := E2E.reallocHook0
  allocZeroed := E2E.allocZeroedHook0
  shim := hookNoop
  stringClone := some E2E.stringCloneHook0
  memset := some hookMemset
  memcpy := some hookMemcpy
  extra := LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts

theorem cliGhostA0Hooks_a0Ghost : CliGhostA0Hooks E2E.HooksE.A0 a0Ghost where
  alloc := E2E.HooksE.allocHook0_ok
  allocNW := E2E.HooksE.allocHook0_nw_ok
  dealloc := E2E.HooksE.deallocHook_ok
  realloc := E2E.HooksE.reallocHook0_ok
  allocZeroed := E2E.HooksE.allocZeroedHook0_ok
  alloc_fs := allocHook0_fs
  dealloc_fs := deallocHook_fs
  realloc_fs := reallocHook0_fs
  alloc_fsT := allocHook0_fsT
  dealloc_fsT := deallocHook_fsT
  realloc_fsT := reallocHook0_fsT
  allocZeroed_fsT := allocZeroedHook0_fsT
  shim_eq := rfl
  memset := ⟨hookMemset, rfl, fun stk hpos => hookMemset_ok stk hpos,
    fun stk hpos => hookMemset_trace_ok stk hpos, hookMemset_region_ok,
    hookMemset_region_trace_ok, hookMemset_fs, hookMemset_fsT⟩
  memcpy := ⟨hookMemcpy, rfl, fun stk => hookMemcpy_ok stk, fun stk => hookMemcpy_trace_ok stk,
    hookMemcpy_region_ok, hookMemcpy_region_trace_ok,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpy_hookOk,
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok, hookMemcpy_fs, hookMemcpy_fsT⟩
  memcpy_exact := fun f hf => by cases hf; exact hookMemcpy_exact
  fmtWrite := ⟨E2E.fmtWriteHook0,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts_lookup_fmtWrite,
    E2E.HooksE.fmtWriteHook0_ok⟩
  formatInner := ⟨E2E.formatInnerHook0,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts_lookup_formatInner,
    E2E.HooksE.formatInnerHook0_ok⟩
  extraOk := fun [_] =>
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts_specOk

theorem cliGhostExterns_a0_fmtWrite_sat (baseExt : LibsignalHooks) {A : RustAlloc}
    {g : CliGhostHooks} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g baseExt) lsFmtWriteSym (fmtWriteSpec A) := by
  obtain ⟨f, hf, hok⟩ := hG.fmtWrite
  exact hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_a0_formatInner_sat (baseExt : LibsignalHooks) {A : RustAlloc}
    {g : CliGhostHooks} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g baseExt) lsFormatInnerSym (formatInnerSpec A) := by
  obtain ⟨f, hf, hok⟩ := hG.formatInner
  exact hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliExternsPlaced_a0_fmtWrite_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym (fmtWriteSpec A) :=
  cliGhostExterns_a0_fmtWrite_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_a0_formatInner_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym (formatInnerSpec A) :=
  cliGhostExterns_a0_formatInner_sat (cliExternsPlaced mmpl W) hG

theorem cliGhostExterns_a0_exactMemcpy_sat (baseExt : LibsignalHooks) {A : RustAlloc}
    {g : CliGhostHooks} (hG : CliGhostA0Hooks A g) :
    HookSatExactMemcpy (cliGhostExterns g baseExt) "memcpy" := by
  obtain ⟨f, hf, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hG.memcpy_exact f hf⟩

/-- `CliGhostA0Hooks` discharges `HkdfPlacedHooksExactSat` on
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks_sha256
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HkdfPlacedHooksExactSat sha256Compress (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := by
      obtain ⟨f, hf, _, _, _, hok, _, _⟩ := hG.memset
      exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩
    memcpy := cliGhostExterns_a0_exactMemcpy_sat (cliExternsPlaced mmpl W) hG
    compress256 :=
      hookSatCompress256_cliGhostExterns_of_extraOk g (cliExternsPlaced mmpl W) hG.extraOk }

theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (hF : W.C.F = sha256Compress) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  hF ▸ HkdfPlacedHooksExactSat.of_a0Hooks_sha256 hG

/-- `Rust.withPanics` specialization of `HkdfPlacedHooksExactSat.of_a0Hooks`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks_withPanics
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (hF : W.C.F = sha256Compress) :
    HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [RunGlue.withPanics_cliGhostExterns mmpl g W]
  exact HkdfPlacedHooksExactSat.of_a0Hooks hG hF

/-- Variant-extern lift of `HkdfPlacedHooksExactSat.of_a0Hooks` (covers any `H` agreeing with
    `cliGhostExterns g (cliExternsPlaced mmpl W)` outside RNG). -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_a0Hooks_ext
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (hF : W.C.F = sha256Compress) {H : LibsignalHooks}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns g (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksExactSat W.C.F H := by
  have hBase : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_a0Hooks hG hF
  refine { memset := ?_, memcpy := ?_, compress256 := ?_ }
  · obtain ⟨f, hf, hok⟩ := hBase.memset
    exact ⟨f, (hExt lsMemsetSym (by decide)).trans hf, hok⟩
  · obtain ⟨f, hf, hex⟩ := hBase.memcpy
    exact ⟨f, (hExt lsMemcpySym (by decide)).trans hf, hex⟩
  · exact hookSatCompress256_of_sym_eq (hExt lsCompress256Sym (by decide)) hBase.compress256

theorem cliGhostA0Hooks_to_fs [LibsignalPlacement] {A : RustAlloc} {g : CliGhostHooks}
    (hG : CliGhostA0Hooks A g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f) :
    CliGhostHooksFs g where
  alloc_fsT := hG.alloc_fsT
  dealloc_fsT := hG.dealloc_fsT
  realloc_fsT := hG.realloc_fsT
  allocZeroed_fsT := hG.allocZeroed_fsT
  shim_fsT := hG.shim_eq ▸ hookNoop_fsT
  stringClone_fsT := hStrFsT
  memset_fsT := by
    obtain ⟨f₀, hf₀, _, _, _, _, _, hfsT⟩ := hG.memset
    intro f hf
    cases hf₀.symm.trans hf
    exact hfsT
  memcpy_fsT := by
    obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, hfsT⟩ := hG.memcpy
    intro f hf
    cases hf₀.symm.trans hf
    exact hfsT
  extra_fsT := hG.extraOk.fsT

theorem a0Ghost_stringClone_fsT :
    ∀ f, a0Ghost.stringClone = some f → HookFsTraced IsFsC f := by
  intro f hf
  cases hf
  exact stringCloneHook0_fsT

theorem a0Ghost_stringClone_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliGhostExterns a0Ghost (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec E2E.HooksE.A0) :=
  ⟨E2E.stringCloneHook0, cliGhostExterns_stringClone_some a0Ghost _ rfl,
    E2E.HooksE.stringCloneHook0_ok⟩

/-- Lifts `HookSat (cliExternsPlaced mmpl W) sym spec` on a non-ghost symbol `sym` to `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliGhostExterns_sat_of_cliExternsPlaced {α : Type}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {spec : Spec α}
    (hsat : HookSat (cliExternsPlaced mmpl W) sym spec)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : cliExtraGhostSyms.contains sym = false ∨ g.extra.lookup sym = none := by
      left; decide) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) sym spec :=
  hookSat_of_eq (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hExtra) hsat

theorem cliGhostExterns_readFile_sat {α : Type} (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {rfh : State → State} {hrfh : HookFsTraced IsFsC rfh} {spec : Spec α}
    (hg : g.readFile = some ⟨rfh, hrfh⟩) (hok : HookOk rfh spec) :
    HookSat (cliGhostExterns g baseExt) lsReadFileSym spec :=
  ⟨rfh, RunGlue.cliGhostExterns_readFile_some g baseExt hg, hok⟩

theorem cliGhostExterns_readStdin_sat {α : Type} (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {rsh : State → State} {hrsh : HookFsTraced IsFsC rsh} {spec : Spec α}
    (hg : g.readStdin = some ⟨rsh, hrsh⟩) (hok : HookOk rsh spec) :
    HookSat (cliGhostExterns g baseExt) lsReadStdinSym spec :=
  ⟨rsh, RunGlue.cliGhostExterns_readStdin_some g baseExt hg, hok⟩

-- Allocator & shim (`cliGhostExterns g (cliExternsPlaced mmpl W)`):
theorem cliExternsPlaced_shim_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli sessionShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim), sessionShim_hookOk⟩

theorem cliExternsPlaced_noAllocShim_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli noAllocShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim), noAllocShim_hookOk⟩

theorem cliExternsPlaced_alloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli (rustAllocSpec A) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.alloc⟩

theorem cliExternsPlaced_allocNW_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli
      (E2E.HooksE.rustAllocNWSpec A) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.allocNW⟩

theorem cliExternsPlaced_dealloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSymCli (rustDeallocSpec A) :=
  ⟨g.dealloc, cliGhostExterns_dealloc g _, hG.dealloc⟩

theorem cliExternsPlaced_realloc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustReallocSymCli (rustReallocSpec A) :=
  ⟨g.realloc, cliGhostExterns_realloc g _, hG.realloc⟩

theorem cliExternsPlaced_allocZeroed_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocZeroedSymCli
      (rustAllocZeroedSpec A) :=
  ⟨g.allocZeroed, cliGhostExterns_allocZeroed g _, hG.allocZeroed⟩

-- libc memory and string ops (`cliGhostExterns g`):
theorem cliExternsPlaced_memset_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (libcMemsetSpec stk) := by
  obtain ⟨f, hf, hok, _, _, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok stk hpos⟩

theorem cliExternsPlaced_sessionMemset_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (sessionMemsetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok stk hpos⟩

theorem cliExternsPlaced_memsetRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" memsetRegionSpec := by
  obtain ⟨f, hf, _, _, hok, _, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩

theorem cliExternsPlaced_sessionMemsetRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩

theorem cliExternsPlaced_memcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (libcMemcpySpec stk) := by
  obtain ⟨f, hf, hok, _, _, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok stk⟩

theorem cliExternsPlaced_sessionMemcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (sessionMemcpySpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok stk⟩

theorem cliExternsPlaced_memcpyRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" memcpyRegionSpec := by
  obtain ⟨f, hf, _, _, hok, _, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_sessionMemcpyRegion_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" sessionMemcpyRegionSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_framelessMemcpy_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec := by
  obtain ⟨f, hf, _, _, _, _, hok, _, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliExternsPlaced_memcpyRegionRO_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec := by
  obtain ⟨f, hf, _, _, _, _, _, hok, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g _ hf, hok⟩

theorem cliGhostExterns_bcmp_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" cliBcmpSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmp_ok

theorem cliGhostExterns_bcmpVregs_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" E2E.HooksE.bcmpVregsSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmpVregs_ok

theorem cliGhostExterns_e2eBcmp_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" E2E.HooksE.e2eBcmpSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.e2eBcmp_ok

theorem cliGhostExterns_strlen_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
        (strlenSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlen_ok stk

theorem cliGhostExterns_strlenRO_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.strlenSpecRO stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlenRO_ok stk

theorem cliGhostExterns_memrchr_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym (withLsRet (memrchrSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.memrchr_ok hstk hstk_ub

theorem cliGhostExterns_memrchrRO_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym
      (withLsRet (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.memrchrSpecRO stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.memrchrRO_ok hstk hstk_ub

theorem cliGhostExterns_fromUtf8_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym (fromUtf8AsciiSpec stk) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8_ok stk

theorem cliGhostExterns_fromUtf8RO_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym
      (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.fromUtf8AsciiSpecRO stk) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8RO_ok stk

theorem cliExternsPlaced_readFile_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hRead : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  cliReadFilePlaced_hookSat mmpl g W stk hRead

theorem cliWriteStdoutHook_ok_placed (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpecPlaced stk) := by
  intro x R s0 hrun hpre _
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1⟩, hmem⟩ := hpre
  obtain ⟨hlen, hrd⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.buf x.bs).canRead hlen hmem
  rw [← hx0] at hrd hcan
  rw [writeStdoutHook_eq hx1 hcan hrd]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl, List.prefix_append _ _, ?_⟩, hmem⟩
  change Process.ProcessOutcome.traceStreamBytes .stdout
    (s0.trace ++ TraceEvent.ofBytes .stdout x.bs) = _
  rw [MainHops.traceStreamBytes_append, MainHops.traceStreamBytes_ofBytes_stdout]

private theorem cliWriteFile_outcome_placed {stk : Nat} {x : WriteFileGhost} {R : SepProp}
    {s0 : State} {ok : Bool} {fs' : FsState} (hrun : s0.status = .Running)
    (hmem : s0.mem ⊨ (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ R)
    (hpost :
      let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
      match cliIo.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) :
    let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (writeFileSpecPlaced cliIo stk) x R s0 sf := by
  intro sf
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpost, List.prefix_append _ _, ?_⟩, hmem⟩
  change Process.ProcessOutcome.traceStreamBytes .stdout
    (s0.trace ++ [.fileChanged (pathStr x.path)]) = _
  rw [MainHops.traceStreamBytes_append, MainHops.traceStreamBytes_fileChanged, List.append_nil]

theorem cliWriteFileHook_ok_placed (stk : Nat) :
    HookOk writeFileHook (writeFileSpecPlaced cliIo stk) := by
  intro x R s0 hrun hpre _
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemB : s0.mem ⊨ (x.buf ↦ₛ x.bs) ∗ (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ R := by
    rw [sepConj_left_comm]; exact hmem
  obtain ⟨hlenB, hrdB⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmemB
  have hcanB := (IsBlock.pointsToBytes x.buf x.bs).canRead hlenB hmemB
  rw [← hx0] at hrdP hcanP
  rw [← hx2] at hrdB hcanB
  rw [writeFileHook_eq hx1 hx3 (by rw [hcanP, hcanB]; rfl) hrdP hrdB hpok' hpok.2.2]
  simp only
  cases hA : blockingAncestorF s0.fs.files (pathStr x.path) with
  | some _ =>
    exact cliWriteFile_outcome_placed hrun hmem (by simp only [cliIo, cliWr, hA]; exact ⟨rfl, rfl⟩)
  | none =>
    cases hB : s0.fs.files (pathStr x.path) with
    | none =>
      exact cliWriteFile_outcome_placed hrun hmem
        (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)
    | some e =>
      cases e with
      | dir =>
        exact cliWriteFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, rfl⟩)
      | file _ =>
        exact cliWriteFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)

theorem cliReadStdinHook_ok_placed (stk : Nat) :
    HookOk readStdinHook (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  refine hookOk_of_on (c := ReadStdinOom) ?_ ?_
  · intro x R s0 ⟨hcap, hne, hnone⟩ _ hpre0 _
    have hpre := hpre0
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
    rw [← hx8] at hcanW
    obtain ⟨fs', -, heq⟩ := readStdinHook_eq hcanW hin
    simp only [hcap, ↓reduceIte] at heq
    rw [heq, vecOk_oom (s := s0.setFs fs') hne hnone]
    refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    change s0.mem ⊨ (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk).onPanic x s0
      (E2E.allocPanicHook (s0.setFs fs')) ∗ R
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨E2E.HooksE.HooksOkAux.allocFailedIn_allocPanicHook (s0.setFs fs'),
      E2E.HooksE.HooksOkAux.trace_prefix_allocPanicHook (s0.setFs fs')⟩,
      Satisfies.mono (sepConj_mono_left (Entails.top_right fun _ => trivial)) hpre0⟩
  · intro x R s0 hnoom hrun hpre _
    simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
    rw [← hx8] at hcanW
    obtain ⟨fs', hfs', heq⟩ := readStdinHook_eq hcanW hin
    by_cases hcap : x.bs.length ≤ stdinCapBytes
    · simp only [hcap, ↓reduceIte] at heq
      have hfit : x.bs ≠ [] → E2E.bumpAddr? (s0.setFs fs').mem x.bs.length 1 ≠ none :=
        fun hne hnone => hnoom ⟨hcap, hne, hnone⟩
      obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok (s := s0.setFs fs') hx8 hmem hfit
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.ok x.bs, ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
      simp only [ioVecAt] at hm ⊢
      exact hm
    · simp only [hcap, ↓reduceIte] at heq
      obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok (s := s0.setFs fs') hx8 hmem
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.error (), ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
      simp only [ioVecAt, sepConj_assoc] at hm ⊢
      exact hm

theorem cliReadFileLitHook_ok_placed (stk : Nat) :
    HookOk readFileHook (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  refine hookOk_of_on (c := ReadFileOom) ?_ ?_
  · intro x R s0 hoom hrun hpre0 hsp
    have hpre := hpre0
    simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
    have hpok' : PathOk (pathStr x.path) = true := hpok.1
    have hlenP : x.path.length ≤ 2 ^ 64 := by omega
    have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
    have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
    have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
        ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
      rw [sepConj_left_comm]; exact hmem
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
    rw [← hx0] at hrdP hcanP
    rw [← hx8] at hcanW
    have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
      readPath_eq_pathStr hx1 hrdP
    have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
      (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
    rw [hp] at heq
    obtain ⟨bs, hv, hne, hnone⟩ := hoom
    rw [hv] at heq
    dsimp only at heq
    rw [heq, vecOk_oom hne hnone]
    exact E2E.HooksE.HooksOkAux.allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp
  · intro x R s0 hnoom hrun hpre _
    simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
    have hpok' : PathOk (pathStr x.path) = true := hpok.1
    have hlenP : x.path.length ≤ 2 ^ 64 := by omega
    have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
    have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
    have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
        ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
      rw [sepConj_left_comm]; exact hmem
    have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
    rw [← hx0] at hrdP hcanP
    rw [← hx8] at hcanW
    have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
      readPath_eq_pathStr hx1 hrdP
    have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
      (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
    rw [hp] at heq
    have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
        cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
      intro r hr
      show cliRd s0.fs.files x.path = _
      unfold cliRd
      rw [← readView_eq_readViewF, hr]; rfl
    cases hv : readView s0.fs (pathStr x.path) with
    | none =>
      rw [hv] at heq
      dsimp only at heq
      obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.error (), ⟨rfl, (hrd none hv).symm, rfl⟩, ?_⟩
      simp only [ioVecAt, sepConj_assoc] at hm ⊢
      exact hm
    | some bs =>
      rw [hv] at heq
      dsimp only at heq
      have hfit : bs ≠ [] → E2E.bumpAddr? s0.mem bs.length 1 ≠ none :=
        fun hne hnone => hnoom ⟨bs, hv, hne, hnone⟩
      obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok hx8 hmemR hfit
      rw [heq, hsf]
      refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
      simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
        satisfies_sepExists, satisfies_pure_sepConj]
      refine ⟨.ok bs, ⟨rfl, (hrd (some bs) hv).symm, rfl⟩, ?_⟩
      simp only [ioVecAt] at hm ⊢
      exact hm

theorem cliExternsPlaced_readFileLit_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hReadLit : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hReadLit

theorem cliGhostExterns_writeFile_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (stk : Nat)
    (hf : g.extra.lookup lsWriteFileSym = some f)
    (hok : HookOk f (writeFileSpecPlaced cliIo stk)) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym (writeFileSpecPlaced cliIo stk) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeFile_hook_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (stk : Nat) (hf : g.extra.lookup lsWriteFileSym = some writeFileHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteFileSym (writeFileSpecPlaced cliIo stk) :=
  cliGhostExterns_writeFile_sat g baseExt stk hf (cliWriteFileHook_ok_placed stk)

theorem a0Ghost_writeFile_sat (baseExt : LibsignalHooks) (stk : Nat) :
    HookSat (cliGhostExterns a0Ghost baseExt) lsWriteFileSym (writeFileSpecPlaced cliIo stk) :=
  cliGhostExterns_writeFile_hook_sat a0Ghost baseExt stk
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts_lookup_writeFile

theorem cliExternsPlaced_readStdin_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hStdin : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadStdinSym
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hStdin

theorem cliGhostExterns_writeStdout_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (stk : Nat)
    (hf : g.extra.lookup lsWriteStdoutSym = some f)
    (hok : HookOk f (writeStdoutSpecPlaced stk)) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym (writeStdoutSpecPlaced stk) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_writeStdout_hook_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (stk : Nat) (hf : g.extra.lookup lsWriteStdoutSym = some writeStdoutHook) :
    HookSat (cliGhostExterns g baseExt) lsWriteStdoutSym (writeStdoutSpecPlaced stk) :=
  cliGhostExterns_writeStdout_sat g baseExt stk hf (cliWriteStdoutHook_ok_placed stk)

theorem a0Ghost_writeStdout_sat (baseExt : LibsignalHooks) (stk : Nat) :
    HookSat (cliGhostExterns a0Ghost baseExt) lsWriteStdoutSym (writeStdoutSpecPlaced stk) :=
  cliGhostExterns_writeStdout_hook_sat a0Ghost baseExt stk
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts.pureExtraGhosts_lookup_writeStdout

/-- Single-block `sha2::sha256::compress256` contract (`x2 = 1#64`). -/
@[expose] def compress256SingleSpec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8)) where
  pre := fun (stA, st, blkA, blk) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ s.readReg64 .x2 = 1#64 ∧
      blk.length = 64⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ (blkA ↦ₛ blk)
  post := fun (stA, st, blkA, blk) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ LibsignalHmac.shaStateBytes (F st blk)) ∗ (blkA ↦ₛ blk)

theorem compress256Hook_single_ok (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (LibsignalHmac.compress256Hook F) (compress256SingleSpec F) := by
  intro ⟨stA, st, blkA, blk⟩ R s0 hrun hpre _
  simp only [compress256SingleSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hblk_len⟩, hmem⟩
  have hst_len : (LibsignalHmac.shaStateBytes st).length = 32 := by
    simp [LibsignalHmac.shaStateBytes]
  have hst_rd : s0.mem.readBytes stA 32 = LibsignalHmac.shaStateBytes st := by
    have hrd := ((IsBlock.pointsToBytes stA (LibsignalHmac.shaStateBytes st)).read hmem).2
    rwa [hst_len] at hrd
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ blk) ∗ ((stA ↦ₛ LibsignalHmac.shaStateBytes st) ∗ R) := by
    ac_nf at hmem ⊢
  have hblk_rd : s0.mem.readBytes blkA 64 = blk := by
    have hrd := ((IsBlock.pointsToBytes blkA blk).read hmem_blk).2
    rwa [hblk_len] at hrd
  have heq :=
    LibsignalSession.CryptoHmacSha256.compress256Hook_one_eq F hx0 hx1 hx2 rfl rfl hst_rd hblk_rd
  let outBytes := LibsignalHmac.shaStateBytes (F st blk)
  have hout_len : outBytes.length = 32 := by simp [outBytes, LibsignalHmac.shaStateBytes]
  have hmem_reg : s0.mem ⊨ memRegion stA outBytes.length ∗ ((blkA ↦ₛ blk) ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans (pointsToBytes_entails_memRegion stA _)
        (by rw [hst_len]; exact Entails.refl _)))
      hmem
  have hlen32 : outBytes.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  rw [heq]
  refine ⟨keepsFrozen_writeBytes_of_memRegion outBytes hlen32 hmem_reg,
    rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [compress256SingleSpec, State.trace_setPC, State.setMem, sepConj_assoc,
    satisfies_pure_sepConj, true_and]
  exact satisfies_writeBytes outBytes hlen32 hmem_reg

theorem cliGhostExterns_compress256Multi_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress256Sym
      (withLsRet (CryptoVerification.LibsignalTripleRatchet.withStack
        (compress256Spec sha256Compress) stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress256_multi_ok hstk

theorem cliGhostExterns_compress256Single_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress256Sym
      (withLsRet (CryptoVerification.LibsignalTripleRatchet.withStack
        (compress256SingleSpec sha256Compress) stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hookOk_congr (hRow.compress256_single_ok hstk)

-- `alloc`, `core::fmt`, `std::time`, `subtle`:
theorem cliExternsPlaced_stringClone_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym (stringCloneSpec A) :=
  hStrClone

theorem cliGhostExterns_fmtWrite_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {A : RustAlloc} {f : State → State}
    (hf : g.extra.lookup lsFmtWriteSym = some f)
    (hok : HookOk f (fmtWriteSpec A)) :
    HookSat (cliGhostExterns g baseExt) lsFmtWriteSym (fmtWriteSpec A) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem cliGhostExterns_formatInner_sat (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {A : RustAlloc} {f : State → State}
    (hf : g.extra.lookup lsFormatInnerSym = some f)
    (hok : HookOk f (formatInnerSpec A)) :
    HookSat (cliGhostExterns g baseExt) lsFormatInnerSym (formatInnerSpec A) :=
  hookSat_cliGhostExterns_of_extra_lookup g baseExt hf hok

theorem a0Ghost_fmtWrite_sat (baseExt : LibsignalHooks) :
    HookSat (cliGhostExterns a0Ghost baseExt) lsFmtWriteSym (fmtWriteSpec E2E.HooksE.A0) :=
  cliGhostExterns_a0_fmtWrite_sat baseExt cliGhostA0Hooks_a0Ghost

theorem a0Ghost_formatInner_sat (baseExt : LibsignalHooks) :
    HookSat (cliGhostExterns a0Ghost baseExt) lsFormatInnerSym (formatInnerSpec E2E.HooksE.A0) :=
  cliGhostExterns_a0_formatInner_sat baseExt cliGhostA0Hooks_a0Ghost

theorem cliGhostExterns_durationSinceEpoch_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet (durationSinceEpochAtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceEpochAt_ok hstk hstk_ub

theorem cliGhostExterns_durationSinceEpochAlloc_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet durationSinceEpochAllocSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceEpochAt_ok (by decide : 208 ≤ allocHookStack) (by decide)

theorem cliGhostExterns_durationSinceBounded_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet durationSinceBoundedSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.durationSinceBounded_ok

theorem cliGhostExterns_timeAdd_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsTimeAddSym (withLsRet timeAddSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.publicApiTimeAdd_ok

theorem blackBoxHook_ok :
    HookOk LibsignalSession.blackBoxHook LibsignalSession.FindReceiverChainIndex.blackBoxSpec := by
  have hsat : HookSat (fun _ => some LibsignalSession.blackBoxHook)
      "subtle::black_box::<u8>" LibsignalSession.FindReceiverChainIndex.blackBoxSpec :=
    LibsignalSession.FindReceiverChainIndex.blackBoxHook_sat rfl
  rcases hsat with ⟨f, hf, hok⟩
  cases hf
  exact hok

theorem cliGhostExterns_blackBox_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      (CryptoVerification.LibsignalTripleRatchet.withStack
        LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.findReceiverBlackBox_ok hstk hstk_ub

theorem cliGhostExterns_blackBox16_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat.blackBoxSpec16 :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.blackBox_ok (by decide : 16 ≤ 16) (by decide)

-- AES-CBC & X25519:
theorem cliExternsPlaced_aesEnc_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hAesEnc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesEncSym (aesEncSpec W.C.E A) :=
  hAesEnc

theorem cliExternsPlaced_aesDec_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hAesDec : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsAesDecSym (aesDecSpec W.C.D A) :=
  hAesDec

theorem cliGhostExterns_pubFromSecretWithStack_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
        (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretWithStack_ok stk hlo hhi

theorem cliGhostExterns_pubFromSecret_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecret_ok hC

theorem cliGhostExterns_pubFromSecretPureByte_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.pubFromSecretPureByte_ok byVal

theorem cliGhostExterns_derivePublicKeyBytesStack_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStack_ok stk hlo hhi

theorem cliGhostExterns_derivePublicKeyBytesStackBudget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsPubFromSecretSym
      (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.derivePublicKeyBytesStackBudget_ok stk hlo hhi

theorem cliGhostExterns_diffieHellmanWithStack_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym
      (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
        (diffieHellmanSpec x25519Ref) stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellmanWithStack_ok stk hlo hhi

theorem cliGhostExterns_diffieHellman_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookSat (cliGhostExterns g baseExt) lsDiffieHellmanSym (withLsRet (dhSpec C)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.diffieHellman_ok hC

theorem cliGhostExterns_staticSecretDrop_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsStaticSecretDropSym zeroizeSecretSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.staticSecretDrop_ok

theorem cliGhostExterns_sharedSecretDrop_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsSharedSecretDropSym zeroizeSecretSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.sharedSecretDrop_ok

-- PQXDH and SPQR (`extra` ghost rows and `libcruxHmac`):
theorem cliGhostExterns_compress512_stackedMaster_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (compress512StackedMasterSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_stackedMaster_ok hstk

theorem cliGhostExterns_compress512_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {Q : E2E.PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_ok hF

theorem cliGhostExterns_compress512_keepsFs_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {Q : E2E.PqxdhPrims} (hF : Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (keepsFs (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_keepsFs_ok hF

theorem cliGhostExterns_compress512_pqxdhStubPlaced_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (compressInPlaceStubSpecPlaced
        (sha512CompressOutBytes (E2E.modelPrims X P0)) 64 128)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_pqxdhStubPlaced_ok X hF

theorem cliGhostExterns_compress512_pqxdhStubPlaced_keepsFs_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookSat (cliGhostExterns g baseExt) lsCompress512SymCli
      (withLsRet (keepsFs (compressInPlaceStubSpecPlaced
        (sha512CompressOutBytes (E2E.modelPrims X P0)) 64 128))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress512_pqxdhStubPlaced_keepsFs_ok X hF

theorem cliGhostExterns_toEdwards_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsToEdwardsSymCli
      (withLsRet (dalekMontToEdExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.toEdwards_ok stk hlo hhi

theorem cliGhostExterns_compress_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsCompressSymCli
      (withLsRet (dalekCompressExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.compress_ok stk hlo hhi

theorem cliGhostExterns_edNegMaster_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli masterEdNegSpec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_master_ok

theorem cliGhostExterns_edNegUnstacked_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (byVal : Bool := false) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli (edwardsPointNegUnstackedSpec byVal) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_unstacked_ok byVal

theorem cliGhostExterns_edNeg_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (E2E.Pqxdh.Shared.cryptoLeafStubSpec
        (fun bs => E2E.vecU8 (dalekEdNegVec (E2E.u8Vec 160 bs))) 160 160) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_cryptoLeafStub_ok

theorem cliGhostExterns_edNegExt_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack) :
    HookSat (cliGhostExterns g baseExt) lsEdNegSymCli
      (withLsRet (dalekEdNegExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.edNeg_ext_ok stk

theorem cliGhostExterns_torsionFree_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsTorsionFreeSymCli
      (withLsRet (dalekTorsionFreeExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.torsionFree_ok stk hlo hhi

theorem cliGhostExterns_dsmb_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsDsmbSymCli
      (withLsRet (dalekDsmbExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.dsmb_ok stk hlo hhi

theorem cliGhostExterns_scalarMod_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsScalarModSymCli
      (withLsRet (dalekScalarModExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.scalarMod_ok stk hlo hhi

theorem cliGhostExterns_scalarWide_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsScalarWideSymCli
      (withLsRet (dalekScalarWideExtSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.scalarWide_ok stk hlo hhi

theorem cliGhostExterns_kemEncapsPreserved_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : E2E.PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (kemEncapsPreservedAtSpec stk Q)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncapsPreserved_ok stk hlo hhi hQ

theorem cliGhostExterns_kemEncaps_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : E2E.PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemEncapsSymCli
      (withLsRet (kemEncapsAtSpec stk Q)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemEncaps_ok stk hlo hhi hQ

theorem cliGhostExterns_kemDecaps_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : E2E.PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookSat (cliGhostExterns g baseExt) lsKemDecapsSymCli
      (withLsRet (kemDecapsAtSpec stk Q)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.kemDecaps_ok stk hlo hhi hQ

theorem cliGhostExterns_mlkemFromSeed_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemFromSeedSymCli
      (withLsRet (mlkemFromSeedAtSpec stk K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemFromSeed_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemPk1_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk1SymCli mlkemPk1Spec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk1_ok

theorem cliGhostExterns_mlkemPk1Ls_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk1SymCli (withLsRet mlkemPk1Spec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk1_ls_ok

theorem cliGhostExterns_mlkemPk2_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk2SymCli mlkemPk2Spec :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk2_ok

theorem cliGhostExterns_mlkemPk2Ls_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsMlkemPk2SymCli (withLsRet mlkemPk2Spec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemPk2_ls_ok

theorem cliGhostExterns_mlkemEncaps1_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps1SymCli
      (withLsRet (mlkemEncaps1AtSpec stk K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps1_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemEncaps2_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (mlkemEncaps2Spec K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2_ok hK

theorem cliGhostExterns_mlkemEncaps2At_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemEncaps2SymCli
      (withLsRet (mlkemEncaps2AtSpec stk K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemEncaps2At_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemDecapsAt_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemDecapsSymCli
      (withLsRet (mlkemDecapsAtSpec stk K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemDecapsAt_ok stk hlo hhi hK

theorem cliGhostExterns_mlkemValidatePk_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (mlkemValidatePkSpec K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePk_ok hK

theorem cliGhostExterns_mlkemValidatePkAt_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks) (hOk : ExtraSpecOk g)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookSat (cliGhostExterns g baseExt) lsMlkemValidatePkSymCli
      (withLsRet (mlkemValidatePkAtSpec stk K)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.mlkemValidatePkAt_ok stk hlo hhi hK

theorem cliExternsPlaced_libcruxHmac_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc}
    (hHmac : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F A)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F A) :=
  hHmac

/-! ## 4. `AllocContractsXCliPlaced` and `AllocContractsFsPlaced` at `cliGhostExterns` -/

private theorem ghost_stub_placed_rocl_ok [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalHookedExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (ls_hook_ok_ultra_of_mem hsat hmem)

theorem allocContractsXCliPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    AllocContractsXCliPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, _, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, _, _, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := ghost_stub_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le⟩
      dealloc := ghost_stub_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack extHookStack_le⟩
      realloc := ghost_stub_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack extHookStack_le⟩
      shim stk _ _ := ghost_stub_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          hookOk_withStack sessionShim_hookOk stk⟩
      memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hMcLibc stk⟩
      session_memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hMcSess stk⟩
      memcpy_region stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, hookOk_withStack hMcReg stk⟩
      session_memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, hookOk_withStack hMcSessReg stk⟩
      memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hMsLibc stk (pos_of_extHookStack_le hle)⟩
      session_memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hMsSess stk (pos_of_extHookStack_le hle)⟩
      memset_region stk _ _ := ghost_stub_placed_rocl_ok ⟨fMs, hMsEq, hookOk_withStack hMsReg stk⟩
      session_memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, hookOk_withStack hMsSessReg stk⟩ }

theorem allocContractsXCliPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsXCliPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  allocContractsXCliPlaced_of_hooks mmpl g W hG

theorem allocContractsFsPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {A : RustAlloc}
    (hG : CliGhostA0Hooks A g) :
    AllocContractsFsPlaced A (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, hMsFs, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, hMcRO, hMcFs, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := ghost_stub_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          (hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le).keepsFs
            hG.alloc_fs⟩
      dealloc := ghost_stub_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          (hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.dealloc_fs⟩
      realloc := ghost_stub_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          (hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.realloc_fs⟩
      shim stk _ _ := ghost_stub_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          (hookOk_withStack sessionShim_hookOk stk).keepsFs hookNoop_fs⟩
      memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, (hMcLibc stk).keepsFs hMcFs⟩
      session_memcpy stk _ _ := ghost_stub_placed_rocl_ok ⟨fMc, hMcEq, (hMcSess stk).keepsFs hMcFs⟩
      memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcReg stk).keepsFs hMcFs⟩
      session_memcpy_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcSessReg stk).keepsFs hMcFs⟩
      memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hMsLibc stk (pos_of_extHookStack_le hle)).keepsFs hMsFs⟩
      session_memset stk hle _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hMsSess stk (pos_of_extHookStack_le hle)).keepsFs hMsFs⟩
      memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack hMsReg stk).keepsFs hMsFs⟩
      session_memset_region stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack hMsSessReg stk).keepsFs hMsFs⟩
      session_memcpy_region_ro stk _ _ := ghost_stub_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack hMcRO stk).keepsFs hMcFs⟩ }

theorem allocContractsFsPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    AllocContractsFsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  allocContractsFsPlaced_of_hooks mmpl g W hG

/-! ## 5. Placed hook bundles at `cliGhostExterns` -/

theorem stage2ContractsMinPlaced_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced.of_hooks
    (cliExternsPlaced_alloc_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_sat mmpl g W hG)
    (cliExternsPlaced_realloc_sat mmpl g W hG)
    (cliExternsPlaced_shim_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_sat mmpl g W hG _)
    (cliGhostExterns_panic_handle_error mmpl g W)
    (cliGhostExterns_panic_handle_alloc_error mmpl g W)

theorem codecHooksPlaced_cli (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g) :
    RecordCodecsBinary.CodecHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_noAllocShim_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_sat mmpl g W hG
  memcpy := cliExternsPlaced_framelessMemcpy_sat mmpl g W hG
  panic_alloc := cliGhostExterns_panic_handle_alloc_error mmpl g W
  panic_raw := cliGhostExterns_panic_handle_error mmpl g W

theorem publicApiDecHooksPlaced_cli (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 g)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec E2E.HooksE.A0)) :
    LibsignalPublicApi.MessageDecrypt.PublicApiDecHooksPlaced E2E.HooksE.A0
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_sat mmpl g W hG
  stringClone := hStrClone
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

end CryptoVerification.SignalSession.Cli.Slots
