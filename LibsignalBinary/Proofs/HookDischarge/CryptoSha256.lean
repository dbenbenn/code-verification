/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclFetch
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateFetch
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateStep
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256 -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge

/-!
# SHA-256 and HMAC Machine-Code Proofs (`LibsignalBinary.Proofs.HookDischarge.CryptoSha256`)

Re-exports placement-generic (`Obj.PlacedLib` / `Obj.MultiPlacedLib`) machine-code proofs for
`rustc 1.98.1`-compiled SHA-256 and HMAC-SHA-256 routines against `sha256CompressState`
(`Sha256Ref`, FIPS 180-4 block compression), together with the `haclSubroutinesTrace_ok`,
`libcruxHmac_budget_ok`, and `libcruxHmac_spqr_ok` assembly theorems.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode (libcruxHmacLib memcpySym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts (HaclInProg HaclSubroutines)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateStep (sha256Update_subroutineOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclSha256
  (haclMemcpySpec haclSubroutines_ok
   sha256Init_subroutineOk sha256UpdateNblocks_subroutineOk
   sha256UpdateLast_withTraceEq_subroutineOk sha256Finish_subroutineOk
   hash256_withTraceEq_subroutineOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep (HmacAuxSubroutines)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmac
  (HaclSubroutinesTrace HmacBudgetAllocSubroutines HmacAllocSubroutines
   libcruxHmac_budget_withHaclCodeLoaded_subroutineOk libcruxHmac_budget_subroutineOk
   libcruxHmac_spqr_withHaclCodeLoaded_subroutineOk libcruxHmac_spqr_subroutineOk)

/-- Assemble `HaclSubroutines` (Blocks `0..5`) directly from `HaclInProg P mpl` and `haclMemcpySpec`. -/
theorem haclSubroutines_all_ok {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    HaclSubroutines P mpl :=
  haclSubroutines_ok hP (sha256Update_subroutineOk hP) hmemcpy

/-- Assemble `HaclSubroutinesTrace` (Blocks `0..5` with `sf.trace = s0.trace`) directly from
`HaclInProg P mpl` and `haclMemcpySpec`. -/
theorem haclSubroutinesTrace_ok {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec) :
    HaclSubroutinesTrace P mpl :=
  let hupd := sha256Update_subroutineOk hP
  ⟨sha256Init_subroutineOk hP,
   sha256UpdateNblocks_subroutineOk hP hupd,
   sha256UpdateLast_withTraceEq_subroutineOk hP hupd hmemcpy,
   sha256Finish_subroutineOk hP,
   hash256_withTraceEq_subroutineOk hP hupd hmemcpy⟩

/-- Budget-threaded `subroutine_ok` for `libcrux_hmac::hmac` (`w0 = 0` SHA-256) against
`withHaclCodeLoaded mpl (libcruxHmacBudgetSpec sha256CompressState M A lim)` from
`HaclInProg P mpl` alone (discharging blocks `0..5` internally). -/
theorem libcruxHmac_budget_withHaclCodeLoaded_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6)
      (LibcruxHmac.withHaclCodeLoaded mpl (libcruxHmacBudgetSpec sha256CompressState M A lim)) :=
  libcruxHmac_budget_withHaclCodeLoaded_subroutineOk hP (haclSubroutinesTrace_ok hP hmemcpy) haux halloc

/-- Budget-threaded `subroutine_ok` for `libcrux_hmac::hmac` (`w0 = 0` SHA-256) against
`libcruxHmacBudgetSpec sha256CompressState M A lim`. -/
theorem libcruxHmac_budget_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacBudgetAllocSubroutines M A lim P mpl) :
    subroutine_ok P (mpl.base 6) (libcruxHmacBudgetSpec sha256CompressState M A lim) :=
  libcruxHmac_budget_subroutineOk hP hCL (haclSubroutinesTrace_ok hP hmemcpy) haux halloc

/-- Unbudgeted `subroutine_ok` for `libcrux_hmac::hmac` (`w0 = 0` SHA-256) against
`withHaclCodeLoaded mpl (libcruxHmacSpec sha256CompressState A)` from
`HaclInProg P mpl` alone (discharging blocks `0..5` internally). -/
theorem libcruxHmac_spqr_withHaclCodeLoaded_ok
    {A : RustAlloc} {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacAllocSubroutines A P mpl) :
    subroutine_ok P (mpl.base 6)
      (LibcruxHmac.withHaclCodeLoaded mpl (libcruxHmacSpec sha256CompressState A)) :=
  libcruxHmac_spqr_withHaclCodeLoaded_subroutineOk hP (haclSubroutinesTrace_ok hP hmemcpy) haux halloc

/-- Unbudgeted `subroutine_ok` for `libcrux_hmac::hmac` (`w0 = 0` SHA-256) against
`libcruxHmacSpec sha256CompressState A`. -/
theorem libcruxHmac_spqr_ok
    {A : RustAlloc} {P : Program} {mpl : Obj.MultiPlacement}
    (hP : HaclInProg P mpl)
    (hCL : ∀ m : Memory, P.CodeLoaded m → libcruxHmacLib.CodeLoaded mpl m)
    (hmemcpy : subroutine_ok P (mpl.ρ memcpySym) haclMemcpySpec)
    (haux : HmacAuxSubroutines P mpl)
    (halloc : HmacAllocSubroutines A P mpl) :
    subroutine_ok P (mpl.base 6) (libcruxHmacSpec sha256CompressState A) :=
  libcruxHmac_spqr_subroutineOk hP hCL (haclSubroutinesTrace_ok hP hmemcpy) haux halloc

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256
