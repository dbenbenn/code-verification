/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI `MessageEncrypt` Hook Bundles

Defines `CliEncHooks` (using `durationSinceBoundedSpec` on `cliExterns W` / `trTrapExterns`) and
`CliEncHooksExt` (contract-backed hooks on `tripleRatchetProgAtExt`), together with call-distance
stepping lemmas.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Hook contract bundle for CLI `MessageEncrypt` on `trTrapProgAt` / `cliExterns`:
identical to `PublicApiHooksNoStores` except `durationSince` uses `durationSinceBoundedSpec`. -/
structure CliEncHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S abs where
  timeAdd : HookSat abs timeAddHookName timeAddSpec
  durationSince : HookSat abs durationSinceHookName durationSinceBoundedSpec

theorem hookSat_trTrap_iff (C : Crypto) (abs : String → Option (State → State))
    {α : Type} {n : String} {spec : Spec α}
    (hk : n ∉ kitOwnNames) (hr : n ≠ rngFillName) :
    HookSat (trTrapExterns C abs) n spec ↔ HookSat abs n spec := by
  simp only [HookSat, trTrapExterns_of_not_mem C abs hk hr]

theorem allocHooks_trTrap_iff (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    AllocHooks A (trTrapExterns C abs) ↔ AllocHooks A abs := by
  constructor
  · intro h
    exact ⟨(hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.dealloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.realloc⟩
  · intro h
    exact ⟨(hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.dealloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.realloc⟩

theorem tripleRatchetHooks_trTrap_iff (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    TripleRatchetHooks C A S (trTrapExterns C abs) ↔ TripleRatchetHooks C A S abs := by
  constructor
  · intro h
    exact ⟨(allocHooks_trTrap_iff C A abs).mp h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.allocZeroed,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.aesEnc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.aesDec,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.formatInner,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.fmtWrite⟩
  · intro h
    exact ⟨(allocHooks_trTrap_iff C A abs).mpr h.alloc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.allocZeroed,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.aesEnc,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.aesDec,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.formatInner,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.fmtWrite⟩

theorem cliEncHooks_trTrap_iff (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) :
    CliEncHooks C A S (trTrapExterns C abs) ↔ CliEncHooks C A S abs := by
  constructor
  · intro h
    exact ⟨(tripleRatchetHooks_trTrap_iff C A S abs).mp h.toTripleRatchetHooks,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.timeAdd,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mp h.durationSince⟩
  · intro h
    exact ⟨(tripleRatchetHooks_trTrap_iff C A S abs).mpr h.toTripleRatchetHooks,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.timeAdd,
      (hookSat_trTrap_iff C abs (by decide) (by decide)).mpr h.durationSince⟩

/-- `CliEncHooks` holds directly on `cliExterns W` at `A := E2E.HooksE.A0`. -/
theorem cliEncHooks_cliExterns (W : CliHooks) (S : SpqrModel) :
    CliEncHooks W.C E2E.HooksE.A0 S (cliExterns W) where
  toTripleRatchetHooks := cliExterns_tripleRatchetHooks W S
  timeAdd := cliExterns_timeAdd W
  durationSince := cliExterns_durationSinceBounded W

/-- Instantiation of `CliEncHooks` at `A := E2E.HooksE.A0` and `abs := trTrapExterns W.C (cliExterns W)`. -/
theorem cliEncHooks_of_runHooks (W : CliHooks) (S : SpqrModel) :
    CliEncHooks W.C E2E.HooksE.A0 S (trTrapExterns W.C (cliExterns W)) :=
  (cliEncHooks_trTrap_iff W.C E2E.HooksE.A0 S (cliExterns W)).mpr (cliEncHooks_cliExterns W S)

/-- Extract `AllocHooks A abs` from `CliEncHooks C A S (trTrapExterns C abs)`. -/
theorem CliEncHooks.alloc_abs {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CliEncHooks C A S (trTrapExterns C abs)) : AllocHooks A abs :=
  (allocHooks_trTrap_iff C A abs).mp h.alloc

/-- Contract-backed hook bundle for CLI `MessageEncrypt` on `tripleRatchetProgAtExt img.base ext`:
carries `TripleRatchetHooks`, `shim`, stacked `mem*` (`memHookStack = allocHookStack = 4096`),
`timeAdd`, and `CliExt.durationSinceEpochSpec` (`UNIX_EPOCH`). -/
structure CliEncHooksExt (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" CliExt.shimSpec
  memcpy : HookSat ext "memcpy" CliExt.memcpySpec
  memcpyRO : HookSat ext "memcpy" CliExt.memcpyROSpec
  memmove : HookSat ext "memmove" CliExt.memmoveSpec
  memset : HookSat ext "memset" CliExt.memsetSpec
  timeAdd : HookSat ext timeAddHookName timeAddSpec
  durationSinceEpoch : HookSat ext durationSinceHookName CliExt.durationSinceEpochSpec

theorem cliEncHooksExt_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CliExternsOk P A ext) : CliEncHooksExt P.C A S ext where
  toTripleRatchetHooks := ⟨hOk.alloc, hOk.allocZeroed, hOk.aesEnc, hOk.aesDec,
    hOk.formatInner, hOk.fmtWrite⟩
  shim := hOk.shim
  memcpy := hOk.memcpy
  memcpyRO := hOk.memcpyRO
  memmove := hOk.memmove
  memset := hOk.memset
  timeAdd := hOk.timeAdd
  durationSinceEpoch := hOk.durationSince

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
