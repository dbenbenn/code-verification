/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `signal_session_io::read_file` Contracts

Establishes `HookOk` for `readFileHook` against `readFileSpecPlaced` and lifts `HookSat` at
`lsReadFileSym` to `subroutine_ok` on any caller block under `[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.E2E.HooksE.HooksOkAux

theorem cliReadFilePlaced_hookSat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hRead : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  hRead

/-- Lifts `HookSat` at `lsReadFileSym` to `subroutine_ok` for `readFileSpecPlaced` under `[LibsignalPlacement]`. -/
theorem cliReadFilePlaced_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  hRead

theorem cliReadFilePlaced_rocl_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (cliReadFilePlaced_ok mmpl g W stk hRead)

end CryptoVerification.SignalSession.Cli.RunSkeleton
