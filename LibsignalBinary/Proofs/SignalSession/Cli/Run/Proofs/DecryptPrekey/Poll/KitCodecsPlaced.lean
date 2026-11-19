/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.RecordCodecs.Assembly
import LibsignalBinary.Proofs.RecordCodecs.SignedAssembly
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.Deps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.MuslStage1Init
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
public import VerifiedLibraries.Musl.Proofs.MemsetProof
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Relocatable `[LibsignalPlacement]` CLI Record Decoders

Instantiates `[LibsignalPlacement]` record decoders (`preKeyRecord_deserialize_placed_ok_of_hooks`,
`identityKeyPair_tryFrom_placed_ok_of_hooks`, `identityKey_decode_placed_ok_of_hooks`,
`decodeKyberPreKeyPlacedSpec`, and `decodeSignedPreKeyPlacedSpec`) at `cliExternsPlaced mmpl W`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecs.Placed
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.Slots
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

set_option maxRecDepth 200000

/-! ## 1. Record Decoders at `cliGhostExterns g (cliExternsPlaced mmpl W)` and `E2E.HooksE.A0` -/

theorem cliPreKeyDeserialize_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_65 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_65).base
      (preKeyDeserializePlacedSpec E2E.HooksE.A0) :=
  Assembly.preKeyRecord_deserialize_placed_ok_of_hooks hh.codecHooks

theorem cliIdentityKeyPairTryFrom_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_84 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_84).base
      (identityKeyPairTryFromPlacedSpec E2E.HooksE.A0) :=
  Assembly.identityKeyPair_tryFrom_placed_ok_of_hooks hh.codecHooks

theorem cliIdentityKeyDecode_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (lsProg_18 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_18).base
      (identityKeyDecodePlacedSpec E2E.HooksE.A0) :=
  Assembly.identityKey_decode_placed_ok_of_hooks (cliGhostExterns g (cliExternsPlaced mmpl W))

theorem cliDecodeKyberPreKey_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hH : SignedHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (d : SignedPortDepsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_595 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_595).base
      (decodeKyberPreKeyPlacedSpec E2E.HooksE.A0) :=
  SignedAssembly.decodeKyberPreKey_placed_ok hH d

theorem cliDecodeSignedPreKey_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    (hH : SignedHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (d : SignedPortDepsPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok (lsProg_595 (cliGhostExterns g (cliExternsPlaced mmpl W))) (blkPl_595).base
      (decodeSignedPreKeyPlacedSpec E2E.HooksE.A0) :=
  SignedAssembly.decodeSignedPreKey_placed_ok hH d

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
