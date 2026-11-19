/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# CLI Self-Identity and Full Identity Store Kit

Extends `cliIdentityStoreSpec` with `CliIdOwnInv` on `g.own` (`cliIdStoreSpecFull` and
`cliIdSelfSpecFull`) so that peer callbacks (`IdentityStoreKitOkIE`) and self-identity callbacks
(`IdentitySelfStoreKitOkI`) share a single `IdentityStoreSpec`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

/-! ## 1. Self-Directory Invariant (`CliIdOwnInv`) & Full `IdentityStoreSpec` -/

/-- Pure invariant on `g.own` (`IdentityFiles.own`) needed by `idKeyPairPollSpec` and
`idRegIdPollSpec`. Preserved across `save_identity` and `is_trusted_identity` because neither
callback modifies `g.own`. -/
structure CliIdOwnInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (own : DirGhost) : Prop where
  ownPathLt : own.path.length < 2 ^ 32
  kpPathOk : pathOk (pathOf own.path (utf8 "identity-key-pair"))
  regPathOk : pathOk (pathOf own.path (utf8 "registration-id"))
  kpSizeOk : ∀ bs, own.get rd F0 (utf8 "identity-key-pair") = .ok bs → bs.length < 2 ^ 32

/-- Full `IdentityFiles` store predicate combining `CliIdOwnInv` on `g.own` with `cliIdStoreAt`. -/
@[expose] def cliIdStoreAtFull (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost) (self : BitVec 64) (g : IdGhost) :
    SepProp :=
  ⌜CliIdOwnInv rd F0 pathOk g.own⌝ ∗ cliIdStoreAt A rd F0 pathOk peer self g

/-- Full `IdentityStoreSpec` equipping `cliIdentityStoreSpec` with `cliIdStoreAtFull`. -/
@[expose] def cliIdStoreSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat) : IdentityStoreSpec A b :=
  { cliIdentityStoreSpec A b rd F0 pathOk peer trustShimStk trustPollStk saveShimStk savePollStk with
    identityAt := cliIdStoreAtFull A rd F0 pathOk peer }

/-- Full `IdentitySelfStoreSpec` over `cliIdStoreSpecFull`. -/
@[expose] def cliIdSelfSpecFull (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat}
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec (cliIdStoreSpecFull A b rd F0 pathOk peer t1 t2 t3 t4) where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := CliSelfSpeErr
  RegIdErr := CliSelfSpeErr
  kpErr := cliSelfSpeErrSpec A
  regIdErr := cliSelfSpeErrSpec A
  kpRel := cliKpRel rd F0
  regIdRel := cliRegIdRel rd F0
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := 0#64
  kpFutVtOff := 0#64
  kpPollOff := 0#64
  kpFutDropOff := cliIdFutDropOff
  regIdShimOff := 0#64
  regIdFutVtOff := 0#64
  regIdPollOff := 0#64
  regIdFutDropOff := cliIdFutDropOff
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := kpShimStk
  kpPollStack := kpPollStk
  regIdShimStack := regIdShimStk
  regIdPollStack := regIdPollStk
  kpBoxAt := idOwnFutBoxAt
  regIdBoxAt := idOwnFutBoxAt
  kpBoxAt_memRegion := idOwnFutBoxAt_memRegion
  regIdBoxAt_memRegion := idOwnFutBoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  regIdFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
