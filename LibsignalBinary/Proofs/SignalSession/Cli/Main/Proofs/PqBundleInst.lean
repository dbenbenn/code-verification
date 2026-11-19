/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj -- shake: keep
public import ProofLib.SepLogic.WPp -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec

/-!
# PQXDH Pre-Key Slot Bundle and `MainOkCliPq` / `MainOkCliSm` Instantiation

Packages concrete `PreKeySignalMessage::try_from` (`Pksm.pksmParse`) and `decrypt_prekey`
(`decPkDef`, `DecPkOk₀`) proofs into `CliPqPrekeyBundleS0`, discharging `MainOkCliSm`, `MainOkCliPq`,
and their tightened (`mainSpecTight`) and `CliExternsOk`-parameterized counterparts.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-- `cliDecryptPrekeyNeed cliRunBudgets` (`1,083,600`) fits within `runNeed_cli_le_resStack`'s
`4,194,304` (`4 MiB`) callee cap. -/
theorem cliDecryptPrekeyNeed_le : cliDecryptPrekeyNeed cliRunBudgets ≤ 4194304 := by
  decide

/-- `DecPkOk₀` holds on `pqRecvInputs` whenever `Pksm.pksmParse m.bytes = some pm`. -/
theorem decPkDomOk_cli (W : PEParams) (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256)
    (pm : PreKeySignalMessage)
    (hst : PqxdhPartyInSpecDomain W st)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m)
    (hparse : Pksm.pksmParse m.bytes = some pm) :
    DecPkOk₀ W Slots.scopeIn
      (runFiles (pqRecvInputs W st (wirePrekey :: m.bytes) rc))
      (addrValE st.party.other) (addrValE st.party) pm := by
  obtain ⟨i, hi, rfl⟩ := pksmParse_bytes_typed hm hparse
  exact decPkOk₀_pqRecv W Slots.scopeIn encodeInjOn_scopeIn
    (ratchetScopeCoversPq_scopeIn W) st m i rc hst hm hi hmatch

/-- `cliDecryptPrekeyNeed extRunBudgets` fits within `4,194,304` (`4 MiB`). -/
theorem cliDecryptPrekeyNeed_ext_le : cliDecryptPrekeyNeed extRunBudgets ≤ 4194304 := by
  decide

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.SignalSession
