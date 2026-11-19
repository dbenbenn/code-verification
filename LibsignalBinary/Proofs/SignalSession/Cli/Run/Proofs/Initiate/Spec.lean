/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs

/-!
# Top-Level `signal_session_handshake::initiate` Slot Contract and Agreement Theorems

Exports `cliInitiate_ok`, `cliInitiate_slotOk`, `initOk₀_pqInit`, `pqInitiateAgrees_initDef`, and
the extern-parameterized slot lifts `cliInitiate_ext_slotOk_of_ok` and `cliInitiate_slotOk_of_ext`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose

/-- `InitOk₀` holds on `runFiles (pqInitInputs W st b t)` for any domain party `st` with `st.session = none`. -/
theorem initOk₀_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = none) :
    InitOk₀ W (runFiles (pqInitInputs W st b t)) (RunRefine.addrValE st.party.other)
      (RunRefine.addrValE st.party) := by
  exact InitS0.initOk₀_pqInit_proof W st b t hwf hs

/-- `PqInitiateAgrees S X W` holds whenever `S.initiate = initDef X W`. -/
theorem pqInitiateAgrees_initDef (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hS : S.initiate = initDef X W) : RunRefine.PqInitiateAgrees S X W := by
  exact InitS0.pqInitiateAgrees_initDef_proof S X W hS

/-! ## Extern-parameterized slot lifts -/

end CryptoVerification.SignalSession.Cli.RunProofs
