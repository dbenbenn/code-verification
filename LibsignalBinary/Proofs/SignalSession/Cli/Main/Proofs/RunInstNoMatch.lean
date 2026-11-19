/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliPqBinaryProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefs
import LibsignalBinary.Proofs.SignalSession.Cli.CliExternsWitness -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatch -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.CommitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Non-Matching Pre-Key (`NoMatch`) `main`-Level Instantiation & ELF Bridges

Wires `cliRunSemD2c` (`decPkDefD2c`, `DecPkOkD2c`) into `mainSpecTight`, establishing the unified
6-clause PQXDH + non-matching pre-key `recv` specification (`MainOkPqAllTight`, `MainOkOverNormTight`),
per-input ELF bridges under `RunAllocOk`, unconditional `cliImg` instantiations, and `CliExternsOk`
generalizations.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Concrete D2(c)-extended `RunSem` at `Slots.scopeIn`, using `decPkDefD2c` and `DecPkOkD2c`. -/
@[expose] noncomputable def cliRunSemD2c (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSem X W
    (decPkDefD2c X ⟨W.C, W.Q⟩ Slots.scopeIn)
    (DecPkOkD2c ⟨W.C, W.Q⟩ Slots.scopeIn)
    Pksm.pksmParse

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen

/-! ## 1. Tightened 6-Clause & `ObservedExceptNorm` `main`-Level Specifications -/

/-- Clause 6 (`NoMatch`) of `MainOkPqAllTight` / `MainOkPqAll`: on a `PqxdhPartyInSpecDomain` state
`st` whose current session `st.session = some (x₀, g₀)` does not match `m`
(`¬ PqSessionMatches x₀ g₀ m`), `Run` agrees with `pqRecvPrekeyModel X WP { st with session := none } m rc`
with exact 2-session outcome `d2cObserve`, canonical-path `ObservedExceptNorm` outside
`sessionFile (partyAddress st.party.other)`, and `Cli.CommitOk`. -/
@[expose] def MainOkNoMatchClause (WP : PEParams) (X : UnreachedPqxdhPrimitives)
    (Run : Inputs → Cli.RunAnswer → Prop) (st : PqParty) : Prop :=
  ∀ (x₀ : RecordExtras) (g₀ : GhostState (List (BitVec 8))) (m : PreKeyMessageFields) (rc : BitVec 256),
    st.session = some (x₀, g₀) →
    m.inner.length + 2048 < 2 ^ 32 →
    ¬ PqSessionMatches x₀ g₀ m →
    ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
      observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
        d2cObserve WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) st.party.other x₀ g₀
          (pqRecvPrekeyModel X WP { st with session := none } m rc) ∧
      ObservedExceptNorm WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (sessionFile (partyAddress st.party.other))
        (pqRecvPrekeyModel X WP { st with session := none } m rc)
        (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
      Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)

open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- `PEParams`-parameterized D2(c) `RunSem` (`cliRunSemD2c` without `CliHooks`). -/
@[expose] noncomputable def Cli.MainHops.cliRunSemD2cExt (X : UnreachedPqxdhPrimitives) (P : PEParams) : RunSem where
  encrypt := encDef P Cli.Slots.scopeIn
  decryptSignal := decSigDef P Cli.Slots.scopeIn
  initiate := initDef X P
  decryptPrekey := decPkDefD2c X P Cli.Slots.scopeIn
  pksmParse := Pksm.pksmParse
  filesOk := Cli.Slots.filesOk₀ Cli.Slots.scopeIn (fun _ => True)
  encOk := Cli.Slots.encOk₀ Cli.Slots.scopeIn
  initOk := InitOk₀ P
  decPkOk := DecPkOkD2c P Cli.Slots.scopeIn

theorem Cli.MainHops.cliRunSemD2c_eq (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    cliRunSemD2c X W = Cli.MainHops.cliRunSemD2cExt X ⟨W.C, W.Q⟩ := rfl

/-- 5-clause PQXDH body (`abbrev` so `Cli.MainOkCliPqTightExt` is `rfl`-equal to
`ProcessOomExt.MainOkCliPqTightExt`). -/
abbrev Cli.MainHops.PqFiveClausesD2cExt (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (Run : Inputs → Cli.RunAnswer → Prop) (st : PqParty) : Prop :=
  (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
    ∃ a, Run (pqInitInputs P st b t) a ∧
      observe (pqInitInputs P st b t).files a =
        pqxdhExpectedOutcome P (pqInitInputs P st b t) (pqInitModel X P st b t) ∧
      Cli.CommitOk (pqInitInputs P st b t) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
    ∃ a, Run (pqSendInputs P st m r) a ∧
      observe (pqSendInputs P st m r).files a =
        pqxdhExpectedOutcome P (pqSendInputs P st m r) (pqSendModel P st m r.toList) ∧
      Cli.CommitOk (pqSendInputs P st m r) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
    ∃ a, Run (pqRecvInputs P st (wireWhisper :: c) rc) a ∧
      observe (pqRecvInputs P st (wireWhisper :: c) rc).files a =
        pqxdhExpectedOutcome P (pqRecvInputs P st (wireWhisper :: c) rc) (pqRecvWhisperModel P st c rc) ∧
      Cli.CommitOk (pqRecvInputs P st (wireWhisper :: c) rc) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    ∃ a, Run (pqRecvInputs P st (wirePrekey :: m.bytes) rc) a ∧
      observe (pqRecvInputs P st (wirePrekey :: m.bytes) rc).files a =
        pqxdhExpectedOutcome P (pqRecvInputs P st (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X P st m rc) ∧
      Cli.CommitOk (pqRecvInputs P st (wirePrekey :: m.bytes) rc) (Cli.MainResult.ofAnswer a)) ∧
  (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    ∃ a, Run (pqRecvInputs P st c rc) a ∧
      observe (pqRecvInputs P st c rc).files a =
        .exited 1 [] (filesOf (pqRecvInputs P st c rc).files) ∧
      Cli.CommitOk (pqRecvInputs P st c rc) (Cli.MainResult.ofAnswer a))

end CryptoVerification.SignalSession
