/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefused
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4RemovePreKey
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Stage P4 Composition with `calleeSavedVRegs` Preservation

Extends the kit-generic Stage P4 theorems (`stageP4_some_v1_vregs_kits_ok`,
`stageP4_v1_vregs_kits_ok`, and E-kit corollaries) with `calleeSavedVRegs` (`D8..D15`)
preservation alongside `ClosureCalleeSavedP4` (`X19..X29`), yielding `CalleeSavedPreserved s0 sf`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

private theorem sepConj_assoc5 (a b c d e f : SepProp) :
    (a ∗ b ∗ c ∗ d ∗ e) ∗ f = a ∗ b ∗ c ∗ d ∗ e ∗ f := by
  simp only [sepConj_assoc]

/-! ## Stage P4 for `opkId? = some opkId` -/

/-- Combines `ClosureCalleeSavedP4 s0 sf` (`x19`–`x29`) with `calleeSavedVRegs sf = calleeSavedVRegs s0`
(`D8`–`D15`) into `CalleeSavedPreserved s0 sf`. -/
theorem _root_.CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.ClosureCalleeSavedP4.toCalleeSavedPreserved
    {s0 sf : State} (hcs : ClosureCalleeSavedP4 s0 sf)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, _⟩
  exact ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
