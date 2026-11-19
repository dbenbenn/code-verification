/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSessionProof
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Stage P4 Outcome Branches, `+0x3cc` Tail, and `none` OPK Arm

Defines the five-way outcome classification `StageP4RawBranch` / `StageP4Branch` (`ok`, `saveErr`,
`markErr`, `removeErr`, `storeErr`), the shared `+0x3cc → exit` `store_session` wrapper
`stageP4_at_3cc_kits`, and `stageP4_none_v1_kits_ok` (`opkId? = none`, skipping `remove_pre_key`).
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

/-! ## Five-way outcome classification -/

/-- Focus a `SepWPp` precondition `P` into `T ∗ F`, letting `(by ...; sep_focus)` infer `F`. -/
theorem SepWPp.focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = T ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hfoc ▸ h

/-- Drop a left factor `Drop` while simultaneously focusing the remaining assertion into `T ∗ F`. -/
theorem SepWPp.drop_focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P P' T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hp : P ⊢ P') (hfoc : P' = (Drop ∗ T) ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.drop_pre_of_entails (by rw [← sepConj_assoc]; exact hfoc ▸ hp) h

/-- Swap a non-adjacent sub-factor `A = B` on `P'` via `sep_focus`, then focus `B ∗ R` into
    `(Drop ∗ T) ∗ F` and drop `Drop`. -/
theorem SepWPp.drop_swap_focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {A B R Drop P P' T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hp : P ⊢ P') (hab : A = B)
    (hfoc1 : P' = A ∗ R)
    (hfoc2 : B ∗ R = (Drop ∗ T) ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.drop_focus_pre hp (by rw [hfoc1, hab, hfoc2]) h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
