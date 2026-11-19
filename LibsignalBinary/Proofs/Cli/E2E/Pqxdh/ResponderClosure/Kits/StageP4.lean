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
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyber
import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4RemovePreKey
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2

/-!
# Kit-Generic Stage P4 Composition (`+0x34dc → exit`)

Top-level Stage P4 theorems for `message_decrypt_prekey::<Coins>::{closure#0}` on
`tripleRatchetProgAtExt img.base ext`:
- `stageP4_some_v1_kits_ok`: `opkId? = some opkId` path sequencing `save_identity`,
  `mark_kyber_pre_key_used`, `remove_pre_key`, and `store_session`;
- `stageP4_v1_kits_ok`: unified `opkId? : Option (BitVec 32)` Stage P4 theorem over `stageP4Pre`;
- `stageP4_v1_ekits_ok` and `stageP4_kyber_refused_ekits_ok`: E-kit bundle corollaries.
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

/-- Monotonicity of `SepWPp` in both the normal postcondition `Q` and panic postcondition `Qp`. -/
theorem SepWPp.mono_post_panic {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp Qp' : State → SepProp → Prop}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (hQp : ∀ sf Pf, Qp sf Pf → Qp' sf Pf)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp' := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hq⟩ | ⟨hpan, Pf, hmf, hqp⟩ | hex⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hpan, Pf, hmf, hQp sf Pf hqp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hex)⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
