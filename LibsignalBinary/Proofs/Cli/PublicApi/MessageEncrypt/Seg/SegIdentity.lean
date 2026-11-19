/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentity -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentityFetch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import ProofLib.RegChain
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI `SegIdentity` Proof (`Otr` → `Key`)

Proves `segIdentity_okV` (`+0x2c8..+0x344`), extracting `remote_identity_key` from the current
`SessionState` and transitioning from `Otr` (`+0x2c8`) to `Key` (`+0x344`) or the missing-key
error tail.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

private theorem exists_pointsTo16_of_memRegion2 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 2 ∗ R) :
    ∃ v : BitVec 16, m ⊨ (a ↦₁₆ v) ∗ R := by
  rw [memRegion_split a 1 1 (by decide), ProofLib.memRegion_one a,
      ProofLib.memRegion_one (a + 1#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨b0, b1, hm⟩ := hm
  rw [pointsTo8_pair] at hm
  exact ⟨_, hm⟩

private theorem pointsTo16_entails_memRegion2 (a : BitVec 64) (v : BitVec 16) :
    (a ↦₁₆ v) ⊢ memRegion a 2 := by
  rw [pointsTo16_split8 a v, memRegion_split a 1 1 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

private theorem exists_pointsTo32_of_memRegion4 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 4 ∗ R) :
    ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [ProofLib.memRegion_four a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem exists_pointsTo64_of_memRegion8 (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 8 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
