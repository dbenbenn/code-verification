/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Seam Definitions for the `segPreKey` Tail (`+0x8b4` and `+0x8c8`)

Defines the intermediate states `PreKeyEncryptState'` (`+0x8b4`, after `kyberMap`) and
`PreKeyEncryptRetState` (`+0x8c8`, after `OTR::encrypt`) shared between `SegPreKeyTailEncrypt` and
`SegPreKeyTailBuildMessage`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

/-- Call scratch (`sp + 0x00 .. sp + 0x58`) at `+0x8b4`. -/
@[expose] def preKeyEncryptScratch' (sp : BitVec 64) (regId spk pkVal : BitVec 32) : SepProp :=
  memRegion sp 0x14 ∗
  ((sp + 0x14#64) ↦₃₂ regId) ∗
  memRegion (sp + 0x18#64) 0xc ∗
  ((sp + 0x24#64) ↦₃₂ spk) ∗
  memRegion (sp + 0x28#64) 0xc ∗
  ((sp + 0x34#64) ↦₃₂ pkVal) ∗
  ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
  ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Poll and staging region (`sp + 0x46a .. sp + 0xb80`) at `+0x8b4`. -/
@[expose] def pollE6c' (A : RustAlloc) (sp : BitVec 64) (kyBoxPtr : BitVec 64)
    (items : PendingPreKey) (kyber : Option PendingKyberPreKey) : SepProp :=
  memRegion (sp + 0x46a#64) 0x436 ∗
  optKyberAt A (sp + 0x8a0#64) kyBoxPtr
    (kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
  memRegion (sp + 0x8b8#64) 0x1fc ∗
  ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
  memRegion (sp + 0xad4#64) 0xac

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
