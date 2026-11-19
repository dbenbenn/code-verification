/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segPreKey` Encryption and `PreKeySignalMessage` Tail (`+0x8b4..+0xa70`)

Composes the `OTR::encrypt` call and error branch (`SegPreKeyTailEncrypt`) with the
`PreKeySignalMessage::new` call and 248-byte result copy (`SegPreKeyTailBuildMessage`) to reach
`CmState` at `+0xa70` from `PreKeyEncryptState` (`+0x8b4`).
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

abbrev preKeyEncryptScratch := preKeyEncryptScratch'
abbrev pollPreKeyEncrypt := pollE6c'
end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

