/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segSignal` Argument Setup Before `OTR::encrypt` (`+0x348..+0x3a0`)

Steps from `SegSignalAckStateV` (`+0x348`, after the pre-key items getter returned `None`) through
key/OTR pointer spills and argument setup to `SegSignalEncStateV` at `OTR::encrypt`'s entry.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

theorem segSignal_focusR' {m : Memory} {B T G F : SepProp} (R : SepProp) (hB : B = T ∗ G)
    (hG : G = R ∗ F) (hm : m ⊨ B) : m ⊨ T ∗ (F ∗ R) := by
  subst hB hG
  rwa [sepConj_comm R F] at hm

theorem segSignal_peel8 {m : Memory} {B G : SepProp} (a : BitVec 64) (hB : B = memRegion a 8 ∗ G)
    (hm : m ⊨ B) : ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ G := by
  subst hB
  rw [ProofLib.memRegion_eight, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

theorem segSignal_peel4 {m : Memory} {B G : SepProp} (a : BitVec 64) (hB : B = memRegion a 4 ∗ G)
    (hm : m ⊨ B) : ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ G := by
  subst hB
  rw [ProofLib.memRegion_four, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
