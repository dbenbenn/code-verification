/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinish
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# CLI `SegFinish` Proof on `trTrapProgAt`

Proves `segFinish_okV_trap` (`Stored` at `+0xe88` → outcome) on `trTrapProgAt`.
-/

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

private theorem encModelOk_priv {C : Crypto} {S : SpqrModel} :
    EncModelOkStmt C S uuidTryParse := by
  rintro x r sess otr taken k m otr' c ⟨hcur, -, hfrom, hrem, hstep5⟩
  unfold EncEncryptStep at hstep5
  cases hp : sess.pendingPreKey with
  | none =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp]⟩
  | some items =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, hts, hexp, hlt, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp, hts, hexp, hlt, Option.bind]⟩

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
