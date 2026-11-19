/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `MessageEncrypt` Finish Segment (`segFinish_ok`)

Verifies `StoredStateV → outcome` (`+0xe88..+0xfac` and result-write tail `+0x5f8..+0x660`): drops
the stored `SessionRecord`, stages the 248-byte `Ok` `CiphertextMessage`, writes `sret`, and returns.
-/

public section

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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
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

theorem prev_hdr_378_weaken (sp prevCap prevPtr : BitVec 64) :
    ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378 ⊢
    memRegion (sp + 0x110#64) 0x390 := by
  have hhdr :
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64)) =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] := by
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hhdr_mem :
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ⊢
        memRegion (sp + 0x110#64) 0x18 :=
    words64At_entails_memRegion (sp + 0x110#64) [prevCap, prevPtr, 0#64] (by simp)
  have hjoin :
      memRegion (sp + 0x110#64) 0x390 =
        memRegion (sp + 0x110#64) 0x18 ∗ memRegion (sp + 0x128#64) 0x378 :=
    memRegion_split' (b := sp + 0x110#64) (b' := sp + 0x128#64) (n := 0x18) (k := 0x378)
      (by decide) (by bv_omega) (by decide)
  have hlhs :
      ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378 =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ∗ memRegion (sp + 0x128#64) 0x378 := by
    rw [← hhdr]; ac_rfl
  rw [hlhs, hjoin]
  exact sepConj_mono_left hhdr_mem

theorem mid_280_to_4a0_weaken (sp : BitVec 64) (k : IdentityKey)
    (w0 w1 w2 w3 : BitVec 64) (bws : List (BitVec 64)) (hbws : bws.length = 27) :
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
      words64At (sp + 0x390#64) bws ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      memRegion (sp + 0x46a#64) 0x36 ⊢
    memRegion (sp + 0x280#64) 0x220 := by
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have h350 : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 :=
    Entails.trans (ProofLib.pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList)
      (Entails.of_eq (congrArg (memRegion (sp + 0x350#64)) (List.Vector.toList_length _)))
  have h370 : words64At (sp + 0x370#64) [w0, w1, w2, w3] ⊢ memRegion (sp + 0x370#64) 0x20 :=
    words64At_entails_memRegion (sp + 0x370#64) [w0, w1, w2, w3] (by simp)
  have h390 : words64At (sp + 0x390#64) bws ⊢ memRegion (sp + 0x390#64) 0xd8 := by
    have hlen : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [hlen]
    exact words64At_entails_memRegion (sp + 0x390#64) bws (by omega)
  have h468 : ((sp + 0x468#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x468#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_intro 0#8
  have h469 : ((sp + 0x469#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_intro 0#8
  have hjoin :
      memRegion (sp + 0x280#64) 0x220 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 200 ∗
            (memRegion (sp + 0x350#64) 0x20 ∗
              (memRegion (sp + 0x370#64) 0x20 ∗
                (memRegion (sp + 0x390#64) 0xd8 ∗
                  (memRegion (sp + 0x468#64) 1 ∗
                    (memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x36)))))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (n := 8) (k := 0x218)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x350#64) (n := 200) (k := 0x150)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x350#64) (b' := sp + 0x370#64) (n := 0x20) (k := 0x130)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x390#64) (n := 0x20) (k := 0x110)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x468#64) (n := 0xd8) (k := 0x38)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x468#64) (b' := sp + 0x469#64) (n := 1) (k := 0x37)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x469#64) (b' := sp + 0x46a#64) (n := 1) (k := 0x36)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono h280 (sepConj_mono_right (sepConj_mono h350
    (sepConj_mono h370 (sepConj_mono h390 (sepConj_mono h468 (sepConj_mono_left h469))))))

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
