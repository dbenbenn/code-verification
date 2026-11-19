/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.RecordX.BridgeCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

/-!
# Widened record scope `DeserializeScopeX` and reachability

**Checked by Lean.** Widens `DeserializeGeneral.SessionScope` to `SessionScopeX` and
`DeserializeScopeX` (allowing `aliceBaseKey` and a zero-ID pending Kyber ciphertext of length
`< 2 ^ 16`), characterizes `SessionScope` as the empty-extras special case, and proves that every
reachable state under `FixedIdRecordExtras` lies in `DeserializeScopeX`.
-/

public section

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E CryptoVerification.E2E.Record

/-- The current session of `toRecord (extrasOf E) g`. -/
@[expose] def sessionOfX (E : Party → RecordExtras) (g : GhostState Bytes) : Session Bytes :=
  { state := g.session
    pendingPreKey := if g.session.pendingPreKey then some (E g.party).pending else none
    pendingKyberPreKey := if g.session.pendingPreKey then (E g.party).kyber else none
    localRegistrationId := (E g.party).localRegistrationId
    remoteRegistrationId := (E g.party).remoteRegistrationId
    aliceBaseKey := (E g.party).aliceBaseKey }

theorem toRecord_extrasOf_eq (E : Party → RecordExtras) (g : GhostState Bytes) :
    toRecord (extrasOf E) g = { currentSession := some (sessionOfX E g) } := rfl

theorem sessionOfX_wf (E : Party → RecordExtras) (g : GhostState Bytes) :
    (sessionOfX E g).Wf := by
  unfold sessionOfX Session.Wf
  cases g.session.pendingPreKey <;> rfl

/-- Widened session scope allowing `aliceBaseKey` and a zero-ID pending Kyber ciphertext of length `< 2 ^ 16`. -/
@[expose] def SessionScopeX (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    s.localRegistrationId = 0 ∧ s.remoteRegistrationId = 0 ∧
    (∀ p, s.pendingPreKey = some p → p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.preKeyId = 0 ∧ k.ciphertext.length < 2 ^ 16) ∧
    s.aliceBaseKey.length < 2 ^ 16

/-- `DeserializeGeneral.SessionScope` is `SessionScopeX` with no Kyber pre-key and an empty `alice_base_key`. -/
theorem sessionScope_iff (s : Session Bytes) :
    DeserializeGeneral.SessionScope s ↔
      SessionScopeX s ∧ s.pendingKyberPreKey = none ∧ s.aliceBaseKey = [] := by
  unfold DeserializeGeneral.SessionScope SessionScopeX
  constructor
  · rintro ⟨h1, hk, hl, hr, ha, hp⟩
    refine ⟨⟨h1, hl, hr, hp, ?_, ?_⟩, hk, ha⟩
    · intro k hk'; rw [hk] at hk'; cases hk'
    · rw [ha]; decide
  · rintro ⟨⟨h1, hl, hr, hp, _, _⟩, hk, ha⟩
    exact ⟨h1, hk, hl, hr, ha, hp⟩

/-- Widened record scope combining `InScope` with `SessionScopeX` on the current session. -/
@[expose] def DeserializeScopeX (r : SessionRecord Bytes) : Prop :=
  InScope r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeX s

theorem deserializeScope_iff (r : SessionRecord Bytes) :
    DeserializeGeneral.DeserializeScope r ↔
      DeserializeScopeX r ∧ ∀ s, r.currentSession = some s →
        s.pendingKyberPreKey = none ∧ s.aliceBaseKey = [] := by
  unfold DeserializeGeneral.DeserializeScope DeserializeScopeX
  constructor
  · rintro ⟨hin, s, hs, hsc⟩
    obtain ⟨hx, hk, ha⟩ := (sessionScope_iff s).1 hsc
    refine ⟨⟨hin, s, hs, hx⟩, ?_⟩
    intro s' hs'
    rw [hs] at hs'; cases hs'
    exact ⟨hk, ha⟩
  · rintro ⟨⟨hin, s, hs, hx⟩, h⟩
    exact ⟨hin, s, hs, (sessionScope_iff s).2 ⟨hx, h s hs⟩⟩

/-! ## Reachability of `DeserializeScopeX` -/

section Reach
variable (Z : EParams) (E : Party → RecordExtras) (hE : ∀ P, FixedIdRecordExtras (E P))
include hE

end Reach

end CryptoVerification.E2E.RecordX
