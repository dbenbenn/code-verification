/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.Scope -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.RecordX.Length

/-!
# PQXDH decoder scope `DeserializeScopeP` and reachability

**Checked by Lean.** Defines the PQXDH record decoder scopes `SessionScopeP`, `DeserializeScopeP`,
and `DeserializeScopeBounded` (arbitrary `u32` registration and pre-key IDs, `timestamp = 0`,
1569-byte ML-KEM-1024 ciphertext, empty or 33-byte `aliceBaseKey`, and arbitrary identity pairs),
and proves that reachable states under `ExtrasPqxdh` satisfy `DeserializeScopeP`.
-/

public section

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession

/-- PQXDH extras invariant: `pending.timestamp = 0`, 1569-byte Kyber ciphertext (if present), and empty or 33-byte `aliceBaseKey`. -/
@[expose] def ExtrasPqxdh (x : RecordExtras) : Prop :=
  x.pending.timestamp = 0 ∧
    (∀ k, x.kyber = some k → k.ciphertext.length = 1569) ∧
    (x.aliceBaseKey = [] ∨ x.aliceBaseKey.length = 33)

end CryptoVerification.E2E

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)

/-- PQXDH decoder session scope: bounded `receiverChains`, `timestamp = 0`, 1569-byte Kyber ciphertext, and empty or 33-byte `aliceBaseKey`. -/
@[expose] def SessionScopeP (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569) ∧
    (s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33)

/-- `RecordInScope` without the `remoteIdentity ≠ some localIdentity` side condition. -/
@[expose] def RecordInScopeP (r : SessionRecord Bytes) : Prop :=
  ∀ s, r.currentSession = some s →
    SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

/-- `InScope` without `s.state.remoteIdentity ≠ some s.state.localIdentity`. -/
@[expose] def InScopeP (r : SessionRecord Bytes) : Prop :=
  RecordInScopeP r ∧ RecordPqEmpty r ∧ RecordRepr r

/-- PQXDH decoder record scope combining `InScopeP` with `SessionScopeP` on the current session. -/
@[expose] def DeserializeScopeP (r : SessionRecord Bytes) : Prop :=
  InScopeP r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeP s

theorem recordInScopeP_of_recordInScope {r : SessionRecord Bytes} (h : RecordInScope r) :
    RecordInScopeP r :=
  fun s hs => (h s hs).2

theorem inScopeP_of_inScope {r : SessionRecord Bytes} (h : InScope r) : InScopeP r :=
  ⟨recordInScopeP_of_recordInScope h.1, h.2⟩

/-- Selects `partyIdentityKey .A` or `partyIdentityKey .B` distinct from `rem`. -/
@[expose] def freshLocalId (rem : Option IdentityKey) : IdentityKey :=
  if rem = some (partyIdentityKey .A) then partyIdentityKey .B else partyIdentityKey .A

theorem remoteIdentity_ne_freshLocalId (rem : Option IdentityKey) :
    rem ≠ some (freshLocalId rem) := by
  unfold freshLocalId
  split_ifs with h
  · rw [h]; decide
  · exact h

theorem sessionScopeP_of_sessionScope {s : Session Bytes} (h : DeserializeGeneral.SessionScope s) :
    SessionScopeP s := by
  obtain ⟨h1, hk, _, _, ha, hp⟩ := h
  refine ⟨h1, ?_, ?_, Or.inl ha⟩
  · intro p hp'
    exact (hp p hp').2.2
  · intro k hk'; rw [hk] at hk'; cases hk'

theorem deserializeScopeP_of_deserializeScope {r : SessionRecord Bytes} (h : DeserializeGeneral.DeserializeScope r) : DeserializeScopeP r := by
  obtain ⟨hin, s, hs, hsc⟩ := h
  exact ⟨inScopeP_of_inScope hin, s, hs, sessionScopeP_of_sessionScope hsc⟩


/-- Bounded-extras session scope unifying `SessionScopeX`, `SessionScopeP`, and `DeserializeGeneral.SessionScope`:
at most `maxReceiverChains` receiver chains, `timestamp = 0` on any pending pre-key,
`aliceBaseKey.length < 2 ^ 16`, and `ciphertext.length < 2 ^ 16` on any pending Kyber pre-key. -/
@[expose] def SessionScopeBounded (s : Session Bytes) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ p, s.pendingPreKey = some p → p.timestamp = 0) ∧
    (∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 16) ∧
    s.aliceBaseKey.length < 2 ^ 16

/-- Bounded-extras record scope unifying `DeserializeScopeX`, `DeserializeScopeP`, and `DeserializeGeneral.DeserializeScope`. -/
@[expose] def DeserializeScopeBounded (r : SessionRecord Bytes) : Prop :=
  InScopeP r ∧ ∃ s, r.currentSession = some s ∧ SessionScopeBounded s

theorem sessionScopeBounded_of_sessionScopeX {s : Session Bytes} (h : SessionScopeX s) :
    SessionScopeBounded s := by
  obtain ⟨hc, _, _, hp, hk, ha⟩ := h
  exact ⟨hc, fun p hp' => (hp p hp').2.2, fun k hk' => (hk k hk').2, ha⟩

theorem sessionScopeBounded_of_sessionScopeP {s : Session Bytes} (h : SessionScopeP s) :
    SessionScopeBounded s := by
  obtain ⟨hc, hp, hk, ha⟩ := h
  refine ⟨hc, hp, fun k hk' => ?_, ?_⟩
  · rw [hk k hk']; decide
  · rcases ha with ha | ha <;> rw [ha] <;> decide

theorem deserializeScopeBounded_of_deserializeScopeP {r : SessionRecord Bytes} (h : DeserializeScopeP r) :
    DeserializeScopeBounded r := by
  obtain ⟨hin, s, hs, hsc⟩ := h
  exact ⟨hin, s, hs, sessionScopeBounded_of_sessionScopeP hsc⟩

/-! ## Reachability of `DeserializeScopeP` -/

section Reach
variable (Z : EParams) (E : Party → RecordExtras) (hE : ∀ P, ExtrasPqxdh (E P))
include hE

end Reach

end CryptoVerification.E2E.RecordX
