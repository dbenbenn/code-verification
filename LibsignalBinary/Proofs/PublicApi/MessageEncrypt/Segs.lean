/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# Segment Specifications for `session_message_encrypt_with_stores`

Defines the nine seam-to-seam segment propositions (`SegLoadSpecV` through `SegFinishSpecV`), the
shared environment `EncEnv` parameterized by record scope `Scope` and SPQR invariant `Q`, and the
public-entry wrapper statement `EntryWrapStmt`.

| Specification | Transition | Offset range |
| --- | --- | --- |
| `SegLoadSpecV` | Entry → `Cur` | `+0x000..+0x20c`, `+0x41c..+0x45c`, `+0x660..+0x680` |
| `SegFromSpecV` | `Cur` → `Otr` | `+0x20c..+0x2c8` |
| `SegIdentitySpecV` | `Otr` → `Key` | `+0x2c8..+0x344` |
| `SegSignalSpecV` | `Key` → `Cm` (`pendingPreKey = none`) | `+0x344..+0x41c`, `+0xa70` |
| `SegPreKeySpecV` | `Key` → `Cm` (`pendingPreKey = some _`) | `+0x344..+0x390`, `+0x680..+0xa70` |
| `SegTrustSpecV` | `Cm` → `Save` | `+0xa70..+0xab0`, `+0xb7c..+0xbd4`, `+0xc78..+0xd50` |
| `SegSaveSpecV` | `Save` → `Apply` | `+0xbd4..+0xc14`, `+0xd50..+0xd9c` |
| `SegApplyStoreSpecV` | `Apply` → `Stored` | `+0xd9c..+0xe88`, `+0xf2c..+0xf3c` |
| `SegFinishSpecV` | `Stored` → outcome | `+0xe88..+0xf2c`, `+0xf3c..+0xfac`, `+0x5f8..+0x660` |
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit


/-- Encryption-side projection of `RecordInScope`, omitting the decrypt-only
`remoteIdentity ≠ some localIdentity` condition while preserving conjunct positions. -/
@[expose] def RecordInScopeEnc (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    True ∧ SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

theorem _root_.CryptoVerification.LibsignalPublicApi.RecordInScope.toEnc
    {r : SessionRecord (List (BitVec 8))} (h : RecordInScope r) :
    RecordInScopeEnc r :=
  fun s hs => ⟨trivial, (h s hs).2⟩

instance (r : SessionRecord (List (BitVec 8))) : Coe (RecordInScope r) (RecordInScopeEnc r) :=
  ⟨RecordInScope.toEnc⟩

theorem StepsThroughEncrypt.inScope {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (hin : ∀ r, Scope r → RecordInScopeEnc r)
    (h : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    StepsThroughEncrypt RecordInScopeEnc C S uuidTryParse x r sess otr taken k m otr' :=
  ⟨h.1, hin r h.2.1, h.2.2⟩

/-- Pure postcondition agreement for the success path: given `StepsThroughEncrypt` and
`okAnswers r c`, `messageEncrypt` returns `Ok m` with RNG draw count `S.draws`. -/
@[expose] def EncModelOkStmt (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) : Prop :=
  ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange),
    StepsThroughEncrypt RecordInScopeEnc C S uuidParse x r sess otr taken k m otr' →
    x.model C S uuidParse (okAnswers r c) =
        (.ok m, [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending,
          .saveIdentity x.rem.val k, .storeSession x.rem.val (storedRecord sess otr' taken)]) ∧
      x.draws S (okAnswers r c) = S.draws otr.pqrState x.rest

/-- Closure of `kit.RecOk` under `messageEncrypt` updates on records in `kit.ScopeAt Scope st0`. -/
@[expose] def EncModelRecOk {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) : Prop :=
  ∀ (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (addr : AddrVal) (r' : SessionRecord (List (BitVec 8))),
    (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) →
    .storeSession addr r' ∈ (x.model C S uuidParse answers).2 →
    kit.RecOk r'

theorem recOk_of_encModelRecOk {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    (hmodel : EncModelOkStmt C S uuidTryParse)
    (hin : ∀ {rem} r, kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hrec : EncModelRecOk kit st0 Scope C S uuidTryParse)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr') :
    kit.RecOk (storedRecord sess otr' taken) := by
  have h15' := h15.inScope (fun r₀ hr₀ => hin r₀ hr₀)
  have hm := (hmodel x r sess otr taken k m otr' .newOrUnchanged h15').1
  apply hrec x (okAnswers r .newOrUnchanged) x.rem.val (storedRecord sess otr' taken)
  · intro r₀ hr₀
    cases hr₀
    exact h15.2.1
  · rw [hm]
    simp

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
