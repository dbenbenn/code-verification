/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Defs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# In-Memory Session Store State-Transition Relations

Pure state-update, answer, and trace relations (`inMemStoreUpdate`, `inMemLoadRel`,
`inMemStoreRel`, `inMemSessCallEvs`, `inMemSessTraceOf`) for `InMemSessionStore`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.InMem.SessionStoreImpl

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.InMem.HashbrownBin

/-- Answer relation for `load_session`: deterministically returns `.ok (some st.record)`. -/
@[expose] def inMemLoadRel (st : InMemSessState) (_rem : AddrVal)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) : Prop :=
  ans = .ok (some st.record)

/-- Answer relation for `store_session`: deterministically returns `.ok ()`. -/
@[expose] def inMemStoreRel (_st : InMemSessState) (_rem : AddrVal)
    (_r' : SessionRecord (List (BitVec 8))) (ans : Except Unit Unit) : Prop :=
  ans = .ok ()

/-- Per-call trace events when `SessionStore` is in-memory (`[]` on session ops) and
`IdentityKeyStore` emits external trust/save events. -/
def inMemSessCallEvs
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    StoreCall AddrVal (List (BitVec 8)) → List TraceEvent
  | .loadSession _ => []
  | .isTrustedIdentity rem k dir => [trustEvent rem k dir ans.isTrustedIdentity]
  | .saveIdentity rem k => [saveEvent rem k ans.saveIdentity]
  | .storeSession _ _ => []

end CryptoVerification.E2E.InMem.SessionStoreImpl
