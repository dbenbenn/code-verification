/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# CLI `MessageDecrypt` Seam States and Segment Specifications

Defines seam program counters, intermediate states, and the twelve segment specifications for
`signal_session_ratchet::decrypt_signal` on the CLI image, together with `_trap` hypotheses at
`trTrapProgAt`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSessionApi

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Seam program counters -/

/-- Decrypt hook bundle (`TripleRatchetHooks` plus `stringClone`) at `ext`. -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  stringClone : HookSat ext stringCloneHookName (stringCloneSpec A)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_tripleRatchetHooks_trap
    {C : Crypto} {A : RustAlloc} {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs)
    (hSC : HookSat abs stringCloneHookName (stringCloneSpec A)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap C A S (trTrapExterns C abs) where
  alloc :=
    { alloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.alloc
      dealloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.dealloc
      realloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.realloc }
  allocZeroed := hookSat_trTrapExterns (by decide) (by decide) hH.allocZeroed
  aesEnc := hookSat_trTrapExterns (by decide) (by decide) hH.aesEnc
  aesDec := hookSat_trTrapExterns (by decide) (by decide) hH.aesDec
  formatInner := hookSat_trTrapExterns (by decide) (by decide) hH.formatInner
  fmtWrite := hookSat_trTrapExterns (by decide) (by decide) hH.fmtWrite
  stringClone := hookSat_trTrapExterns (by decide) (by decide) hSC

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_noStores_trap
    {C : Crypto} {A : RustAlloc} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : StoreKit.Identity.PublicApiHooksNoStores C A S abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap C A S (trTrapExterns C abs) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_tripleRatchetHooks_trap
    h.toTripleRatchetHooks h.stringClone

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
