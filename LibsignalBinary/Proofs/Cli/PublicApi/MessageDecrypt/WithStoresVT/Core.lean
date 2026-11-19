/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegBatch1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegRegionNoneExt
import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.StoreCallSite
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSaveAux
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExt
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExt
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge

/-!
# Ext-Generic Token-Framed `MessageDecrypt` Assembly (`WithStoresVT.Core`)

Assembles the twelve `MessageDecrypt` segments at `tripleRatchetProgAtExt img.base ext` for:
- `withStoresDecSpecVTP`: tight-panic (`Extra := fun _ _ => False`), weak-precondition
  (`RecordInScopeP` and `IdOrDistinctSid`) specification with `TokenInit img` framed across
  `recordDecryptSpecTPTight`;
- `withStoresDecSpecVT`: `TokenInit img` framed over `withStoresDecSpecV` across `recordDecryptSpecT`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.MessageDecrypt


/-! ## `TrapsOnly` transfer for `region_ok` -/

theorem region_ok_of_trapsOnly {α : Type} {P₁ P₂ : Program} {entry exit : BitVec 64}
    {spec : Spec α} (htr : TrapsOnly P₁ P₂)
    (h : region_ok P₁ entry exit spec) :
    region_ok P₂ entry exit spec := by
  intro x R s0 hpc hrun hpre hL₂
  have hL₁ : P₁.CodeLoaded s0.mem := CodeLoaded_of_trapsOnly htr hL₂
  obtain ⟨sf, hsteps, hout⟩ := h x R s0 hpc hrun hpre hL₁
  rcases hout with ⟨hpc_sf, hrun_sf, hpost⟩ | ⟨hpan_sf, honp⟩
  · exact ⟨sf, Steps.of_trapsOnly htr hsteps (.of_running hrun_sf),
      Or.inl ⟨hpc_sf, hrun_sf, hpost⟩⟩
  · exact ⟨sf, Steps.of_trapsOnly htr hsteps (.of_panicked hpan_sf),
      Or.inr ⟨hpan_sf, honp⟩⟩

/-! ## `IdOrDistinctSid`, `withStoresDecSpecVT`, and `withStoresDecSpecVTP` -/

/-- Identity/service-ID guard required by `recordDecryptSpecP`: every loaded in-scope current
session has `remoteIdentity ≠ some localIdentity`, or `loc` and `rem` satisfy `DistinctSid parse`. -/
@[expose] def IdOrDistinctSid {A : RustAlloc} {b : BitVec 64}
    (parse : UuidParser) (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (x : DecryptGhost) : Prop :=
  ∀ r ses, kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some ses →
    ses.state.remoteIdentity ≠ some ses.state.localIdentity ∨
      CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes

theorem idOrDistinctSid_of_distinctSid {A : RustAlloc} {b : BitVec 64}
    {parse : UuidParser} {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    (hdist : CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes) :
    IdOrDistinctSid parse kit st0 Scope x :=
  fun _ _ _ _ => Or.inr hdist

theorem idOrDistinctSid_of_scopeIn {A : RustAlloc} {b : BitVec 64}
    {parse : UuidParser} {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    (hscopeIn : ∀ r, Scope r → RecordInScope r) :
    IdOrDistinctSid parse kit st0 Scope x :=
  fun r ses hsc hcur => Or.inl (hscopeIn r hsc.1 ses hcur).1

section ChainVTP

end ChainVTP

section ChainVT

end ChainVT

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
