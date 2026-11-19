/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPoll
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPoll
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Shims
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet

/-!
# CLI Store Vtable and `KitOk` Bundles for Poll Closure

Proves vtable offset equalities, store quietness, spatial `stageP1VtablesAt` introduction, and
`KitOk` / `FsAt` discharges for all six CLI poll store kits (`cliPoll*Kit` and `Ext` variants).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

theorem cliPollSess_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSessKit A b F0 Scope peer σ).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

theorem cliPollPk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (pid : BitVec 32) (σ : DpKitStk) :
    (cliPollPkKit A b F0 pid σ).Quiet :=
  cliPreKeyStoreSpec_quiet cliIo.rd F0 cliWrOk pid
    σ.pkGetShim σ.pkGetPoll σ.pkRemoveShim σ.pkRemovePoll

theorem cliPollSpk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (sid : BitVec 32) (σ : DpKitStk) :
    (cliPollSpkKit A b F0 sid σ).Quiet :=
  cliSignedPreKeyStoreSpec_quiet cliIo.rd F0 cliWrOk sid σ.spkGetShim σ.spkGetPoll

theorem cliPollKpk_quiet {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) :
    (cliPollKpkKit A b F0 kid sid kbk σ).Quiet :=
  cliKpkStoreSpecFull_quiet cliIo.rd F0 cliWrOk kid sid kbk
    σ.kpkGetShim σ.kpkGetPoll σ.kpkMarkShim σ.kpkMarkPoll

/-! ## Spatial Stage P1 Vtable Bundle -/

/-- Connects `(cliPollSessKit … Slots.scopeKit …).loadRel StoresGhost.opened.sessions peer.val (.ok opt)`
to `Slots.loadRec Scope F0 peer.val =.ok opt`. -/
theorem loadRec_of_cliPollSess_loadRel {A : RustAlloc} {b : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk}
    {opt : Option (SessionRecord (List (BitVec 8)))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hf : Slots.FilesOkPeer Scope F0 peer.val)
    (hrel : (cliPollSessKit A b F0 Slots.scopeKit peer σ).loadRel
      StoresGhost.opened.sessions peer.val (.ok opt)) :
    Slots.loadRec Scope F0 peer.val = .ok opt := by
  obtain ⟨bs, hget, hans⟩ := hrel
  have hans' : SessLoadAns Slots.scopeKit
      (StoresGhost.opened.sessions.get cliIo.rd F0 (Cli.addressText peer.val)) (.ok opt) := by
    rw [hget]; exact hans
  have h1 := (Slots.loadRec_unique hinjK hans').symm
  rwa [loadRec_scopeKit_eq hinjK hsub hf] at h1

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
