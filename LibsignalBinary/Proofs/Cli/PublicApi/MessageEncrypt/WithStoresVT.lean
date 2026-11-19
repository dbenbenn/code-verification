/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4
public import LibsignalBinary.Proofs.E2E.Record.Support.Repr -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.Encrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Core
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItems
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# CLI MessageEncrypt `WithStoresVT`: assembly on `trTrapProgAt` and transfer to `cliExterns`

1. Chains `Seg1..Seg6` (`h45_seg*_okVT_trap`) into `withStores_okVT_fs_trap` (and corollary
   `withStores_okVT_trap`) on `trTrapProgAt img.base C abs`.
2. Proves the empty-SPQR `OtrEncryptOkQ_trap (· = [])` on `trTrapProgAt` (`h45_otrEncryptOkQ_empty_trap`)
   and restricts `kit` to `rem = x.rem.val` (`h45_kitAt`) to discharge the `RecordPqEmpty` arm via
   `withStores_okV_fs_trap` with `TokenInit img` framed.
3. Unifies the `64 ≤ x.rest.length` arm (`withStores_okVT_fs_trap` + `otrEncryptV1_run_trap`) and
   the `RecordPqEmpty` arm (`withStores_okV_fs_trap` + `spqrV1_emptyOk`), then transfers via
   `Slots.subroutine_ok_cli_of_trTrap` to deliver `withStores_okVT_fs_cli` on
   `tripleRatchetProgAtExt img.base (cliExterns W)`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

section SpqrSendEmptyTrap

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end SpqrSendEmptyTrap

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt


open CryptoVerification.LibsignalSpqrV1 (spqrV1 spqrV1_emptyOk)
open CryptoVerification.SignalSession (CliHooks cliExterns)
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Segment Chaining & `withStores_okVT_fs_trap` -/

@[reducible] private def h45_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) : SessionStoreSpec A b :=
  { kit with
    addrOk := fun rem => kit.addrOk rem ∧ rem = target
    loadRel := fun st rem ans => kit.loadRel st rem ans ∧ rem = target }

private theorem h45_pure_mono {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ : SepProp) ⊢ ⌜ψ⌝ :=
  Entails.pure_left_only fun hφ => Entails.pure_right_only (h hφ) (Entails.refl _)

private theorem h45_storeFinal_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt kit target).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitAt, ih]

private theorem h45_traceOfWith_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitAt kit target) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls :=
  rfl

private theorem h45_stackV_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b) :
    withStoresEncStackV (h45_kitAt kit target) ikit = withStoresEncStackV kit ikit :=
  rfl

private theorem h45_callsRel_kitAt_imp {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt kit target).callsRel st0 ans calls → kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => exact id
  | cons c cs ih =>
    cases c with
    | loadSession rem =>
      intro ⟨⟨hl, _⟩, hcs⟩
      exact ⟨hl, ih st0 hcs⟩
    | isTrustedIdentity _ _ _ =>
      intro hcs
      exact ih st0 hcs
    | saveIdentity _ _ =>
      intro hcs
      exact ih st0 hcs
    | storeSession rem r' =>
      intro ⟨hs, hcs⟩
      exact ⟨hs, ih st0 hcs⟩

private theorem h45_stepsThroughEncrypt_mono {Scope1 Scope2 : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (himp : ∀ r', Scope1 r' → Scope2 r')
    (h : StepsThroughEncrypt Scope1 C S parse x r sess otr taken k m otr') :
    StepsThroughEncrypt Scope2 C S parse x r sess otr taken k m otr' :=
  ⟨h.1, himp r h.2.1, h.2.2⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
