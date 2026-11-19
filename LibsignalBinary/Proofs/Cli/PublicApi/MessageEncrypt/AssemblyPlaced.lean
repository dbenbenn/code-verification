/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.SegmentProofsPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import GeneratedLean.LibsignalSessionPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import ProofLib.RegChain
public import ProofLib.StdStartup.MuslStage1Init
import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymA
import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymB
import LibsignalBinary.Proofs.CryptoGames.Ratchet.LibsignalSessionApiFacts
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# Relocatable CLI `MessageEncrypt` Assembly

Composes the nine `[LibsignalPlacement]` segment contracts on `lsProg_464 H` (`blkPl_464`) into
`withStores_placed_okV` and `withStores_placed_okV_fs`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit


variable [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}

/-- Chain a `[LibsignalPlacement]` segment into the rest of the run on `lsProg_464 H`. -/
theorem segExitPlaced_chain {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord H x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_464 H)
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (lsProg_464 H)
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext) hL
  · exact ⟨sf, hst, hout⟩

/-- `segExitPlaced_chain` carrying `EncFsCtxPlaced` across the seam. -/
theorem segExitPlaced_chainFs {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (hfs : EncFsCtxPlaced kit ikit H s0 s)
    (h1 : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord H x R s0 s next)
    (h2 : ∀ s', EncFsCtxPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_464 H)
        (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (lsProg_464 H)
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext) hL
  · exact ⟨sf, hst, hout⟩

/-- `session_message_encrypt_with_stores` (`blkPl_464`) satisfies `withStoresEncPlacedSpecV`
with both kits' `envOk` on the entry files from `EncSegsVPlaced`, given `KitFsOk`. -/
theorem withStores_placed_ok_of_segsV_fs {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (hSegs : EncSegsVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 H)) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withEnvPre (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have ⟨haddr_ss, haddr_id⟩ := withStoresEncPlacedSpecV_pre_addrOk hpre
  have hfs0 : EncFsCtxPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  refine segExitPlaced_chainFs hfs0 (hSegs.load hEnv x R s0 hfs0 hpc hrun hal hpre) ?_
  rintro s hfs ⟨r, g, sess, hCur⟩
  refine segExitPlaced_chainFs hfs (hSegs.fromS hEnv x r g sess R s0 s hCur) ?_
  rintro s hfs ⟨otr, taken, pqCap, pqPtr, hOtr⟩
  refine segExitPlaced_chainFs hfs (hSegs.identity hEnv x r sess otr taken pqCap pqPtr R s0 s hOtr) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord H x R s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr'
          pqCap' pqPtr' R s0 s') := by
    cases hp : sess.pendingPreKey with
    | none => exact hSegs.signal hEnv x r sess otr taken pqCap pqPtr k R s0 s hp hKey
    | some _ =>
      exact hSegs.preKey hEnv x r sess otr taken pqCap pqPtr k R s0 s (by simp [hp]) hKey
  refine segExitPlaced_chainFs hfs hCm ?_
  rintro s hfs ⟨m, otr', pqCap', pqPtr', hCmS⟩
  refine segExitPlaced_chainFs hfs
    (hSegs.trust hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hCmS) ?_
  intro s hfs hSave
  refine segExitPlaced_chainFs hfs
    (hSegs.save hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hSave) ?_
  rintro s hfs ⟨c, hApply⟩
  refine segExitPlaced_chainFs hfs
    (hSegs.applyStore hEnv x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s haddr_ss hfs hApply) ?_
  intro s _ hStored
  exact segExitPlaced_chain (hSegs.finish hEnv x r sess otr taken k m otr' c R s0 s hStored)
    (fun _ hF => False.elim hF)

/-- `session_message_encrypt_with_stores` (`blkPl_464`) satisfies `withStoresEncPlacedSpecV`
from `EncSegsVPlaced` when both kits have trivial `envOk`. -/
theorem withStores_placed_ok_of_segsV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (hSegs : EncSegsVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  subroutine_ok_of_withEnvPre (withStores_placed_ok_of_segsV_fs hEnv hSegs (.inl htriv))
    fun s => htriv s.fs.files

/-- Relocatable `session_message_encrypt_with_stores` contract for arbitrary session and
identity stores with trivial `envOk` under `[LibsignalPlacement]`. -/
theorem withStores_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  withStores_placed_ok_of_segsV hEnv encSegsV_placed_ok htriv

/-- Relocatable `session_message_encrypt_with_stores` contract preserving both kits' `envOk`
on the entry files, given `KitFsOk`. -/
theorem withStores_placed_okV_fs {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 H)) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withEnvPre (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStores_placed_ok_of_segsV_fs hEnv encSegsV_placed_ok hKitFs

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
