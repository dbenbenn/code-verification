/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Stage 3 PQXDH Step B2 (`+0x0968 → +0x0a70`: `DH3`)

Advances from `+0x0968` (`F_X25519 ++ dh1 ++ dh2` at `secretsPtr`, `len = 96`) across
`DH3 = X25519(ekASk, spkB)` to `+0x0a70` with `F_X25519 ++ dh1 ++ dh2 ++ dh3` at `secretsPtr`
(`len = 128`).
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem sec96_re (secretsPtr : BitVec 64) (bs : SignalPqxdh.Bytes) (h96 : (bytesToBv8 bs).length = 96) :
    (secretsPtr ↦ₛ bytesToBv8 bs) ∗ memRegion (secretsPtr + 96#64) 32 ∗
      memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32 ⊢
    memRegion secretsPtr 192 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion_len h96)) ?_
  rw [memRegion_merge_at (secretsPtr + 128#64) 32 32 (secretsPtr + 160#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (secretsPtr + 96#64) 32 64 (secretsPtr + 128#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at secretsPtr 96 96 (secretsPtr + 96#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

private theorem s3_repack3 (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) :
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      (let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
       ((fsp + 0x298#64) ↦ₛ ekAPk) ∗ memRegion (fsp + 0x2b8#64) 0x48 ∗
       ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
       memRegion (fsp + 0x308#64) 0x40 ∗
       ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
       ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
       ((fsp + 0x388#64) ↦ₛ ekAPk) ∗ ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
       ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
       ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
       ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
       A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
       ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
       (match b.opk with
        | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
        | none => memRegion (fsp + 0x439#64) 32) ∗
       ((fsp + 0x459#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x45a#64) 6) =
    stage3KeySlotsAt A fsp b kp ekASk ekAPk pqspkPtr opkId := by
  dsimp only [stage3KeySlotsAt]; ac_rfl

set_option Elab.async false

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
