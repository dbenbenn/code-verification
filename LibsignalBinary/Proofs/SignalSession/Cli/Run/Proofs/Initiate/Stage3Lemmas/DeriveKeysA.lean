/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Ciphertext Boxing and Serialization (`0x0ff8 → 0x1044`)

Allocates `ctBoxPtr` (1568 bytes, OOM → `0x193c`), copies `ct`, invokes
`<kem::Ciphertext>::serialize` (`kemCtPtr`, 1569 bytes), stores `(kemCtPtr, 1569)` at
`[fsp + 0x60 .. 0x70)`, and frees `ctBoxPtr` (`derive_keys_a_ok` and `derive_keys_a_ok_ext`).
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

private theorem ct1568_split_hdr (p : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 1568) :
    (p ↦ₛ bs) ⊢
      (∃∗ w0, p ↦₆₄ w0) ∗ (∃∗ w1, (p + 8#64) ↦₆₄ w1) ∗ memRegion (p + 16#64) 1552 := by
  refine Entails.trans (pointsToBytes_entails_memRegion_len h) ?_
  rw [← memRegion_merge_at p 8 1560 (p + 8#64) (by clear * -; bv_omega) (by decide),
      ← memRegion_merge_at (p + 8#64) 8 1552 (p + 16#64) (by clear * -; bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  exact Entails.of_eq (by ac_rfl)

private theorem s3_pc_sub_entry (a b : BitVec 64) :
    a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-- `CliExternsOk`-compatible `<kem::Ciphertext>::serialize` contract (`tryCloneFromRefStackX = 16432` bytes). -/
@[expose] def kemCiphertextSerializeExtSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrPtr, boxPtr, ctBytes) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568⌝ ∗
    (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
    (boxPtr ↦ₛ ctBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun (hdrPtr, boxPtr, ctBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧ tempPtr ≠ 0#64⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗ (boxPtr ↦ₛ ctBytes) ∗
      (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
