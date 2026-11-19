/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrust -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 1 Segment 4 (`0x01fc → 0x0390`): `load_session(peer)` and Stage 2 Handoff

Verifies `stage1_load_session_ok` and `stage1_load_session_ext_ok`: invokes `sessLoadShim`,
`sessLoadPoll`, `memcpy(312)`, `futDrop`, and `__rust_dealloc(24, 8)`, resolves `InitOk₀.noSession`
to `ans = .ok none` (`x22 = -1`), and establishes `AtStage2` and `stage2Mem` at `0x0390`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open Stage1Norm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-- Splits `[sp + 0x5ba, sp + initLocalsSize)` into future slots (`+0x5c0`, `+0x5c8`), 312-byte record slot (`+0x5f8`), and 368-byte `sret` (`+0x1600`). -/
theorem load_frame_5ba_split (sp : BitVec 64) :
    memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (sp + 0x5ba#64) 6 ∗
        (∃∗ f0 : BitVec 64, (sp + 0x5c0#64) ↦₆₄ f0) ∗
        (∃∗ f1 : BitVec 64, (sp + 0x5c8#64) ↦₆₄ f1) ∗
        memRegion (sp + 0x5d0#64) 40 ∗
        memRegion (sp + 0x5f8#64) 312 ∗
        memRegion (sp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (sp + 0x1600#64) 368 ∗
        memRegion (sp + 0x1770#64) (initLocalsSize - 0x1770) := by
  rw [show initLocalsSize - 0x5ba =
        6 + (8 + (8 + (40 + (312 + ((0x1600 - 0x730) + (368 + (initLocalsSize - 0x1770))))))) by decide,
      memRegion_split (sp + 0x5ba#64) 6 _ (by decide),
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 40 _ (by decide),
      memRegion_split _ 312 _ (by decide),
      memRegion_split _ (0x1600 - 0x730) _ (by decide),
      memRegion_split _ 368 _ (by decide)]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]

/-- Merges `[sp + 0x5ba, sp + initLocalsSize)` back after `sessLoadPoll` and `memcpy(312)`. -/
theorem load_frame_5ba_merge (sp : BitVec 64) (f0 f1 : BitVec 64) :
    memRegion (sp + 0x5ba#64) 6 ∗
      ((sp + 0x5c0#64) ↦₆₄ f0) ∗
      ((sp + 0x5c8#64) ↦₆₄ f1) ∗
      memRegion (sp + 0x5d0#64) 40 ∗
      memRegion (sp + 0x5f8#64) 312 ∗
      memRegion (sp + 0x730#64) (0x1600 - 0x730) ∗
      memRegion (sp + 0x1600#64) 368 ∗
      memRegion (sp + 0x1770#64) (initLocalsSize - 0x1770) ⊢
      memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  rw [load_frame_5ba_split sp]
  sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
