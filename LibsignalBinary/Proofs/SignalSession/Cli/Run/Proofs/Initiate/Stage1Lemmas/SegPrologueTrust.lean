/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Stage 1 Segment 1 (`0x0000 → 0x0154`): Prologue and `is_trusted_identity`

Steps through `signal_session_handshake::initiate`'s prologue, invokes `idTrustShim`, `idTrustPoll`,
`futDrop`, and `__rust_dealloc(32, 8)`, discharges the untrusted-identity `Err` exit at `0x0244`,
and establishes `stage2Mem` at `0x0154` on the `Ok(true)` branch.
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

theorem prologue_low_d0_merge_sp (sp : BitVec 64) :
    (∃∗ l0 : BitVec 64, (sp - 7408#64) ↦₆₄ l0) ∗ memRegion (sp - 7400#64) 120 ∗
      (∃∗ l80 : BitVec 64, (sp - 7280#64) ↦₆₄ l80) ∗
      (∃∗ l88 : BitVec 32, (sp - 7272#64) ↦₃₂ l88) ∗ memRegion (sp - 7268#64) 4 ∗
      (∃∗ l90 : BitVec 64, (sp - 7264#64) ↦₆₄ l90) ∗
      (∃∗ l98 : BitVec 64, (sp - 7256#64) ↦₆₄ l98) ∗
      (∃∗ la0 : BitVec 64, (sp - 7248#64) ↦₆₄ la0) ∗
      (∃∗ la8 : BitVec 64, (sp - 7240#64) ↦₆₄ la8) ∗
      (∃∗ lb0 : BitVec 64, (sp - 7232#64) ↦₆₄ lb0) ∗
      (∃∗ lb8 : BitVec 64, (sp - 7224#64) ↦₆₄ lb8) ∗
      (∃∗ lc0 : BitVec 64, (sp - 7216#64) ↦₆₄ lc0) ∗
      (∃∗ lc8 : BitVec 64, (sp - 7208#64) ↦₆₄ lc8) ⊢
      memRegion (sp - 7408#64) 208 := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro lc8
  apply Entails.sepExists_elim; intro lc0
  apply Entails.sepExists_elim; intro lb8
  apply Entails.sepExists_elim; intro lb0
  apply Entails.sepExists_elim; intro la8
  apply Entails.sepExists_elim; intro la0
  apply Entails.sepExists_elim; intro l98
  apply Entails.sepExists_elim; intro l90
  apply Entails.sepExists_elim; intro l88
  apply Entails.sepExists_elim; intro l80
  apply Entails.sepExists_elim; intro l0
  simpa (disch := decide) only
    [cliInitiateFrame, BitVec.add_zero, bv_sub_add_lit, Nat.reduceAdd, Nat.reduceSub,
      BitVec.ofNat_eq_ofNat] using
    prologue_low_d0_merge (sp - BitVec.ofNat 64 cliInitiateFrame)
      l0 l80 l88 l90 l98 la0 la8 lb0 lb8 lc0 lc8

theorem prologue_high_5ba_merge_sp (sp : BitVec 64) :
    memRegion (sp - 5942#64) 30 ∗
      (∃∗ wk0 : BitVec 64, (sp - 5912#64) ↦₆₄ wk0) ∗
      (∃∗ wk1 : BitVec 64, (sp - 5904#64) ↦₆₄ wk1) ∗
      (∃∗ wk2 : BitVec 64, (sp - 5896#64) ↦₆₄ wk2) ∗
      memRegion (sp - 5888#64) 1696 ∗
      (∃∗ probe : BitVec 64, (sp - 4192#64) ↦₆₄ probe) ∗
      memRegion (sp - 4184#64) 4088 ⊢
      memRegion (sp - 5942#64) 5846 := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro probe
  apply Entails.sepExists_elim; intro wk2
  apply Entails.sepExists_elim; intro wk1
  apply Entails.sepExists_elim; intro wk0
  simpa (disch := decide) only
    [cliInitiateFrame, initLocalsSize, BitVec.add_zero, bv_sub_add_lit, Nat.reduceAdd,
      Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
    prologue_high_5ba_merge (sp - BitVec.ofNat 64 cliInitiateFrame) wk0 wk1 wk2 probe

/-- Bundle fields outside the 32-byte `idKey` slice at `+120`. -/
@[expose] def bundleRestAt (x : InitGhost) (opkId2 : BitVec 32) : SepProp :=
  (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗ (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
    ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
    ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
    ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
    ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
    (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
    ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
    ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
    ((x.bundleA + 116#64) ↦₃₂ opkId2) ∗
    ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
    ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
    (match x.bundle.opk with
     | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (x.bundleA + 157#64) 32) ∗
    ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

