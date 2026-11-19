/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.StatesPb
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import ProofLib.Disproof.Basic
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.StdStartup.MuslStage1Init
public import VerifiedLibraries.Musl.Spec
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
public import VerifiedLibraries.Musl.Proofs.MemsetProof
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2ClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5ePlacedBudget

/-!
# Guarded-Tight `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) Envelope & Placed Contracts

Defines the structural leaf guard `StatesIntoPbTightDom` (`≤ 16` encoder/decoder slots, encoder slot
length `≤ 640` GF16s, decoder slot length `≤ 576` points, and `ct1.length ≤ 2400` on `ct1`-cloning
arms), proves `StatesIntoPbVariantExactEnv st evs → SpqrTightEvs 42 376193 2400 evs` under
`StatesIntoPbTightDom st`, lifts `BOkTight` and `TopStateTight` / `SpqrStateTight640` across
`States.from_pb`, `States.recv`, and `States.send`, and derives guarded-tight Block `334` contracts.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Message MlKem PolyDecoder PolyEncoder PqRatchetState States V1Recv V1Send V1State
   pbToPqRatchetState spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1Sampled Ct2Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (Ct1Received EkSentCt1Received HeaderSent KeysSampled)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.Erasure (msgPoints)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight DecWFTight EncWF isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight
   st_bSendClosed_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrTightEvs StatesIntoPbTightEnv decoderIntoPbEnv_tight encoderIntoPbEnv_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps (needed_isRodata_and_le_36)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (EncPtsBoundedAt StatesPtsBoundedAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbEnv encoderIntoPbSpec encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (StatesIntoPbAllocPlacedBudget statesIntoPbPlacedRoSpecXOfEnv
   statesIntoPbPlacedSpecOfEnv statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget (KeysUnsampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget (Ct2SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget (KeysSampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlacedBudget (Ct1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (NoHeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget (HeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget (EkSentCt1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget (HeaderSentEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget (EkReceivedCt1SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (ct1CloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget (Ct1AcknowledgedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (Ct1CloneAndDropEnv Ct1SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
  (StatesIntoPbExactEnv StatesIntoPbPlacedOkExtOfEnv StatesIntoPbPlacedOkXOfEnv
   StatesIntoPbPlacedRoFreeOkXOfEnv StatesIntoPbVariantExactEnv
   states_into_pb_cl_placed_blockProgram_ok_x_of_env
   states_into_pb_cl_placed_blockProgram_ro_cro_ok_x_of_env
   states_into_pb_cl_placed_ok_ext_of_env
   states_into_pb_cl_placed_ok_x_of_env
   states_into_pb_cl_placed_ro_cro_ok_x_of_env)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ## 1. Structural Leaf Guard (`StatesIntoPbTightDom`) -/

/-- Structural encoder slot-count and per-slot length cap for `<PolyEncoder>::into_pb` tight credit. -/
@[expose] def EncIntoPbTightDom (enc : PolyEncoder) : Prop :=
  (encoderIntoPbVecs enc).length ≤ 16 ∧ ∀ cs ∈ encoderIntoPbVecs enc, cs.length ≤ 640

/-- Structural decoder slot-count and per-slot length cap for `<PolyDecoder>::into_pb` tight credit. -/
@[expose] def DecIntoPbTightDom (dec : PolyDecoder) : Prop :=
  dec.pts.length ≤ 16 ∧ ∀ s ∈ dec.pts, s.vec.length ≤ 576

/-- Per-constructor structural leaf domain on `States` making `<States>::into_pb` (Block `334`)
    satisfy `StatesIntoPbTightEnv` (`SpqrTightEvs 42 376193 2400`). -/
@[expose] def StatesIntoPbTightDom {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => EncIntoPbTightDom s.sending_hdr
  | .headerSent s => EncIntoPbTightDom s.sending_ek ∧ DecIntoPbTightDom s.receiving_ct1
  | .ct1Received s => EncIntoPbTightDom s.sending_ek
  | .ekSentCt1Received s => DecIntoPbTightDom s.receiving_ct2
  | .noHeaderReceived s => DecIntoPbTightDom s.receiving_hdr
  | .headerReceived s => DecIntoPbTightDom s.receiving_ek
  | .ct1Sampled s =>
      s.uc.ct1.length ≤ 2400 ∧ EncIntoPbTightDom s.sending_ct1 ∧ DecIntoPbTightDom s.receiving_ek
  | .ekReceivedCt1Sampled s =>
      s.uc.ct1.length ≤ 2400 ∧ EncIntoPbTightDom s.sending_ct1
  | .ct1Acknowledged s =>
      s.uc.ct1.length ≤ 2400 ∧ DecIntoPbTightDom s.receiving_ek
  | .ct2Sampled s => EncIntoPbTightDom s.sending_ct2

/-! ## 2. Core 11-Arm Tight Inclusion & Guarded Envelopes -/

private theorem e2cr_ct1CloneEvents_tight {ct1 : List (BitVec 8)} (h : ct1.length ≤ 2400) :
    SpqrTightEvs 1 9789 2400 (ct1CloneEvents ct1) := by
  unfold ct1CloneEvents
  split
  · exact SpqrTightEvs.nil 1 9789 2400
  · exact SpqrTightEvs.rustAlloc h (by decide)

private theorem e2cr_ct1CloneAndDropEnv_tight {ct1 : List (BitVec 8)} {evs : List AllocEvent}
    (h : ct1.length ≤ 2400) (hEnv : Ct1CloneAndDropEnv ct1 evs) :
    SpqrTightEvs 1 9789 2400 evs := by
  rcases hEnv with h1 | ⟨evs1, evs2, rfl, h1, h2⟩
  · rw [h1]
    exact e2cr_ct1CloneEvents_tight h
  · rw [h1]
    exact ((e2cr_ct1CloneEvents_tight h).append (SpqrTightEvs.of_freeOnly h2)).mono
      (by omega) (by omega) (by decide)

private theorem e2cr_arm11_ct2Sampled_tight {F : ShaCompress}
    {s : Ct2Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : EncIntoPbTightDom s.sending_ct2) (hEnv : Ct2SampledEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm10_ct1Acknowledged_tight {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ DecIntoPbTightDom s.receiving_ek)
    (hEnv : Ct1AcknowledgedEnv s evs) :
    StatesIntoPbTightEnv evs := by
  obtain ⟨evs_d1, evs_dec, rfl, hd1, hdec⟩ := hEnv
  exact (((e2cr_ct1CloneEvents_tight hDom.1).append (SpqrTightEvs.of_freeOnly hd1)).append
    (decoderIntoPbEnv_tight hDom.2.1 hDom.2.2 hdec)).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm9_ekReceivedCt1Sampled_tight {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ EncIntoPbTightDom s.sending_ct1)
    (hEnv : EkReceivedCt1SampledEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with hcd | ⟨evs_cd, evs_enc, rfl, hcd, henc⟩
  · exact (e2cr_ct1CloneAndDropEnv_tight hDom.1 hcd).mono (by decide) (by decide) (by decide)
  · exact ((e2cr_ct1CloneAndDropEnv_tight hDom.1 hcd).append
      (encoderIntoPbEnv_tight hDom.2.1 hDom.2.2 henc)).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm8_ct1Sampled_tight {F : ShaCompress}
    {s : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ EncIntoPbTightDom s.sending_ct1 ∧
      DecIntoPbTightDom s.receiving_ek)
    (hEnv : Ct1SampledEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with hcd | ⟨evs_cd, evs_rest, rfl, hcd, hrest⟩
  · exact (e2cr_ct1CloneAndDropEnv_tight hDom.1 hcd).mono (by decide) (by decide) (by decide)
  · rcases hrest with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
    · exact ((e2cr_ct1CloneAndDropEnv_tight hDom.1 hcd).append
        (encoderIntoPbEnv_tight hDom.2.1.1 hDom.2.1.2 henc)).mono
        (by decide) (by decide) (by decide)
    · exact ((e2cr_ct1CloneAndDropEnv_tight hDom.1 hcd).append
        ((encoderIntoPbEnv_tight hDom.2.1.1 hDom.2.1.2 henc).append
          (decoderIntoPbEnv_tight hDom.2.2.1 hDom.2.2.2 hdec))).mono
        (by decide) (by decide) (by decide)

private theorem e2cr_arm7_headerReceived_tight {F : ShaCompress}
    {s : HeaderReceived spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : DecIntoPbTightDom s.receiving_ek) (hEnv : HeaderReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm6_noHeaderReceived_tight {F : ShaCompress}
    {s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : DecIntoPbTightDom s.receiving_hdr) (hEnv : NoHeaderReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm5_ekSentCt1Received_tight {F : ShaCompress}
    {s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : DecIntoPbTightDom s.receiving_ct2) (hEnv : EkSentCt1ReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm4_ct1Received_tight {F : ShaCompress}
    {s : Ct1Received spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : EncIntoPbTightDom s.sending_ek) (hEnv : Ct1ReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm3_headerSent_tight {F : ShaCompress}
    {s : HeaderSent spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : EncIntoPbTightDom s.sending_ek ∧ DecIntoPbTightDom s.receiving_ct1)
    (hEnv : HeaderSentEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
  · exact (encoderIntoPbEnv_tight hDom.1.1 hDom.1.2 henc).mono (by decide) (by decide) (by decide)
  · exact ((encoderIntoPbEnv_tight hDom.1.1 hDom.1.2 henc).append
      (decoderIntoPbEnv_tight hDom.2.1 hDom.2.2 hdec)).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm2_keysSampled_tight {F : ShaCompress}
    {s : KeysSampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : EncIntoPbTightDom s.sending_hdr) (hEnv : KeysSampledEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem e2cr_arm1_keysUnsampled_tight {evs : List AllocEvent}
    (hEnv : KeysUnsampledEnv evs) :
    StatesIntoPbTightEnv evs := by
  rw [hEnv]
  exact SpqrTightEvs.nil 42 376193 2400

/-- Exact 11-arm tight inclusion on `TopClPlacedBudget.StatesIntoPbVariantExactEnv`
    (`StatesIntoPbTightEnv = SpqrTightEvs 42 376193 2400`). -/
theorem statesIntoPbVariantExactEnv_tight {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : StatesIntoPbTightDom st)
    (hEnv : StatesIntoPbVariantExactEnv st evs) :
    StatesIntoPbTightEnv evs := by
  cases st with
  | keysUnsampled _ => exact e2cr_arm1_keysUnsampled_tight hEnv
  | keysSampled _ => exact e2cr_arm2_keysSampled_tight hDom hEnv
  | headerSent _ => exact e2cr_arm3_headerSent_tight hDom hEnv
  | ct1Received _ => exact e2cr_arm4_ct1Received_tight hDom hEnv
  | ekSentCt1Received _ => exact e2cr_arm5_ekSentCt1Received_tight hDom hEnv
  | noHeaderReceived _ => exact e2cr_arm6_noHeaderReceived_tight hDom hEnv
  | headerReceived _ => exact e2cr_arm7_headerReceived_tight hDom hEnv
  | ct1Sampled _ => exact e2cr_arm8_ct1Sampled_tight hDom hEnv
  | ekReceivedCt1Sampled _ => exact e2cr_arm9_ekReceivedCt1Sampled_tight hDom hEnv
  | ct1Acknowledged _ => exact e2cr_arm10_ct1Acknowledged_tight hDom hEnv
  | ct2Sampled _ => exact e2cr_arm11_ct2Sampled_tight hDom hEnv

/-- Exact ghost-indexed tight inclusion on
    `LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget.StatesIntoPbExactEnv`
    (proved against Block `334` producers
    `TopClPlacedBudget.states_into_pb_cl_placed_blockProgram_ro_cro_ok_x_of_env`,
    `states_into_pb_cl_placed_blockProgram_ok_x_of_env`, `states_into_pb_cl_placed_ok_x_of_env`,
    `states_into_pb_cl_placed_ro_cro_ok_x_of_env`, and `states_into_pb_cl_placed_ok_ext_of_env`). -/
theorem statesIntoPbExactEnv_tight {F : ShaCompress}
    {g : StatesIntoPbGhost F} {evs : List AllocEvent}
    (hDom : StatesIntoPbTightDom g.st)
    (hEnv :
      LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget.StatesIntoPbExactEnv g evs) :
    StatesIntoPbTightEnv evs :=
  statesIntoPbVariantExactEnv_tight hDom hEnv

/-- Domain-split guarded-tight ghost-indexed envelope (`PreEnv = PostEnv`, zero existentials):
    `StatesIntoPbTightEnv` on `StatesIntoPbTightDom g.st`, falling back to
    `TopClPlacedBudget.StatesIntoPbExactEnv g` outside the domain (preserving `FitsEnv`). -/
@[expose] def StatesIntoPbGuardedTightEnv {F : ShaCompress}
    (g : StatesIntoPbGhost F) (evs : List AllocEvent) : Prop :=
  (StatesIntoPbTightDom g.st ∧ StatesIntoPbTightEnv evs) ∨
    (¬ StatesIntoPbTightDom g.st ∧
      LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget.StatesIntoPbExactEnv g evs)

/-- Unconditional inclusion `TopClPlacedBudget.StatesIntoPbExactEnv ⊆ StatesIntoPbGuardedTightEnv`
    (directly instantiates `hIntoPb` of `cliSpqrRecvPlacedContracts_ofEnv` and
    `cliStatesIntoPb_sendCoins_ok_of_env`). -/
theorem statesIntoPbExactEnv_imp_guardedTight {F : ShaCompress}
    (g : StatesIntoPbGhost F) (evs : List AllocEvent)
    (hEnv :
      LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget.StatesIntoPbExactEnv g evs) :
    StatesIntoPbGuardedTightEnv g evs := by
  by_cases hDom : StatesIntoPbTightDom g.st
  · exact Or.inl ⟨hDom, statesIntoPbExactEnv_tight hDom hEnv⟩
  · exact Or.inr ⟨hDom, hEnv⟩

/-! ## 3. Domain Bridges from `BOkTight` & `SpqrTrialDomainLiftAux.TopStateTight` -/

private theorem e2cr_encIntoPbTightDom_of_encWF {len : Nat} {enc : PolyEncoder}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152) (hwf : EncWF len enc) :
    EncIntoPbTightDom enc := by
  obtain ⟨msg, hinv, hmlen⟩ := hwf
  rcases hinv with hs | ⟨polys, hs, hplen, hp⟩
  · unfold EncIntoPbTightDom encoderIntoPbVecs
    rw [hs]
    dsimp only
    refine ⟨by simp [msgPoints], fun cs hcs => ?_⟩
    unfold msgPoints at hcs
    rw [List.mem_map] at hcs
    rcases hcs with ⟨pt, hpt, rfl⟩
    rcases List.mem_map.mp hpt with ⟨j, _, rfl⟩
    simp only [List.length_map, List.length_range, hmlen]
    exact Nat.le_trans (needed_isRodata_and_le_36 hlen j).2 (by decide)
  · unfold EncIntoPbTightDom encoderIntoPbVecs
    rw [hs]
    dsimp only
    refine ⟨by simp [hplen], fun cs hcs => ?_⟩
    rcases List.mem_map.mp hcs with ⟨p, hp_mem, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp_mem
    rw [(hp j hj).1, hmlen]
    exact Nat.le_trans (needed_isRodata_and_le_36 hlen j).2 (by decide)

private theorem e2cr_decIntoPbTightDom_of_decWFTight {n : Nat} {d : PolyDecoder}
    (hd : DecWFTight n d) (hn : n ≤ 576) :
    DecIntoPbTightDom d := by
  refine ⟨Nat.le_of_eq hd.1.2.1, fun s hs => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
  let S := (d.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset
  have hnec : d.necessaryPoints j ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    rw [hd.1.1]
    dsimp only
    split_ifs <;> omega
  have hsub_union :
      S ⊆ S.filter (· < d.necessaryPoints j) ∪ S.filter (d.necessaryPoints j ≤ ·) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hlt : x < d.necessaryPoints j
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, by omega⟩
  have hsub_range : S.filter (· < d.necessaryPoints j) ⊆ Finset.range (d.necessaryPoints j) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact hx.2
  have hlt_card : (S.filter (· < d.necessaryPoints j)).card ≤ d.necessaryPoints j := by
    have hc := Finset.card_le_card hsub_range
    rwa [Finset.card_range] at hc
  have hge_card : (S.filter (d.necessaryPoints j ≤ ·)).card ≤ d.necessaryPoints j := hd.2 j hj
  have htot_card : S.card ≤
      (S.filter (· < d.necessaryPoints j)).card + (S.filter (d.necessaryPoints j ≤ ·)).card :=
    (Finset.card_le_card hsub_union).trans (Finset.card_union_le _ _)
  have hnd : (d.pts[j].vec.map fun pt => pt.x.value.toNat).Nodup := (hd.1.2.2 j hj).imp ne_of_lt
  have hlen : d.pts[j].vec.length = S.card := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  omega

/-- Any `BOkTight` SPQR V1 braid state satisfies `StatesIntoPbTightDom`:
    - Encoder slots: `EncWF len` (`len ∈ {96, 160, 960, 1152}`) gives `16` slots of length
      `len / 32 ≤ 36 ≤ 640` (`SpqrSendRodataCaps.needed_isRodata_and_le_36`),
    - Decoder slots: `SendTotal.DecWFTight n` (`n ∈ {48, 80, 480, 576}`) gives `16` slots of length
      `≤ 2 * 36 = 72 ≤ 576`,
    - `ct1` byte cap: `Codec.UcOk.ctCt1Sent` / `Codec.UcOk.ctCt1SentEkReceived` (`Codec/StatesPb`)
      gives `ct1.length = CIPHERTEXT1_SIZE = 2080 ≤ 2400`. -/
theorem statesIntoPbTightDom_of_bokTight {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (hbok : BOkTight st) :
    StatesIntoPbTightDom st := by
  rcases hbok with ⟨hb, hdt⟩
  cases st with
  | keysUnsampled _ =>
    trivial
  | keysSampled _ =>
    exact e2cr_encIntoPbTightDom_of_encWF (Or.inl rfl) hb.2.2
  | headerSent _ =>
    exact ⟨e2cr_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2.1,
      e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ct1Received _ =>
    exact e2cr_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2
  | ekSentCt1Received _ =>
    exact e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | noHeaderReceived _ =>
    exact e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | headerReceived _ =>
    exact e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | ct1Sampled _ =>
    exact ⟨by rw [hb.2.1.2.2]; decide,
      e2cr_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2.1,
      e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ekReceivedCt1Sampled _ =>
    exact ⟨by rw [hb.2.1.2.1]; decide,
      e2cr_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2⟩
  | ct1Acknowledged _ =>
    exact ⟨by rw [hb.2.1.2.2]; decide,
      e2cr_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ct2Sampled _ =>
    exact e2cr_encIntoPbTightDom_of_encWF (Or.inr (Or.inl rfl)) hb.2

/-! ## 4. Placed Block `334` (`<States>::into_pb`) Guarded-Tight Producer Corollaries -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
