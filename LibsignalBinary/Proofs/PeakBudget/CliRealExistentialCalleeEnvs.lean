/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import LibsignalBinary.Proofs.E2E.Seed.Defs

/-!
# Witness-Free Existential Real CLI Callee Envelopes

Constructs the mode-dispatched guarded-existential `CliRunCalleeEnvs` bundle
`mkExistentialRealCalleeEnvs` and its `CliRealCalleeFineSpecs` witness `existentialRealCalleeFineSpecs`
using `CliPqxdhInputs` and `cliIo_rd_ok_length_le_sessionCapBytes` (`bs.length ≤ 2 MiB` from
`IoHooks.readViewF`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs fileCapBytes)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliIdentityStoreSpec cliIdentityVtRoSym cliSessionStoreSpec cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRd parseArgs readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose ( InitGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (phaseGroupSpec_exists_guarded w3InitiateSlotEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (CliMainEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs CliRunOpenedEnv)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliPqRealCallDomain CliRealCalleeFineSpecs cliPqRealCallDomain_recvPrekey_nonvacuous
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS emptyPhaseCreditSpec emptyPhaseGroupSpec
   recordSerializeCancelEnv_aliceInitiated_fine_groupSpec w3InitRealCum w3InitRealGrpS
   w3InitRealLive w3InitRealMaxReq w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliAddrTextEnv CliDirGetEnv CliDirPutEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (CliSessLoadPollEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
  (w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot (W1SendRealDom W1SendRealParams peer_and_rem_name_le_40_of_send w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq w1SendRealDcanPeak w1SendRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (W2RealRecordSerEnv W2RealTdEnv W2RecvWhisperRealDom W2RecvWhisperRealParams
   W2RecvWhisperRealSlotEnv idPeers_rd_length_le_64_of_cliPqInputs_recv
   peer_and_rem_name_le_40_of_recv w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec
   w2RealIdentityKitEnv w2RealSessionKitEnv w2RealTd_phaseCredit w2Real_hStoreEq
   w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3InitiateSlotEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (RecordAliceInitiatedAnyCkBounds mkW3InitiateSlotParamsDeser
   recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820
   recordSerializeTightCum_aliceInitiatedAnyCk_le_32485
   w3InitiateSlotTightDeltaCum_sessionCap_eq w3InitiateSlotTightDeltaLive
   w3InitiateSlotTightDeltaPeak w3InitiateSlotTightMaxReq w3InitiateSlotTight_real192_eq
   w3InitiateSlot_opened_tight_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealEnv W4RecvPrekeyRealParams w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4RecvPrekeyRealDomOf cliRealDirectRunCum_i cliRealDirectRunGrpS_i cliRealDirectRunLive_i
   cliRealDirectRunMaxReq_i cliRealDirectRunPeak_i w4RecvPrekeyReal1MiB_i_Cum
   w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak
   w4RecvPrekeyReal1MiB_i_eq w4RecvPrekeyReal1MiB_i_singleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive
   pksmCanonSliceLive_le_peak pksmCanonSliceMaxReq pksmCanonSlicePeak
   pksmCanonSlice_fine_groupSpec pksmCanonSlice_fine_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv deserCancelFineCum deserCancelFineGrpS deserCancelFineLive
   deserCancelFineMaxReq deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv w2_hLoadEq_of_cliSessionKitBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (recordTryDecryptEnvArgs)

/-! ## Guarded Existential Credit and `cliIo.rd` `2 MiB` Cap -/

private theorem phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

/-- Every successful `cliIo.rd F path = .ok bs` lookup satisfies `bs.length ≤ sessionCapBytes`
(`IoHooks.readViewF` enforces `bs.length ≤ fileCapBytes`). -/
theorem cliIo_rd_ok_length_le_sessionCapBytes (F : FsFiles) (path bs : List (BitVec 8))
    (hrd : cliIo.rd F path = .ok bs) : bs.length ≤ sessionCapBytes := by
  change cliRd F path = .ok bs at hrd
  unfold cliRd at hrd
  split at hrd
  · cases hrd
  · rename_i rbs hrv
    injection hrd with h
    subst h
    unfold readViewF at hrv
    split at hrv
    · cases hrv
    · injection hrv with h
      subst h
      exact Nat.zero_le _
    · split at hrv
      · split at hrv
        · rename_i hle
          injection hrv with h
          subst h
          exact Nat.le_trans hle (by unfold fileCapBytes sessionCapBytes; decide)
        · cases hrv
      · cases hrv
      · injection hrv with h
        subst h
        exact Nat.zero_le _

/-! ## Real Slot Specs for `W1` (`send`) and `W2` (`recv` Whisper) -/

theorem w2Real_hLoadEq_noFb [LibsignalPlacement] {A : RustAlloc}
    {i : Inputs} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {x : DecryptGhost}
    {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hrem : x.rem.val = peer.val) :
    ∀ evs,
      (w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv).loadPollEnv
        StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv (runFiles i) StoresGhost.opened.sessions peer evs :=
  w2_hLoadEq_of_cliSessionKitBudgetEnv
    (A := A) (F := runFiles i) (pathOk := pathOk) (Scope := scopeKit) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (fileCap := sessionCapBytes)
    (vtSym := cliSessionVtRoSym) (idVtSym := cliIdentityVtRoSym)
    (AddrValEnv := fun _ => CliAddrTextEnv peer)
    (GetEnv := CliDirGetEnv (ReadFileRuleEnv cliIo.rd))
    (DeserEnv := ofBytesEnv DeserEnv)
    (SerValEnv := W2RealRecordSerEnv)
    (PutEnv := fun d _ _ => SeqEnv (CliDirPutEnv d [] []) FreeOnlyEvs)
    (DeserByBytesEnv := DeserEnv)
    (rem := x.rem.val)
    hrem (by decide : sessionCapBytes ≤ 2097152)
    (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
      (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) bs hrd)
    (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)

/-- `SingleSlotFineSpec` for `W2RecvWhisperRealSlotEnv`, discharging the session file-size cap via
`cliIo_rd_ok_length_le_sessionCapBytes`. -/
def w2RecvWhisperRealSlot_dcan_singleSlotFineSpec_noFb [LibsignalPlacement]
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (R : W2RecvWhisperRealParams)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hdom : W2RecvWhisperRealDom (.recv peerAddr) R) :
    SingleSlotFineSpec (W2RecvWhisperRealSlotEnv W i R) where
  cum := w2RecvWhisperRealDcanCum
  live := w2RecvWhisperRealDcanLive
  peak := w2RecvWhisperRealDcanPeak
  maxReq := w2RecvWhisperRealDcanMaxReq
  grpS := w2RecvWhisperRealDcanGrpS
  credit := by
    obtain ⟨hpeerAddr, hrem, hct⟩ := hdom peerAddr rfl
    obtain ⟨hpeer, hremName, hidKeyLen⟩ := peer_and_rem_name_le_40_of_recv hparse hpeerAddr hrem
    exact w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec
      R.pathOk R.peer R.s1 R.s2 R.s3 R.s4 R.t1 R.t2 R.t3 R.t4
      R.parse R.x RecordDeserializeCancelEnv R.peer.name.bytes
      (w2RealSessionKitEnv R.A (runFiles i) R.pathOk R.peer R.s1 R.s2 R.s3 R.s4
        RecordDeserializeCancelEnv)
      (w2RealIdentityKitEnv (A := R.A) (runFiles i) R.pathOk R.peer R.t1 R.t2 R.t3 R.t4)
      (W2RealTdEnv W.C.F W.Q.K)
      hi hparse hpeerAddr hrem hpeer hremName hidKeyLen
      (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
        (pathOf StoresGhost.opened.sessions.path (addressText R.peer.val)) bs hrd)
      (idPeers_rd_length_le_64_of_cliPqInputs_recv hi hparse hpeerAddr)
      (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
      (w2Real_hLoadEq_noFb hrem) (fun _ _ h => h) (fun _ _ h => h)
      (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst)
      (fun _rec ses G G₁ _hIn _hcur _hgv _hDom _hRel hTop _hVe _hVcp _hPqLt31 _hPqFile =>
        w2RealTd_phaseCredit W.C.F W.Q.K
          (recordTryDecryptEnvArgs (recGhostOf R.x 0#64 G ses.state) G₁) hTop hct)
  live_le_peak := w2RecvWhisperRealDcan_live_le_peak
  groups := by
    obtain ⟨hpeerAddr, hrem, _⟩ := hdom peerAddr rfl
    exact w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec
      R.pathOk R.peer R.s1 R.s2 R.s3 R.s4 R.t1 R.t2 R.t3 R.t4
      R.parse R.x RecordDeserializeCancelEnv R.peer.name.bytes
      (w2RealSessionKitEnv R.A (runFiles i) R.pathOk R.peer R.s1 R.s2 R.s3 R.s4
        RecordDeserializeCancelEnv)
      (w2RealIdentityKitEnv (A := R.A) (runFiles i) R.pathOk R.peer R.t1 R.t2 R.t3 R.t4)
      hi hparse hpeerAddr hrem
      (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
        (pathOf StoresGhost.opened.sessions.path (addressText R.peer.val)) bs hrd)
      (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
      (w2Real_hLoadEq_noFb hrem) (fun _ _ h => h) (fun _ _ h => h)
      (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst)

/-! ## Mode-Dispatched Guarded-Existential Real Callee Envelopes -/

/-- Concrete `W3` (`init`) `SingleSlotFineSpec` at `RecordDeserializeCancelEnv`. -/
def w3InitReal_singleSlotFineSpec_noA0
    {x : InitGhost}
    (hpeer : x.peer.name.bytes.length ≤ 40)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress)
    {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost}
    {r_rec : SessionRecord (List (BitVec 8))}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : RecordAliceInitiatedAnyCkBounds g_rec r_rec) :
    SingleSlotFineSpec
      (W3InitiateSlotEnv
        (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
          x ownKeyName ownRegName F x_spqr g_rec r_rec)) where
  cum := w3InitRealCum
  live := w3InitRealLive
  peak := w3InitRealPeak
  maxReq := w3InitRealMaxReq
  grpS := w3InitRealGrpS
  credit := by
    have h0 := w3InitiateSlot_opened_tight_phaseCredit
      (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
      rfl rfl rfl hpeer hkeyName hregName hspqrKey hfileCap
      (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
      (recordSerializeTightCum_aliceInitiatedAnyCk_le_32485 halice)
      (recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820 halice)
      (by decide)
    have hcr : PhaseCreditSpec fineCostModel
        (W3InitiateSlotEnv
          (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
            x ownKeyName ownRegName F x_spqr g_rec r_rec))
        (7874410 + deserCancelFineCum)
        (w3InitiateSlotTightDeltaLive sessionCapBytes 0 deserCancelFineLive 0)
        (w3InitiateSlotTightDeltaPeak sessionCapBytes 0 deserCancelFineLive deserCancelFinePeak 0)
        (w3InitiateSlotTightMaxReq sessionCapBytes 0 deserCancelFineMaxReq 3820) := by
      refine h0.mono ?_ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      rw [w3InitiateSlotTightDeltaCum_sessionCap_eq]
      omega
    obtain ⟨_, _, hlive, hpeak, hreq, _⟩ := w3InitiateSlotTight_real192_eq
    dsimp only [deserCancelFineLive, deserCancelFinePeak, deserCancelFineMaxReq] at hcr
    rw [hlive, hpeak, hreq] at hcr
    exact hcr
  live_le_peak := w3InitReal_caps_le.2.2.1
  groups :=
    w3InitiateSlotEnv_groupSpec fineCostModel
      (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
      (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
      (recordSerializeCancelEnv_aliceInitiated_fine_groupSpec halice)

/-- Call-site parameter bundle for the `W3` (`init`) slot (`W3InitiateSlotEnv` at `RecordDeserializeCancelEnv`). -/
structure W3InitRealParams where
  rd : ReadRule
  x : InitGhost
  ownKeyName : List (BitVec 8)
  ownRegName : List (BitVec 8)
  F : ShaCompress
  x_spqr : InitialStateGhost
  g_rec : RecordGhost
  r_rec : SessionRecord (List (BitVec 8))

/-- Concrete `W3` (`init`) slot envelope at `W3InitRealParams`. -/
@[expose] def W3InitRealSlotEnv (w : W3InitRealParams) (evs : List AllocEvent) : Prop :=
  W3InitiateSlotEnv
    (mkW3InitiateSlotParamsDeser w.rd RecordDeserializeCancelEnv
      w.x w.ownKeyName w.ownRegName w.F w.x_spqr w.g_rec w.r_rec)
    evs

end LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
