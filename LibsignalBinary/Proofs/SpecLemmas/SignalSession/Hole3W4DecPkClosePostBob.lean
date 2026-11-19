/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmAB
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmC
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmUP
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWire

/-!
# Post-Bob `prev1` `decryptPrekey` (`W4`) Slot Assembly

Combines the untrusted/Stage-P1-Ok (`Hole3W4DecPkArmUP`), Path-A/B
(`Hole3W4DecPkArmAB`), and Path-C (`Hole3W4DecPkArmC`) envelope inclusions to prove
`DecPkD2cSlotOkFrozenPlaced` at `cliDecPkCanonSlotEnvExact' X W`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkClosePostBob

open Arm64 (GhostName HookSat)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalFullPlacement LibsignalPlacement lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives libcruxHmacHookMallocng)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsAesDecSym lsReadFileSym)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOkD2c)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecBudgetSpecErrRo)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
  (dpx_deserEnv dpx_p2OverErrEnv dpx_p2OverOkEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (DecPkD2cSlotOkFrozenPlaced)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (SessionGetPrev0Guard cliDecPkCanonSlotEnvExact'
   cliDecPkCanonSlotEnvExact'_eq_dom0'Prev0GuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
  (cliVerNe1e04_full_placed_ok_raw)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrHmacHookSatBudget
  (hpo_cliLibcruxHmac_budget_hookSat)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmAB (w4pb_armAB_sub_dom0')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmC (w4pb_armC_sub_dom0')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmUP (w4pb_armUP_sub_dom0')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkFresh
  (W4fGuardSlotIncl w4f_decPkD2cSlotOk_frozen_of_poll_and_guardIncl
   w4f_guardIncl_of_guarded_sub w4f_pollCallees_of_f3Hooks w4f_try507_of_tdEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
  (W4r2PollCustomP3GvSeqFreeEnv w4r2_poll_d2c_customP3_gvSeqFree_frozen_at_of_init75
   w4r2_wideM3PathCP3Envs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWire
  (w4wire_hp3Fits_wideM3 w4wire_init75_of_hooks w4wire_overPrevEncOK_of_scopeIn_v4
   w4wire_stageP2PathA_frozen_of_init75 w4wire_stageP2PathCOver_archive_frozen_of_init75)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty
   w4s2_spqrSeams_topStateGuarded w4s2_spqrSeams_topStateGuarded_of_hmac)

/-- Embeds `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`
under `FilesOkPeer`, `DecPkOkD2c`, `PeerSpqrStateTight640`, and `SessionGetPrev0Guard`. -/
theorem w4s2_pollGv_sub_canonPostBob [LibsignalPlacement]
    (A : RustAlloc) (X' X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hPrev0 : SessionGetPrev0Guard g.F g.peer.val)
    (hPoll :
      W4r2PollCustomP3GvSeqFreeEnv A W X'
        (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv
        (dpx_p2OverErrEnv A X' W) (dpx_p2OverOkEnv A X' W)
        w4s2_TryDecryptTopStateGuardedEnv
        (fun W' => w4r2_wideM3PathCP3Envs (w4s2_TryDecryptTopStateGuardedEnv W') VerNeTightTopRawEnv)
        g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  change realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X' W g evs
  rcases hPoll with hTrusted | hPathC
  · rcases hTrusted with hUntrusted | hP1 | hPathA | hPathB
    · exact w4pb_armUP_sub_dom0' A X' W g evs (Or.inl hUntrusted)
    · exact w4pb_armUP_sub_dom0' A X' W g evs (Or.inr hP1)
    · exact w4pb_armAB_sub_dom0' A X' W g evs hfPeer hdecOk hTight hPrev0 (Or.inl hPathA)
    · exact w4pb_armAB_sub_dom0' A X' W g evs hfPeer hdecOk hTight hPrev0 (Or.inr hPathB)
  · exact w4pb_armC_sub_dom0' A X' W g evs hfPeer hdecOk hTight hPrev0 hPathC

/-- Discharges `DecPkD2cSlotOkFrozenPlaced` at `W4PostBobPrev1Dom.cliDecPkCanonSlotEnvExact' X W`
from an explicit `hHmac` `HookSat` witness. -/
theorem w4s2_decPkD2cSlotOk_canonPostBob_of_hmac [LibsignalFullPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (X : UnreachedPqxdhPrimitives) (γ : GhostName) (tp brkStart : BitVec 64)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hHmac : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (withLsRet (LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec W.C.F fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesDec : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))) :
    DecPkD2cSlotOkFrozenPlaced mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (cliDecPkCanonSlotEnvExact' X W) := by
  let A := fineHookRustCliAllocBudget γ mmpl tp brkStart
  have hCal := w4f_pollCallees_of_f3Hooks mmpl ghFixed W γ tp brkStart
    hPl_mng hGSpqr hsat hHooks
  have hInit75 := w4wire_init75_of_hooks mmpl ghFixed W hGSpqr hF
  have hSpqrTd := w4s2_spqrSeams_topStateGuarded_of_hmac mmpl ghFixed W hF hK γ tp brkStart hGSpqr hHmac
    hCal.hh.formatInner
  have hTry0 := w4f_try507_of_tdEnv (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
    mmpl ghFixed W 0#64 hCal.hG hF hX hPub hAesDec hSpqrTd hCal.hh.fmtWrite hCal.hh.formatInner
    (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K) (fun _ _ h => h)
  have hVerNeAt := cliVerNe1e04_full_placed_ok_raw mmpl ghFixed W hCal.hG
  have hpoll := fun X' S =>
    w4r2_poll_d2c_customP3_gvSeqFree_frozen_at_of_init75
      (DeserEnv := dpx_deserEnv)
      (P2OverErrEnv := dpx_p2OverErrEnv A.repAlloc X' W)
      (P2OverOkEnv := dpx_p2OverOkEnv A.repAlloc X' W)
      (p3c := fun W' => w4r2_wideM3PathCP3Envs (w4s2_TryDecryptTopStateGuardedEnv W') VerNeTightTopRawEnv)
      hDropNz mmpl ghFixed W X' S hCal.hG hF hX hDec
      (w4wire_stageP2PathA_frozen_of_init75 A cliBudgetLimits (ReadFileRuleEnvFixed cliIo.rd)
        X' mmpl ghFixed W hDropNz hCal.hG hF hX hDec hInit75)
      (w4wire_stageP2PathCOver_archive_frozen_of_init75 A cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) X' mmpl ghFixed W hDropNz hCal.hG hF hX hDec hInit75 hCal.hReadPoll
        (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))
      hInit75 hCal.hRaw hCal.hReadPoll hTry0 w4wire_overPrevEncOK_of_scopeIn_v4 hVerNeAt
      (fun _ _ _ _ _ _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ _ _ h => h)
      w4wire_hp3Fits_wideM3
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
  have hIncl : ∀ X',
      W4fGuardSlotIncl (M := fineCostModel) cliBudgetLimits W scopeIn
        (W4r2PollCustomP3GvSeqFreeEnv A.repAlloc W X'
          (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv
          (dpx_p2OverErrEnv A.repAlloc X' W) (dpx_p2OverOkEnv A.repAlloc X' W)
          w4s2_TryDecryptTopStateGuardedEnv
          (fun W' =>
            w4r2_wideM3PathCP3Envs (w4s2_TryDecryptTopStateGuardedEnv W') VerNeTightTopRawEnv))
        (cliDecPkCanonSlotEnvExact' X W) := by
    intro X'
    rw [cliDecPkCanonSlotEnvExact'_eq_dom0'Prev0GuardedFixed]
    exact w4f_guardIncl_of_guarded_sub fun g hfPeer hdecOk hTight evs hPoll hPrev0 =>
      w4s2_pollGv_sub_canonPostBob A.repAlloc X' X W g evs hfPeer hdecOk hTight hPrev0 hPoll
  exact w4f_decPkD2cSlotOk_frozen_of_poll_and_guardIncl mmpl ghFixed W hCal.hh
    hCal.hReadHelpers hCal.hDeserHelpers hpoll hIncl

/-- Discharges `DecPkD2cSlotOkFrozenPlaced` at `W4PostBobPrev1Dom.cliDecPkCanonSlotEnvExact' X W`. -/
theorem w4s2_decPkD2cSlotOk_canonPostBob [LibsignalFullPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmacLookup : ghFixed.extra.lookup spqrLibcruxHmacSym =
      some (libcruxHmacHookMallocng mmpl W.C.F))
    (X : UnreachedPqxdhPrimitives) (γ : GhostName) (tp brkStart : BitVec 64)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr : CliGhostSpqrAllocHooks fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : CliRunHooksBundle mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesDec : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))) :
    DecPkD2cSlotOkFrozenPlaced mmpl ghFixed W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (cliDecPkCanonSlotEnvExact' X W) :=
  w4s2_decPkD2cSlotOk_canonPostBob_of_hmac mmpl ghFixed W hF hX hPub hDec hK X γ tp brkStart hDropNz hPl_mng hGSpqr
    (hpo_cliLibcruxHmac_budget_hookSat γ mmpl tp brkStart cliBudgetLimits ghFixed W hPl_mng hHmacLookup)
    hsat hHooks hAesDec

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkClosePostBob
