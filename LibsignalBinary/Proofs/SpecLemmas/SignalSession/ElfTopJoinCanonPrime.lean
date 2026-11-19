/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.AesDecErrRoBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3CutPostBob

/-!
# Post-Bob `prev1` Block-579 `signal_session::run` Composition

Provides `canonOrFallbackRunEnvExact'`, `hole3_hrun_canonOrFallback'_of_slots`, and
`hole3_gap2_hrun_canonSlice'`, substituting `cliDecPkCanonSlotEnvExact' X W` for
`cliDecPkCanonSlotEnvExact X W` in the outer block-579 `run` composition.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification
  (ExternsDistinctOnHooked LibsignalFrozen LibsignalFullPlacement
   LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives libcruxHmacHookMallocng)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsAesDecSym lsAesEncSym
   lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost mkSlot runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecBudgetSpecErrRo)
open LibsignalBinary.Heap.SpecBudget (aesEncBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (DecPkD2cSlotOkFrozenPlaced)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (cliDecPkCanonSlotEnvExact' cliDecPkCanonSlotEnvExact'_ghost_congr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliInitSlotOkPlaced CliPubCalleesFrozenPlaced CliRunHooksBundle cliPubCallees_d2c_frozen_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunEnv run_ok_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
  (hc_kemDeserialize_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_canonOrFallbackPksmEnv_congr hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr
   hole3_initEnv_r1c_congr hole3_pksmSlotOk_canonOrFallback hole3_w1_inner hole3_w1_inner_of_hmac
   hole3_w2_inner hole3_w2_inner_of_hmac hole3_w3_init libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3CutPostBob
  (hole3_w4_decPk' hole3_w4_decPk'_of_hmac)

/-- `RunEnv` abbreviation over `binaryKitRunSlotEnvsExact`, `cliDecPkCanonSlotEnvExact'`, and `CanonicalOrFallbackPksmEnv FallbackEnv`. -/
abbrev canonOrFallbackRunEnvExact'
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (mpl mmpl : MultiPlacement) (brkStart : BitVec 64)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
      (CanonicalOrFallbackPksmEnv FallbackEnv)
      (cliRunSemD2c_placed X W))

private theorem tjcp_cliPubCallees_canonOrFallback'_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W A cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (binaryKitRunSlotEnvsExact W A cliRunBudgets
          (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
        (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
      W :=
  cliPubCallees_d2c_frozen_ok mmpl gh W hHooks
    (hole3_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W A)
    (hole3_decSigEnv_r3a_congr W A)
    hole3_canonOrFallbackPksmEnv_congr
    (cliDecPkCanonSlotEnvExact'_ghost_congr X W)

/-- Block-579 `runSpecTightPlaced (LibsignalFrozen lsmpl)` composition on `mProgPlaced` using `cliDecPkCanonSlotEnvExact'`. -/
theorem hole3_hrun_canonOrFallback'_of_slots [LibsignalFullPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Inner : (mkSlot
      (encSlotSpecPlaced A lim (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hW2Inner : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W) X W)
    (hDecPk : DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim
      (cliDecPkCanonSlotEnvExact' X W)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)))
        uuidTryParse
        (runRel (cliRunSemD2c_placed X W))
        cliWrOk cliResStack) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let S := cliRunSemD2c_placed X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hh := hHooks.runHooks
  have hpub := tjcp_cliPubCallees_canonOrFallback'_frozen_ok mmpl gh X W hHooks
  have hcallees : RunCalleesPlaced A lim (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      H cliRunBudgets (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := hW1Inner
      decryptSignal := hW2Inner
      initiate := hInit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hDecPk X S needs sEnvs rfl rfl rfl rfl rfl
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S (cliDecryptPrekeyNeed cliRunBudgets))
      hh
      hcallees
      (hole3_pksmSlotOk_canonOrFallback mmpl gh W hG S rfl)
      (runNeed_cli_le_resStack_placed A lim sEnvs
        (S := S) (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets) (by decide))
      (by decide)
      (by decide)

/-- Outer block-579 `run` composition from an explicit `hHmac` `HookSat` witness. -/
theorem hole3_gap2_hrun_canonSlice'_of_hmac
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hHmac :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
        (withLsRet (LibsignalBinary.Heap.SpecBudget.libcruxHmacBudgetSpec W.C.F fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesEnc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesEncSym
        (withLsRet (aesEncBudgetSpec W.C.E fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (hAesDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (h547 : mpl.base 547 ≠ 0#64) :
    @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced
        (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart hblk hext_nodup
          X W γ tp)
        uuidTryParse
        (runRel (cliRunSemD2c_placed X W))
        cliWrOk cliResStack) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact hole3_hrun_canonOrFallback'_of_slots mmpl ghFixed X W h547 hGSpqr.toCliGhostAllocHooks hHooks
    (hole3_w1_inner_of_hmac hLs hblk hext_nodup ghFixed hPl_mng X W hF hK γ tp hGSpqr hHmac hFs hsat hHooks hAesEnc h547)
    (hole3_w2_inner_of_hmac hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hK γ tp hGSpqr hHmac hFs hsat hHooks hAesDec h547)
    (hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hF512 hEnc γ tp hGSpqr hFs hsat hghNoAlloc hHooks h547)
    (hole3_w4_decPk'_of_hmac hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hDec hK γ tp hGSpqr hHmac hFs hsat hHooks hAesDec h547)

/-- Outer block-579 `run` composition instantiating `hole3_w1_inner`, `hole3_w2_inner`, `hole3_w3_init`, and `hole3_w4_decPk'`. -/
theorem hole3_gap2_hrun_canonSlice'
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : ExternsDistinctOnHooked mpl.ρ)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (hHmacLookup : ghFixed.extra.lookup spqrLibcruxHmacSym =
      some (libcruxHmacHookMallocng mmpl W.C.F))
    (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hAesEnc :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesEncSym
        (withLsRet (aesEncBudgetSpec W.C.E fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (hAesDec :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsAesDecSym
        (withLsRet (cliAesDecBudgetSpecErrRo W.C.D fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)))
    (h547 : mpl.base 547 ≠ 0#64) :
    @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced
        (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart hblk hext_nodup
          X W γ tp)
        uuidTryParse
        (runRel (cliRunSemD2c_placed X W))
        cliWrOk cliResStack) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact hole3_hrun_canonOrFallback'_of_slots mmpl ghFixed X W h547 hGSpqr.toCliGhostAllocHooks hHooks
    (hole3_w1_inner hLs hblk hext_nodup ghFixed hPl_mng X W hF hK hHmacLookup γ tp hGSpqr hFs hsat hHooks hAesEnc h547)
    (hole3_w2_inner hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hK hHmacLookup γ tp hGSpqr hFs hsat hHooks hAesDec h547)
    (hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hF512 hEnc γ tp hGSpqr hFs hsat hghNoAlloc hHooks h547)
    (hole3_w4_decPk' hLs hblk hext_nodup ghFixed hPl_mng X W hF hX hPub hDec hK hHmacLookup γ tp hGSpqr hFs hsat hHooks hAesDec h547)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
