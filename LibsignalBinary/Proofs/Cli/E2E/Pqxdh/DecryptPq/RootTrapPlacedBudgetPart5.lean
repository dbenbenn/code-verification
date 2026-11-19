/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeyTrap507PlacedBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Budget-Threaded Block `507` CLI Segment `S4` Seams (`s4_507_cli_ofEnv`, `s4_507_cli`)

CLI hook-table instantiations of `S4SeamPlaced` (`ConsumeMsgKey`) on Block `507`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart5

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement libsignalSessionExterns lsBlackBoxU8Sym lsRustDeallocSym ls_hook_ok lsmpl
)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508 instIsLsBlockProg_508)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsFmtWriteSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_panic_all)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeyTrap507PlacedBudget (
  consumeMsgKey_507_placed_ok_ofEnv
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget (
  CmkSeg4Env s4DefaultEnv
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S4SeamPlaced)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (
  fmtWriteProtoAddrCliLsSpec fmtWriteProtoAddrLsEnvSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs (CliFmtWriteEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat
  cliGhostExterns_blackBoxSat_budget_sat cliGhostExterns_sessionMemmove_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget (addr_display_placed_ok_at)

section CmkBbSat

open SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded blkPC_24 blkPl_24 extract_withLsCodeLoaded lsRustReallocSym withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (ls_subroutine_ok_transfer_of_plain)
open LibsignalBinary.Heap (rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkEnv cmkPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat (grow_one_placed_ok_at_cmk_sat hmac_sha256_placed_ro_ok_at_cmk_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat (find_receiver_chain_index_placed_ok_at_cmk_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (cmkPlacedRoSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat (consume_message_key_placed_ro_run_of_sat)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (cmkRawSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local irreducible]
  CryptoVerification.LibsignalSession.cmkDummyImg
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg

private theorem cmkPlacedSpec_pre_eq_raw [LibsignalPlacement] (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').pre x s =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced F A').pre x s ∗
        ⌜LibsignalCodeLoaded lsmpl s.mem⌝ := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmkPlacedSpec_post_eq_raw [LibsignalPlacement] (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s0 sf : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').post x s0 sf =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F A').post x s0 sf := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmk_raw_placed_cro_ok_at_block_bb_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced F A lim CmkEnv)) := by
  have hcmk0 : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
    consume_message_key_placed_ro_run_of_sat F A lim H
      (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
      (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
      (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm
  have htr : subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeLoaded lsmpl (cmkPlacedRoSpec F A lim)) :=
    ls_subroutine_ok_transfer_of_plain hcmk0 hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine htr.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [cmkRawSpecPlaced] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    dsimp only [withLsCodeLoaded, cmkPlacedRoSpec, cmkPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [cmkPlacedSpec_pre_eq_raw, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hp.1, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro, hp.2⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [cmkPlacedRoSpec, cmkPlacedSpec, cmkRawSpecPlaced, withLsCodeRoLoaded] at hq ⊢
      simp only [cmkPlacedSpec_post_eq_raw] at hq
      exact hq
    · exact Or.inr (Or.inl ⟨hpan, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

end CmkBbSat

/-! ## Hook and Bundle Witnesses -/

private theorem cmkAllocHooks_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    CmkAllocHooks A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  ⟨cliExternsPlaced_alloc_budget_sat mmpl g W hG,
   cliExternsPlaced_dealloc_budget_sat mmpl g W hG,
   cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq,
   cliGhostExterns_panic_all mmpl g W _ (by decide),
   cliGhostExterns_panic_all mmpl g W _ (by decide),
   cliGhostExterns_panic_all mmpl g W _ (by decide)⟩

/-! ## Segment `S4` CLI Seams -/

theorem s4_507_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {fmtWriteEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrLsEnvSpec M A lim fmtWriteEnv))
    (ctl : BitVec 64) (S : SpqrModel)
    (hFmtWriteSub : ∀ evs, CliFmtWriteEnv evs → fmtWriteEnv evs := by exact fun _ h => h) :
    S4SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (CmkSeg4Env fmtWriteEnv) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have haddrDisplay := addr_display_placed_ok_at
    (prog := (blkPC_508).rebase (blkPl_508).base H) hFmtWrite
  have hcmk := cmk_raw_placed_cro_ok_at_block_bb_sat
    (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    W.C.F A lim (cmkAllocHooks_cli mmpl g W hG)
    (cliGhostExterns_sessionMemmove_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk 4096)
    (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs.hookSatCompress256_cliGhostExterns_of_extraOk_eq
      g (cliExternsPlaced mmpl W) hG.extraOk hF)
  have hdealloc := ls_hook_ok
    (prog := (blkPC_508).rebase (blkPl_508).base H)
    (k := libsignalSessionExterns.idxOf lsRustDeallocSym) (by decide)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
  exact consumeMsgKey_507_placed_ok_ofEnv W.C A lim ctl S fmtWriteEnv H
    haddrDisplay hcmk hdealloc hFmtWriteSub

theorem s4_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteProtoAddrCliLsSpec M A lim))
    (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S s4DefaultEnv :=
  s4_507_cli_ofEnv mmpl g W hG hF hFmtWrite ctl S

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart5
