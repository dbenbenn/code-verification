/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.ChainPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519CallerBridges
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Budget-Threaded CLI Block `433` Pinned Segment `S3` Seam

Proves `dhStep_pinned_433_cli` (`S3TightSeamPinnedPlaced`) on Block `433` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_40 blkPl_40 ls_hook_ok_ultra_of_mem ls_subroutine_ok_of_block lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks SpqrModel hookMemset_eq_memsetHook keys_ls_hook_ok_of_mem
  keys_ls_subroutine_ok_of_block_cro
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (blkPC_434 blkPl_434 instIsLsBlockProg_434)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_shim
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  hookSat_cliGhostExterns_of_extraOk
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (S3TightSeamPinnedPlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitClMainPlacedBudget (
  s3_commit_pinned_cmk_cl_budget_placed_ok_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStep433PlacedBudget (
  s3_pinned_cro_placed_okT_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepCoinsFillBridgePlacedBudget (
  coinsFill_433_cro_placed_cli
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.ChainPlacedBudget (drop_chain_placed_ok)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (growOneSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetBbSat (
  calculateAgreement_placed_ok_unconditional_sat
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat (
  expand_multi_info_placed_vm_ok_of_other_block_sat extract_placed_vm_ok_of_other_block_sat
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_realloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_sessionMemsetRegion_budget_sat
  cliGhostExterns_blackBoxSat_budget_sat cliGhostExterns_sessionMemmove_budget_sat
  cliGhostExterns_sharedSecretDrop_budget_sat cliGhostExterns_staticSecretDrop_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPbBudget (chain_key_to_pb_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec derivePublicKeyBytesBudgetSpec noAllocShim_hookOk
  publicKeySerializeSpec
  subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget (
  derive_public_key_bytes_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget (
  growOneChain_placed_ok_of_noop_at_block
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (dhCommitBlockVmWp_549)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (dhStepBlockVmWp_549)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.KeysSat (
  createChain_placed_ok_of_contracts_budget_sat
)

private theorem blk433_s3_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

private theorem createChain_433_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 40) (withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  have _ : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG hF
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
  exact keys_ls_subroutine_ok_of_block_cro
    (createChain_placed_ok_of_contracts_budget_sat
      (keys_ls_subroutine_ok_of_block_cro
        (calculateAgreement_placed_ok_unconditional_sat
          (hookSat_cliGhostExterns_of_extraOk g (cliExternsPlaced mmpl W) hG.extraOk
            fun _ _ hRow => by rw [hX]; exact hRow.diffieHellmanWithStack_budget_ok 1808)
          (cliGhostExterns_sharedSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
          (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
          ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
          (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
          (cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)))
      (extract_placed_vm_ok_of_other_block_sat W.C (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (expand_multi_info_placed_vm_ok_of_other_block_sat W.C
        (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))
    (by decide) (by decide) (by decide)

private theorem derivePk_433_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 200)
      (withLsCodeRoLoaded lsmpl (withLsRet (derivePublicKeyBytesStackBudgetSpec W.C.pubKey 1904))) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.X25519CallerBridges.derive_public_key_bytes_placed_withLsRet_stackBudget_ok_of_hookSat
        1904
        (hookSat_cliGhostExterns_of_extraOk g (cliExternsPlaced mmpl W) hG.extraOk
          fun _ _ hRow => by rw [hPub]; exact hRow.derivePublicKeyBytesStackBudget_ok 1904))))

private theorem pkSer_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (public_key_serialize_placed_ok
      ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG)))

private theorem chainKeyToPb_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 22) (withLsCodeLoaded lsmpl (chainKeyToPbSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (chain_key_to_pb_placed_ok
      ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
      (cliExternsPlaced_alloc_budget_sat mmpl g W hG)))

private theorem growOne_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 43) (withLsCodeLoaded lsmpl (growOneSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact growOneChain_placed_ok_of_noop_at_block
    ((cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq))
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)

private theorem dropChain_433_cl_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 445) (withLsCodeLoaded lsmpl (dropChainSpec M A lim)) := by
  have _ := instIsLsBlockProg_434 (cliGhostExterns g (cliExternsPlaced mmpl W))
  exact ls_subroutine_ok_of_block (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (drop_chain_placed_ok (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)))

/-- Pinned `S3TightSeamPinnedPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem dhStep_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hF : W.C.F = CryptoVerification.LibsignalSpqrV1.sha256Compress)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := blk433_s3_entry_eq
  have _ := instIsLsBlockProg_434 H
  exact s3_pinned_cro_placed_okT_cli
    (dhStepBlockVmWp_549 H) W.C A lim ctl S
    (createChain_433_cro_ok mmpl g W hG hF hX)
    (derivePk_433_cro_ok mmpl g W hG hPub)
    (lsRetAddr624_base_add 434 1972#64 (by decide) (by decide))
    (coinsFill_433_cro_placed_cli mmpl g W hG)
    (ls_hook_ok_ultra_of_mem
      (cliGhostExterns_staticSecretDrop_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk))
    (s3_commit_pinned_cmk_cl_budget_placed_ok_cli
      (dhCommitBlockVmWp_549 H) W.C A lim ctl uuidTryParse spqrNoPanic
      (pkSer_433_cl_ok mmpl g W hG)
      (chainKeyToPb_433_cl_ok mmpl g W hG)
      (growOne_433_cl_ok mmpl g W hG)
      (dropChain_433_cl_ok mmpl g W hG)
      (ls_hook_ok_ultra_of_mem
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩)
      (ls_hook_ok_ultra_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
      (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
      (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget
        (ls_hook_ok_ultra_of_mem (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)))
      (ls_hook_ok_ultra_of_mem
        (cliGhostExterns_sessionMemmove_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk dropChainStack))
      (hlr_alloc := lsRetAddr624_base_add 434 0xa00#64 (by decide) (by decide))
      (hlr_dealloc := lsRetAddr624_base_add 434 0xaf0#64 (by decide) (by decide))
      (hlr_ls := lsRetAddr624_base_add 434 0xb8c#64 (by decide) (by decide)))

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4
