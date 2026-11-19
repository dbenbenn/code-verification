/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.ConsumeCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded and `VmPreserved` Relocatable `ConsumeMessageKeyTransfer` Contracts

Provides `[LibsignalPlacement]` `RustCliAllocBudget M` and `VmPreserved` contracts and cross-block
transfer corollaries for `RatchetState::consume_message_key` (Block `24`),
`RatchetState::find_receiver_chain_index` (Block `26`), `crypto::hmac_sha256` (Block `73`),
`RawVec<Chain>::grow_one` (Block `43`), `PublicKey::deserialize` (Block `201`), `ct_eq`
(Block `213`), and `<PublicKey as PartialEq>::eq` (Block `212`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPC_26 blkPC_43 blkPC_73 blkPC_201 blkPC_212 blkPC_213
  blkPl_24 blkPl_26 blkPl_43 blkPl_73 blkPl_201 blkPl_212 blkPl_213
  extract_withLsCodeLoaded lsBlackBoxU8Sym lsNoAllocShimSym
  lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (
  cmkName ctEqName deserializeName findIndexName growOneChainName
  hmacName hookSat_withPanics_blackBox ls_subroutine_ok_transfer
  ls_subroutine_ok_transfer_of_plain publicKeyEqName
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (growOneSpec hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv HmacPlacedOk cmkPlacedSpec cmkShimSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget (findPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (cmkPlacedRoSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget (hmac_sha256_placed_ok hmac_sha256_placed_ro_ok)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (cmkRawSpecPlaced)

/-! ## Relocatable `[LibsignalPlacement]` Budget & `VmPreserved` Contracts -/

section Placed

variable [LibsignalPlacement]

attribute [local irreducible]
  CryptoVerification.LibsignalSession.cmkDummyImg
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg

/-- Lift a `withLsCodeLoaded lsmpl { spec with pre := spec.pre ∗ ⌜LibsignalRoLoaded lsmpl ·.mem⌝ }`
    contract to `withLsCodeRoLoaded lsmpl spec`. -/
private theorem subroutine_ok_cro_of_cl_ro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        { spec with pre := fun g s => spec.pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ })) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, sepConj_left_comm (spec.pre x s0), satisfies_pure_sepConj]
  exact ⟨hro, hp⟩

/-! ### 1. `RatchetState::consume_message_key` (Block `24`) -/

private theorem cmkPlacedSpec_pre_eq_raw (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').pre x s =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced F A').pre x s ∗
        ⌜LibsignalCodeLoaded lsmpl s.mem⌝ := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmkPlacedSpec_post_eq_raw (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s0 sf : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').post x s0 sf =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F A').post x s0 sf := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

/-- Relocatable `VmPreserved` contract for `find_receiver_chain_index` (Block `26`). -/
theorem findIndex_placed_ok {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.find_receiver_chain_index_placed_ok
    A h_bb

theorem findIndex_placed_ok_at_block {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  ls_subroutine_ok_transfer (findIndex_placed_ok A h_bb) hi

/-! ### 3. `crypto::hmac_sha256` (Block `73`) -/

/-- Relocatable `VmPreserved` contract for `crypto::hmac_sha256` (Block `73`). -/
theorem hmac_placed_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.CryptoHmacSha256.hmacPlacedSpec F))) :=
  hmac_sha256_placed_ok F h_mc h_ms h_c256

theorem hmac_placed_ro_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  hmac_sha256_placed_ro_ok F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok F h_mc h_ms h_c256) hi

theorem hmac_placed_cro_ok_at_block {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.hmacSpec F))) :=
  subroutine_ok_cro_of_cl_ro (hmac_placed_ro_ok_at_block F h_mc h_ms h_c256 hi)

/-! ### 4. `RawVec<Chain>::grow_one` (Block `43`) -/

/-- Budget-threaded relocatable contract for `RawVec<Chain>::grow_one` (Block `43`, `HookSat` shim). -/
theorem growOneChain_placed_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym cmkShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget.grow_one_placed_ok h_shim h_alloc h_realloc

theorem growOneChain_placed_ok_of_noop {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget.grow_one_placed_ok_of_noop
    h_shim h_alloc h_realloc

theorem growOneChain_placed_ok_at_block {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_shim : HookSat H lsRustNoAllocShimSym cmkShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) :=
  ls_subroutine_ok_transfer (growOneChain_placed_ok h_shim h_alloc h_realloc) hi

theorem growOneChain_placed_ok_of_noop_at_block {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (growOneSpec M A lim)) :=
  ls_subroutine_ok_transfer (growOneChain_placed_ok_of_noop h_shim h_alloc h_realloc) hi

/-! ### 5. `PublicKey::deserialize` (Block `201`), `ct_eq` (Block `213`), `PublicKey::eq` (Block `212`) -/

/-- Relocatable `VmPreserved` contract for `PublicKey::deserialize` (Block `201`). -/
theorem deserialize_placed_ok (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      (withVmPreserved
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.deserialize_vm_placed_ok H

theorem deserialize_placed_ok_withLsCodeLoaded (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (deserialize_placed_ok H)

theorem deserialize_placed_ok_at_block {callerProg : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 201)
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)) :=
  ls_subroutine_ok_transfer (deserialize_placed_ok_withLsCodeLoaded H) hi

/-- Relocatable `VmPreserved` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`). -/
theorem ctEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withVmPreserved CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.ct_eq_placed_ok h_bb

theorem ctEq_placed_ok_withLsCodeLoaded {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ctEq_placed_ok h_bb)

theorem ctEq_placed_ok_at_block {callerProg : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 213)
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec)) :=
  ls_subroutine_ok_transfer (ctEq_placed_ok_withLsCodeLoaded h_bb) hi

/-- Relocatable `VmPreserved` contract for `<PublicKey as PartialEq>::eq` (Block `212`). -/
theorem publicKeyEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec)) :=
  LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.publicKey_eq_placed_ok h_bb

theorem publicKeyEq_placed_ok_at_block {callerProg : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl
        (withVmPreserved
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec)) :=
  ls_subroutine_ok_transfer (publicKeyEq_placed_ok h_bb) hi

end Placed

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
