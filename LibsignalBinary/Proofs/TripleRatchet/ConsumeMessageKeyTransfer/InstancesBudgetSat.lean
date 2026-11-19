/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.ConsumeCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest

/-!
# `HookSat`-Parameterized Budget Contracts for `consume_message_key`, `hmac_sha256`, and `new_from_slice`

Specializes the contracts of `ConsumeMessageKeyTransfer.InstancesBudget`
(Block `24` `RatchetState::consume_message_key`, Block `73` `crypto::hmac_sha256`, and Block `114`
`<Hmac<Sha256> as KeyInit>::new_from_slice`) to `HookSatExactMemcpy`,
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`, and `HookSatCompress256 H lsCompress256Sym F`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPC_73 blkPC_114 blkPl_24 blkPl_73 blkPl_114
  extract_withLsCodeLoaded lsBlackBoxU8Sym lsNoAllocShimSym
  lsRustReallocSym lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CallingConventionPreserved_of_calleeSaved disjointRegions_of_ro_rw
  lsCompress256Sym lsMemcpySym lsSha256IVAddr rodata_placed_sha256IV
)
open CryptoVerification.LibsignalTripleRatchet (
  extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (
  isBlock_nfsResult ls_subroutine_ok_transfer ls_subroutine_ok_transfer_of_plain
)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv cmkPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (cmkPlacedRoSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat (
  consume_message_key_placed_ro_run_of_hooks_sat consume_message_key_placed_ro_run_sat
  hmac_sha256_placed_ok_sat hmac_sha256_placed_ro_ok_sat
  new_from_slice_placed_runsTo_vm_sat
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (cmkRawSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  HookSatCompress256 newFromSliceSpecSat newFromSliceStackSat
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

section Placed

variable [LibsignalPlacement]

attribute [local irreducible]
  CryptoVerification.LibsignalSession.cmkDummyImg
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg

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

/-- Budget-threaded relocatable `consume_message_key` contract on Block `24` under
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem cmk_placed_ro_ok_sat {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
  consume_message_key_placed_ro_run_of_hooks_sat F A lim H h_bb h_realloc h_mc h_ms h_c256 hA hmm

theorem cmk_placed_ro_ok_of_noop_sat {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
  consume_message_key_placed_ro_run_sat F A lim H h_bb h_shim h_realloc h_mc h_ms h_c256 hA hmm

theorem cmk_placed_ro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24) (cmkPlacedRoSpec F A lim) := by
  have htr : subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeLoaded lsmpl (cmkPlacedRoSpec F A lim)) :=
    ls_subroutine_ok_transfer_of_plain
      (cmk_placed_ro_ok_sat F A lim hA hmm h_bb h_realloc h_mc h_ms h_c256) hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by
    have hp := hpre
    dsimp only [cmkPlacedRoSpec, cmkPlacedSpec] at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp2 := hp.2
    unfold CryptoVerification.LibsignalSession.cmkPlacedSpec at hp2
    exact (extract_withLsCodeLoaded hp2).1
  refine htr.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

theorem cmk_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkPlacedSpec F A lim)) := by
  have hbase :=
    cmk_placed_ro_ok_at_block_sat (callerProg := callerProg) F A lim hA hmm h_bb h_realloc
      h_mc h_ms h_c256 hi
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨_, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine hbase.mono_outcome g R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [cmkPlacedRoSpec]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hro, hp⟩

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

theorem cmk_raw_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced F A lim CmkEnv)) := by
  have hbase :=
    cmk_placed_ro_ok_at_block_sat (callerProg := callerProg) F A lim hA hmm h_bb h_realloc
      h_mc h_ms h_c256 hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine hbase.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [cmkRawSpecPlaced] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    dsimp only [cmkPlacedRoSpec, cmkPlacedSpec]
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

/-! ### 2. `crypto::hmac_sha256` (Block `73`) -/

/-- Relocatable `VmPreserved` `crypto::hmac_sha256` contract on Block `73` under
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem hmac_placed_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.CryptoHmacSha256.hmacPlacedSpec F))) :=
  hmac_sha256_placed_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok_sat F h_mc h_ms h_c256) hi

theorem hmac_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.hmacSpec F))) :=
  subroutine_ok_cro_of_cl_ro (hmac_placed_ro_ok_at_block_sat F h_mc h_ms h_c256 hi)

/-! ### 3. `<Hmac<Sha256> as KeyInit>::new_from_slice` (Block `114`, `key.length ≤ 64`) -/

private theorem new_from_slice_placed_ro_vm_ok_plain_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : HookSatCompress256 H lsCompress256Sym F) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      { withVmPreserved (newFromSliceSpecSat F) with
        pre := fun g s =>
          (withVmPreserved (newFromSliceSpecSat F)).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withVmPreserved, newFromSliceSpecSat] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 720#64) 720
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 720#64) 720 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStackSat, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 720#64) 720 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStackSat, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 720#64) 720 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStackSat, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 720#64) 720 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_key : s0.mem.Readable keyA key.length := by
    intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hb_key.permNoLazy_rw hsep_key ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 720#64) 720 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hal : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  intro hL114
  obtain ⟨sf, hsteps, hvm_all, htr_all, hvregs_all,
      hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩ :=
    new_from_slice_placed_runsTo_vm_sat (F := F) h_mc h_c256 hpc hrun
      (by rw [hx2_len]; exact hkey_len) hiv_eq hread_iv
      (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
      (by rw [hx0]; exact hrw_out) hrw_stk
      (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
      (by rw [hx1, hx2_len]; exact hread_key)
      (by rw [hx1, hx2_len]; exact hdisj_key)
      hal hL114
  rw [hx1, hx2_len, hkey_eq] at hst_sf
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee hvregs_all⟩⟩
  dsimp only [withVmPreserved, newFromSliceSpecSat]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm_all, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr_all, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := S2Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStackSat, stackAt]
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-- `VmPreserved` + `HookSatExactMemcpy` + `HookSatCompress256` contract for `new_from_slice`
(Block `114`, `720`-B stack, `key.length ≤ 64`, `0` `memset` calls). -/
theorem new_from_slice_placed_ro_vm_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpecSat F) with
          pre := fun g s =>
            (withVmPreserved (newFromSliceSpecSat F)).pre g s ∗
              ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice_placed_ro_vm_ok_plain_sat F h_mc h_c256)

/-- Cross-block transfer of `new_from_slice_placed_ro_vm_ok_sat` to any `callerProg` (block `i`). -/
theorem new_from_slice_placed_ro_vm_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpecSat F) with
          pre := fun g s =>
            (withVmPreserved (newFromSliceSpecSat F)).pre g s ∗
              ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (new_from_slice_placed_ro_vm_ok_sat F h_mc h_c256) hi

/-- Cross-block `withLsCodeRoLoaded lsmpl (withVmPreserved (newFromSliceSpecSat F))` form of
`new_from_slice_placed_ro_vm_ok_at_block_sat` (consumed by `ComputeBudgetSat`, `DeriveBudgetSat`,
and `ResponderCore.CryptoCalleesPlacedBudget*Sat`). -/
theorem new_from_slice_placed_cro_budget_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : HookSatCompress256 H
      CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym F)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (newFromSliceSpecSat F))) :=
  subroutine_ok_cro_of_cl_ro (new_from_slice_placed_ro_vm_ok_at_block_sat F h_mc h_c256 hi)

end Placed

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
