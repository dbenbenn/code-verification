/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.CodeLayout
public meta import Lean

/-!
# Shared Base Contracts for `SessionState` and Serialization Callees

Proves `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` for `<PrivateKey>::serialize`
(Block `208`), `<PublicKey>::serialize` (Block `205`), `<RawVecInner>::finish_grow [local#1]`
(Block `45`), and `<RawVec<Chain>>::grow_one` (Block `43`), plus fast `SepWP` frame/state helpers
shared by the `SessionState` method shards.
-/

public meta section

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

open Lean Meta Elab Tactic

partial def flattenSepConjAtoms (e : Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``ProofLib.sepConj 2 then
    let l ← flattenSepConjAtoms (e.getArg! 0)
    let r ← flattenSepConjAtoms (e.getArg! 1)
    return l ++ r
  else
    return #[e]

def mkSepConjChain (xs : Array Expr) : Expr :=
  if h : xs.size = 0 then
    mkConst ``ProofLib.emp
  else
    let last := xs[xs.size - 1]
    xs.extract 0 (xs.size - 1) |>.foldr (fun a acc => mkApp2 (mkConst ``ProofLib.sepConj) a acc) last

elab "sep_frame_ac_rfl" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, lhs, rhs) := tgt.eq?
    | throwError "sep_frame_ac_rfl: expected equality goal, got {tgt}"
  let rhs := rhs.consumeMData
  if rhs.isAppOfArity ``ProofLib.sepConj 2 then
    let tExpr := rhs.getArg! 0
    let fExpr := rhs.getArg! 1
    if fExpr.consumeMData.isMVar then
      let pAtoms ← flattenSepConjAtoms lhs
      let tAtoms ← flattenSepConjAtoms tExpr
      let mut rem := pAtoms
      for t in tAtoms do
        let mut foundIdx? : Option Nat := none
        for idx in [:rem.size] do
          if foundIdx?.isNone then
            if rem[idx]! == t then
              foundIdx? := some idx
        if foundIdx?.isNone then
          for idx in [:rem.size] do
            if foundIdx?.isNone then
              if ← withoutModifyingState (isDefEq rem[idx]! t) then
                foundIdx? := some idx
        match foundIdx? with
        | some idx => rem := rem.eraseIdxIfInBounds idx
        | none => throwError "sep_frame_ac_rfl: atom {t} not found in precondition"
      let frame := mkSepConjChain rem
      let ok ← isDefEq fExpr frame
      if !ok then
        throwError "sep_frame_ac_rfl: failed to unify frame metavariable with {frame}"
  evalTactic (← `(tactic| sep_ac_rfl))

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

end

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  libsignalMutatedBlocks libsignalSessionLib
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  ls_subroutine_ok_of_block lsmpl lsρ sepWP_seq_lscl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Bytes CryptoLeafCall FinishGrowGhost SessionStateNewGhost
  WithReceiverChainGhost WithSenderChainGhost
  blkLib_eq_43 blkLib_eq_45 blkLib_eq_205 blkLib_eq_208
  blkPC_43 blkPl_43 blkPC_45 blkPl_45 blkPC_205 blkPl_205 blkPC_208 blkPl_208
  bv_sub_add_lit' bytesToBv8 encodeEC
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvent FitsEvents RustCliAllocBudget VmPreserved
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomExternSpecWithStack rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec rustAllocShimVmSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.reduceSub])

local macro "wp_clean_setMem" : tactic =>
  `(tactic| (
    try (conv => arg 3; simp only [State.setMem_setMem])
    try (conv => arg 4; simp only [State.setMem_setMem])))

@[local simp, local wp_norm, local arm64_norm]
theorem bytesToBv8_length (bs : Bytes) : (bytesToBv8 bs).length = bs.length :=
  List.length_map _

theorem hookSat_sessionShimBudget_of_rustAllocShimVm {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec) :
    HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec := by
  refine HookSat.mono h fun u R s0 hp => ⟨u, R, hp, fun sf hq => ?_⟩
  dsimp only [rustAllocShimVmSpec, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1.2.1, hq.2⟩

theorem hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
    memcpyRegionSpec, allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    rwa [sepConj_assoc]
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0f, hacp.2.1⟩, ?_⟩
    rwa [← sepConj_assoc]

theorem sepWP_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hf : P = T ∗ F) (h : SepWP prog ret s (T ∗ F) Q) : SepWP prog ret s P Q :=
  hf ▸ h

/-! ## 1. `rustDeallocBytesSpec` & `dealloc_bytes_placed_ok` -/

@[expose] def rustDeallocBytesSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × Nat × Nat) × M.σ) where
  pre := fun ((p, bs, n, align), st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = n ∧ (s.readReg64 .x2).toNat = align ∧
      bs.length = n ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p n align ∗ (p ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun ((_, _, n, align), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents n align) st) sf ∗ stackAt s0.sp allocHookStack

theorem dealloc_bytes_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {H : LibsignalHooks} {i : Nat} [IsLsBlockProg prog i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocBytesSpec M A lim) := by
  have hd : subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_of_mem hdealloc (by decide) hi hunmut
  apply subroutine_ok_outcome_intro
  intro ⟨⟨p, bs, n, align⟩, st⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (p, n, align, st) s0 ∗ R := by
    unfold rustDeallocBytesSpec at hpre
    unfold rustCliDeallocBudgetSpec
    dsimp only at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlen, hlr⟩, hpre⟩
    refine ⟨⟨hx0, hx1, hx2, hlr⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpre ⊢
    refine Satisfies.mono ?_ hpre
    rw [← hlen]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pointsToBytes_entails_memRegion p bs)))
  refine (hd.to_outcome (p, n, align, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    unfold rustCliDeallocBudgetSpec at hpost
    unfold rustDeallocBytesSpec
    dsimp only at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hacp, _⟩, hpost⟩
    exact ⟨hacp.2.1, hpost⟩
  · exact Or.inr hrest

/-! ## 2. `<PrivateKey>::serialize` (Block `208`) -/

private theorem stackAt_privKeySerialize (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 := stackAt_split_top sp 32 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp allocHookStack 4 (by decide)
  have h3 : (32 + allocHookStack : Nat) = allocHookStack + 8 * 4 := by decide
  have h4 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 4) = 32#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

@[expose] def privKeySerializePlacedEvents : List AllocEvent :=
  rustAllocEvents 32 1

@[expose] def PrivKeySerializePlacedEnv (evs : List AllocEvent) : Prop :=
  evs = privKeySerializePlacedEvents

@[expose] def privKeySerializePlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun ((privKeyPtr, sk, outVecPtr), st) s =>
    ⌜s.readReg64 .x0 = privKeyPtr ∧ s.readReg64 .x8 = outVecPtr ∧ sk.length = 32 ∧
      FitsEvents M lim st privKeySerializePlacedEvents⌝ ∗
      (privKeyPtr ↦ₛ sk) ∗ cells outVecPtr 3 ∗
      (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun ((privKeyPtr, sk, outVecPtr), st) s0 sf =>
    ∃∗ bufPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ bufPtr ≠ 0⌝ ∗ (privKeyPtr ↦ₛ sk) ∗
      (outVecPtr ↦₆₄ 32#64) ∗ ((outVecPtr + 8#64) ↦₆₄ bufPtr) ∗ ((outVecPtr + 16#64) ↦₆₄ 32#64) ∗
      (bufPtr ↦ₛ sk) ∗ A.live bufPtr 32 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents privKeySerializePlacedEvents st) sf

theorem privKeySerialize_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H) (blkPl_208).base
      (privKeySerializePlacedSpec M A lim) := by
  unfold privKeySerializePlacedSpec privKeySerializePlacedEvents
  simp only [stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨privKeyPtr, sk, outVecPtr⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = privKeyPtr› ‹s0.readReg64 .x8 = outVecPtr›
  obtain ⟨w0, w1, w2, w3, _, hsk_cells⟩ := exists_unpack64_of_length_32 ‹sk.length = 32›
  have hfe_raw : FitsEvent M lim st (.alloc 32) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 32 1)› :
      FitsEvents M lim st [.alloc 32]).1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (32 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (32, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  conv => arg 4; simp only [hm32, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hsk_cells (s0.readReg64 (Reg.gpr 0#5))]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  simp only [hsk_cells, sepConj_assoc]
  wp_done

theorem privKeySerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H) (blkPl_208).base
      (privKeySerializePlacedSpec M A lim) :=
  privKeySerialize_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 3. `<PublicKey>::serialize` Allocating & Raw-Stack Variants (Block `205`) -/

private theorem memRegion_33_cells_alloc (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗ ((a + 17#64) ↦₆₄ u1) ∗ ((a +
        25#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 1 32 (by decide), memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide), memRegion_one, memRegion_eight,
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem bytesToBv8_encodeEC_alloc (bs : Bytes) :
    bytesToBv8 (encodeEC bs) = 5#8 :: bytesToBv8 bs := rfl

@[expose] def ecPubKeySerializeAllocEvents : List AllocEvent :=
  rustAllocEvents 33 1

@[expose] def EcPubKeySerializeAllocEnv (evs : List AllocEvent) : Prop :=
  evs = ecPubKeySerializeAllocEvents

@[expose] def ecPubKeySerializeAllocPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × Bytes) × M.σ) where
  pre := fun ((keyPtr, keyBytes), st) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32 ∧
      FitsEvents M lim st ecPubKeySerializeAllocEvents⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
      (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool lim st s
  post := fun ((keyPtr, keyBytes), st) s0 sf =>
    ∃∗ slicePtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 = 33#64 ∧
        slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
      A.live slicePtr 33 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗
      A.pool lim (M.stepEvents ecPubKeySerializeAllocEvents st) sf

theorem ecPubKeySerialize_alloc_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeAllocPlacedSpec M A lim) := by
  unfold ecPubKeySerializeAllocPlacedSpec ecPubKeySerializeAllocEvents
  simp only [bytesToBv8_encodeEC_alloc, stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨keyPtr, keyBytes⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = keyPtr›
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by
    simp [bytesToBv8, ‹keyBytes.length = 32›]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hfe_raw : FitsEvent M lim st (.alloc 33) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 33 1)› :
      FitsEvents M lim st [.alloc 33]).1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (33 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  wp_call halloc' (33, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  conv => arg 4; simp only [memRegion_33_cells_alloc, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 =>
    SepWP.exists_elim fun b0 => ?_
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_done

theorem ecPubKeySerialize_alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeAllocPlacedSpec M A lim) :=
  ecPubKeySerialize_alloc_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

@[expose] def ecPubKeySerializeRawPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec ((BitVec 64 × Bytes) × M.σ) where
  pre := fun ((keyPtr, keyBytes), st) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32 ∧
      FitsEvents M lim st ecPubKeySerializeAllocEvents⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ stackAt (s.sp - 32#64) allocHookStack ∗
      cells (s.sp - 32#64) 4 ∗ A.pool lim st s
  post := fun ((keyPtr, keyBytes), st) s0 sf =>
    ∃∗ slicePtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 = 33#64 ∧
        slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
      A.live slicePtr 33 1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      cells (s0.sp - 32#64) 4 ∗ A.pool lim (M.stepEvents ecPubKeySerializeAllocEvents st) sf

theorem ecPubKeySerializeRaw_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeRawPlacedSpec M A lim) := by
  refine subroutine_ok_mono (ecPubKeySerialize_alloc_placed_ok_of_session hshim halloc) ?_ ?_
  · intro g R s0 hp
    simpa only [ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocPlacedSpec,
      stackAt_privKeySerialize, sepConj_assoc] using hp
  · intro g R s0 sf hq
    simpa only [ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocPlacedSpec,
      stackAt_privKeySerialize, sepConj_assoc] using hq

theorem ecPubKeySerializeRaw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeRawPlacedSpec M A lim) :=
  ecPubKeySerializeRaw_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 4. `<RawVecInner>::finish_grow [local#1]` (Block `45`) -/

private theorem umulh_104_eq_zero {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    BitVec.truncate 64 ((104#128 * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth]
  have h1 : (104#128 : BitVec 128).toNat = 104 := rfl
  have h2 : new.toNat < 2 ^ 128 := by omega
  have h3 : 104 * new.toNat < 2 ^ 128 := by omega
  rw [h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : 104 * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_104_toNat {new : BitVec 64} (h : new.toNat * 104 < 2 ^ 64) :
    (104#64 * new).toNat = new.toNat * 104 := by
  rw [BitVec.toNat_mul]
  have : (104#64 : BitVec 64).toNat = 104 := rfl
  rw [this, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_104_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 < 2 ^ 64) : 104#64 * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_104_toNat h] at ht
  change new.toNat * 104 = 0 at ht
  omega

private theorem hi_104_eq_false {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    (9223372036854775800#64).ult (104#64 * new) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, mul_104_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 104)
  omega

private theorem beq_mul_104_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 ≤ 9223372036854775800) : (104#64 * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_104_ne_zero h0 (by omega)

private theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧
      rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩

@[expose] def finishGrowZeroEvents (new : BitVec 64) : List AllocEvent :=
  rustAllocEvents (new.toNat * 104) 8

@[expose] def FinishGrowZeroEnv (new : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = finishGrowZeroEvents new

@[expose] def finishGrowZeroSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FinishGrowGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (finishGrowZeroEvents new)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack
  post := fun ((out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
      A.pool lim (M.stepEvents (finishGrowZeroEvents new) st) sf ∗
      cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finishGrowZero_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec M A lim) := by
  unfold finishGrowZeroSpec finishGrowZeroEvents
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩, st⟩
  dsimp only at *
  subst fsp cap
  have hbound : new.toNat * 104 ≤ 9223372036854775800 := by omega
  have humulh := umulh_104_eq_zero hbound
  have hhi := hi_104_eq_false hbound
  have hcbz := beq_mul_104_zero_eq_false ‹0 < new.toNat› hbound
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have h8le : 8 ≤ new.toNat * 104 := by omega
  have hev_eq : rustAllocEvents (new.toNat * 104) 8 = [.alloc (new.toNat * 104)] := by
    simp only [rustAllocEvents, (by decide : (8 : Nat) ≤ 16), h8le, and_self, ↓reduceIte]
  have hfe_raw : FitsEvent M lim st (.alloc (new.toNat * 104)) :=
    (hev_eq ▸ ‹FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8)›).1
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hpos : 0 < new.toNat * 104 := by omega
  have hal : (8 : Nat) ≤ 2 ^ 31 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_clean_setMem
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_clean_setMem
  dsimp only [rustAllocEvents] at halloc'
  wp_call halloc' (new.toNat * 104, 8, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  conv => arg 4; simp only [rustAllocEvents, (by decide : (8 : Nat) ≤ 16), h8le, and_self,
    ↓reduceIte]
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  wp_done

theorem finishGrowZero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec M A lim) :=
  finishGrowZero_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

/-! ## 5. `<RawVec<Chain>>::grow_one` Zero-Capacity Variants (Block `43`) -/

private theorem stackAt_growOneChain (sp : BitVec 64) :
    memRegion (sp - 4208#64) 80 ∗ memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      cells (sp - 64#64) 8 ∗ cells (sp - 112#64) 6 ∗ stackAt (sp - 112#64) allocHookStack := by
  have htop1 := stackAt_split_top sp 32 allocHookStack (by decide)
  have htop2 := stackAt_split_top sp 80 (32 + allocHookStack) (by decide)
  have hc1 := stackAt_split_cells sp (48 + allocHookStack) 8 (by decide)
  have hc2 := stackAt_split_cells (sp - 64#64) allocHookStack 6 (by decide)
  have hn1 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have hn2 : BitVec.ofNat 64 (80 + (32 + allocHookStack)) = 4208#64 := rfl
  have hn3 : (80 + (32 + allocHookStack) : Nat) = (48 + allocHookStack) + 8 * 8 := by decide
  have hn4 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  have hn5 : (48 + allocHookStack : Nat) = allocHookStack + 8 * 6 := by decide
  have hn6 : BitVec.ofNat 64 (8 * 6) = 48#64 := rfl
  have hn7 : sp - 64#64 - 48#64 = sp - 112#64 := by bv_arith
  rw [hn1] at htop1
  rw [hn2] at htop2
  rw [hn4] at hc1
  rw [hn6, hn7] at hc2
  rw [← htop1, ← htop2, hn3, hc1, hn5, hc2]
  sep_ac_rfl

@[expose] def growOneChainZeroEvents : List AllocEvent :=
  rustAllocEvents 416 8

@[expose] def GrowOneChainZeroEnv (evs : List AllocEvent) : Prop :=
  evs = growOneChainZeroEvents

@[expose] def growOneChainZeroPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((vecPtr, oldPtr), st) s =>
    ⌜s.readReg64 .x0 = vecPtr ∧ FitsEvents M lim st growOneChainZeroEvents⌝ ∗
      (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool lim st s ∗
      cells (s.sp - 64#64) 8 ∗ cells (s.sp - 112#64) 6 ∗ stackAt (s.sp - 112#64) allocHookStack
  post := fun ((vecPtr, _oldPtr), st) s0 sf =>
    ∃∗ newPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗
      (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
      A.live newPtr 416 8 ∗ memRegion newPtr 416 ∗
      A.pool lim (M.stepEvents growOneChainZeroEvents st) sf ∗
      cells (s0.sp - 64#64) 8 ∗ cells (s0.sp - 112#64) 6 ∗ stackAt (s0.sp - 112#64) allocHookStack

theorem growOneChain_zero_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)) := by
  unfold withLsCodeLoaded growOneChainZeroPlacedSpec growOneChainZeroEvents
  cells_unfold
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_43).rebase (blkPl_43).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finishGrowZero_placed_ok_of_session hshim halloc))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0
  simp only [withLsCodeLoaded, finishGrowZeroSpec, finishGrowZeroEvents, cells,
    sepExists_sepConj_right, sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hfg0
  wp_init x s0
  rcases x with ⟨⟨vecPtr, oldPtr⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfe1 : FitsEvent M lim st (.alloc 416) :=
    (by simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 416 8)› :
      FitsEvents M lim st [.alloc 416]).1
  subst vecPtr
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
  wp_steps_sync_pool (lsmpl.base 45)
  wp_clean_setMem
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl1
  wp_call hfg0 ((s0.sp - 56#64, 0#64, oldPtr, 4#64, [], v_stk_7, v_stk_8, v_stk_9, s0.sp - 64#64), st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  wp_clean_setMem
  wp_done

theorem growOneChain_zero_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)) :=
  growOneChain_zero_placed_ok_of_session (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

@[expose] def growOneChainZeroRegionPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((vecPtr, oldPtr), st) s =>
    ⌜s.readReg64 .x0 = vecPtr ∧ FitsEvents M lim st growOneChainZeroEvents⌝ ∗
      (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool lim st s ∗
      memRegion (s.sp - 4208#64) 80 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack
  post := fun ((vecPtr, _oldPtr), st) s0 sf =>
    ∃∗ newPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗
      (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr + 8#64) ↦₆₄ newPtr) ∗
      A.live newPtr 416 8 ∗ memRegion newPtr 416 ∗
      A.pool lim (M.stepEvents growOneChainZeroEvents st) sf ∗
      memRegion (s0.sp - 4208#64) 80 ∗ memRegion (s0.sp - 4128#64) 32 ∗
      stackAt s0.sp allocHookStack

theorem growOneChain_zero_region_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) := by
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec M A lim)).pre g s0 ∗ R := by
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpre
  refine ((growOneChain_zero_placed_ok_of_session hshim halloc).to_outcome
    g R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem growOneChain_zero_region_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroRegionPlacedSpec M A lim)) :=
  growOneChain_zero_region_placed_ok_of_session
    (hookSat_sessionShimBudget_of_rustAllocShimVm hshim) halloc

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget
