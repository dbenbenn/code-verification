/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMultPlaced -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded `gf::parallel_mult`

Thin budget-pool wrapper delegating to `PointsToPolysSumMultPlaced.parallelMult_placed_sepWP`
and transporting `A.pool lim st` via `VmPreserved`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16 parallelMult)
open CryptoVerification.SpqrV1.GF.Mul2U16 (OnceCallHookOk tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (onceScratch416 shiftSlotsRawAt_pl)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget)

/-- Budget-threaded full inlined `spqr::encoding::gf::parallel_mult` (`+2736 -> +3784`),
    delegating to the unified `VmPreserved`-threaded proof in `PointsToPolysSumMultPlaced`. -/
theorem parallelMult_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    (hOnce : OnceCallHookOk (Rust.withPanics ext))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (cs : List GF16) (hcs_ne : cs ≠ []) (hn : cs.length ≤ 0x0555555555555555)
    (yv : BitVec 16)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp clonePtr v24 v25 v26 v27 u112 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2736#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cs.length)
    (hx21 : s.readReg64 .x21 = BitVec.zeroExtend 64 yv)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hx24 : s.readReg64 .x24 = v24)
    (hx25 : s.readReg64 .x25 = v25)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 : State,
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 3784#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 cs.length →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = v24 → s1.readReg64 .x25 = v25 →
      s1.readReg64 .x26 = v26 → s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 → s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16SliceAt clonePtr (parallelMult ⟨yv⟩ cs) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
         ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
         ∃∗ u112' : BitVec 64, ∃∗ u136' : BitVec 64,
           ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
           shiftSlotsRawAt_pl fsp ∗ onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       gf16SliceAt clonePtr cs ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
       ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗ onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (CryptoVerification.SpqrV1.Poly.NextChunk.parallelMult_placed_sepWP hOnce cs hcs_ne hn yv
      s hcl fsp clonePtr v24 v25 v26 v27 u112 u136 hfsp_align
      (A.pool lim st s ∗ Frame)
      hpc hrun hsp hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
  intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  simp only [sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u112'
  apply SepWP.exists_elim; intro u136'
  have hpool : A.pool lim st s = A.pool lim st s1 :=
    (A.pool_transport lim st s s1 hvm1).symm
  rw [hpool]
  refine SepWP.weaken_pre ?_
    (hcont s1 hcl1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)
  refine Entails.trans (Entails.of_eq (show
    gf16SliceAt clonePtr (parallelMult ⟨yv⟩ cs) ∗
      ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
      ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
      ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
      shiftSlotsRawAt_pl fsp ∗ onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s1 ∗ Frame =
    A.pool lim st s1 ∗
      gf16SliceAt clonePtr (parallelMult ⟨yv⟩ cs) ∗
      ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ v24) ∗
      ((fsp + 80#64) ↦₆₄ v26) ∗ ((fsp + 96#64) ↦₆₄ v25) ∗
      (((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt_pl fsp ∗ onceScratch416 fsp ∗ stackAt fsp allocHookStack ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) by sep_ac_rfl)) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact Entails.sepExists_right u112' (Entails.sepExists_right u136' (Entails.refl _))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux
