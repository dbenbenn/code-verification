/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FinishGrowBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import VerifiedLibraries.RustStd.Proofs.CoreFmt.MallocngBudgetRdl
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `RustCliAllocBudget` Adapter and Bridges for `core::fmt::write` and `format_inner`

Connects `VerifiedLibraries.RustStd`'s concrete ARM64 `MultiPlacedLib` proofs (`coreMultiLib`,
`coreFmtMultiLib`, and `allocMultiLib`) to `LibsignalBinary.Heap.RustCliAllocBudget M`:

- **Linker symbol constants & 1- and 2-hop `b`-stub lifts:** `lsFmtWriteSym` and `lsFormatInnerSym`
  (`libsignal_session` GNU-target crate disambiguators) bridged to the pinned `rustc 1.98.1`
  `aarch64-unknown-linux-musl` sysroot symbols `coreFmtWriteSym` and `allocFormatInnerSym`.
- **`AllocEvent` isomorphism & `toRustAllocBudget M A lim`:** bidirectional mapping between
  `VerifiedLibraries.Mallocng.AllocEvent` and `LibsignalBinary.Heap.AllocEvent`, plus the
  `PoolMemTransport` class (with automatic instances for all `mallocng` and `fineCostModel`
  pools, including `mallocngHookRustCliAllocBudget` and `fineHookRustCliAllocBudget`).
- **Callee subroutine bridges:** lifts `rustCliAllocBudgetSpecBase M A lim false`,
  `rustCliReallocBudgetSpecBase M A lim`, `rustAllocShimVmSpec`, and `memcpySymWords` /
  `allocMemcpyVmSpec` directly to `rustBudgetAllocSpec`, `rustBudgetReallocSpec`,
  `budgetAllocShimSpec`, and `budgetMemcpySpec`.
- **`Vec<u8>` ↔ `FmtBuf` bridges:** definitional (`rfl`) equivalence between
  `Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗ fmtBufVecAt ...` and
  `CryptoVerification.RustHeap.vecU8At A.repAlloc out cap ptr bs`, yielding both exit
  entailments (`⊢ vecU8 A.repAlloc out bs` and `⊢ ∃∗ bs', vecU8 A.repAlloc out bs'`) and entry
  decomposition (`vecU8_entails_exists_fmtBuf`).
- **Known-bytes `FmtBuf` run & `FormatInnerBudgetSafe` algebra:** shared helper lemmas discharging
  `FormatInnerBudgetSafe` and computing exact byte/event outputs for concrete CLI call shapes.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj

open Arm64 Arm64.Obj Arm64.Process SepProp
open Arm64.Program (HooksUnfetched)
open ProofLib hiding MallocngAddrs
open ProofLib.ProgramReflection
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv FitsEvent
   FitsEvents MallocngCostModelIface MallocngCostModelSound NullAllowed OomPreserved
   PoolPreserved RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntriesBase RustLayoutOk
   VmMemPreserved VmPreserved
   mallocngBudgetPoolAt_transport_mem mallocngRustCliAllocBudget mallocngRustCliAllocBudgetAt
   rustCliAllocBudgetSpecBase rustCliReallocBudgetSpecBase)
open LibsignalBinary.Heap.Fine (fineCostModel fineRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec checkBranchStub2 rustAllocShimVmSpec subroutine_ok_of_branchStub
   subroutine_ok_of_branchStub2 subroutine_ok_of_branchStub2_wordTree
   subroutine_ok_of_branchStub_wordTree)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (fineHookRustCliAllocBudget mallocngHookBudgetPool_transport_mem
   mallocngHookRustCliAllocBudget)
open VerifiedLibraries.Mallocng (MallocngAddrs mallocngAddrsOfPlacement mallocngAlignedEffSize)
open VerifiedLibraries.Mallocng.Proofs (memcpySymWords)
open VerifiedLibraries.RustStd
  (FmtBuf FmtBufStart FmtCall FmtInnerBudgetArgsOk FmtOp FmtOpsAbort FmtOpsRun FmtReaches FmtRun
   FmtWriteFrame FormatInnerBudgetSafe IoCallFrame RustAllocBudget StringBufAppend
   StringBufAppendPanics StringWriteAddrs allocFormatInnerSym budgetAllocShimSpec budgetAllocShim_ok
   budgetMemcpySpec budgetMemcpy_ok_all_of_hasWords budgetMemcpy_ok_of_hasWords checkShimInstrsAt
   coreFmtWriteSym fmtBufVecAt fmtEstimatedCapacity fmtInnerBudgetOom fmtInnerBudgetPanic
   fmtInnerBudgetStep fmtInnerBudgetW fmtLiteralLen fmtSrcBytes rustBudgetAllocSpec
   rustBudgetReallocSpec stringAppendEvents stringGrowCap stringNextCap)

/-! ## Linker Symbol Names (`libsignal_session` vs `rustc 1.98.1` musl sysroot) -/

/-- Mangled `core::fmt::write` symbol referenced by `libsignal_session`. -/
abbrev lsFmtWriteSym : String :=
  "_RNvNtCskxtBwYRO61I_4core3fmt5write"

/-- Mangled `alloc::fmt::format::format_inner` symbol referenced by `libsignal_session`. -/
abbrev lsFormatInnerSym : String :=
  "_RNvNvNtCs69KKACWg7bl_5alloc3fmt6format12format_inner"

theorem sysrootFmtWriteSym_eq :
    coreFmtWriteSym = "core::fmt::write" := rfl

theorem sysrootFormatInnerSym_eq :
    allocFormatInnerSym = "alloc::fmt::format::format_inner" := rfl

/-! ## `AllocEvent` Isomorphism (`VerifiedLibraries.Mallocng` ↔ `LibsignalBinary.Heap`) -/

/-- Map a `VerifiedLibraries.Mallocng.AllocEvent` to the identical `LibsignalBinary.Heap.AllocEvent`. -/
@[expose] def toCliAllocEvent : VerifiedLibraries.Mallocng.AllocEvent → AllocEvent
  | .alloc sz => .alloc sz
  | .aligned al sz => .aligned al sz
  | .free al sz => .free al sz
  | .realloc al old new => .realloc al old new

/-- Map a `LibsignalBinary.Heap.AllocEvent` to the identical `VerifiedLibraries.Mallocng.AllocEvent`. -/
@[expose] def ofCliAllocEvent : AllocEvent → VerifiedLibraries.Mallocng.AllocEvent
  | .alloc sz => .alloc sz
  | .aligned al sz => .aligned al sz
  | .free al sz => .free al sz
  | .realloc al old new => .realloc al old new

/-- Pull back a `LibsignalBinary.Heap.AllocEvent` envelope predicate to `VerifiedLibraries.Mallocng.AllocEvent`. -/
@[expose] def toRustStdEnv (Env : List AllocEvent → Prop) :
    List VerifiedLibraries.Mallocng.AllocEvent → Prop :=
  fun evs => Env (evs.map toCliAllocEvent)

/-- `LibsignalBinary.Heap.AllocEvent` list emitted by a single `String` growth step from capacity
    `oldCap` to `newCap` (`alloc(newCap, 1)` when `oldCap = 0`, else `realloc(oldCap, newCap, 1)`). -/
@[expose] def stringGrowStepEvents (oldCap newCap : Nat) : List AllocEvent :=
  if oldCap = 0 then LibsignalBinary.Heap.rustAllocEvents newCap 1
  else LibsignalBinary.Heap.rustReallocEvents oldCap newCap 1

theorem toCliAllocEvent_ofCliAllocEvent (ev : AllocEvent) :
    toCliAllocEvent (ofCliAllocEvent ev) = ev := by
  cases ev <;> rfl

theorem ofCliAllocEvent_toCliAllocEvent (ev : VerifiedLibraries.Mallocng.AllocEvent) :
    ofCliAllocEvent (toCliAllocEvent ev) = ev := by
  cases ev <;> rfl

theorem map_toCliAllocEvent_ofCliAllocEvent (evs : List AllocEvent) :
    (evs.map ofCliAllocEvent).map toCliAllocEvent = evs := by
  induction evs with
  | nil => rfl
  | cons ev rest ih => simp only [List.map_cons, toCliAllocEvent_ofCliAllocEvent, ih]

theorem map_ofCliAllocEvent_toCliAllocEvent (evs : List VerifiedLibraries.Mallocng.AllocEvent) :
    (evs.map toCliAllocEvent).map ofCliAllocEvent = evs := by
  induction evs with
  | nil => rfl
  | cons ev rest ih => simp only [List.map_cons, ofCliAllocEvent_toCliAllocEvent, ih]

theorem map_toCliAllocEvent_rustAllocEvents (size align : Nat) :
    (VerifiedLibraries.RustStd.rustAllocEvents size align).map toCliAllocEvent =
      LibsignalBinary.Heap.rustAllocEvents size align := by
  unfold VerifiedLibraries.RustStd.rustAllocEvents LibsignalBinary.Heap.rustAllocEvents
  split <;> rfl

theorem map_toCliAllocEvent_rustReallocEvents (old new align : Nat) :
    (VerifiedLibraries.RustStd.rustReallocEvents old new align).map toCliAllocEvent =
      LibsignalBinary.Heap.rustReallocEvents old new align := by
  unfold VerifiedLibraries.RustStd.rustReallocEvents LibsignalBinary.Heap.rustReallocEvents
  split <;> rfl

theorem map_toCliAllocEvent_stringAppendEvents (st : FmtBuf) (n : Nat)
    (hcap : st.cap.toNat < 2 ^ 64 := BitVec.isLt st.cap) :
    (stringAppendEvents st n).map toCliAllocEvent =
      if st.bytes.length + n ≤ st.cap.toNat then st.evs.map toCliAllocEvent
      else st.evs.map toCliAllocEvent ++
        stringGrowStepEvents st.cap.toNat (stringGrowCap st.cap.toNat st.bytes.length n) := by
  have _ := hcap
  unfold stringAppendEvents stringGrowStepEvents
  split
  · rfl
  · rw [List.map_append]
    have hzero : (st.cap = 0#64) ↔ (st.cap.toNat = 0) :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    by_cases hc : st.cap = 0#64
    · simp only [hc, ↓reduceIte]
      exact congrArg (st.evs.map toCliAllocEvent ++ ·) (map_toCliAllocEvent_rustAllocEvents _ 1)
    · have hcn : st.cap.toNat ≠ 0 := fun h => hc (hzero.mpr h)
      simp only [hc, hcn, ↓reduceIte]
      exact congrArg (st.evs.map toCliAllocEvent ++ ·) (map_toCliAllocEvent_rustReallocEvents _ _ 1)

/-! ## Process & Virtual-Memory Preservation Bridges -/

theorem allocCallPreserved_iff_ioCallFrame {s0 sf : State} :
    AllocCallPreserved s0 sf ↔ IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  unfold AllocCallPreserved IoCallFrame
  constructor
  · rintro ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩
    exact ⟨⟨hsig, htp, hbrks, horc, hsym⟩, hfs, htr⟩
  · rintro ⟨⟨hsig, htp, hbrks, horc, hsym⟩, hfs, htr⟩
    exact ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩

theorem allocCallPreserved_of_ioCallFrame {s0 sf : State}
    (hio : IoCallFrame s0 sf) (hfs : sf.fs = s0.fs) (htr : sf.trace = s0.trace) :
    AllocCallPreserved s0 sf :=
  allocCallPreserved_iff_ioCallFrame.mpr ⟨hio, hfs, htr⟩

theorem vmPreserved_of_fmtWriteFrame {s s' : State} (h : FmtWriteFrame s s') :
    VmPreserved s s' :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.1⟩,
   h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2,
   FdsHiFrame.of_fs_eq h.2.1⟩

theorem pool_of_fmtWriteFrame {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s s' : State} (h : FmtWriteFrame s s') :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_transport lim st s s' (vmPreserved_of_fmtWriteFrame h)

theorem rustLayoutOk_iff (size align : Nat) :
    VerifiedLibraries.RustStd.RustLayoutOk size align ↔ RustLayoutOk size align := by
  unfold VerifiedLibraries.RustStd.RustLayoutOk RustLayoutOk LayoutOk
  tauto

/-! ## `PoolMemTransport` and `toRustAllocBudget` Adapter -/

/-- `A.pool lim st` depends on process/VM state only through `VmMemPreserved` (`brkStart`, `brk`,
    `tpidrEl0`, `physMemAvail`, and `mem.perm`, independent of `fs.fds`), matching
    `VerifiedLibraries.RustStd.VmPreserved`. Satisfied automatically by all `mallocng` and
    `fineCostModel` budget pools. -/
class PoolMemTransport {M : AllocCostModel} (A : RustCliAllocBudget M) : Prop where
  pool_transport_mem : ∀ (lim : BudgetLimits) (st : M.σ) {s s' : State},
    VmMemPreserved s s' → A.pool lim st s' = A.pool lim st s

instance instPoolMemTransportMallocngAt (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I) (γ : GhostName) (addrs : MallocngAddrs)
    (tp brkStart : BitVec 64) :
    PoolMemTransport (mallocngRustCliAllocBudgetAt M I hS γ addrs tp brkStart) where
  pool_transport_mem lim st _ _ hvm :=
    mallocngBudgetPoolAt_transport_mem M I γ addrs tp brkStart lim st hvm

instance instPoolMemTransportMallocng (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolMemTransport (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart) where
  pool_transport_mem lim st _ _ hvm :=
    mallocngBudgetPoolAt_transport_mem M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st hvm

instance instPoolMemTransportFine (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolMemTransport (fineRustCliAllocBudget γ mpl tp brkStart) where
  pool_transport_mem lim st _ _ hvm :=
    mallocngBudgetPoolAt_transport_mem fineCostModel _ γ (mallocngAddrsOfPlacement mpl) tp brkStart
      lim st hvm

instance instPoolMemTransportMallocngHook (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hS : MallocngCostModelSound M I) (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolMemTransport (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart) where
  pool_transport_mem lim st _ _ hvm :=
    mallocngHookBudgetPool_transport_mem M I γ mpl tp brkStart lim st hvm

instance instPoolMemTransportFineHook (γ : GhostName) (mpl : MultiPlacement)
    (tp brkStart : BitVec 64) :
    PoolMemTransport (fineHookRustCliAllocBudget γ mpl tp brkStart) where
  pool_transport_mem lim st _ _ hvm :=
    mallocngHookBudgetPool_transport_mem fineCostModel _ γ mpl tp brkStart lim st hvm

theorem not_nullAllowed_of_cliFitsEvent {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {size align : Nat} (hal : align ≤ 2 ^ 31)
    (h : FitsEvent M lim st (.alloc size) ∨
      FitsEvent M lim st (.aligned (max align 8) size) ∨
      ∃ old, FitsEvent M lim st (.realloc align old size)) :
    ¬ VerifiedLibraries.RustStd.NullAllowed size align := by
  change ¬ NullAllowed size align
  rcases h with hAlloc | hAligned | ⟨old, hRealloc⟩
  · rcases hAlloc with ⟨_, _, _, hva⟩
    have hreq : size ≤ M.stepReserve (.alloc size) st := M.req_le_stepReserve (.alloc size) st
    unfold NullAllowed; omega
  · rcases hAligned with ⟨_, _, _, hva⟩
    have hsize_eff : size ≤ (AllocEvent.aligned (max align 8) size).reqBytes := by
      dsimp only [AllocEvent.reqBytes, mallocngAlignedEffSize]
      split <;> omega
    have hreq : (AllocEvent.aligned (max align 8) size).reqBytes ≤
        M.stepReserve (.aligned (max align 8) size) st :=
      M.req_le_stepReserve (.aligned (max align 8) size) st
    unfold NullAllowed; omega
  · rcases hRealloc with ⟨_, _, _, hva⟩
    have hreq : size ≤ M.stepReserve (.realloc align old size) st :=
      M.req_le_stepReserve (.realloc align old size) st
    unfold NullAllowed; omega

/-- Adapt `(A : RustCliAllocBudget M)` at `lim : BudgetLimits` into a
    `VerifiedLibraries.RustStd.RustAllocBudget` with `σ = M.σ`, `pool st s = A.pool lim st s`,
    and `live = A.live`. -/
@[expose] def toRustAllocBudget (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) : RustAllocBudget where
  σ := M.σ
  step ev st := M.step (toCliAllocEvent ev) st
  FitsEvent st ev := FitsEvent M lim st (toCliAllocEvent ev)
  pool st s := A.pool lim st s
  live := A.live
  block_valid p n al := by
    refine Entails.trans (A.block_valid p n al) ?_
    refine Entails.pure_left fun ⟨hp, hmod, hfit, hlay⟩ => ?_
    exact Entails.pure_right ⟨hp, hmod, hfit, (rustLayoutOk_iff n al).mpr hlay⟩ (Entails.refl _)
  pool_transport st _ _ hvm :=
    PoolMemTransport.pool_transport_mem lim st hvm
  fits_not_nullAllowed st size align hal hfit :=
    not_nullAllowed_of_cliFitsEvent hal hfit

theorem toRustAllocBudget_stepEvents (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (evs : List VerifiedLibraries.Mallocng.AllocEvent) (st : M.σ) :
    (toRustAllocBudget M A lim).stepEvents evs st =
      M.stepEvents (evs.map toCliAllocEvent) st := by
  induction evs generalizing st with
  | nil => rfl
  | cons ev rest ih =>
    simp only [RustAllocBudget.stepEvents, List.map_cons, AllocCostModel.stepEvents_cons]
    exact ih (M.step (toCliAllocEvent ev) st)

theorem toRustAllocBudget_fitsEvents (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (st : M.σ) (evs : List VerifiedLibraries.Mallocng.AllocEvent) :
    (toRustAllocBudget M A lim).FitsEvents st evs ↔
      FitsEvents M lim st (evs.map toCliAllocEvent) := by
  induction evs generalizing st with
  | nil => exact Iff.rfl
  | cons ev rest ih =>
    simp only [RustAllocBudget.FitsEvents, List.map_cons, LibsignalBinary.Heap.fitsEvents_cons]
    exact and_congr_right fun _ => ih (M.step (toCliAllocEvent ev) st)

theorem fitsEnv_toRustAllocBudget_of_cli (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) {st : M.σ} {Env : List AllocEvent → Prop}
    (h : FitsEnv M lim st Env) :
    VerifiedLibraries.RustStd.FitsEnv (toRustAllocBudget M A lim) st (toRustStdEnv Env) := by
  intro evs hevs
  rw [toRustAllocBudget_fitsEvents]
  exact h (evs.map toCliAllocEvent) hevs

/-! ## Callee Subroutine Bridges (`__rust_alloc`, `__rust_realloc`, Shim, `memcpy`) -/

/-- Bridge `rustCliAllocBudgetSpecBase M A lim false` directly to
    `rustBudgetAllocSpec (toRustAllocBudget M A lim)`. -/
theorem rustBudgetAlloc_of_cliBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (rustCliAllocBudgetSpecBase M A lim false)) :
    subroutine_ok P addr (rustBudgetAllocSpec (toRustAllocBudget M A lim)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, (st : M.σ)⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustBudgetAllocSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay⟩, hrest⟩
  have hpreC : s0.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, (rustLayoutOk_iff size align).mp hlay⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpecBase] at hpost
    dsimp only [rustBudgetAllocSpec]
    by_cases hz : sf.readReg64 .x0 = 0
    · simp only [hz, ↓reduceIte] at hpost ⊢
      exact hpost
    · simp only [hz, ↓reduceIte, Bool.false_eq_true] at hpost ⊢
      rw [toRustAllocBudget_stepEvents M A lim _ st, map_toCliAllocEvent_rustAllocEvents]
      exact hpost
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [rustCliAllocBudgetSpecBase] at hoom
    dsimp only [rustBudgetAllocSpec]
    rwa [toRustAllocBudget_fitsEvents M A lim st, map_toCliAllocEvent_rustAllocEvents]

/-- Bridge `rustCliReallocBudgetSpecBase M A lim` directly to
    `rustBudgetReallocSpec (toRustAllocBudget M A lim)`. -/
theorem rustBudgetRealloc_of_cliBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P addr (rustBudgetReallocSpec (toRustAllocBudget M A lim)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, (st : M.σ)⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustBudgetReallocSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlay, hleOld, hleNew⟩, hrest⟩
  have hpreC :
      s0.mem ⊨ (rustCliReallocBudgetSpecBase M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustCliReallocBudgetSpecBase]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, (rustLayoutOk_iff new align).mp hlay, hleOld, hleNew⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (p, old, align, new, bs, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliReallocBudgetSpecBase] at hpost
    dsimp only [rustBudgetReallocSpec]
    by_cases hz : sf.readReg64 .x0 = 0
    · simp only [hz, ↓reduceIte] at hpost ⊢
      exact hpost
    · simp only [hz, ↓reduceIte] at hpost ⊢
      rw [toRustAllocBudget_stepEvents M A lim _ st, map_toCliAllocEvent_rustReallocEvents]
      exact hpost
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [rustCliReallocBudgetSpecBase] at hoom
    dsimp only [rustBudgetReallocSpec]
    rwa [toRustAllocBudget_fitsEvents M A lim st, map_toCliAllocEvent_rustReallocEvents]

theorem rustBudgetAlloc_of_entriesBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] (lim : BudgetLimits) {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) :
    subroutine_ok P addrs.alloc (rustBudgetAllocSpec (toRustAllocBudget M A lim)) :=
  rustBudgetAlloc_of_cliBase (h.alloc lim)

theorem rustBudgetRealloc_of_entriesBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] (lim : BudgetLimits) {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) :
    subroutine_ok P addrs.realloc (rustBudgetReallocSpec (toRustAllocBudget M A lim)) :=
  rustBudgetRealloc_of_cliBase (h.realloc lim)

/-- Bridge `rustAllocShimVmSpec` (`emp` frame) to `budgetAllocShimSpec` (`Rust.hookFrame s.sp`). -/
theorem budgetAllocShim_of_vm {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr rustAllocShimVmSpec) :
    subroutine_ok P addr budgetAllocShimSpec := by
  apply subroutine_ok.of_codeLoaded
  intro () R s0 hpc hrun hpre hsp0 _hcl
  dsimp only [budgetAllocShimSpec] at hpre
  have hpre' : s0.mem ⊨ rustAllocShimVmSpec.pre () s0 ∗ (Rust.hookFrame s0.sp ∗ R) := by
    dsimp only [rustAllocShimVmSpec]
    rwa [emp_sepConj]
  refine h.mono_outcome () (Rust.hookFrame s0.sp ∗ R) s0 hpc hrun hpre' hsp0 fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec, budgetAllocShimSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.1.1, hpost.1.2.toVmMemPreserved⟩, hpost.2⟩
  · dsimp only [rustAllocShimVmSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustAllocShimVmSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustAllocShimVmSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem budgetAllocShim_of_hasInstrs {P : Program} {shimAddr : BitVec 64}
    (h : hasInstrs P shimAddr [.ret .x30]) :
    subroutine_ok P shimAddr budgetAllocShimSpec :=
  budgetAllocShim_ok h

/-- Bridge `allocMemcpyVmSpec` (`src ↦ₛ bs`) to `budgetMemcpySpec false`. -/
theorem budgetMemcpy_false_of_vm {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr allocMemcpyVmSpec) :
    subroutine_ok P addr (budgetMemcpySpec false) := by
  refine subroutine_ok_refine h fun (dst, src, bs) R s0 hm => ?_
  simp only [budgetMemcpySpec, fmtSrcBytes, Bool.false_eq_true, ↓reduceIte] at hm
  refine ⟨(dst, src, bs), hm, fun sf hpost => ?_⟩
  simp only [allocMemcpyVmSpec, budgetMemcpySpec, fmtSrcBytes, Bool.false_eq_true, ↓reduceIte]
    at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, hpost.1.2.1, hpost.1.2.2.toVmMemPreserved⟩, hpost.2⟩

/-- `budgetMemcpySpec true` (read-only source `src ↦ᵣ bs`) from `memcpySymWords` in `P`. -/
theorem budgetMemcpy_true_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr (budgetMemcpySpec true) :=
  budgetMemcpy_ok_of_hasWords true P memcpyAddr hsvc hhooks h_words

/-- `∀ ro, budgetMemcpySpec ro` from `memcpySymWords` in `P`. -/
theorem budgetMemcpy_all_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    ∀ ro, subroutine_ok P memcpyAddr (budgetMemcpySpec ro) :=
  budgetMemcpy_ok_all_of_hasWords P memcpyAddr hsvc hhooks h_words

/-! ## `Vec<u8>` (`CryptoVerification.RustHeap`) ↔ `FmtBuf` (`VerifiedLibraries.RustStd`) Bridges -/

/-- `Arm64.Rust.vecHeader` paired with `fmtBufVecAt (toRustAllocBudget M A lim)` is definitionally
    identical (`rfl`) to `CryptoVerification.RustHeap.vecU8At A.repAlloc`. -/
theorem vecHeader_fmtBufVecAt_eq_vecU8At (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
      fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs =
    CryptoVerification.RustHeap.vecU8At A.repAlloc out cap ptr bs :=
  rfl

theorem vecHeader_fmtBufVecAt_entails_vecU8At (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
      fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs ⊢
    CryptoVerification.RustHeap.vecU8At A.repAlloc out cap ptr bs :=
  Entails.refl _

theorem vecHeader_fmtBufVecAt_entails_vecU8 (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
      fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs ⊢
    CryptoVerification.RustHeap.vecU8 A.repAlloc out bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecHeader_fmtBufVecAt_entails_exists_vecU8 (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
      fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs ⊢
    ∃∗ bs' : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A.repAlloc out bs' :=
  Entails.sepExists_right bs (vecHeader_fmtBufVecAt_entails_vecU8 M A lim out cap ptr bs)

theorem vecU8At_entails_vecHeader_fmtBufVecAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8At A.repAlloc out cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
      fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs := by
  rw [← vecHeader_fmtBufVecAt_eq_vecU8At M A lim out cap ptr bs]
  dsimp only [fmtBufVecAt]
  rw [sepConj_comm (Arm64.Rust.vecHeader _ _ _ _) (⌜_⌝ ∗ _), sepConj_assoc]
  refine Entails.pure_left fun hinv => Entails.pure_right hinv ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Entry decomposition of `vecU8 A.repAlloc out bs` into an initial `FmtBuf` header + buffer for
    `core::fmt::write` on an existing `String`. -/
theorem vecU8_entails_exists_fmtBuf (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits)
    (out : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8 A.repAlloc out bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        Arm64.Rust.vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
        fmtBufVecAt (toRustAllocBudget M A lim) cap ptr bs := by
  unfold CryptoVerification.RustHeap.vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (vecU8At_entails_vecHeader_fmtBufVecAt M A lim out cap ptr bs))

/-! ## Linker Alias / Unconditional `b`-Stub Lift Lemmas -/

/-- `A.pool lim st` is invariant under `State.setPC`. -/
theorem pool_of_setPC {M : AllocCostModel} (A : RustCliAllocBudget M) [PoolMemTransport A]
    (lim : BudgetLimits) (st : M.σ) (s : State) (pc' : BitVec 64) :
    A.pool lim st (s.setPC pc') = A.pool lim st s :=
  PoolMemTransport.pool_transport_mem (A := A) (s := s) (s' := s.setPC pc') lim st
    (by cases s; exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩)

/-- `FmtInnerBudgetArgsOk` is invariant under `State.setPC`. -/
theorem fmtInnerBudgetArgsOk_setPC (P : Program) (B : RustAllocBudget) (st0 : B.σ)
    (va : StringWriteAddrs) (R : SepProp)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop)
    (stackBytes : Nat) (t0 : State) (pc' : BitVec 64) (cs : List FmtCall) :
    FmtInnerBudgetArgsOk P B st0 va R ArgStep ArgPanic ArgOom stackBytes (t0.setPC pc') cs =
      FmtInnerBudgetArgsOk P B st0 va R ArgStep ArgPanic ArgOom stackBytes t0 cs := by
  have hw : ∀ out,
      fmtInnerBudgetW B st0 va R (t0.setPC pc') out = fmtInnerBudgetW B st0 va R t0 out := by
    intro out; funext st s; cases t0; rfl
  have hp : fmtInnerBudgetPanic (t0.setPC pc') ArgPanic = fmtInnerBudgetPanic t0 ArgPanic := by
    funext c st sf; cases c <;> (cases t0; rfl)
  unfold FmtInnerBudgetArgsOk
  simp only [hw, hp]

/-- Lift `subroutine_ok` across a 1-instruction `b targetAddr` linker stub (`aliasAddr → targetAddr`)
    for `fmtWriteBudgetEnvSpec M A lim Env` (preserving all pure/frame postconditions). -/
theorem fmtWriteBudgetEnvSpec_of_branchStub {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop} {P : Program}
    (aliasAddr targetAddr : BitVec 64)
    (hStub : hasInstrs P aliasAddr [.b (targetAddr - aliasAddr)])
    (hTarget : subroutine_ok P targetAddr
      (LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok P aliasAddr
      (LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec M A lim Env) :=
  subroutine_ok_of_branchStub aliasAddr targetAddr hStub
    (by
      rintro ⟨_, _, st⟩ s pc'
      dsimp only [LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec]
      rw [pool_of_setPC A lim st s pc']
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    hTarget

/-- Lift `subroutine_ok` across a 2-hop `b` stub (`snapstubAddr → aliasAddr → targetAddr`) via
    `checkBranchStub2` over a `WordTree` for `fmtWriteBudgetEnvSpec M A lim Env`. -/
theorem fmtWriteBudgetEnvSpec_of_branchStub2_wordTree {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {P : Program} {t : WordTree} (n : Nat)
    (snapstubAddr aliasAddr targetAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr targetAddr = true)
    (hTarget : subroutine_ok P targetAddr
      (LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok P snapstubAddr
      (LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec M A lim Env) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr targetAddr hcode hwf
    hhookSnap hhookAlias hok
    (by
      rintro ⟨_, _, st⟩ s pc'
      dsimp only [LibsignalBinary.Heap.SpecBudget.fmtWriteBudgetEnvSpec]
      rw [pool_of_setPC A lim st s pc']
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    hTarget

/-- Lift `subroutine_ok` across a 1-instruction `b targetAddr` linker stub (`aliasAddr → targetAddr`)
    for `formatInnerBudgetEnvSpec M A lim Env`. -/
theorem formatInnerBudgetEnvSpec_of_branchStub {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop} {P : Program}
    (aliasAddr targetAddr : BitVec 64)
    (hStub : hasInstrs P aliasAddr [.b (targetAddr - aliasAddr)])
    (hTarget : subroutine_ok P targetAddr
      (LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec M A lim Env)) :
    subroutine_ok P aliasAddr
      (LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec M A lim Env) :=
  subroutine_ok_of_branchStub aliasAddr targetAddr hStub
    (by
      rintro ⟨_, st⟩ s pc'
      dsimp only [LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec]
      rw [pool_of_setPC A lim st s pc']
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    hTarget

/-- Lift `subroutine_ok` across a 2-hop `b` stub (`snapstubAddr → aliasAddr → targetAddr`) via
    `checkBranchStub2` over a `WordTree` for `formatInnerBudgetEnvSpec M A lim Env`. -/
theorem formatInnerBudgetEnvSpec_of_branchStub2_wordTree {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {P : Program} {t : WordTree} (n : Nat)
    (snapstubAddr aliasAddr targetAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr targetAddr = true)
    (hTarget : subroutine_ok P targetAddr
      (LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec M A lim Env)) :
    subroutine_ok P snapstubAddr
      (LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec M A lim Env) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr targetAddr hcode hwf
    hhookSnap hhookAlias hok
    (by
      rintro ⟨_, st⟩ s pc'
      dsimp only [LibsignalBinary.Heap.SpecBudget.formatInnerBudgetEnvSpec]
      rw [pool_of_setPC A lim st s pc']
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    hTarget

/-! ## Known-Bytes `FmtBuf` Run & `FormatInnerBudgetSafe` Algebra -/

/-- Bytes appended by `FmtCall` `c` when argument `idx` renders as `argBytes idx`. -/
@[expose] def callBytes (argBytes : Nat → List (BitVec 8)) : FmtCall → List (BitVec 8)
  | .writeStr _ bs => bs
  | .fmtArg idx _ _ _ => argBytes idx

/-- Argument callback step relation appending `argBytes idx` and returning `Ok`. -/
@[expose] def knownArgStep (argBytes : Nat → List (BitVec 8)) (c : FmtCall) (st : FmtBuf)
    (ok : Bool) (st' : FmtBuf) : Prop :=
  ok = true ∧ StringBufAppend st (callBytes argBytes c) st'

/-- Argument callback panic relation (`StringBufAppendPanics`). -/
@[expose] def knownArgPanic (argBytes : Nat → List (BitVec 8)) (c : FmtCall) (st : FmtBuf)
    (_ : State) : Prop :=
  StringBufAppendPanics st (callBytes argBytes c).length

/-- Argument callback out-of-memory relation (`¬ A.FitsEvents st0 (stringAppendEvents ...)`). -/
@[expose] def knownArgOom (B : RustAllocBudget) (st0 : B.σ) (argBytes : Nat → List (BitVec 8))
    (c : FmtCall) (st : FmtBuf) (_ : State) : Prop :=
  ¬ B.FitsEvents st0 (stringAppendEvents st (callBytes argBytes c).length)

theorem knownStep_iff (argBytes : Nat → List (BitVec 8)) (c : FmtCall) (st : FmtBuf) (ok : Bool)
    (st' : FmtBuf) :
    fmtInnerBudgetStep (knownArgStep argBytes) c st ok st' ↔
      ok = true ∧ StringBufAppend st (callBytes argBytes c) st' := by
  cases c <;> rfl

theorem knownOom_iff (B : RustAllocBudget) (st0 : B.σ) (argBytes : Nat → List (BitVec 8))
    (c : FmtCall) (st : FmtBuf) (sf : State) :
    fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes) c st sf ↔
      ¬ B.FitsEvents st0 (stringAppendEvents st (callBytes argBytes c).length) := by
  cases c <;> rfl

/-- Length, capacity, and cumulative `AllocEvent` log of a `FmtBuf` (carrying `LibsignalBinary.Heap.AllocEvent`). -/
structure CliBufShape where
  len : Nat
  cap : BitVec 64
  evs : List AllocEvent

/-- Advance a `CliBufShape` by appending `n` bytes. -/
@[expose] def CliBufShape.append (sh : CliBufShape) (n : Nat) : CliBufShape :=
  if sh.len + n ≤ sh.cap.toNat then
    ⟨sh.len + n, sh.cap, sh.evs⟩
  else
    let newCap := stringGrowCap sh.cap.toNat sh.len n
    ⟨sh.len + n, BitVec.ofNat 64 newCap, sh.evs ++ stringGrowStepEvents sh.cap.toNat newCap⟩

/-- Fold `CliBufShape.append` over a sequence of appended byte lengths `ns`. -/
@[expose] def CliBufShape.run (sh : CliBufShape) (ns : List Nat) : CliBufShape :=
  ns.foldl CliBufShape.append sh

/-- Initial `CliBufShape` of `String::with_capacity(cap0)`. -/
@[expose] def startCliBufShape (cap0 : Nat) : CliBufShape :=
  ⟨0, BitVec.ofNat 64 cap0,
    if cap0 = 0 then [] else LibsignalBinary.Heap.rustAllocEvents cap0 1⟩

/-- Exact `LibsignalBinary.Heap.AllocEvent` trace of appending `ns` byte slices onto an existing
    `String` of initial length `len0` and capacity `cap0`. -/
@[expose] def fmtWriteKnownEvents (len0 : Nat) (cap0 : BitVec 64) (ns : List Nat) :
    List AllocEvent :=
  ((CliBufShape.mk len0 cap0 []).run ns).evs

/-- Exact `LibsignalBinary.Heap.AllocEvent` trace of `format_inner` starting with
    `String::with_capacity(cap0)` and appending `ns` byte slices. -/
@[expose] def formatInnerKnownEvents (cap0 : Nat) (ns : List Nat) : List AllocEvent :=
  ((startCliBufShape cap0).run ns).evs

/-- Project a `FmtBuf` to its `CliBufShape`. -/
@[expose] def cliBufShapeOf (st : FmtBuf) : CliBufShape :=
  ⟨st.bytes.length, st.cap, st.evs.map toCliAllocEvent⟩

/-- Per-call appended byte lengths along `cs`. -/
abbrev callLens (argBytes : Nat → List (BitVec 8)) (cs : List FmtCall) : List Nat :=
  cs.map fun c => (callBytes argBytes c).length

theorem cliBufShape_of_start {cap0 : Nat} {st : FmtBuf} (h : FmtBufStart cap0 st) :
    cliBufShapeOf st = startCliBufShape cap0 := by
  rcases h with ⟨hbs, hcap, hevs⟩
  unfold cliBufShapeOf startCliBufShape
  split at hevs
  · rename_i hz
    rcases hevs with ⟨_, he⟩
    simp only [hbs, List.length_nil, hcap, he, List.map_nil, hz, ↓reduceIte]
  · rename_i hnz
    simp only [hbs, List.length_nil, hcap, hevs, hnz, ↓reduceIte,
      map_toCliAllocEvent_rustAllocEvents]

theorem map_stringAppendEvents_eq_cliBufShape (st : FmtBuf) (n : Nat) :
    (stringAppendEvents st n).map toCliAllocEvent = ((cliBufShapeOf st).append n).evs := by
  rw [map_toCliAllocEvent_stringAppendEvents st n]
  unfold cliBufShapeOf CliBufShape.append
  split <;> rfl

theorem cliBufShape_append {st st' : FmtBuf} {bs : List (BitVec 8)}
    (h : StringBufAppend st bs st') :
    cliBufShapeOf st' = (cliBufShapeOf st).append bs.length := by
  rcases h with ⟨hbs, hcap, hevs, _⟩
  have hev : st'.evs.map toCliAllocEvent = ((cliBufShapeOf st).append bs.length).evs := by
    rw [hevs, map_stringAppendEvents_eq_cliBufShape]
  unfold cliBufShapeOf CliBufShape.append stringNextCap at *
  split
  · rename_i hle
    simp only [hle, ↓reduceIte] at hcap hev
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hcap
    simp only [hbs, List.length_append, hcap, hev]
  · rename_i hnle
    simp only [hnle, ↓reduceIte] at hcap hev
    simp only [hbs, List.length_append, hcap, hev]

theorem cliBufShape_run_append (sh : CliBufShape) (ns ms : List Nat) :
    sh.run (ns ++ ms) = (sh.run ns).run ms :=
  List.foldl_append

theorem cliBufShape_run_cons (sh : CliBufShape) (n : Nat) (ns : List Nat) :
    sh.run (n :: ns) = (sh.append n).run ns :=
  rfl

theorem cliBufShape_append_evs_prefix (sh : CliBufShape) (n : Nat) :
    ∃ suf, (sh.append n).evs = sh.evs ++ suf := by
  unfold CliBufShape.append
  split
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨_, rfl⟩

theorem cliBufShape_run_evs_prefix (sh : CliBufShape) (ns : List Nat) :
    ∃ suf, (sh.run ns).evs = sh.evs ++ suf := by
  induction ns generalizing sh with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons n rest ih =>
    obtain ⟨s1, hs1⟩ := cliBufShape_append_evs_prefix sh n
    obtain ⟨s2, hs2⟩ := ih (sh.append n)
    exact ⟨s1 ++ s2, by rw [cliBufShape_run_cons, hs2, hs1, List.append_assoc]⟩

theorem run_known {argBytes : Nat → List (BitVec 8)} {cs : List FmtCall} {st : FmtBuf} {b : Bool}
    {st' : FmtBuf} (h : FmtRun (fmtInnerBudgetStep (knownArgStep argBytes)) cs st b st') :
    b = true ∧ cliBufShapeOf st' = (cliBufShapeOf st).run (callLens argBytes cs) ∧
      st'.bytes = st.bytes ++ cs.flatMap (callBytes argBytes) := by
  induction h with
  | nil st => exact ⟨rfl, rfl, by simp⟩
  | @cons_ok c cs st st' st'' b hstep _ ih =>
    obtain ⟨-, happ⟩ := (knownStep_iff argBytes c st true st').mp hstep
    obtain ⟨hb, hsh, hby⟩ := ih
    refine ⟨hb, ?_, ?_⟩
    · rw [hsh, cliBufShape_append happ]; rfl
    · rw [hby, happ.1, List.flatMap_cons, List.append_assoc]
  | cons_err hstep =>
    exact absurd ((knownStep_iff _ _ _ _ _).mp hstep).1 Bool.false_ne_true

theorem reaches_known {argBytes : Nat → List (BitVec 8)} {cs : List FmtCall} {st₀ st : FmtBuf}
    {c : FmtCall} (h : FmtReaches (fmtInnerBudgetStep (knownArgStep argBytes)) cs st₀ c st) :
    ∃ pre post, cs = pre ++ c :: post ∧
      cliBufShapeOf st = (cliBufShapeOf st₀).run (callLens argBytes pre) := by
  obtain ⟨pre, post, hcs, hrun⟩ := h
  exact ⟨pre, post, hcs, (run_known hrun).2.1⟩

theorem reaches_fmtWriteEvents_prefix {argBytes : Nat → List (BitVec 8)} {cs : List FmtCall}
    {st₀ st : FmtBuf} {c : FmtCall} (h0 : st₀.evs = [])
    (h : FmtReaches (fmtInnerBudgetStep (knownArgStep argBytes)) cs st₀ c st) :
    ∃ suf, fmtWriteKnownEvents st₀.bytes.length st₀.cap (callLens argBytes cs) =
      (stringAppendEvents st (callBytes argBytes c).length).map toCliAllocEvent ++ suf := by
  obtain ⟨pre, post, hcs, hsh⟩ := reaches_known h
  have hsh0 : cliBufShapeOf st₀ = ⟨st₀.bytes.length, st₀.cap, []⟩ := by
    simp only [cliBufShapeOf, h0, List.map_nil]
  rw [hsh0] at hsh
  obtain ⟨suf, hsuf⟩ := cliBufShape_run_evs_prefix
    (((CliBufShape.mk st₀.bytes.length st₀.cap []).run (callLens argBytes pre)).append
      (callBytes argBytes c).length)
    (callLens argBytes post)
  refine ⟨suf, ?_⟩
  rw [map_stringAppendEvents_eq_cliBufShape, hsh, ← hsuf, fmtWriteKnownEvents, hcs, callLens,
    List.map_append, List.map_cons, cliBufShape_run_append, cliBufShape_run_cons]

theorem reaches_formatInnerEvents_prefix {argBytes : Nat → List (BitVec 8)} {cs : List FmtCall}
    {cap0 : Nat} {st₀ st : FmtBuf} {c : FmtCall} (hstart : FmtBufStart cap0 st₀)
    (h : FmtReaches (fmtInnerBudgetStep (knownArgStep argBytes)) cs st₀ c st) :
    ∃ suf, formatInnerKnownEvents cap0 (callLens argBytes cs) =
      (stringAppendEvents st (callBytes argBytes c).length).map toCliAllocEvent ++ suf := by
  obtain ⟨pre, post, hcs, hsh⟩ := reaches_known h
  rw [cliBufShape_of_start hstart] at hsh
  obtain ⟨suf, hsuf⟩ := cliBufShape_run_evs_prefix
    (((startCliBufShape cap0).run (callLens argBytes pre)).append (callBytes argBytes c).length)
    (callLens argBytes post)
  refine ⟨suf, ?_⟩
  rw [map_stringAppendEvents_eq_cliBufShape, hsh, ← hsuf, formatInnerKnownEvents, hcs, callLens,
    List.map_append, List.map_cons, cliBufShape_run_append, cliBufShape_run_cons]

theorem not_appendPanics_of_fits (B : RustAllocBudget) {st0 : B.σ} {st : FmtBuf} {n : Nat}
    (hfit : B.FitsEvents st0 (stringAppendEvents st n)) :
    ¬ StringBufAppendPanics st n := by
  rintro ⟨hlt, hcase⟩
  have hnot : ¬ st.bytes.length + n ≤ st.cap.toNat := by omega
  unfold stringAppendEvents at hfit
  simp only [hnot, ↓reduceIte] at hfit
  rw [B.fitsEvents_append] at hfit
  have hnull : ¬ VerifiedLibraries.RustStd.NullAllowed (stringGrowCap st.cap.toNat st.bytes.length n) 1 := by
    split at hfit
    · exact B.fits_not_nullAllowed_alloc (by decide) hfit.2
    · exact B.fits_not_nullAllowed_realloc (by decide) hfit.2
  have hge : st.bytes.length + n ≤ stringGrowCap st.cap.toNat st.bytes.length n := by
    unfold stringGrowCap; omega
  rcases hcase with hov | hn
  · exact hnull (by unfold VerifiedLibraries.RustStd.NullAllowed; omega)
  · exact hnull hn

/-- Discharge `FormatInnerBudgetSafe` for any CLI envelope `Env` containing
    `formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs)`. -/
theorem knownFmt_safe_of_env (M : AllocCostModel) (A : RustCliAllocBudget M) [PoolMemTransport A]
    (lim : BudgetLimits) (st0 : M.σ) (Env : List AllocEvent → Prop)
    (argBytes : Nat → List (BitVec 8)) (x1 : BitVec 64) (cs : List FmtCall)
    (hlit : fmtLiteralLen cs < 2 ^ 60)
    (hEnv : Env (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs))) :
    FormatInnerBudgetSafe (toRustAllocBudget M A lim) st0 (toRustStdEnv Env)
      (knownArgStep argBytes) (knownArgPanic argBytes)
      (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) x1 cs := by
  let B := toRustAllocBudget M A lim
  let cap0 := fmtEstimatedCapacity x1 cs
  refine ⟨hlit, ?_, ?_, ?_, ?_⟩
  · intro st₀ hstart
    obtain ⟨suf, hsuf⟩ := cliBufShape_run_evs_prefix (startCliBufShape cap0) (callLens argBytes cs)
    refine ⟨suf.map ofCliAllocEvent, ?_⟩
    unfold toRustStdEnv
    rw [List.map_append, map_toCliAllocEvent_ofCliAllocEvent]
    have h0 := congrArg CliBufShape.evs (cliBufShape_of_start hstart)
    simp only [cliBufShapeOf] at h0
    rw [h0, ← hsuf]
    exact hEnv
  · intro st₀ st hstart hrun
    have h := (run_known hrun).2.1
    rw [cliBufShape_of_start hstart] at h
    have hev := congrArg CliBufShape.evs h
    simp only [cliBufShapeOf] at hev
    unfold toRustStdEnv
    rw [hev]
    exact hEnv
  · rintro ⟨st₀, st, -, hrun⟩
    exact absurd (run_known hrun).1 Bool.false_ne_true
  · intro hfitE st₀ c st sf hstart hreach
    obtain ⟨suf, hsuf⟩ := reaches_formatInnerEvents_prefix hstart hreach
    have hevMem : toRustStdEnv Env
        ((formatInnerKnownEvents cap0 (callLens argBytes cs)).map ofCliAllocEvent) := by
      unfold toRustStdEnv
      rw [map_toCliAllocEvent_ofCliAllocEvent]
      exact hEnv
    have hall := (toRustAllocBudget_fitsEvents M A lim st0 _).mp (hfitE _ hevMem)
    rw [map_toCliAllocEvent_ofCliAllocEvent, hsuf,
      LibsignalBinary.Heap.fitsEvents_append] at hall
    have hfitAppend : B.FitsEvents st0 (stringAppendEvents st (callBytes argBytes c).length) :=
      (toRustAllocBudget_fitsEvents M A lim st0 _).mpr hall.1
    refine ⟨fun _ _ _ _ _ => not_appendPanics_of_fits B hfitAppend, ?_⟩
    cases c <;> exact fun h => h hfitAppend

/-- Single-`str` operation inversion for `FmtOpsRun`. -/
theorem fmtOpsRun_str_inv {σ : Type} {S : σ → List (BitVec 8) → Bool → σ → Prop}
    {C : σ → BitVec 32 → Bool → σ → Prop} {bs : List (BitVec 8)} {st st' : σ} {ok : Bool}
    (h : FmtOpsRun S C [.str bs] st ok st') : S st bs ok st' := by
  cases h with
  | str_ok hs hr => cases hr; exact hs
  | str_err hs => exact hs

/-- Single-`str` operation inversion for `FmtOpsAbort`. -/
theorem fmtOpsAbort_str_inv {σ : Type} {S : σ → List (BitVec 8) → Bool → σ → Prop}
    {C : σ → BitVec 32 → Bool → σ → Prop} {Ab : σ → Nat → State → Prop}
    {bs : List (BitVec 8)} {st : σ} {sf : State}
    (h : FmtOpsAbort S C Ab [.str bs] st sf) : Ab st bs.length sf := by
  obtain ⟨pre, op, post, _, heq, hrun, hab⟩ := h
  cases pre with
  | nil =>
    cases hrun
    simp only [List.nil_append, List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hab
  | cons _ _ =>
    have hl := congrArg List.length heq
    simp only [List.length_cons, List.length_append, List.length_nil] at hl
    omega

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
