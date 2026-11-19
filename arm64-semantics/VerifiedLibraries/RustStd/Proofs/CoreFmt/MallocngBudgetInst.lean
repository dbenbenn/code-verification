/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.MallocngBridge
public import ProofLib.SepLogic.WP.StepsProcess
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.Cost.Model
public import VerifiedLibraries.Mallocng.Proofs.Cost.ModelOom
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.WriterOps
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics

/-!
# Budgeted `mallocng` Instance for `RustAllocBudget`

Process-level virtual and physical memory budget limits (`MallocngBudgetLimits`,
`FitsMallocngEvent`), the budgeted heap pool `mallocngBudgetPool`, the `RustAllocBudget`
instance `mallocngRustAllocBudget`, and `ProgContainsMallocng` C-entry and `memcpy` lifts.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Process-Level Budget Limits and `AllocEvent` Predicates -/

/-- Requested user byte size of an `AllocEvent` (`0` for `.free`). -/
def _root_.VerifiedLibraries.Mallocng.AllocEvent.reqBytes : AllocEvent → Nat
  | .alloc req => req
  | .aligned _ req => req
  | .free _ _ => 0
  | .realloc _ _ new => new

/-- Whether an `AllocEvent` satisfies `mallocng`'s `MallocngMaxAllocSize` request ceiling (so the
    underlying C call never takes its immediate `> MallocngMaxAllocSize` rejection path). -/
def _root_.VerifiedLibraries.Mallocng.AllocEvent.withinMaxAlloc : AllocEvent → Prop
  | .alloc req => req ≤ MallocngMaxAllocSize
  | .aligned align req => mallocngAlignedEffSize align req ≤ MallocngMaxAllocSize
  | .free _ _ => True
  | .realloc align _ new => mallocngAlignedEffSize align new ≤ MallocngMaxAllocSize

instance (ev : AllocEvent) : Decidable ev.withinMaxAlloc := by
  cases ev <;> dsimp only [AllocEvent.withinMaxAlloc] <;> infer_instance

theorem tight2_req_le_stepReserve (ev : AllocEvent) (st : mallocngTight2CostModel.σ) :
    ev.reqBytes ≤ mallocngTight2CostModel.stepReserve ev st := by
  cases ev <;>
    simp only [AllocEvent.reqBytes, mallocngTight2CostModel, mallocngTight2Reserve,
      mallocngAlignedEffSize] <;>
    (try split) <;> omega

/-- Process-level static virtual-memory bounds and physical-plus-RW capacity floor. -/
structure MallocngBudgetLimits where
  staticCount : Nat
  staticBytes : Nat
  physCap : Nat
  deriving DecidableEq, Repr

/-- Physical and 48-bit virtual-address headroom for one `mallocng` call reserving `stepB` bytes
    from a heap state with at most `dynIvs` dynamic intervals totalling `fp` bytes alongside static
    mappings `(lim.staticCount, lim.staticBytes)`. -/
def FitsMallocngStep (lim : MallocngBudgetLimits) (stepB dynIvs fp : Nat) : Prop :=
  lim.staticBytes + fp + stepB ≤ lim.physCap ∧
  MMAP_MIN_ADDR + lim.staticBytes + fp + stepB +
    (lim.staticCount + dynIvs + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48

instance (lim : MallocngBudgetLimits) (stepB dynIvs fp : Nat) :
    Decidable (FitsMallocngStep lim stepB dynIvs fp) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Model-level fit predicate for executing `ev` from `st` within `lim`. -/
def FitsMallocngEvent (M : AllocCostModel) (lim : MallocngBudgetLimits)
    (st : M.σ) (ev : AllocEvent) : Prop :=
  ev.withinMaxAlloc ∧
    FitsMallocngStep lim (M.stepReserve ev st) (M.maxDynIvs st) (M.footprint st)

instance (M : AllocCostModel) (lim : MallocngBudgetLimits) (st : M.σ) (ev : AllocEvent) :
    Decidable (FitsMallocngEvent M lim st ev) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## `mallocngBudgetPool`, Startup Initialization, and `mallocngRustAllocBudget` -/

/-- Mapped-interval coverage and conserved physical-plus-RW capacity invariant carried inside
    `mallocngBudgetPool`. -/
def MallocngBudgetVmOk (lim : MallocngBudgetLimits)
    (staticIvs ivs : List (BitVec 64 × Nat)) (s : State) : Prop :=
  staticIvs.length ≤ lim.staticCount ∧
  (staticIvs.map Prod.snd).sum ≤ lim.staticBytes ∧
  lim.physCap ≤ ProofLib.physPlusRw s ∧
  ∀ a : BitVec 64, (s.mem.perm a).mapped = true →
    MallocngInIntervals staticIvs a ∨ MallocngInIntervals ivs a

theorem MallocngBudgetVmOk.transport {lim : MallocngBudgetLimits}
    {staticIvs ivs : List (BitVec 64 × Nat)} {s s' : State}
    (hVm : VmPreserved s s') :
    MallocngBudgetVmOk lim staticIvs ivs s' = MallocngBudgetVmOk lim staticIvs ivs s := by
  rcases hVm with ⟨_, hPhys, hPerm⟩
  have hPprw : ProofLib.physPlusRw s' = ProofLib.physPlusRw s := by
    unfold ProofLib.physPlusRw
    rw [hPhys, ProofLib.rwBytes_congr hPerm]
  apply propext
  unfold MallocngBudgetVmOk
  rw [hPprw]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, h3, fun a ha => ?_⟩
  · rw [← hPerm a] at ha; exact h4 a ha
  · rw [hPerm a] at ha; exact h4 a ha

/-- Budgeted `mallocng` pool predicate: owns `I.HeapM γ mAddrs s.tpidrEl0 s.brkStart s.brk st ivs`
    whole (keeping `StdErrnoCell s.tpidrEl0` inside `pool`), a state-independent invariant `extra`,
    and `MallocngBudgetVmOk` witnessing mapped-interval coverage and `lim.physCap ≤ physPlusRw s`. -/
def mallocngBudgetPool (M : AllocCostModel) (I : MallocngCostModelIface M)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName)
    (mAddrs : MallocngAddrs) (st : M.σ) (s : State) : SepProp :=
  ∃∗ ivs : List (BitVec 64 × Nat),
  ∃∗ staticIvs : List (BitVec 64 × Nat),
    ⌜MallocngBudgetVmOk lim staticIvs ivs s⌝ ∗
    I.HeapM γ mAddrs s.tpidrEl0 s.brkStart s.brk st ivs ∗
    extra

/-- Live allocation token for `mallocngRustAllocBudget`: pairs `⌜p.toNat % al = 0 ∧ RustLayoutOk n al⌝`
    with `I.BlockM γ p n (max al 16)`. -/
def mallocngBudgetLive {M : AllocCostModel} (I : MallocngCostModelIface M)
    (γ : GhostName) (p : BitVec 64) (n al : Nat) : SepProp :=
  ⌜p.toNat % al = 0 ∧ RustLayoutOk n al⌝ ∗ I.BlockM γ p n (max al 16)

theorem mallocngBudgetPool_of_heapM (M : AllocCostModel) (I : MallocngCostModelIface M)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName)
    (mAddrs : MallocngAddrs) (st : M.σ) (staticIvs : List (BitVec 64 × Nat)) (s : State)
    (hLen : staticIvs.length ≤ lim.staticCount)
    (hSum : (staticIvs.map Prod.snd).sum ≤ lim.staticBytes)
    (hPhys : lim.physCap ≤ ProofLib.physPlusRw s)
    (hCov : ∀ a : BitVec 64, (s.mem.perm a).mapped = true → MallocngInIntervals staticIvs a) :
    I.HeapM γ mAddrs s.tpidrEl0 s.brkStart s.brk st [] ∗ extra ⊢
      mallocngBudgetPool M I lim extra γ mAddrs st s := by
  unfold mallocngBudgetPool
  refine Entails.sepExists_right [] (Entails.sepExists_right staticIvs ?_)
  exact Entails.pure_right ⟨hLen, hSum, hPhys, fun a ha => Or.inl (hCov a ha)⟩ (Entails.refl _)

theorem mallocngBudgetPool_of_init_resources {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (lim : MallocngBudgetLimits) (extra : SepProp)
    (mAddrs : MallocngAddrs) (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hLen : staticIvs.length ≤ lim.staticCount)
    (hSum : (staticIvs.map Prod.snd).sum ≤ lim.staticBytes)
    (hPhys : lim.physCap ≤ ProofLib.physPlusRw s0)
    (hCov : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true → MallocngInIntervals staticIvs a)
    (hmem : s0.mem ⊨ MallocngStartupResources mAddrs s0.tpidrEl0 ∗ (extra ∗ R)) :
    ∃ γ : GhostName,
      s0.mem ⊨ mallocngBudgetPool M I lim extra γ mAddrs M.init s0 ∗ R := by
  have hbupd := Satisfies.mono
    (sepConj_mono_left (hSound.init_resources mAddrs s0.tpidrEl0 s0.brkStart htpLo htpHi hbrkWf))
    hmem
  have hbupd2 := Satisfies.mono (bupd_frame_r _ _) hbupd
  rw [satisfies_bupd, sepExists_sepConj_left, satisfies_sepExists] at hbupd2
  obtain ⟨γ, hγ⟩ := hbupd2
  have hHeapEq :
      I.HeapM γ mAddrs s0.tpidrEl0 s0.brkStart s0.brkStart M.init [] =
        I.HeapM γ mAddrs s0.tpidrEl0 s0.brkStart s0.brk M.init [] := by rw [hbrk]
  rw [hHeapEq, ← sepConj_assoc] at hγ
  exact ⟨γ, Satisfies.mono
    (sepConj_mono_left
      (mallocngBudgetPool_of_heapM M I lim extra γ mAddrs M.init staticIvs s0
        hLen hSum hPhys hCov))
    hγ⟩

theorem mallocngBudgetPool_of_init {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (lim : MallocngBudgetLimits) (extra : SepProp)
    (mpl : Obj.MultiPlacement) (auxvPtr : BitVec 64)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (htpLo : 0xa4 ≤ s0.tpidrEl0.toNat) (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf s0.brkStart)
    (hbrk : s0.brk = s0.brkStart)
    (hLen : staticIvs.length ≤ lim.staticCount)
    (hSum : (staticIvs.map Prod.snd).sum ≤ lim.staticBytes)
    (hPhys : lim.physCap ≤ ProofLib.physPlusRw s0)
    (hCov : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true → MallocngInIntervals staticIvs a)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ (extra ∗ R)) :
    ∃ γ : GhostName,
      s0.mem ⊨
        mallocngBudgetPool M I lim extra γ (mallocngAddrsOfPlacement mpl) M.init s0 ∗ R := by
  obtain ⟨γ, hbupd⟩ :=
    hSound.init mpl s0.tpidrEl0 s0.brkStart auxvPtr (extra ∗ R) s0.mem htpLo htpHi hbrkWf hmem
  have hHeapEq :
      I.HeapM γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart s0.brkStart M.init [] =
        I.HeapM γ (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 s0.brkStart s0.brk M.init [] := by
    rw [hbrk]
  rw [satisfies_bupd, hHeapEq, ← sepConj_assoc] at hbupd
  exact ⟨γ, Satisfies.mono
    (sepConj_mono_left
      (mallocngBudgetPool_of_heapM M I lim extra γ (mallocngAddrsOfPlacement mpl)
        M.init staticIvs s0 hLen hSum hPhys hCov))
    hbupd⟩

/-- Cost-model-parametric `RustAllocBudget` instance over any `(M, I)` satisfying
    `MallocngCostModelSound M I` and `∀ ev st, ev.reqBytes ≤ M.stepReserve ev st`. -/
def mallocngRustAllocBudget (M : AllocCostModel) (I : MallocngCostModelIface M)
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp)
    (γ : GhostName) (mAddrs : MallocngAddrs) : RustAllocBudget where
  σ := M.σ
  step := M.step
  FitsEvent := FitsMallocngEvent M lim
  pool := mallocngBudgetPool M I lim extra γ mAddrs
  live := mallocngBudgetLive I γ
  block_valid p n al := by
    refine Entails.pure_left fun ⟨hAl, hLayout⟩ => ?_
    refine Entails.trans (hSound.block_nonnull γ p n (max al 16)) ?_
    refine Entails.pure_left fun ⟨hpNe, _, hBound48, _⟩ => ?_
    have hBound64 : p.toNat + n < 2 ^ 64 := Nat.lt_of_le_of_lt hBound48 (by decide)
    exact Entails.pure_right ⟨hpNe, hAl, hBound64, hLayout⟩
      (Entails.pure_right ⟨hAl, hLayout⟩ (Entails.refl _))
  pool_transport st s s' hVm := by
    have hVmOkEq : ∀ staticIvs ivs,
        MallocngBudgetVmOk lim staticIvs ivs s' = MallocngBudgetVmOk lim staticIvs ivs s :=
      fun _ _ => MallocngBudgetVmOk.transport hVm
    rcases hVm with ⟨⟨hBs, hBrk, hTp⟩, _, _⟩
    simp only [mallocngBudgetPool, hVmOkEq, hTp, hBs, hBrk]
  fits_not_nullAllowed st size align hAl31 hDisj := by
    have hSz48 : size ≤ 2 ^ 48 := by
      rcases hDisj with ⟨_, _, hVa⟩ | ⟨_, _, hVa⟩ | ⟨old, _, _, hVa⟩
      · have hReq := hReqLe (.alloc size) st
        dsimp only [AllocEvent.reqBytes] at hReq
        omega
      · have hReq := hReqLe (.aligned (max align 8) size) st
        dsimp only [AllocEvent.reqBytes] at hReq
        omega
      · have hReq := hReqLe (.realloc align old size) st
        dsimp only [AllocEvent.reqBytes] at hReq
        omega
    unfold NullAllowed
    omega

/-! ## `allocMallocng` Validity, OOM Discharge, and Placed C-Entry Lifting -/

private theorem execMremap_mremapStep (s : State) : MallocngMremapStep s (execMremap s) := by
  intro hflags hal holdPos hnewPos hnewMax holdFit hrw hanon
  have hflags' : s.readReg64 Reg.x3 = MREMAP_MAYMOVE := hflags
  have holdNe : s.readReg64 Reg.x1 ≠ 0#64 := by
    intro hz; rw [hz] at holdPos; contradiction
  have hnewNe : s.readReg64 Reg.x2 ≠ 0#64 := by
    intro hz; rw [hz] at hnewPos; contradiction
  by_cases hnewLim : (s.readReg64 Reg.x2).toNat ≤ USER_VA_LIMIT
  · cases hmf : s.oracle.mremapRefusal s.oracleIdx with
    | some r =>
      cases r with
      | enomem =>
        refine Or.inl ⟨12, by decide, by decide, Or.inr ?_⟩
        simpa [ENOMEM] using
          ProofLib.execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewLim holdFit hrw hanon (Or.inl hmf)
      | efault =>
        refine Or.inl ⟨14, by decide, by decide, Or.inr ?_⟩
        have heq : EFAULT_RET = -BitVec.ofNat 64 14 := by decide
        simpa [heq] using
          ProofLib.execMremap_efault_of_refusal s (Or.inr hflags') hal holdNe hnewNe hnewLim holdFit hrw hanon hmf
    | none =>
      cases hsan : sanitizeMmapAddr
          (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
          (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x2).toNat) with
      | none =>
        refine Or.inl ⟨12, by decide, by decide, Or.inr ?_⟩
        simpa [ENOMEM] using
          ProofLib.execMremap_enomem_of_fail s hflags' hal holdNe hnewNe hnewLim holdFit hrw hanon (Or.inr ⟨hmf, hsan⟩)
      | some newBase =>
        obtain ⟨hne, hnbAl, hnbFit, hcan⟩ := ProofLib.sanitizeMmapAddr_spec hsan
        by_cases hphys : pageAlignUp (s.readReg64 Reg.x2).toNat ≤
            s.physMemAvail + pageAlignUp (s.readReg64 Reg.x1).toNat
        · refine Or.inr (Or.inr ⟨newBase, hne, hnbAl, by simpa [USER_VA_LIMIT] using hnbFit, hcan, ?_⟩)
          have hrem : mallocngRemapRw s.mem (s.readReg64 Reg.x0)
              (pageAlignUp (s.readReg64 Reg.x1).toNat) newBase
              (pageAlignUp (s.readReg64 Reg.x2).toNat) =
              s.mem.remapRw (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat)
                newBase (pageAlignUp (s.readReg64 Reg.x2).toNat) := rfl
          rw [hrem]
          exact ProofLib.execMremap_ok s hflags' hal holdNe hnewNe hnewLim holdFit hrw hanon hmf hsan hphys
        · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
          exact ProofLib.execMremap_oom s hflags' hal holdNe hnewNe hnewLim holdFit hrw hanon hmf hsan (by omega)
  · refine Or.inl ⟨22, by decide, by decide, Or.inl ?_⟩
    simpa [EINVAL] using ProofLib.execMremap_einval_of_newLen_gt s (Or.inr hflags') hnewLim

theorem allocMallocng_svcValid : MallocngSvcValid ProofLib.allocMallocng := by
  intro s; refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx8
    simp [ProofLib.allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable,
      hx8, SYS_BRK, SYS_MPROTECT]
  · intro hx8
    simp [ProofLib.allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable,
      hx8, SYS_MUNMAP, SYS_MPROTECT, SYS_BRK]
  · intro hx8
    simp [ProofLib.allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable,
      hx8, SYS_MMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP]
  · intro hx8 hx2
    simp [ProofLib.allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable,
      hx8, hx2, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP]
  · intro hx8
    have heq : ProofLib.allocMallocng s = execMremap s := by
      simp [ProofLib.allocMallocng, Syscall.alloc, Syscall.dispatch, Syscall.allocTable,
        hx8, MALLOCNG_SYS_MREMAP, SYS_MREMAP, SYS_MPROTECT, SYS_BRK, SYS_MUNMAP]
    rw [heq]; exact execMremap_mremapStep s

theorem allocMallocng_sanitizedSvc : MallocngSanitizedSvc ProofLib.allocMallocng := by
  intro s hrun hx8 hprot hflags hoff hlen hoom
  rw [(allocMallocng_svcValid s).2.2.1 hx8] at hoom
  dsimp only [execMmap] at hoom
  have hf_prot : ((s.readReg64 Reg.x2 != MMAP_PROT_RW && s.readReg64 Reg.x2 != MMAP_PROT_NONE ||
      (s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        s.readReg64 Reg.x3 != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      s.readReg64 Reg.x5 != 0#64)) = false := by
    rcases hprot with hp | hp <;> simp [hp, hflags, hoff, MMAP_PROT_NONE, MMAP_PROT_RW,
      MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED]
  have h1_pos : 0 < (s.readReg64 Reg.x1).toNat :=
    Nat.pos_of_ne_zero fun h0 => hlen (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hf_len0 : ((s.readReg64 Reg.x1).toNat == 0) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt h1_pos)
  have hf_fix : (s.readReg64 Reg.x3 == MMAP_FLAGS_PRIVATE_ANON_FIXED) = false := by
    rw [hflags]; decide
  simp only [hf_prot, hf_len0, hf_fix, Bool.false_eq_true, ↓reduceIte] at hoom
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 Reg.x1).toNat) with
  | none =>
    left; rintro ⟨gap, hmin, hgapAl, hfit, hcan⟩
    have hpos : 0 < pageAlignUp (s.readReg64 Reg.x1).toNat := by unfold pageAlignUp PAGE_SIZE; omega
    have hal : pageAlignUp (s.readReg64 Reg.x1).toNat % PAGE_SIZE = 0 := by
      unfold pageAlignUp PAGE_SIZE; omega
    obtain ⟨base, hsome⟩ := sanitizeMmapAddr_exists_of_gap
      (s.oracle.mmap s.oracleIdx) hpos hal hmin hgapAl (by simpa [USER_VA_LIMIT] using hfit) hcan
    rw [hsan] at hsome; nomatch hsome
  | some base =>
    rw [hsan] at hoom; dsimp only at hoom; split at hoom
    · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle,
        State.status_setMem, hrun] at hoom
      nomatch hoom
    · split at hoom
      · next hphys =>
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hphys
        exact Or.inr (Nat.lt_of_not_ge hphys)
      · simp only [State.status_advancePC, State.status_writeReg64, State.status_nextOracle,
          State.status_setPhysMemAvail, State.status_setMem, hrun] at hoom
        nomatch hoom

private theorem alloc_eq_standard_of_not_exception {s : State}
    (hne : ∀ msg, (ProofLib.allocMallocng s).status ≠ .Exception msg) :
    ProofLib.allocMallocng s = Syscall.standard s := by
  unfold ProofLib.allocMallocng at hne ⊢
  by_cases hcond :
      (s.readReg64 Reg.x8 == SYS_MPROTECT && s.readReg64 Reg.x2 != MMAP_PROT_RW) = true
  · simp only [hcond, ↓reduceIte, State.setStatus] at hne
    exact False.elim (hne _ rfl)
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    have hstd : Syscall.standard = execSyscall := rfl
    rw [hstd]
    unfold Syscall.alloc Syscall.dispatch at hne
    cases hfind : Syscall.allocTable.find? (·.1 == s.readReg64 Reg.x8) with
    | none =>
      simp only [hfind, State.setStatus] at hne
      exact False.elim (hne _ rfl)
    | some p =>
      rcases p with ⟨nr, fn⟩
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred : (nr == s.readReg64 Reg.x8) = true :=
        List.find?_some (p := fun x : BitVec 64 × (State → State) => x.1 == s.readReg64 Reg.x8)
          hfind
      have hx8 : s.readReg64 .x8 = nr := (beq_iff_eq.mp hpred).symm
      simp only [Syscall.allocTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> injection h with hnr _ <;> subst hnr
      · rw [alloc_brk s hx8, execSyscall_brk s hx8]
      · rw [alloc_munmap s hx8, execSyscall_munmap s hx8]
      · rw [alloc_mremap s hx8, execSyscall_mremap s hx8]
      · rw [alloc_mmap s hx8, execSyscall_mmap s hx8]
      · rw [alloc_mprotect s hx8, execSyscall_mprotect s hx8]
      · rw [alloc_madvise s hx8]
        unfold execSyscall Syscall.standard Syscall.dispatch Syscall.standardTable
          Syscall.stdioTable Syscall.fileIoOnlyTable Syscall.pollTable Syscall.allocTable
        simp [hx8, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE]

private theorem steps_not_exception_at_start {Q : Program} {s sf : State}
    (h : Steps Q s sf)
    (hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory) :
    ∀ msg, s.status ≠ .Exception msg := by
  intro msg hst
  cases h with
  | refl =>
    rcases hend with hr | hr | ⟨_, hr⟩ | hr <;> rw [hst] at hr <;> nomatch hr
  | step h1 _ =>
    have hr : s.status = .Running := by cases h1 <;> assumption
    rw [hst] at hr; nomatch hr

private theorem steps_pureMem_of_withSvc_alloc_outcome {s0 sf : State}
    (h : Steps (Program.pureMem.withSvc ProofLib.allocMallocng) s0 sf)
    (hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory) :
    Steps Program.pureMem s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 hrest ih =>
    have hne2 : ∀ msg, s2.status ≠ .Exception msg := steps_not_exception_at_start hrest hend
    have hsteps_rest : Steps Program.pureMem s2 s3 := ih hend
    have hext : ∀ pc, (Program.pureMem.withSvc ProofLib.allocMallocng).externAt? pc = none :=
      fun _ => rfl
    have hsvcEq : (Program.pureMem.withSvc ProofLib.allocMallocng).svc = ProofLib.allocMallocng :=
      rfl
    have hf_eq : (Program.pureMem.withSvc ProofLib.allocMallocng).fetchMem s1.mem s1.pc =
        Program.pureMem.fetchMem s1.mem s1.pc := rfl
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hne_svc : ∀ msg, (ProofLib.allocMallocng s1).status ≠ .Exception msg := by
          rwa [Program.evalInst_svc0, hsvcEq, ProofLib.evalSvc_allocMallocng] at hne2
        have hbase_svc : Program.pureMem.svc = Syscall.standard := rfl
        have hev_eq : (Program.pureMem.withSvc ProofLib.allocMallocng).evalInst
              (.system false 0#16) s1 =
            Program.pureMem.evalInst (.system false 0#16) s1 := by
          rw [Program.evalInst_svc0, hsvcEq, ProofLib.evalSvc_allocMallocng,
              Program.evalInst_svc0, hbase_svc, evalSvc_standard,
              alloc_eq_standard_of_not_exception hne_svc]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev_eq : (Program.pureMem.withSvc ProofLib.allocMallocng).evalInst inst s1 =
            Program.pureMem.evalInst inst s1 := by
          rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, evalInst_eq_execInst_of_not_isSvc0 hnsvc0]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
    | halt_unmapped _ _ _ =>
      have heq := Steps.from_not_running hrest (by simp)
      subst heq
      simp at hend
    | extern _ he _ _ => rw [hext] at he; nomatch he
    | extern_fault _ he _ => rw [hext] at he; nomatch he

/-- Strengthen `spec : Spec α` with `extra : SepProp` framing and `physPlusRw sf = physPlusRw s0`
    conservation on both `.Running` and `.OutOfMemory`. -/
def withPhysAndExtra {α : Type} (extra : SepProp) (spec : Spec α) : Spec α where
  pre x s := spec.pre x s ∗ extra
  post x s0 sf := ⌜ProofLib.physPlusRw sf = ProofLib.physPlusRw s0⌝ ∗ spec.post x s0 sf ∗ extra
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom x s0 sf := ⌜ProofLib.physPlusRw sf = ProofLib.physPlusRw s0⌝ ∗ spec.onOom x s0 sf

theorem mallocngBudgetSubroutine_to_prog {S α : Type} [ToBaseSpec S α]
    {P : Program} {mpl : Obj.MultiPlacement} (extra : SepProp)
    {fnName : String} {spec : S}
    (hP : ProgContainsMallocng P mpl)
    (hbase_indep : ∀ b₁ b₂, ToBaseSpec.toSpec spec b₁ = ToBaseSpec.toSpec spec b₂)
    (hsub : mallocngMultiEntryOk mpl ProofLib.allocMallocng fnName spec) :
    subroutine_ok P (VerifiedLibraries.mallocngLib.fnAddr mpl fnName)
      (withPhysAndExtra extra (ToBaseSpec.toSpec spec P.base)) := by
  obtain ⟨_, i, _, hfn, hok⟩ := hsub
  obtain ⟨hi, _⟩ := Obj.lookupBlockSym_some hfn
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hcode
  have hcl_all : VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem := hP.codeLoaded s0.mem hcode
  have hcl_i : (mallocngBlockProg mpl i ProofLib.allocMallocng).CodeLoaded s0.mem :=
    hcl_all.blockProgram hi
  rw [hbase_indep (mpl.base i) P.base] at hok
  dsimp only [withPhysAndExtra] at hpre
  rw [sepConj_assoc] at hpre
  have hpre_cl : s0.mem ⊨
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl (ToBaseSpec.toSpec spec P.base)).pre x s0 ∗
        (extra ∗ R) := by
    show s0.mem ⊨ ((ToBaseSpec.toSpec spec P.base).pre x s0 ∗
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mpl s0.mem⌝) ∗ (extra ∗ R)
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl_all]
    exact hpre
  obtain ⟨sf, hsteps_blk, hout⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome hok x (extra ∗ R) s0 hpc hrun hpre_cl hsp hcl_i
  have hsteps_alloc : Steps (Program.pureMem.withSvc ProofLib.allocMallocng) s0 sf :=
    ProofLib.steps_withSvc_alloc_of_noHooks
      (fun pc => Obj.MultiPlacedLib.externAt?_blockProgram_none _ mpl i pc)
      rfl (fun _ => rfl) hsteps_blk
  have hpprw : ProofLib.physPlusRw sf = ProofLib.physPlusRw s0 :=
    ProofLib.physPlusRw_steps_withSvc_alloc (fun _ => rfl) hsteps_alloc
  have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
    rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  have hsteps_pure : Steps Program.pureMem s0 sf :=
    steps_pureMem_of_withSvc_alloc_outcome hsteps_alloc hend
  have hsteps_P : Steps P s0 sf :=
    steps_prog_of_pureMem_outcome hP.svc_eq (hP.hooks_unfetched s0.mem hcode)
      (Memory.KeepsFrozen.refl s0.mem) hsteps_pure hend
  refine reaches_outcome_steps hsteps_P (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withPhysAndExtra]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpprw, ?_⟩
    exact hq
  · exact Or.inr (Or.inl ⟨hp, satisfies_drop_mid hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, satisfies_drop_mid hex⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [withPhysAndExtra]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpprw, satisfies_drop_mid hoom⟩

/-- Program-level `subroutine_ok` bundle for the 4 `mallocng` C entry points consumed by
    `__rdl_alloc` and `__rdl_realloc` (`malloc`, `free`, `realloc`, `posix_memalign`) over `(M, I)`
    with conserved `physPlusRw` and `extra` framing. -/
structure MallocngBudgetCContracts (M : AllocCostModel) (I : MallocngCostModelIface M)
    (extra : SepProp) (P : Program) (mAddrs : MallocngAddrs)
    (cAddrs : MallocngCEntryAddrs) : Prop where
  malloc_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.malloc
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelMallocSpec M I ProofLib.allocMallocng γ mAddrs) P.base))
  free_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.free
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelFreeSpec M I γ mAddrs) P.base))
  realloc_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.realloc
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelReallocSpec M I ProofLib.allocMallocng γ mAddrs) P.base))
  posixMemalign_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.posixMemalign
      (withPhysAndExtra extra
        (ToBaseSpec.toSpec (mallocngModelPosixMemalignSpec M I ProofLib.allocMallocng γ mAddrs)
          P.base))

theorem MallocngBudgetCContracts.of_placed {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I) (extra : SepProp)
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mpl) :
    MallocngBudgetCContracts M I extra P (mallocngAddrsOfPlacement mpl)
      (mallocngPlacedCAddrs mpl) := by
  have hEntries := hSound.entries_ok mpl ProofLib.allocMallocng hP.placeable allocMallocng_svcValid
  exact
    { malloc_ok := fun γ =>
        mallocngBudgetSubroutine_to_prog extra hP (fun _ _ => rfl) (hEntries.malloc_ok γ)
      free_ok := fun γ =>
        mallocngBudgetSubroutine_to_prog extra hP (fun _ _ => rfl) (hEntries.free_ok γ)
      realloc_ok := fun γ =>
        mallocngBudgetSubroutine_to_prog extra hP (fun _ _ => rfl) (hEntries.realloc_ok γ)
      posixMemalign_ok := fun γ =>
        mallocngBudgetSubroutine_to_prog extra hP (fun _ _ => rfl) (hEntries.posixMemalign_ok γ) }

theorem mallocngStepOomCond_false_of_pool {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    {lim : MallocngBudgetLimits} {γ : GhostName} {mAddrs : MallocngAddrs}
    {tp brkStart brk : BitVec 64} {st : M.σ} {ev : AllocEvent} {stepB : Nat}
    {staticIvs ivs0 : List (BitVec 64 × Nat)} {R : SepProp} {s1 sf : State}
    (hVmOk : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hHeap : s1.mem ⊨ I.HeapM γ mAddrs tp brkStart brk st ivs0 ∗ R)
    (hFits : FitsMallocngStep lim (M.stepReserve ev st) (M.maxDynIvs st) (M.footprint st))
    (hStep : stepB ≤ M.stepReserve ev st)
    (hPhysEq : ProofLib.physPlusRw sf = ProofLib.physPlusRw s1)
    (hOom : MallocngStepOomCond ProofLib.allocMallocng stepB s1 sf) :
    False := by
  have hEnt := Entails.extract_heap_fact
    (P := I.HeapM γ mAddrs tp brkStart brk st ivs0)
    (fun h hh => hSound.heap_footprint_bound γ mAddrs tp brkStart brk st ivs0 h hh)
  have hSatPure := Satisfies.mono (sepConj_mono_left hEnt) hHeap
  rw [sepConj_assoc, satisfies_pure_sepConj] at hSatPure
  obtain ⟨⟨hHeapLen, hHeapSum, _⟩, _⟩ := hSatPure
  rcases hVmOk with ⟨hStLen, hStSum, hPhysCap, hCovOr⟩
  rcases hFits with ⟨hRam, hVa⟩
  have hCov : ∀ a : BitVec 64, (s1.mem.perm a).mapped = true →
      MallocngInIntervals (staticIvs ++ ivs0) a := by
    intro a ha
    rcases hCovOr a ha with ⟨iv, hm, hin⟩ | ⟨iv, hm, hin⟩
    · exact ⟨iv, List.mem_append_left _ hm, hin⟩
    · exact ⟨iv, List.mem_append_right _ hm, hin⟩
  have hSum : ((staticIvs ++ ivs0).map Prod.snd).sum =
      (staticIvs.map Prod.snd).sum + (ivs0.map Prod.snd).sum := by
    simp [List.map_append, List.sum_append]
  have hLen : (staticIvs ++ ivs0).length = staticIvs.length + ivs0.length := List.length_append
  have hVaRoom : VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom
      ((staticIvs ++ ivs0).map Prod.snd).sum (staticIvs ++ ivs0).length stepB := by
    refine VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom.mono
      (S₂ := lim.staticBytes + M.footprint st)
      (n₂ := lim.staticCount + M.maxDynIvs st)
      (b₂ := M.stepReserve ev st)
      ?_ (by omega) (by omega) hStep
    unfold VerifiedLibraries.Mallocng.Proofs.Cost.VaRoom
    omega
  exact VerifiedLibraries.Mallocng.Proofs.Cost.mallocngStepOomCond_false_of_fits
    allocMallocng_sanitizedSvc hCov hPhysEq (by omega) hVaRoom hOom

theorem modelPostEnv_entails_budgetPool {M : AllocCostModel} {I : MallocngCostModelIface M}
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName) (mAddrs : MallocngAddrs)
    {tp brkStart : BitVec 64} {stf : M.σ} {staticIvs ivs0 : List (BitVec 64 × Nat)}
    {s1 sf : State}
    (hVmOk1 : MallocngBudgetVmOk lim staticIvs ivs0 s1)
    (hPhysEq : ProofLib.physPlusRw sf = ProofLib.physPlusRw s1) :
    MallocngModelPostEnv M I γ mAddrs tp brkStart stf ivs0 s1 sf ∗ extra ⊢
      mallocngBudgetPool M I lim extra γ mAddrs stf sf := by
  unfold MallocngModelPostEnv MallocngModelEnv mallocngBudgetPool
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun ivsf => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hNoOrph => Entails.pure_left fun ⟨htp, hbs⟩ => ?_
  rw [← htp, ← hbs]
  refine Entails.sepExists_right staticIvs ?_
  rcases hVmOk1 with ⟨hLen, hSum, hPhys1, hCov1⟩
  have hVmOkf : MallocngBudgetVmOk lim staticIvs ivsf sf := by
    refine ⟨hLen, hSum, by omega, fun a ha => ?_⟩
    cases hm1 : (s1.mem.perm a).mapped
    · exact Or.inr (hNoOrph a ha (Or.inl hm1))
    · rcases hCov1 a hm1 with hSt | hDyn
      · exact Or.inl hSt
      · exact Or.inr (hNoOrph a ha (Or.inr hDyn))
  exact Entails.pure_right hVmOkf (Entails.refl _)

/-- Total-correctness `memcpy` contract strengthened with `VmPreserved s0 sf` so
    `mallocngBudgetPool` transports across the copy stage of `__rdl_realloc`. -/
def mallocngMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem mallocngMemcpy_len_le_2pow63 {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

theorem mallocngMemcpy_ok_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr mallocngMemcpySpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp hLP
  let P0 : Program := { P with externs := fun _ => none, overrides := fun _ => none }
  have hP0_no_ext : ∀ pc, P0.externAt? pc = none := by
    intro pc; simp [P0, Program.externAt?, Program.hookAtOff?]
  have hP0_words : P0.hasWords memcpyAddr memcpySymWords := by
    obtain ⟨h1, h2, _⟩ := h_words
    exact ⟨h1, h2, by simp [P0, Program.hookFree]⟩
  have hP0_cl : P0.CodeLoaded s0.mem := hLP.of_base_code rfl rfl
  simp only [mallocngMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := mallocngMemcpy_len_le_2pow63 (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt)))
      hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_process
    (P := P0)
    (memcpy_pureWords_ok memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    (memcpy_allInstrs_noSvc_noMsr memcpyAddr)
    hP0_words hP0_no_ext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  have hP0_svc : P0.svc = Syscall.standard := hsvc
  obtain ⟨sf, hsteps_P0, hout⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome hLift () R s0 hpc hrun
      (by
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩)
      hsp hP0_cl
  have hsteps_pure : Steps Program.pureMem s0 sf := by
    clear hout hm_pts hm_ex hm hm_assoc hpc hrun hsp hLP hx0 hx1 hx2 hP0_cl
    induction hsteps_P0 with
    | refl s => exact Steps.refl s
    | @step s1 s2 s3 h1 _ ih =>
      have hf_eq : P0.fetchMem s1.mem s1.pc = Program.pureMem.fetchMem s1.mem s1.pc := by
        unfold Program.fetchMem; rw [hP0_no_ext s1.pc]; rfl
      have hev_eq : ∀ inst, P0.evalInst inst s1 = Program.pureMem.evalInst inst s1 := fun inst => by
        simp only [Program.evalInst, hP0_svc]; rfl
      cases h1 with
      | @exec inst hr1 hfe =>
        rw [hev_eq inst] at ih
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) ih
      | halt_unmapped hr1 hfe _ =>
        exact Steps.step (Step.halt_unmapped hr1 (hf_eq ▸ hfe) rfl) ih
      | extern _ he _ _ => rw [hP0_no_ext s1.pc] at he; nomatch he
      | extern_fault _ he _ => rw [hP0_no_ext s1.pc] at he; nomatch he
  have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
    rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  have hsteps_P : Steps P s0 sf :=
    steps_prog_of_pureMem_outcome hsvc (hhooks s0.mem hLP)
      (Memory.KeepsFrozen.refl s0.mem) hsteps_pure hend
  refine reaches_outcome_steps hsteps_P (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [mallocngMemcpySpec]
    refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
    rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
    exact Entails.pure_right
      ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩, ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm⟩⟩
      (Entails.refl _)
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

end VerifiedLibraries.RustStd
