/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.MallocngBudgetRdlAlloc
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FinishGrowBudget
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics

/-!
# Budgeted `__rust_alloc` Wrapper and `memcpy` Contracts

Proves `budgetMemcpySpec ro` for `musl` `memcpySymWords` (`budgetMemcpy_ok_of_hasWords`,
`budgetMemcpy_ok_all_of_hasWords`) and resolves `rustBudgetAllocSpec` at
`allocMultiLib.resolve mpl allocRustAllocSym` (`rustBudgetAlloc_resolve_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib.SepLogic
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.RustStd.CoreFmt

private theorem fmtSrcBytes_eq_memcpySrc (ro : Bool) (src : BitVec 64) (bs : List (BitVec 8)) :
    fmtSrcBytes ro src bs = memcpySrc ro src bs := by
  cases ro <;> rfl

private theorem budgetMemcpy_len_le_2pow63 {m : Memory} {ro : Bool} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ fmtSrcBytes ro src bs) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    cases ro <;> simp only [fmtSrcBytes, Bool.false_eq_true, ↓reduceIte] at h
    · refine Satisfies.pointsToBytes_to_ro ?_
      rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
    · rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
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

private theorem memcpy_pureWords_ro_ok (ro : Bool) (addr dst src : BitVec 64)
    (dstBs srcBs : List (BitVec 8)) (n : BitVec 64)
    (hdstLen : dstBs.length = n.toNat) (hsrcLen : srcBs.length = n.toNat)
    (hn63 : n.toNat ≤ 2 ^ 63) :
    subroutine_ok (pureWordsProg addr memcpySymWords) addr
      { pre := fun (_ : Unit) s =>
          ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ s.readReg64 .x2 = n⌝ ∗
          (dst ↦ₛ dstBs) ∗ memcpySrc ro src srcBs
        post := fun _ s0 sf =>
          ⌜sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab ∧ sf.readReg64 .x0 = dst⌝ ∗
          (dst ↦ₛ srcBs) ∗ memcpySrc ro src srcBs } := by
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre
  refine ⟨(dst ↦ₛ dstBs) ∗ memcpySrc ro src srcBs, by rwa [sepConj_assoc], ?_⟩
  refine SepWP.mono (memcpy_sepwp ro (pureWordsProg addr memcpySymWords) addr
    (memcpy_pureWords_hasWords addr) s0
    dst src n dstBs srcBs hpc hrun hx0 hx1 hx2 hdstLen hsrcLen hn63) ?_
  intro sf P_f _ _ ⟨⟨hx0f, hspf, hcsf, _hfs, _htr, _htp, _hbrks, horc, hsym, _hsig, _hbrk⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' := Satisfies.mono (sepConj_mono_left hent) hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
  exact ⟨⟨horc, hsym, hx0f⟩, hm'⟩

/-- `budgetMemcpySpec ro` (read-only or shared source) for `memcpySymWords` placed at
    `memcpyAddr` in any `P` with `P.svc = Syscall.standard` and `HooksUnfetched`. -/
theorem budgetMemcpy_ok_of_hasWords (ro : Bool) (P : Program) (memcpyAddr : BitVec 64)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr (budgetMemcpySpec ro) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp hLP
  let P0 : Program := { P with externs := fun _ => none, overrides := fun _ => none }
  have hP0_no_ext : ∀ pc, P0.externAt? pc = none := by
    intro pc; simp [P0, Program.externAt?, Program.hookAtOff?]
  have hP0_words : P0.hasWords memcpyAddr memcpySymWords := by
    obtain ⟨h1, h2, _⟩ := h_words
    exact ⟨h1, h2, by simp [P0, Program.hookFree]⟩
  have hP0_cl : P0.CodeLoaded s0.mem := hLP.of_base_code rfl rfl
  simp only [budgetMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ fmtSrcBytes ro src bs) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := budgetMemcpy_len_le_2pow63 (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        (fmtSrcBytes ro src bs ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt)))
      hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_process
    (P := P0)
    (memcpy_pureWords_ro_ok ro memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    (memcpy_allInstrs_noSvc_noMsr memcpyAddr)
    hP0_words hP0_no_ext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  have hP0_svc : P0.svc = Syscall.standard := hsvc
  obtain ⟨sf, hsteps_P0, hout⟩ :=
    ProofLib.subroutine_ok_elim_steps_outcome hLift () R s0 hpc hrun
      (by
        simp only [sepConj_assoc, satisfies_pure_sepConj, ← fmtSrcBytes_eq_memcpySrc]
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
    dsimp only [budgetMemcpySpec]
    rw [fmtSrcBytes_eq_memcpySrc]
    refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
    rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
    exact Entails.pure_right
      ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩, ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm⟩⟩
      (Entails.refl _)
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem budgetMemcpy_ok_all_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    ∀ ro, subroutine_ok P memcpyAddr (budgetMemcpySpec ro) := fun ro =>
  budgetMemcpy_ok_of_hasWords ro P memcpyAddr hsvc hhooks h_words

/-- Lift `rdlAlloc_budget_thunk_ok` to `allocMultiLib.resolve mpl allocRustAllocSym` via
    `thunkAddrs.alloc`. -/
theorem rustBudgetAlloc_resolve_ok {M : AllocCostModel} {I : MallocngCostModelIface M}
    (hSound : MallocngCostModelSound M I)
    (hReqLe : ∀ (ev : AllocEvent) (st : M.σ), ev.reqBytes ≤ M.stepReserve ev st)
    (lim : MallocngBudgetLimits) (extra : SepProp) (γ : GhostName)
    {P : Program} {mAddrs : MallocngAddrs} {cAddrs : MallocngCEntryAddrs}
    {thunkAddrs rdlAddrs : RustStdAllocAddrs} {memcpyAddr : BitVec 64}
    (mpl : Obj.MultiPlacement)
    (hThunks : RustStdThunkCode P thunkAddrs rdlAddrs)
    (hShims : RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr)
    (hC : MallocngBudgetCContracts M I extra P mAddrs cAddrs)
    (hTie : allocMultiLib.resolve mpl allocRustAllocSym = thunkAddrs.alloc) :
    subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym)
      (rustBudgetAllocSpec (mallocngRustAllocBudget M I hSound hReqLe lim extra γ mAddrs)) := by
  rw [hTie]
  exact rdlAlloc_budget_thunk_ok hSound hReqLe lim extra γ thunkAddrs.alloc rdlAddrs.alloc
    hThunks.alloc_thunk hShims.alloc_instrs hC

end VerifiedLibraries.RustStd
