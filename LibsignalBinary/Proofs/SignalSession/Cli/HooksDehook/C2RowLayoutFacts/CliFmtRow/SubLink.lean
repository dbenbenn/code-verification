/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.AllocRo -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.TrapStubs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Link Bundles `CliFmtWriteSubLink` & `CliFormatInnerSubLink` on `c2FmtProgTrap lr` (`CliFmtRow.SubLink`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.SubLink

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.RustStd (coreFmtMultiLib coreMultiLib formatterWriteStrSym)
open VerifiedLibraries.RustStd.CoreFmt (LibBlockNoExtern LibKeepNoExtern writeStrKeep)
open CryptoVerification
  (LibsignalPlacement libsignalSessionLib_blocks_length ls_resolve_data_ultra lsmpl lsρ)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap (BudgetLimits zeroBudgetLimits)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (lsFmtWriteSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (resolve_lsExtern_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
  (c2AllocMpl c2AllocMpl_placeable c2_alloc_fmtWriteTie c2_alloc_handleError_resolve
   c2_alloc_memcpy_resolve c2_alloc_noAllocShim_resolve c2_alloc_rustAlloc_resolve
   c2_alloc_rustRealloc_resolve c2_alloc_seg2_sub_keepLib2Text
   c2_alloc_stringWriter_codeLoaded_of_rxCode)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
  (c2CoreFmtActiveKeep c2CoreFmtMpl c2CoreFmtMpl_placeable c2CoreMpl c2CoreMpl_placeable
   c2_coreFmt_active_sub_keepLib2Text c2_coreFmt_codeLoadedWhere_active_of_rxCode
   c2_coreFmt_codeLoadedWhere_str_of_rxCode c2_coreFmt_codeLoadedWhere_u32_of_rxCode
   c2_coreFmt_codeLoadedWhere_u64_of_rxCode c2_coreFmt_codeLoadedWhere_u8_of_rxCode
   c2_core_block_sub_keepLib2Text c2_core_codeLoaded_of_rxCode
   c2_resolve_fmtWrite_fnAddr c2_resolve_strDisplayFmt_fnAddr
   c2_resolve_u32DisplayFmt_fnAddr c2_resolve_u64DisplayFmt_fnAddr c2_resolve_u8DisplayFmt_fnAddr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.AllocRo
  (allocWriter_noExtern_fmtWrite c2AllocMpl_codeLoaded_of_c2FmtProg c2FmtWriteInternalIndices
   c2FormatInnerInternalIndices c2MplAllocCli c2MplAllocCli_handleError_resolve
   c2MplAllocCli_memcpy_resolve c2MplAllocCli_noAllocShim_resolve c2MplAllocCli_placeable
   c2MplAllocCli_rustAlloc_resolve c2MplAllocCli_rustRealloc_resolve
   c2MplAllocCli_stringWriter_codeLoaded c2MplAllocCli_vtable_eq
   c2_disjoint_fmtWrite_ok c2_disjoint_formatInner_ok c2_lsSub_codeLen_eq_lsLen
   lsBlock_noExtern_of_disjoint)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code
  (ls_codeLoaded_of_c2FmtProg rxCode_of_c2FmtProg_codeLoaded)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2FmtProg c2FmtProgTrap c2FmtProgTrap_codeLoaded_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs
  (c2FmtProgTrap_externAt_handleError c2FmtProgTrap_externAt_none_of_ge_stub_not_panic)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.TrapStubs
  (c2FmtProgTrap_allocShim_ok c2FmtProgTrap_memcpy_ok c2FmtProgTrap_rustAlloc_ok
   c2FmtProgTrap_rustRealloc_ok withExecFrozenBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (LsRetAddrFmtWrite LsRetAddrFormatInner cliStrRefDisplayShimBlocks cliStringDisplayShimBlocks
   lsU32DisplayFmtSym lsU8DisplayFmtSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
  (CliFmtWriteSubLink CliFormatInnerSubLink fmtWriteSubLsKeep formatInnerSubLsKeep
   formatInnerSubLsKeep_of_spqr lsStrDisplayFmtSym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
  (lsFormatterWriteStrSym lsU64DisplayFmtSym spqrErrorDispKeep)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3LsRetAddr624_lt_firstExternStub isLinkedPanicAddr_false_of_band keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2FirstExternStubAddr)

attribute [local irreducible] c2FmtProg c2FmtProgTrap f3TrialRxProg

private theorem ls_resolve_fmtWrite [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsFmtWriteSym = lsρ lsFmtWriteSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem ls_resolve_u8 [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsU8DisplayFmtSym = lsρ lsU8DisplayFmtSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem ls_resolve_u32 [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsU32DisplayFmtSym = lsρ lsU32DisplayFmtSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem ls_resolve_u64 [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsU64DisplayFmtSym = lsρ lsU64DisplayFmtSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem ls_resolve_strDisplay [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsStrDisplayFmtSym = lsρ lsStrDisplayFmtSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem ls_resolve_writeStr [LibsignalPlacement] :
    libsignalSessionLib.resolve lsmpl lsFormatterWriteStrSym = lsmpl.ρ lsFormatterWriteStrSym :=
  ls_resolve_data_ultra (eagerReduce (Eq.refl true))

private theorem c2_resolve_writeStr_fnAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl lsFormatterWriteStrSym =
      coreFmtMultiLib.fnAddr c2CoreFmtMpl formatterWriteStrSym :=
  (resolve_lsExtern_eq_cliElf_rho hLs lsFormatterWriteStrSym).trans (by rfl_kernel)

private def checkBlockNoPanic (L : MultiPlacedLib) (mpl : MultiPlacement) (j : Nat) : Bool :=
  let b := (mpl.base j).toNat
  let len := (L.blockLib j).text.code.length
  Nat.ble c2FirstExternStubAddr.toNat b &&
  Nat.blt (b + len) (2 ^ 64) &&
  (Nat.ble (b + len) 0x479798 ||
   (Nat.ble 0x4797d0 b && Nat.ble (b + len) 0x47a20c) ||
   (Nat.ble 0x47a3d8 b && Nat.ble (b + len) 0x47a9c4) ||
   (Nat.ble 0x47aa78 b && Nat.ble (b + len) 0x47aba0) ||
   (Nat.ble 0x47ac2c b && Nat.ble (b + len) 0x4cb070) ||
   Nat.ble 0x4cb0e4 b)

private theorem noExtern_c2FmtProgTrap_of_noPanic
    {L : MultiPlacedLib} {mpl : MultiPlacement} {j : Nat}
    {lr : BitVec 64} (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hchk : checkBlockNoPanic L mpl j = true) :
    LibBlockNoExtern L mpl (c2FmtProgTrap lr) j := by
  unfold checkBlockNoPanic at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨hge_stub, hlt64⟩, hband⟩
  intro off hoff
  let pc := mpl.base j + BitVec.ofNat 64 off
  have hpc_nat : pc.toNat = (mpl.base j).toNat + off := by
    dsimp only [pc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hnp : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts.isLinkedPanicAddr pc = false := by
    apply isLinkedPanicAddr_false_of_band
    rcases hband with ((((hb0 | hb1) | hb2) | hb3) | hb4) | hb5
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  exact c2FmtProgTrap_externAt_none_of_ge_stub_not_panic hlr
    (by dsimp only [pc] at hpc_nat; omega) hnp

set_option maxRecDepth 200000 in
private theorem c2Core_blk0_noPanic_chk : checkBlockNoPanic coreMultiLib c2CoreMpl 0 = true := by
  rfl_kernel

set_option maxRecDepth 200000 in
private theorem c2CoreFmt_active_noPanic_chk :
    (([0, 1, 2, 3, 4, 5, 6, 8, 9, 10] : List Nat).all fun j =>
      checkBlockNoPanic coreFmtMultiLib c2CoreFmtMpl j) = true := by
  rfl_kernel

private theorem c2CoreFmt_active_noExtern_trap {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {j : Nat} (hj : j < 11) (hne : j ≠ 7) :
    LibBlockNoExtern coreFmtMultiLib c2CoreFmtMpl (c2FmtProgTrap lr) j := by
  have hmem : j ∈ ([0, 1, 2, 3, 4, 5, 6, 8, 9, 10] : List Nat) := by
    match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 8, _ | 9, _ | 10, _ => decide
    | 7, _ => exact False.elim (hne rfl)
  exact noExtern_c2FmtProgTrap_of_noPanic hlr
    (List.all_eq_true.mp c2CoreFmt_active_noPanic_chk j hmem)

set_option maxRecDepth 200000 in
private theorem c2Alloc_seg2_noPanic_chk :
    (([1, 2, 3, 6, 7] : List Nat).all fun j =>
      checkBlockNoPanic (VerifiedLibraries.RustStd.allocMultiLib) c2AllocMpl j) = true := by
  rfl_kernel

private theorem c2Alloc_seg2_noExtern_trap {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    {j : Nat} (hj : j ∈ ([1, 2, 3, 6, 7] : List Nat)) :
    LibBlockNoExtern VerifiedLibraries.RustStd.allocMultiLib c2AllocMpl (c2FmtProgTrap lr) j :=
  noExtern_c2FmtProgTrap_of_noPanic hlr (List.all_eq_true.mp c2Alloc_seg2_noPanic_chk j hj)

private theorem c2_coreFmt_codeLoadedWhere_writeStr_of_rxCode {m : Memory}
    (hRx : f3TrialRxProg.CodeLoaded m) :
    coreFmtMultiLib.CodeLoadedWhere writeStrKeep c2CoreFmtMpl m := by
  have hsub : ((List.range 11).all fun j => !(writeStrKeep j) || c2CoreFmtActiveKeep j) = true := by
    decide
  have hlen : coreFmtMultiLib.blocks.length = 11 := by decide
  intro j hj hk
  rw [hlen] at hj
  have hall := List.all_eq_true.mp hsub j (List.mem_range.mpr hj)
  simp only [hk, Bool.not_true, Bool.false_or] at hall
  exact c2_coreFmt_codeLoadedWhere_active_of_rxCode hRx j (by rw [hlen]; exact hj) hall

theorem c2_fmtWriteSubLink [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits)
    {lr : BitVec 64} (hRet : LsRetAddrFmtWrite lr) :
    CliFmtWriteSubLink fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
      lim (c2FmtProgTrap lr) c2CoreMpl c2MplAllocCli c2CoreFmtMpl := by
  have hlr : lr.toNat < c2FirstExternStubAddr.toNat :=
    f3LsRetAddr624_lt_firstExternStub hLs hRet.toLsRetAddr624
  have ⟨_, _, hplLs, _⟩ := hLs
  have hCore0Len : (coreMultiLib.blockLib 0).text.code.length = 436 := by decide
  have hNoExtCore0 : ∀ off : Nat, off < 436 →
      (c2FmtProgTrap lr).externAt? (c2CoreMpl.base 0 + BitVec.ofNat 64 off) = none := by
    have h0 := noExtern_c2FmtProgTrap_of_noPanic hlr c2Core_blk0_noPanic_chk
    intro off hoff
    exact h0 off (by omega)
  refine
    { linkAlloc := fun k =>
        { plCore := c2CoreMpl_placeable
          clCore := fun m hm =>
            c2_core_codeLoaded_of_rxCode
              (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
          noExtCore0 := hNoExtCore0
          plAlloc := c2MplAllocCli_placeable k
          clAllocWriter := fun m hm =>
            c2MplAllocCli_stringWriter_codeLoaded k ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm)
          noExtAlloc1 := allocWriter_noExtern_fmtWrite hLs hRet k (Or.inl rfl)
          noExtAlloc2 := allocWriter_noExtern_fmtWrite hLs hRet k (Or.inr (Or.inl rfl))
          noExtAlloc6 := allocWriter_noExtern_fmtWrite hLs hRet k (Or.inr (Or.inr (Or.inl rfl)))
          noExtAlloc7 := allocWriter_noExtern_fmtWrite hLs hRet k (Or.inr (Or.inr (Or.inr rfl)))
          panicHandleErr := by
            rw [c2MplAllocCli_handleError_resolve k]
            exact c2FmtProgTrap_externAt_handleError hlr
          memcpyAll := fun ro => by
            rw [c2MplAllocCli_memcpy_resolve k]
            exact c2FmtProgTrap_memcpy_ok hlr ro
          allocShim := by
            rw [c2MplAllocCli_noAllocShim_resolve k]
            exact c2FmtProgTrap_allocShim_ok hlr
          rustAlloc := by
            rw [c2MplAllocCli_rustAlloc_resolve k]
            exact c2FmtProgTrap_rustAlloc_ok hlr mmpl hMm γ tp brkStart hlim
          rustRealloc := by
            rw [c2MplAllocCli_rustRealloc_resolve k]
            exact c2FmtProgTrap_rustRealloc_ok hlr mmpl hMm γ tp brkStart hlim }
      vtEq := c2MplAllocCli_vtable_eq hLs
      plFmt := c2CoreFmtMpl_placeable
      noExtFmtStr := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_str_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtFmtU8 := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU8 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u8_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      plLs := hplLs
      noExtLs := by
        rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
        intro bi hbi hk
        have hbi_cases : bi ∈ ([121, 191, 214, 216, 217, 498, 537] : List Nat) := by
          unfold fmtWriteSubLsKeep at hk
          simp only [cliStringDisplayShimBlocks, decide_eq_true_eq,
            List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide
        have hbiMem : bi ∈ c2FmtWriteInternalIndices := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbi_cases
          rcases hbi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hbi624 : bi < 624 := by
          rw [libsignalSessionLib_blocks_length] at hbi; exact hbi
        have hSubMem : bi ∈
            ([78, 121, 170, 191, 214, 215, 216, 217,
              392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbi_cases ⊢
          rcases hbi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hLenEq : (libsignalSessionLib.blockLib bi).text.code.length =
            LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen bi :=
          Nat.beq_eq.mp (List.all_eq_true.mp c2_lsSub_codeLen_eq_lsLen bi hSubMem)
        exact lsBlock_noExtern_of_disjoint hLs c2_disjoint_fmtWrite_ok hj ho hlrEq hnotInt
          hbiMem hbi624 hLenEq
      clLs := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm) j hj
      tieFmtWrite := ls_resolve_fmtWrite.symm.trans (c2_resolve_fmtWrite_fnAddr hLs)
      tieU8 := ls_resolve_u8.symm.trans (c2_resolve_u8DisplayFmt_fnAddr hLs)
      tieStrDisplay := ls_resolve_strDisplay.symm.trans (c2_resolve_strDisplayFmt_fnAddr hLs) }

theorem c2_formatInnerSubLink [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (hlim : lim ≠ zeroBudgetLimits)
    {lr : BitVec 64} (hRet : LsRetAddrFormatInner lr) :
    CliFormatInnerSubLink fineCostModel
      (withExecFrozenBudget (fineHookRustCliAllocBudget γ mmpl tp brkStart))
      lim (c2FmtProgTrap lr) c2CoreMpl c2AllocMpl c2CoreFmtMpl := by
  have hlr : lr.toNat < c2FirstExternStubAddr.toNat :=
    f3LsRetAddr624_lt_firstExternStub hLs hRet.toLsRetAddr624
  have ⟨_, _, hplLs, _⟩ := hLs
  have hCore0Len : (coreMultiLib.blockLib 0).text.code.length = 436 := by decide
  have hNoExtCore0 : ∀ off : Nat, off < 436 →
      (c2FmtProgTrap lr).externAt? (c2CoreMpl.base 0 + BitVec.ofNat 64 off) = none := by
    have h0 := noExtern_c2FmtProgTrap_of_noPanic hlr c2Core_blk0_noPanic_chk
    intro off hoff
    exact h0 off (by omega)
  have hNoExtLsAll : LibKeepNoExtern libsignalSessionLib formatInnerSubLsKeep lsmpl
      (c2FmtProgTrap lr) := by
    rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
    intro bi hbi hk
    have hbi_cases : bi ∈
        ([78, 121, 170, 191, 214, 215, 216, 217,
          392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat) := by
      unfold formatInnerSubLsKeep spqrErrorDispKeep at hk
      simp only [cliStringDisplayShimBlocks, cliStrRefDisplayShimBlocks, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with (rfl | rfl | rfl | rfl | rfl) |
          (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl |
          (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
    have hbiMem : bi ∈ c2FormatInnerInternalIndices := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbi_cases
      rcases hbi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hbi624 : bi < 624 := by
      rw [libsignalSessionLib_blocks_length] at hbi; exact hbi
    have hLenEq : (libsignalSessionLib.blockLib bi).text.code.length =
        LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen bi :=
      Nat.beq_eq.mp (List.all_eq_true.mp c2_lsSub_codeLen_eq_lsLen bi hbi_cases)
    exact lsBlock_noExtern_of_disjoint hLs c2_disjoint_formatInner_ok hj ho hlrEq hnotInt
      hbiMem hbi624 hLenEq
  refine
    { plCore := c2CoreMpl_placeable
      clCore := fun m hm =>
        c2_core_codeLoaded_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtCore0 := hNoExtCore0
      plAlloc := c2AllocMpl_placeable
      clAllocWriter := fun m hm =>
        c2_alloc_stringWriter_codeLoaded_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtAlloc1 := c2Alloc_seg2_noExtern_trap hlr (by decide)
      noExtAlloc2 := c2Alloc_seg2_noExtern_trap hlr (by decide)
      noExtAlloc6 := c2Alloc_seg2_noExtern_trap hlr (by decide)
      noExtAlloc7 := c2Alloc_seg2_noExtern_trap hlr (by decide)
      panicHandleErr := by
        rw [c2_alloc_handleError_resolve]
        exact c2FmtProgTrap_externAt_handleError hlr
      memcpyAll := fun ro => by
        rw [c2_alloc_memcpy_resolve]
        exact c2FmtProgTrap_memcpy_ok hlr ro
      allocShim := by
        rw [c2_alloc_noAllocShim_resolve]
        exact c2FmtProgTrap_allocShim_ok hlr
      rustAlloc := by
        rw [c2_alloc_rustAlloc_resolve]
        exact c2FmtProgTrap_rustAlloc_ok hlr mmpl hMm γ tp brkStart hlim
      rustRealloc := by
        rw [c2_alloc_rustRealloc_resolve]
        exact c2FmtProgTrap_rustRealloc_ok hlr mmpl hMm γ tp brkStart hlim
      clAlloc := fun m hm =>
        c2AllocMpl_codeLoaded_of_c2FmtProg ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm)
      noExtAlloc3 := c2Alloc_seg2_noExtern_trap hlr (by decide)
      fmtWriteTie := c2_alloc_fmtWriteTie
      plFmt := c2CoreFmtMpl_placeable
      noExtFmtWriteStr := c2CoreFmt_active_noExtern_trap hlr (by decide) (by decide)
      clFmtWriteStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_writeStr_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtFmtU32 := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU32 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u32_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtFmtU64 := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU64 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u64_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtLs := fun bi hbi hspqr =>
        hNoExtLsAll bi hbi (formatInnerSubLsKeep_of_spqr hspqr)
      clLs := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm) j hj
      tieWriteStr := ls_resolve_writeStr.symm.trans (c2_resolve_writeStr_fnAddr hLs)
      tieFmtWrite := ls_resolve_fmtWrite.symm.trans (c2_resolve_fmtWrite_fnAddr hLs)
      tieU32 := ls_resolve_u32.symm.trans (c2_resolve_u32DisplayFmt_fnAddr hLs)
      tieU64 := ls_resolve_u64.symm.trans (c2_resolve_u64DisplayFmt_fnAddr hLs)
      noExtFmtStr := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtStr := fun m hm =>
        c2_coreFmt_codeLoadedWhere_str_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      noExtFmtU8 := fun j hj hk =>
        c2CoreFmt_active_noExtern_trap hlr
          (by rw [show coreFmtMultiLib.blocks.length = 11 by decide] at hj; exact hj)
          (by intro h7; subst h7; cases hk)
      clFmtU8 := fun m hm =>
        c2_coreFmt_codeLoadedWhere_u8_of_rxCode
          (rxCode_of_c2FmtProg_codeLoaded ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm))
      plLs := hplLs
      noExtLsAll := hNoExtLsAll
      clLsAll := fun m hm j hj _ =>
        ls_codeLoaded_of_c2FmtProg hLs ((c2FmtProgTrap_codeLoaded_iff lr m).mp hm) j hj
      tieU8 := ls_resolve_u8.symm.trans (c2_resolve_u8DisplayFmt_fnAddr hLs)
      tieStrDisplay := ls_resolve_strDisplay.symm.trans (c2_resolve_strDisplayFmt_fnAddr hLs) }

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.SubLink
