/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FormatInnerBudgetEntry
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.StringWriteStrBudget
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FinishGrowBudget
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteProof

/-!
# Placed Composition for Budgeted `format_inner`

Proves `allocFormatInnerBudget_placed_ok`: `alloc::fmt::format::format_inner` at
`allocMultiLib.fnAddr mpl allocFormatInnerSym` satisfies `allocFormatInnerBudgetSpec` with
`va := allocStringWriteAddrs mpl`, composing `allocFormatInnerBudget_ok`, `coreFmtWrite_ok`, and
`budgetWriteStr_fmtWriteStrCall_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (AllocEvent)
open VerifiedLibraries.RustStd.CoreFmt
open FormatInnerBudget

private theorem subroutine_ok_of_multiCodeLoaded_b {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (hcl : ∀ m, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (hok : subroutine_ok P addr (lib.withCodeLoaded mpl spec)) :
    subroutine_ok P addr spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R₀ s0 hpc hrun hpre hsp0 hclP
  have hpre' : s0.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0 ∗ R₀ := by
    dsimp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_comm _ ⌜lib.CodeLoaded mpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl s0.mem hclP, hpre⟩
  exact hok.mono_outcome x R₀ s0 hpc hrun hpre' hsp0 fun _ hout => hout

private theorem allocStringWriteAddrs_writeStr_eq_resolve_b (mpl : MultiPlacement) :
    (allocStringWriteAddrs mpl).writeStr = allocMultiLib.resolve mpl allocStringWriteStrSym := by
  have h : lookupBlockSym allocStringWriteStrSym allocMultiLib.blocks = some (7, 0) := by
    decide +kernel
  simp [allocStringWriteAddrs, MultiPlacedLib.resolve, h]

/-- `alloc::fmt::format::format_inner` (`allocMultiLib` block `3`) satisfies
    `allocFormatInnerBudgetSpec` at `va := allocStringWriteAddrs mpl`, with `core::fmt::write`
    (`coreMultiLib` block `0`) and `<String as fmt::Write>::write_str` (`allocMultiLib` blocks
    `7`, `1`, `2`) discharged internally. -/
theorem allocFormatInnerBudget_placed_ok
    (P : Program) (A : RustAllocBudget) (E : List AllocEvent → Prop) (R : SepProp)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop) (stackBytes : Nat)
    (mpl : MultiPlacement) (hpl : allocMultiLib.Placeable mpl)
    (hcl : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoaded mpl m)
    (hext3 : LibBlockNoExtern allocMultiLib mpl P 3)
    (hext7 : LibBlockNoExtern allocMultiLib mpl P 7)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) =
      some Rust.panicked)
    (hmemcpy : subroutine_ok P (allocMultiLib.resolve mpl "memcpy") (budgetMemcpySpec true))
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym)
      budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym)
      (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A))
    (mplCore : MultiPlacement) (hplCore : coreMultiLib.Placeable mplCore)
    (hclCore : ∀ m, P.CodeLoaded m → coreMultiLib.CodeLoaded mplCore m)
    (hfmtWriteTie : allocMultiLib.resolve mpl fmtInnerCoreFmtWriteRawSym =
      coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (hext_core0 : ∀ off : Nat, off < 436 →
      P.externAt? (mplCore.base 0 + BitVec.ofNat 64 off) = none) :
    subroutine_ok P (allocMultiLib.fnAddr mpl allocFormatInnerSym)
      (allocFormatInnerBudgetSpec P A E (allocStringWriteAddrs mpl) R ArgStep ArgPanic ArgOom
        stackBytes) := by
  have hclAll : ∀ m, P.CodeLoaded m →
      allocMultiLib.CodeLoadedWhere (fun _ => true) mpl m :=
    fun m hm => (hcl m hm).toWhere _
  refine subroutine_ok_of_multiCodeLoaded_b hcl
    (allocFormatInnerBudget_ok P A E (allocStringWriteAddrs mpl) R ArgStep ArgPanic ArgOom
      stackBytes mpl hpl (allocStringWriteAddrs_vtable_eq_resolve mpl) hext3 hshim halloc ?_ ?_)
  · intro st0 t0 out
    rw [hfmtWriteTie]
    exact subroutine_ok_of_multiCodeLoaded_b hclCore
      (coreFmtWrite_ok hplCore hext_core0
        (fmtInnerBudgetW A st0 (allocStringWriteAddrs mpl) R t0 out)
        (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanicInv t0 ArgPanic)
        (fmtInnerBudgetOom A st0 ArgOom) stackBytes)
  · intro hstk1 hstk2 st0 t0 out ptr bs
    rw [allocStringWriteAddrs_writeStr_eq_resolve_b mpl]
    exact subroutine_ok_of_withCodeLoadedWhere_imp hclAll
      (budgetWriteStr_fmtWriteStrCall_ok A rfl rfl rfl hpl st0 (allocStringWriteAddrs mpl) R
        ArgStep ArgPanic ArgOom t0 stackBytes out ptr bs hext7 hext1 hext2 ⟨hstk1, hstk2⟩
        hpanic hmemcpy hshim halloc hrealloc)

end VerifiedLibraries.RustStd
