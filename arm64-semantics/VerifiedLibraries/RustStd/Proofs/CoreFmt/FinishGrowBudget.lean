/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.WriterOps
public import VerifiedLibraries.RustStd.Proofs.Wave2.AllocRawVecGrow
public import VerifiedLibraries.Musl.Spec.Top
public meta import ProofLib.ProgramReflection

/-!
# Budgeted `RawVecInner::finish_grow` and `String`-Writer Callee Bridges

Defines UTF-8 character encoding (`encodeUtf8Char`), `StringBuf` writer step, panic, and OOM
relations, `FmtWriteFrame` callee bridges (`budgetAllocShimSpec`, `budgetMemcpySpec`), and the
placement-generic budgeted proof `budgetFinishGrow_ok` for
`<alloc::raw_vec::RawVecInner>::finish_grow` (`allocBlocks[2]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open VerifiedLibraries.Mallocng (AllocEvent)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern PureSegPreserved
   sepWP_seg_lib_block_pureWhere sepWPp_seg_lib_block_pureWhere)

/-! ## Symbols, Call-Cone Keep Predicates, and UTF-8 Character Encoding -/

abbrev allocStringWriteCharSym : String :=
  "<alloc::string::String as core::fmt::Write>::write_char [rust_alloc]"

abbrev allocBudgetHandleErrorSym : String :=
  "_RNvNtCshlmZ2E5RoO1_5alloc7raw_vec12handle_error"

/-- Call-cone block keep predicate for `<String as Write>::{write_str, write_char}` in
    `allocMultiLib` (blocks `1`, `2`, `6`, `7`). -/
def stringWriterKeep (j : Nat) : Bool :=
  j == 1 || j == 2 || j == 6 || j == 7

/-- Call-cone block keep predicate for `<String as Write>::write_str` in `allocMultiLib`
    (blocks `1`, `2`, `7`). -/
def stringWriteStrKeep (j : Nat) : Bool :=
  j == 1 || j == 2 || j == 7

/-- Call-cone block keep predicate for `<String as Write>::write_char` in `allocMultiLib`
    (blocks `1`, `2`, `6`). -/
def stringWriteCharKeep (j : Nat) : Bool :=
  j == 1 || j == 2 || j == 6

/-- UTF-8 byte sequence emitted by `<String as fmt::Write>::write_char` for code-point word `c`. -/
def encodeUtf8Char (c : BitVec 32) : List (BitVec 8) :=
  if c.toNat < 128 then
    [c.setWidth 8]
  else if c.toNat < 2048 then
    [((c >>> 6).setWidth 8) ||| 0xc0#8, (c.setWidth 8 &&& 0x3f#8) ||| 0x80#8]
  else if c.toNat < 65536 then
    [((c >>> 12).setWidth 8) ||| 0xe0#8,
     (((c >>> 6).setWidth 8) &&& 0x3f#8) ||| 0x80#8,
     (c.setWidth 8 &&& 0x3f#8) ||| 0x80#8]
  else
    [((c >>> 18).setWidth 8) ||| 0xf0#8,
     (((c >>> 12).setWidth 8) &&& 0x3f#8) ||| 0x80#8,
     (((c >>> 6).setWidth 8) &&& 0x3f#8) ||| 0x80#8,
     (c.setWidth 8 &&& 0x3f#8) ||| 0x80#8]

@[simp] theorem encodeUtf8Char_length (c : BitVec 32) :
    (encodeUtf8Char c).length = charUtf8Len c := by
  unfold encodeUtf8Char charUtf8Len
  repeat' (split <;> simp)

theorem encodeUtf8Char_ascii {b : Nat} (hb : b < 0x80) :
    encodeUtf8Char (BitVec.ofNat 32 b) = [BitVec.ofNat 8 b] := by
  have hlt32 : b < 2 ^ 32 := by omega
  have hto : (BitVec.ofNat 32 b).toNat < 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]; omega
  simp only [encodeUtf8Char, hto, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 8)]

def StringBufStrStep (st : FmtBuf) (bs : List (BitVec 8)) (ok : Bool) (st' : FmtBuf) : Prop :=
  ok = true ∧ StringBufAppend st bs st'

def StringBufCharStep (st : FmtBuf) (c : BitVec 32) (ok : Bool) (st' : FmtBuf) : Prop :=
  ok = true ∧ StringBufAppend st (encodeUtf8Char c) st'

def StringBufWriterPanic (t0 : State) (st : FmtBuf) (n : Nat) (sf : State) : Prop :=
  sf.fs = t0.fs ∧ sf.trace = t0.trace ∧ StringBufAppendPanics st n

def StringBufWriterOom (A : RustAllocBudget) (st0 : A.σ) (st : FmtBuf) (n : Nat) (_ : State) :
    Prop :=
  ¬ A.FitsEvents st0 (stringAppendEvents st n)

/-! ## Block `6` (`write_char`) Fetch Generation -/

def allocLib06 : PlacedLib := allocMultiLib.blockLib 6
def allocPl06 [AllocPlacement] : Placement := allocMultiLib.blockPlacement AllocPlacement.mpl 6
theorem allocPlaceable06 [AllocPlacement] : allocLib06.Placeable allocPl06 :=
  allocMultiLib.placeable_blockLib (by decide) AllocPlacement.placeable
def allocPC06 [AllocPlacement] : Program := allocLib06.program allocPl06

def allocProg06 : Program :=
  { code := allocLib06.text.code, symbols := allocLib06.text.symbols }
def allocTree06 : WordTree := word_tree_of% allocProg06
theorem alloc06_code_eq : allocLib06.text.code = allocTree06.toBytes := by rfl_kernel
theorem alloc06_tree_size : allocTree06.checkSize? = some 71 := by rfl_kernel
def allocSymChars06 : List (List Char × Nat) := sym_chars_of% allocProg06
theorem alloc06_symbols_eq : allocLib06.text.symbols = toStringSymbols allocSymChars06 := by rfl_kernel
theorem alloc06_symbols_fresh : allFreshCharSymbols allocSymChars06 = true := by rfl_kernel

section
set_option linter.literalFetch false
gen_placed_fetches allocPC06 allocLib06 allocTree06 alloc06_code_eq alloc06_tree_size
  via_placement allocPl06 allocPlaceable06 [0x0 → 0x118]
gen_placed_fnOffs allocPC06 allocLib06 allocSymChars06 alloc06_symbols_eq alloc06_symbols_fresh
end

theorem allocBlockNoSvc0_06 : checkBlockNoSvc0 (allocMultiLib.blockLib 6).text = true := by
  decide

theorem allocWriteChar_lookup :
    lookup allocStringWriteCharSym allocMultiLib.blocks[6].symbols = some 0 := by
  decide

/-! ## Callee Contracts and `FmtWriteFrame` Bridges -/

/-- `__rustc::__rust_no_alloc_shim_is_unstable_v2` contract preserving both `AllocCallPreserved`
    and `VmPreserved` (so `RustAllocBudget.pool` transports across the 1-instruction shim). -/
def budgetAllocShimSpec : Spec Unit where
  pre := fun _ s => Rust.hookFrame s.sp
  post := fun _ s0 sf =>
    ⌜AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗ Rust.hookFrame s0.sp

theorem budgetAllocShim_ok {P : Program} {shimAddr : BitVec 64}
    (hinstrs : hasInstrs P shimAddr [.ret .x30]) :
    subroutine_ok P shimAddr budgetAllocShimSpec := by
  have h0 : P.fetch shimAddr = some (.ret .x30) := by simpa [hasInstrs] using hinstrs
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  dsimp only [budgetAllocShimSpec] at hpre ⊢
  refine ⟨Rust.hookFrame s0.sp, hpre, ?_⟩
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simpa [wp_norm, arm64_norm] using hrun)
  refine ⟨fun hm => ?_, rfl, ?_⟩
  · have hpres : AllocCallPreserved s0 (s0.setPC (s0.readReg64 (Reg.gpr 30#5))) ∧
        VmPreserved s0 (s0.setPC (s0.readReg64 (Reg.gpr 30#5))) :=
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl⟩⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpres, hm⟩
  · rw [CalleeSavedPreserved.iff_regs]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem subroutine_ok_budgetAllocShim_of_fmtWriteFrame {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      { Rust.shimSpec with
        post := fun x s0 sf => ⌜FmtWriteFrame s0 sf⌝ ∗ Rust.shimSpec.post x s0 sf }) :
    subroutine_ok P entry budgetAllocShimSpec := by
  refine subroutine_ok_refine h fun () R s0 hm => ?_
  dsimp only [budgetAllocShimSpec] at hm
  refine ⟨s0.sp, ?_, fun sf hpost => ?_⟩
  · dsimp only [Rust.shimSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨rfl, hm⟩
  · dsimp only [budgetAllocShimSpec, Rust.shimSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hf, hpost⟩
    have hacp : AllocCallPreserved s0 sf :=
      ⟨hf.2.1, hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1,
       hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1⟩
    exact ⟨⟨hacp, VmPreserved.of_fmtWriteFrame hf⟩, hpost⟩

/-- `memcpy(dst, src, bs.length)` contract parameterized by `ro : Bool` (`fmtSrcBytes ro src bs`),
    preserving `AllocCallPreserved` and `VmPreserved`. -/
def budgetMemcpySpec (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64⌝ ∗
      (memRegion dst bs.length ∗ fmtSrcBytes ro src bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      ((dst ↦ₛ bs) ∗ fmtSrcBytes ro src bs)

theorem subroutine_ok_budgetMemcpy_true_of_fmtWriteFrame {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      { VerifiedLibraries.Musl.memcpyROSpec with
        post := fun x s0 sf =>
          ⌜FmtWriteFrame s0 sf⌝ ∗ VerifiedLibraries.Musl.memcpyROSpec.post x s0 sf }) :
    subroutine_ok P entry (budgetMemcpySpec true) := by
  refine subroutine_ok_refine h fun (dst, src, bs) R s0 hm => ?_
  simp only [budgetMemcpySpec, fmtSrcBytes, ↓reduceIte] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hlt⟩, hm_sp⟩
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf hpost => ?_⟩
  · dsimp only [VerifiedLibraries.Musl.memcpyROSpec, CType.MutSlice8, CType.Bytes,
      VerifiedLibraries.Musl.RoSlice8, CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, htoNat, Satisfies.mono (by sep_entail) hm_sp⟩
  · simp only [budgetMemcpySpec, fmtSrcBytes, ↓reduceIte]
    dsimp only [VerifiedLibraries.Musl.memcpyROSpec,
      CType.MutSlice8, CType.Bytes, VerifiedLibraries.Musl.RoSlice8, CType.SemType.interp] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hf, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, hx0_f⟩, hpost⟩
    have hacp : AllocCallPreserved s0 sf :=
      ⟨hf.2.1, hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1,
       hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, hacp, VmPreserved.of_fmtWriteFrame hf⟩, Satisfies.mono (by sep_entail) hpost⟩

theorem subroutine_ok_budgetMemcpy_false_of_fmtWriteFrame {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry
      { VerifiedLibraries.Musl.memcpySpec with
        post := fun x s0 sf =>
          ⌜FmtWriteFrame s0 sf⌝ ∗ VerifiedLibraries.Musl.memcpySpec.post x s0 sf }) :
    subroutine_ok P entry (budgetMemcpySpec false) := by
  refine subroutine_ok_refine h fun (dst, src, bs) R s0 hm => ?_
  simp only [budgetMemcpySpec, fmtSrcBytes, Bool.false_eq_true, ↓reduceIte] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hlt⟩, hm_sp⟩
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf hpost => ?_⟩
  · dsimp only [VerifiedLibraries.Musl.memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      CType.SliceLen, CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, htoNat, Satisfies.mono (by sep_entail) hm_sp⟩
  · simp only [budgetMemcpySpec, fmtSrcBytes, Bool.false_eq_true, ↓reduceIte]
    dsimp only [VerifiedLibraries.Musl.memcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      CType.SemType.interp] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hf, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, hx0_f⟩, hpost⟩
    have hacp : AllocCallPreserved s0 sf :=
      ⟨hf.2.1, hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1,
       hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, hacp, VmPreserved.of_fmtWriteFrame hf⟩, Satisfies.mono (by sep_entail) hpost⟩

/-- Wrap `spec` with `allocMultiLib.CodeLoadedWhere keep mpl` in both `pre` and `post` so callers
    in both `SepWP` and `SepWPp` preserve `CodeLoadedWhere keep mpl` across calls. -/
def allocWithCodeLoadedWhere {α : Type} (keep : Nat → Bool) (mpl : MultiPlacement)
    (spec : Spec α) : Spec α :=
  { allocMultiLib.withCodeLoadedWhere keep mpl spec with
    post := fun x s0 sf =>
      ⌜allocMultiLib.CodeLoadedWhere keep mpl sf.mem⌝ ∗ spec.post x s0 sf }

theorem subroutine_ok_of_allocWithCodeLoadedWhere {α : Type}
    {keep : Nat → Bool} {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (allocWithCodeLoadedWhere keep mpl spec)) :
    subroutine_ok P entry (allocMultiLib.withCodeLoadedWhere keep mpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocWithCodeLoadedWhere] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

theorem subroutine_ok_of_withCodeLoadedWhere_imp {α : Type}
    {keep : Nat → Bool} {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hcl : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoadedWhere keep mpl m)
    (h : subroutine_ok P entry (allocMultiLib.withCodeLoadedWhere keep mpl spec)) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [MultiPlacedLib.withCodeLoadedWhere]
  rw [sepConj_assoc, pure_sepConj_of_true (hcl s0.mem hL)]
  exact hpre

theorem allocCallPreserved_of_fmtWriteFrame {s s' : State} (hf : FmtWriteFrame s s') :
    AllocCallPreserved s s' :=
  ⟨hf.2.1, hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1,
   hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1⟩

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem allocCall_vm_of_pureSeg {s s' sm' sm : State}
    (hcpu_in : SameCpuState s' s) (hcpu_out : SameCpuState sm sm')
    (hseg : PureSegPreserved s sm)
    (hsig : sm'.sigActions = s'.sigActions) (htp : sm'.tpidrEl0 = s'.tpidrEl0) :
    AllocCallPreserved s sm ∧ VmPreserved s sm := by
  have hf := fmtWriteFrame_of_pureSeg hseg
    (hcpu_out.sigActions_eq.trans (hsig.trans hcpu_in.sigActions_eq))
    (hcpu_out.tpidrEl0_eq.trans (htp.trans hcpu_in.tpidrEl0_eq))
  exact ⟨allocCallPreserved_of_fmtWriteFrame hf, VmPreserved.of_fmtWriteFrame hf⟩

theorem satisfies_fmtBufVecAt_bounds {A : RustAllocBudget}
    {cap ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp} {m : Memory}
    (hm : (fmtBufVecAt A cap ptr bs ∗ R).Satisfies m) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 := by
  dsimp only [fmtBufVecAt] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

theorem oomPreserved_of_allocCall {s0 sm sf : State}
    (hacp : AllocCallPreserved s0 sm) (hoom : OomPreserved sm sf) :
    OomPreserved s0 sf :=
  ⟨hoom.1.trans hacp.1, hoom.2.1.trans hacp.2.1, hoom.2.2.trans hacp.2.2.1⟩

/-! ## Budgeted `RawVecInner::finish_grow` (`allocBlocks[2]`) -/

def stringGrowStepEvents (oldCap : BitVec 64) (newCap : Nat) : List AllocEvent :=
  if oldCap = 0#64 then rustAllocEvents newCap 1 else rustReallocEvents oldCap.toNat newCap 1

/-- Budget-threaded contract for `liballoc`'s `<alloc::raw_vec::RawVecInner>::finish_grow`
    (`allocBlocks[2]`, `168` B) over `A : RustAllocBudget` and `fmtBufVecAt A`.
    Ghost: `(outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st)`. -/
def budgetFinishGrowSpec (A : RustAllocBudget) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
      BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × A.σ) where
  pre := fun (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧
      s0.readReg64 .x1 = oldCap ∧
      s0.readReg64 .x2 = oldPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 newCap ∧
      0 < newCap ∧ newCap < 2 ^ 64 ∧ bs.length ≤ newCap⌝ ∗
    (stackAt s0.sp (32 + Rust.hookStack) ∗
      vecHeader outPtr v0 v1 v2 ∗
      fmtBufVecAt A oldCap oldPtr bs ∗
      A.pool st s0)
  post := fun (outPtr, _, _, _, oldCap, oldPtr, bs, newCap, st) s0 sf =>
    ∃∗ isErr : Bool, ∃∗ newPtr : BitVec 64, ∃∗ errW1 : BitVec 64, ∃∗ errW2 : BitVec 64,
      ⌜AllocCallPreserved s0 sf⌝ ∗
      (stackAt s0.sp (32 + Rust.hookStack) ∗
        (if isErr then
          ⌜NullAllowed newCap 1⌝ ∗
          vecHeader outPtr 1#64 errW1 errW2 ∗
          fmtBufVecAt A oldCap oldPtr bs ∗
          A.pool st sf
         else
          ⌜newCap < 2 ^ 63⌝ ∗
          vecHeader outPtr 0#64 newPtr (BitVec.ofNat 64 newCap) ∗
          fmtBufVecAt A (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool (A.stepEvents (stringGrowStepEvents oldCap newCap) st) sf))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun (_, _, _, _, oldCap, _, _, newCap, st) s0 sf =>
    ⌜¬ A.FitsEvents st (stringGrowStepEvents oldCap newCap) ∧ OomPreserved s0 sf⌝

def BudgetGrowHighGprs (s0 s1 : State) : Prop :=
  s1.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5) ∧
  s1.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5) ∧
  s1.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5) ∧
  s1.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5) ∧
  s1.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s1.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s1.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s1.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)

theorem BudgetGrowHighGprs.trans {s0 s1 s2 : State}
    (h01 : BudgetGrowHighGprs s0 s1) (h12 : BudgetGrowHighGprs s1 s2) :
    BudgetGrowHighGprs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

theorem BudgetGrowHighGprs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    BudgetGrowHighGprs s0 s1 :=
  ⟨h.readReg64_x21, h.readReg64_x22, h.readReg64_x23, h.readReg64_x24,
   h.readReg64_x25, h.readReg64_x26, h.readReg64_x27, h.readReg64_x28⟩

section FinishGrowProof
arm64_proof_prelude

private abbrev budgetFinishGrowSavedSlots (s0 : State) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))

private theorem budgetFinishGrow_stack_split (sp : BitVec 64) :
    stackAt sp (32 + Rust.hookStack) =
      ∃∗ st0, ∃∗ st1, ∃∗ st2, ∃∗ st3,
        Rust.hookFrame (sp - 32#64) ∗
        (((sp - 32#64) ↦₆₄ st0) ∗ ((sp - 24#64) ↦₆₄ st1) ∗
          ((sp - 16#64) ↦₆₄ st2) ∗ ((sp - 8#64) ↦₆₄ st3)) := by
  rw [show 32 + Rust.hookStack = Rust.hookStack + 8 * 4 by decide,
    stackAt_split_cells sp Rust.hookStack 4 (by decide)]
  simp only [Nat.reduceMul, cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_right, ProofLib.stackAt, Rust.hookFrame]
  simp only [bv_lin_norm]

private theorem budgetFinishGrow_stack_refold (sp w0 w1 w2 w3 : BitVec 64) :
    Rust.hookFrame (sp - 32#64) ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      stackAt sp (32 + Rust.hookStack) := by
  rw [budgetFinishGrow_stack_split sp]
  exact Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <| Entails.refl _

private theorem budgetFinishGrow_realloc_pc [AllocPlacement] :
    allocPl02.base + 40#64 + (allocPl02.ρ allocRustReallocSym - allocPl02.base - 40#64) =
      allocMultiLib.resolve AllocPlacement.mpl allocRustReallocSym := by
  change allocPl02.base + 40#64 +
    (allocMultiLib.resolve AllocPlacement.mpl allocRustReallocSym - allocPl02.base - 40#64) =
    allocMultiLib.resolve AllocPlacement.mpl allocRustReallocSym
  bv_lin

private theorem budgetFinishGrow_shim_pc [AllocPlacement] :
    allocPl02.base + 84#64 + (allocPl02.ρ allocRustNoAllocShimSym - allocPl02.base - 84#64) =
      allocMultiLib.resolve AllocPlacement.mpl allocRustNoAllocShimSym := by
  change allocPl02.base + 84#64 +
    (allocMultiLib.resolve AllocPlacement.mpl allocRustNoAllocShimSym - allocPl02.base - 84#64) =
    allocMultiLib.resolve AllocPlacement.mpl allocRustNoAllocShimSym
  bv_lin

private theorem budgetFinishGrow_alloc_pc [AllocPlacement] :
    allocPl02.base + 96#64 + (allocPl02.ρ allocRustAllocSym - allocPl02.base - 96#64) =
      allocMultiLib.resolve AllocPlacement.mpl allocRustAllocSym := by
  change allocPl02.base + 96#64 +
    (allocMultiLib.resolve AllocPlacement.mpl allocRustAllocSym - allocPl02.base - 96#64) =
    allocMultiLib.resolve AllocPlacement.mpl allocRustAllocSym
  bv_lin

private theorem budgetRustLayoutOk_one {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega, by decide⟩

private theorem budgetBit63_eq_zero_of_lt {n : Nat} (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n / 2 ^ 63 = 0 := Nat.div_eq_of_lt hlt
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem budgetBit63_eq_one_of_ge {n : Nat} (hge : 2 ^ 63 ≤ n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).getLsbD 63 = true := by
  have hd : n / 2 ^ 63 = 1 := by omega
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  rfl

private theorem budgetFinishGrow_post_err [AllocPlacement]
    (A : RustAllocBudget) {keep : Nat → Bool} (hk2 : keep 2 = true)
    {P : Program} (hext2 : LibBlockNoExtern allocMultiLib allocMpl P 2)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : A.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : allocMultiLib.CodeLoadedWhere keep allocMpl se.mem)
    (hpc : se.pc = allocPl02.base + 100#64 ∨ se.pc = allocPl02.base + 44#64)
    (hrun : se.status = .Running) (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 32#64)
    (hx0 : se.readReg64 .x0 = 0#64)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : BudgetGrowHighGprs s0 se) (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se) (hnull : NullAllowed newCap 1)
    (hpost : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (allocWithCodeLoadedWhere keep allocMpl (budgetFinishGrowSpec A)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) → post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (Rust.hookFrame (s0.sp - 32#64) ∗ budgetFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗ fmtBufVecAt A oldCap oldPtr bs ∗ A.pool st se)
      post oomProp := by
  apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e
  change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 32#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = 0#64 := (hcpu_e.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr := (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [budgetFinishGrowSavedSlots, vecHeader]
  rcases hpc with hpc | hpc <;>
  · have hpc_e' := hcpu_e.pc_eq.trans hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
      fun sf hcpu_f hcl_f hseg_f => ?_
    have ⟨hacp_ef, hvm_ef⟩ :=
      allocCall_vm_of_pureSeg hcpu_e hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_ef : A.pool st se = A.pool st sf := (A.pool_transport st se sf hvm_ef).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2,
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))⟩
    refine SepWP.done hpc_f hrun_f (hpost sf hsp_f hcs_f ?_)
    have hstk_back := budgetFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    dsimp only [allocWithCodeLoadedWhere, budgetFinishGrowSpec]
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right true <| Entails.sepExists_right 0#64 <|
        Entails.sepExists_right 1#64 <| Entails.sepExists_right (BitVec.ofNat 64 newCap) <| Entails.refl _)
    simp only [↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef), pure_sepConj_of_true hnull]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail

private theorem budgetFinishGrow_post_ok [AllocPlacement]
    (A : RustAllocBudget) {keep : Nat → Bool} (hk2 : keep 2 = true)
    {P : Program} (hext2 : LibBlockNoExtern allocMultiLib allocMpl P 2)
    {s0 se : State} {outPtr v0 v1 v2 oldCap oldPtr newPtr : BitVec 64}
    {bs : List (BitVec 8)} {newCap : Nat} {st : A.σ}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcl : allocMultiLib.CodeLoadedWhere keep allocMpl se.mem)
    (hpc : se.pc = allocPl02.base + 100#64 ∨ se.pc = allocPl02.base + 44#64)
    (hrun : se.status = .Running) (hsp0 : s0.spAligned = true) (hsp_eq : se.sp = s0.sp - 32#64)
    (hx0 : se.readReg64 .x0 = newPtr) (hnewPtr_ne0 : newPtr ≠ 0#64)
    (hx19 : se.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap)
    (hx20 : se.readReg64 (.gpr 20#5) = outPtr)
    (hgprs : BudgetGrowHighGprs s0 se) (hvregs : calleeSavedVRegs se = calleeSavedVRegs s0)
    (hacp_0e : AllocCallPreserved s0 se) (hnew_lt63 : newCap < 2 ^ 63)
    (hpost : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ (allocWithCodeLoadedWhere keep allocMpl (budgetFinishGrowSpec A)).post
          (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st) s0 sf) → post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) se
      (Rust.hookFrame (s0.sp - 32#64) ∗ budgetFinishGrowSavedSlots s0 ∗
        vecHeader outPtr v0 v1 v2 ∗ fmtBufVecAt A (BitVec.ofNat 64 newCap) newPtr bs ∗
        A.pool (A.stepEvents (stringGrowStepEvents oldCap newCap) st) se)
      post oomProp := by
  have hnewPtr_beq0 : (newPtr == 0#64) = false := beq_false_of_ne hnewPtr_ne0
  apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl
    (mid := s0.readReg64 .lr)
  intro se' hcpu_e
  change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
  have hrun_e' : se'.status = .Running := hcpu_e.status_eq.trans hrun
  have hsp_e_in : se'.sp = s0.sp - 32#64 := hcpu_e.sp_eq.trans hsp_eq
  have hsp_e' : se'.spAligned = true := by
    rw [hcpu_e.spAligned]; simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 32#64 hsp0
  have hx0_e' : se'.readReg64 (.gpr 0#5) = newPtr := (hcpu_e.readReg64 .x0).trans hx0
  have hx19_e' : se'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := (hcpu_e.readReg64 _).trans hx19
  have hx20_e' : se'.readReg64 (.gpr 20#5) = outPtr := (hcpu_e.readReg64 _).trans hx20
  wp_conv_pre => simp only [budgetFinishGrowSavedSlots, vecHeader]
  rcases hpc with hpc | hpc <;>
  · have hpc_e' := hcpu_e.pc_eq.trans hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_e')
      fun sf hcpu_f hcl_f hseg_f => ?_
    have ⟨hacp_ef, hvm_ef⟩ :=
      allocCall_vm_of_pureSeg hcpu_e hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_ef :
        A.pool (A.stepEvents (stringGrowStepEvents oldCap newCap) st) se =
        A.pool (A.stepEvents (stringGrowStepEvents oldCap newCap) st) sf :=
      (A.pool_transport _ se sf hvm_ef).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun_e'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.1,
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu_e.readReg64 _).trans hgprs.2.2.2.2.2.2.2,
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs se').trans
          (hcpu_e.calleeSavedVRegs.trans hvregs))⟩
    refine SepWP.done hpc_f hrun_f (hpost sf hsp_f hcs_f ?_)
    have hstk_back := budgetFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    dsimp only [allocWithCodeLoadedWhere, budgetFinishGrowSpec]
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right false <| Entails.sepExists_right newPtr <|
        Entails.sepExists_right 0#64 <| Entails.sepExists_right 0#64 <| Entails.refl _)
    simp only [Bool.false_eq_true, ↓reduceIte, hpool_eq_ef, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true (allocCallPreserved_trans hacp_0e hacp_ef), pure_sepConj_of_true hnew_lt63]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail

set_option maxHeartbeats 800000 in
/-- Placement-generic, budget-threaded proof of `liballoc`'s `<alloc::raw_vec::RawVecInner>::finish_grow`
    (`allocBlocks[2]`, `168` B) over `A : RustAllocBudget`. -/
theorem budgetFinishGrow_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk2 : keep 2 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl)
    {P : Program}
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocFinishGrowSym)
      (allocWithCodeLoadedWhere keep mpl (budgetFinishGrowSpec A)) := by
  letI : AllocPlacement := ⟨mpl, hpl⟩
  rw [allocResolve_eq_base hpl 2 allocFinishGrowSym (by decide) allocFinishGrow_lookup]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, st⟩ R s0 hpc hrun hpre hsp0
  dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere,
    budgetFinishGrowSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le_new⟩, hmem⟩
  have ⟨hbs_le_old, hold_lt, holdPtr_ne⟩ :
      bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64 :=
    satisfies_fmtBufVecAt_bounds (m := s0.mem)
      (R := stackAt s0.sp (32 + Rust.hookStack) ∗ vecHeader outPtr v0 v1 v2 ∗ A.pool st s0 ∗ R)
      (Satisfies.mono (by sep_entail) hmem)
  refine ⟨_, hmem, ?_⟩
  wp_conv_pre =>
    rw [budgetFinishGrow_stack_split s0.sp]
    simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 => ?_
  by_cases hge63 : 2 ^ 63 ≤ newCap
  · have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = true := budgetBit63_eq_one_of_ge hge63 hnew_lt64
    have hnull : NullAllowed newCap 1 := by unfold NullAllowed; omega
    apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl0
      (mid := s0.readReg64 .lr)
    intro s1' hcpu1
    change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = allocPl02.base := hcpu1.pc_eq.trans hpc
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
    have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
    have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
    have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
    have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
    have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
    wp_conv_pre => simp only [vecHeader, ← hsp1_in]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
      fun sf hcpu_f hcl_f hseg_f => ?_
    have ⟨hacp_0f, hvm_0f⟩ :=
      allocCall_vm_of_pureSeg hcpu1 hcpu_f hseg_f (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_0f : A.pool st s0 = A.pool st sf := (A.pool_transport st s0 sf hvm_0f).symm
    have hpc_f : sf.pc = s0.readReg64 .lr := hcpu_f.pc_eq.trans (by simp [arm64_norm])
    have hrun_f : sf.status = .Running := hcpu_f.status_eq.trans hrun1'
    have hsp_f : sf.sp = s0.sp := hcpu_f.sp_eq.trans (by simp [arm64_norm])
    have hcs_f : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _),
        by rw [hcpu_f.readReg64]; simp [arm64_norm],
        hcpu_f.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans
          hcpu1.calleeSavedVRegs)⟩
    refine SepWP.done hpc_f hrun_f
      ⟨fun hm_f => Satisfies.mono (sepConj_mono_left ?_) hm_f, hsp_f, hcs_f⟩
    have hstk_back := budgetFinishGrow_stack_refold s0.sp
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5))
      (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
    rw [pure_sepConj_of_true hcl_f]
    refine Entails.trans ?_
      (Entails.sepExists_right true <| Entails.sepExists_right 0#64 <|
        Entails.sepExists_right 0#64 <| Entails.sepExists_right v2 <| Entails.refl _)
    simp only [↓reduceIte, hsp1_in, hpool_eq_0f, vecHeader, bv_lin_norm]
    rw [pure_sepConj_of_true hacp_0f, pure_sepConj_of_true hnull]
    refine Entails.trans ?_ (sepConj_mono_left hstk_back)
    sep_entail
  · have hnew_lt63 : newCap < 2 ^ 63 := Nat.lt_of_not_ge hge63
    have hbit63 : (BitVec.ofNat 64 newCap).getLsbD 63 = false := budgetBit63_eq_zero_of_lt hnew_lt63
    have hlay : RustLayoutOk newCap 1 := budgetRustLayoutOk_one hnew_pos hnew_lt63
    have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by bv_omega
    by_cases hold0 : oldCap = 0#64
    · subst hold0
      have hbs_nil : bs = [] := by simpa using hbs_le_old
      subst hbs_nil
      apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl0
        (mid := allocMultiLib.resolve mpl allocRustNoAllocShimSym)
      intro s1' hcpu1
      change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl02.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = 0#64 := (hcpu1.readReg64 .x1).trans hx1
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done budgetFinishGrow_shim_pc (by simpa [arm64_norm] using hrun1')
        fun sm_sh hcpu_sh hcl_sh hseg_sh => ?_
      have ⟨hacp_0sh, hvm_0sh⟩ :=
        allocCall_vm_of_pureSeg hcpu1 hcpu_sh hseg_sh (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0sh : A.pool st s0 = A.pool st sm_sh := (A.pool_transport st s0 sm_sh hvm_0sh).symm
      have hpc_sh : sm_sh.pc = allocMultiLib.resolve mpl allocRustNoAllocShimSym :=
        hcpu_sh.pc_eq.trans budgetFinishGrow_shim_pc
      have hrun_sh : sm_sh.status = .Running := hcpu_sh.status_eq.trans hrun1'
      have hsp_sh_eq : sm_sh.sp = s0.sp - 32#64 := hcpu_sh.sp_eq.trans (by simp [arm64_norm])
      have hsp_sh : sm_sh.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_sh_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_sh : sm_sh.readReg64 .lr =
          allocPl02.base + (reloc_call_off% allocLib02.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64) := by
        rw [hcpu_sh.readReg64 .lr]; simp [arm64_norm]
      have hx19_sh : sm_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hx20_sh : sm_sh.readReg64 (.gpr 20#5) = outPtr := by
        rw [hcpu_sh.readReg64]; simp [arm64_norm]
      have hgprs_sh : BudgetGrowHighGprs s0 sm_sh := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_sh.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_sh : calleeSavedVRegs sm_sh = calleeSavedVRegs s0 :=
        hcpu_sh.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0sh]
      apply seqCodeLoadedWhere hcl_sh
        (mid := allocPl02.base + (reloc_call_off% allocLib02.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2" + 4#64))
      apply (SepWP.call_subroutine_frame hshim (x := ())
        hpc_sh hrun_sh hsp_sh hlr_sh
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
      · intro R' hm'
        dsimp only [budgetAllocShimSpec]; rw [hsp_sh_eq]; exact Satisfies.mono (by sep_frame) hm'
      · intro sf_sh hpc_sfsh hrun_sfsh hsp_sfsh hcs_sfsh
        refine SepWP.done hpc_sfsh hrun_sfsh fun hcl_sfsh => ?_
        dsimp only [budgetAllocShimSpec]; wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; rintro ⟨hacp_sh, hvm_sh⟩
        have hpool_eq_sh : A.pool st sm_sh = A.pool st sf_sh :=
          (A.pool_transport st sm_sh sf_sh hvm_sh).symm
        have hsp_sfsh_eq : sf_sh.sp = s0.sp - 32#64 := hsp_sfsh.trans hsp_sh_eq
        have hx19_sfsh : sf_sh.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap :=
          hcs_sfsh.readReg64_x19.trans hx19_sh
        have hx20_sfsh : sf_sh.readReg64 (.gpr 20#5) = outPtr :=
          hcs_sfsh.readReg64_x20.trans hx20_sh
        have hgprs_sfsh : BudgetGrowHighGprs s0 sf_sh :=
          hgprs_sh.trans (BudgetGrowHighGprs.of_calleeSaved hcs_sfsh)
        have hvregs_sfsh : calleeSavedVRegs sf_sh = calleeSavedVRegs s0 :=
          hcs_sfsh.vregs.trans hvregs_sh
        apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl_sfsh
          (mid := allocMultiLib.resolve mpl allocRustAllocSym)
        intro sa' hcpu_a
        change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
        have hpc_a' : sa'.pc = allocPl02.base + 88#64 := hcpu_a.pc_eq.trans hpc_sfsh
        have hrun_a' : sa'.status = .Running := hcpu_a.status_eq.trans hrun_sfsh
        have hsp_a_in : sa'.sp = s0.sp - 32#64 := hcpu_a.sp_eq.trans hsp_sfsh_eq
        have hx19_a' : sa'.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := (hcpu_a.readReg64 _).trans hx19_sfsh
        have hx20_a' : sa'.readReg64 (.gpr 20#5) = outPtr := (hcpu_a.readReg64 _).trans hx20_sfsh
        wp_sym_steps
        refine SepWP.done budgetFinishGrow_alloc_pc (by simpa [arm64_norm] using hrun_a')
          fun sm_al hcpu_al hcl_al hseg_al => ?_
        have ⟨hacp_shal, hvm_shal⟩ :=
          allocCall_vm_of_pureSeg hcpu_a hcpu_al hseg_al (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq_shal : A.pool st sf_sh = A.pool st sm_al :=
          (A.pool_transport st sf_sh sm_al hvm_shal).symm
        have hacp_0al : AllocCallPreserved s0 sm_al :=
          allocCallPreserved_trans hacp_0sh (allocCallPreserved_trans hacp_sh hacp_shal)
        have hpc_al : sm_al.pc = allocMultiLib.resolve mpl allocRustAllocSym :=
          hcpu_al.pc_eq.trans budgetFinishGrow_alloc_pc
        have hrun_al : sm_al.status = .Running := hcpu_al.status_eq.trans hrun_a'
        have hsp_al_eq : sm_al.sp = s0.sp - 32#64 :=
          (hcpu_al.sp_eq.trans (by simp [arm64_norm])).trans hsp_a_in
        have hsp_al : sm_al.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_al_eq]; exact s0.spAligned_sub 32#64 hsp0
        have hlr_al : sm_al.readReg64 .lr =
            allocPl02.base + (reloc_call_off% allocLib02.text.relocs
              "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64) := by
          rw [hcpu_al.readReg64 .lr]; simp [arm64_norm]
        have hx0_al_nat : (sm_al.readReg64 .x0).toNat = newCap := by
          rw [hcpu_al.readReg64 .x0]; simpa [arm64_norm] using hnew_toNat
        have hx1_al_nat : (sm_al.readReg64 .x1).toNat = 1 := by
          rw [hcpu_al.readReg64 .x1]; simp [arm64_norm]
        have hx19_al : sm_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx19_a'
        have hx20_al : sm_al.readReg64 (.gpr 20#5) = outPtr := by
          rw [hcpu_al.readReg64]; simpa [arm64_norm] using hx20_a'
        have hgprs_al : BudgetGrowHighGprs s0 sm_al :=
          ⟨by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.1,
           by rw [hcpu_al.readReg64]; simpa [arm64_norm] using (hcpu_a.readReg64 _).trans hgprs_sfsh.2.2.2.2.2.2.2⟩
        have hvregs_al : calleeSavedVRegs sm_al = calleeSavedVRegs s0 :=
          hcpu_al.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sa').trans
            (hcpu_a.calleeSavedVRegs.trans hvregs_sfsh))
        wp_conv_pre => simp only [hsp_sh_eq, hpool_eq_sh, hpool_eq_shal]
        apply seqCodeLoadedWhere hcl_al
          (mid := allocPl02.base + (reloc_call_off% allocLib02.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc" + 4#64))
        apply (SepWP.call_subroutine_frame halloc (x := (newCap, 1, st))
          hpc_al hrun_al hsp_al hlr_al
          (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
          (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
          (h_oom := fun _ sf_oom _ hm_oom => by
            have hm' := Satisfies.drop_mid hm_oom
            dsimp only [rustBudgetAllocSpec, stringGrowStepEvents] at hm' ⊢
            simp only [↓reduceIte]; rw [satisfies_pure_sepConj] at hm' ⊢
            exact ⟨⟨hm'.1.1, oomPreserved_of_allocCall hacp_0al hm'.1.2⟩, hm'.2⟩))
        · intro R' hm'
          dsimp only [rustBudgetAllocSpec]; rw [sepConj_assoc, satisfies_pure_sepConj, hsp_al_eq]
          exact ⟨⟨hx0_al_nat, hx1_al_nat, hlay⟩, Satisfies.mono (by sep_frame) hm'⟩
        · intro sf_al hpc_sfal hrun_sfal hsp_sfal hcs_sfal
          refine SepWP.done hpc_sfal hrun_sfal fun hcl_sfal => ?_
          dsimp only [rustBudgetAllocSpec]; wp_conv_pre => simp only [sepConj_assoc]
          apply SepWP.pure_elim; intro hacp_al
          have hsp_sfal_eq : sf_al.sp = s0.sp - 32#64 := hsp_sfal.trans hsp_al_eq
          have hx19_sfal : sf_al.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := hcs_sfal.readReg64_x19.trans hx19_al
          have hx20_sfal : sf_al.readReg64 (.gpr 20#5) = outPtr := hcs_sfal.readReg64_x20.trans hx20_al
          have hgprs_sfal : BudgetGrowHighGprs s0 sf_al := hgprs_al.trans (BudgetGrowHighGprs.of_calleeSaved hcs_sfal)
          have hvregs_sfal : calleeSavedVRegs sf_al = calleeSavedVRegs s0 := hcs_sfal.vregs.trans hvregs_al
          by_cases hx0_al0 : sf_al.readReg64 .x0 = 0#64
          · wp_conv_pre =>
              simp only [show (0 : BitVec 64) = 0#64 from rfl, hx0_al0, ↓reduceIte, hsp_al_eq, sepConj_assoc]
              rw [sepConj_left_comm (Rust.hookFrame _) ⌜NullAllowed newCap 1⌝,
                sepConj_left_comm (A.pool st sf_al) ⌜NullAllowed newCap 1⌝]
            apply SepWP.pure_elim; intro hnull_al
            refine SepWP.weaken_pre (by dsimp only [budgetFinishGrowSavedSlots, vecHeader]; sep_entail) <|
              budgetFinishGrow_post_err A hk2 hext2 hcl_sfal (Or.inl hpc_sfal) hrun_sfal hsp0 hsp_sfal_eq
                hx0_al0 hx19_sfal hx20_sfal hgprs_sfal hvregs_sfal
                (allocCallPreserved_trans hacp_0al hacp_al) hnull_al
                fun sf hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
          · wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl, hx0_al0, ↓reduceIte, hsp_al_eq,
              pure_sepConj_of_true (Nat.mod_one (sf_al.readReg64 .x0).toNat), sepConj_assoc]
            refine SepWP.weaken_pre (by
              dsimp only [budgetFinishGrowSavedSlots, vecHeader, fmtBufVecAt, stringGrowStepEvents]
              simp only [↓reduceIte, hnew_ne0, hnew_toNat, List.length_nil, Nat.sub_zero,
                BitVec.add_zero, pointsToBytes_nil]
              rw [pure_sepConj_of_true ⟨Nat.zero_le 0, by decide, holdPtr_ne⟩]
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                  (by rw [pure_sepConj_of_true ⟨Nat.zero_le _, hnew_lt63, hx0_al0⟩]; exact Entails.refl _)))))
              sep_entail) <|
              budgetFinishGrow_post_ok A hk2 hext2 hcl_sfal (Or.inl hpc_sfal) hrun_sfal hsp0 hsp_sfal_eq
                rfl hx0_al0 hx19_sfal hx20_sfal hgprs_sfal hvregs_sfal
                (allocCallPreserved_trans hacp_0al hacp_al) hnew_lt63
                fun sf hsp_f hcs_f {_Pre_f} hent =>
                  ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
    · have hold_beq0 : (oldCap == 0#64) = false := beq_false_of_ne hold0
      wp_conv_pre =>
        simp only [fmtBufVecAt, hold0, ↓reduceIte,
          pure_sepConj_of_true
            (⟨hbs_le_old, hold_lt, holdPtr_ne⟩ :
              bs.length ≤ oldCap.toNat ∧ oldCap.toNat < 2 ^ 63 ∧ oldPtr ≠ 0#64),
          sepConj_assoc]
      apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 2 ⟨by decide, hk2⟩ hext2 allocBlockNoSvc0_02 hcl0
        (mid := allocMultiLib.resolve mpl allocRustReallocSym)
      intro s1' hcpu1
      change SepWP (allocPC02.rebase allocPl02.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = allocPl02.base := hcpu1.pc_eq.trans hpc
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 (.gpr 0#5) = outPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 (.gpr 1#5) = oldCap := (hcpu1.readReg64 .x1).trans hx1
      have hx2_1' : s1'.readReg64 (.gpr 2#5) = oldPtr := (hcpu1.readReg64 .x2).trans hx2
      have hx3_1' : s1'.readReg64 (.gpr 3#5) = BitVec.ofNat 64 newCap := (hcpu1.readReg64 .x3).trans hx3
      have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) := hcpu1.readReg64 _
      have hx19_1' : s1'.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) := hcpu1.readReg64 _
      have hx20_1' : s1'.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5) := hcpu1.readReg64 _
      have hx29_1' : s1'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu1.readReg64 _
      wp_conv_pre => simp only [← hsp1_in]
      wp_sym_steps
      refine SepWP.done budgetFinishGrow_realloc_pc (by simpa [arm64_norm] using hrun1')
        fun sm_re hcpu_re hcl_re hseg_re => ?_
      have ⟨hacp_0re, hvm_0re⟩ :=
        allocCall_vm_of_pureSeg hcpu1 hcpu_re hseg_re (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_0re : A.pool st s0 = A.pool st sm_re := (A.pool_transport st s0 sm_re hvm_0re).symm
      have hpc_re : sm_re.pc = allocMultiLib.resolve mpl allocRustReallocSym :=
        hcpu_re.pc_eq.trans budgetFinishGrow_realloc_pc
      have hrun_re : sm_re.status = .Running := hcpu_re.status_eq.trans hrun1'
      have hsp_re_eq : sm_re.sp = s0.sp - 32#64 := hcpu_re.sp_eq.trans (by simp [arm64_norm])
      have hsp_re : sm_re.spAligned = true := by
        simp only [State.spAligned]; rw [hsp_re_eq]; exact s0.spAligned_sub 32#64 hsp0
      have hlr_re : sm_re.readReg64 .lr =
          allocPl02.base + (reloc_call_off% allocLib02.text.relocs
            "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64) := by
        rw [hcpu_re.readReg64 .lr]; simp [arm64_norm]
      have hx0_re : sm_re.readReg64 .x0 = oldPtr := by rw [hcpu_re.readReg64 .x0]; simp [arm64_norm]
      have hx1_re_nat : (sm_re.readReg64 .x1).toNat = oldCap.toNat := by
        rw [hcpu_re.readReg64 .x1]; simpa [arm64_norm] using congrArg BitVec.toNat hx1_1'
      have hx2_re_nat : (sm_re.readReg64 .x2).toNat = 1 := by rw [hcpu_re.readReg64 .x2]; simp [arm64_norm]
      have hx3_re_nat : (sm_re.readReg64 .x3).toNat = newCap := by
        rw [hcpu_re.readReg64 .x3]; simpa [arm64_norm] using hnew_toNat
      have hx19_re : sm_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hx20_re : sm_re.readReg64 (.gpr 20#5) = outPtr := by rw [hcpu_re.readReg64]; simp [arm64_norm]
      have hgprs_re : BudgetGrowHighGprs s0 sm_re := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_re.readReg64]; simpa [arm64_norm] using (hcpu1.readReg64 _)
      have hvregs_re : calleeSavedVRegs sm_re = calleeSavedVRegs s0 :=
        hcpu_re.calleeSavedVRegs.trans
          ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)
      wp_conv_pre => simp only [hsp1_in, hpool_eq_0re]
      apply seqCodeLoadedWhere hcl_re
        (mid := allocPl02.base + (reloc_call_off% allocLib02.text.relocs
          "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc" + 4#64))
      apply (SepWP.call_subroutine_frame hrealloc
        (x := (oldPtr, oldCap.toNat, 1, newCap, bs, st))
        hpc_re hrun_re hsp_re hlr_re
        (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
        (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
        (h_oom := fun _ sf_oom _ hm_oom => by
          have hm' := Satisfies.drop_mid hm_oom
          dsimp only [rustBudgetReallocSpec, stringGrowStepEvents] at hm' ⊢
          simp only [hold0, ↓reduceIte]; rw [satisfies_pure_sepConj] at hm' ⊢
          exact ⟨⟨hm'.1.1, oomPreserved_of_allocCall hacp_0re hm'.1.2⟩, hm'.2⟩))
      · intro R' hm'
        dsimp only [rustBudgetReallocSpec]; rw [sepConj_assoc, satisfies_pure_sepConj, hsp_re_eq]
        exact ⟨⟨hx0_re, hx1_re_nat, hx2_re_nat, hx3_re_nat, hlay, hbs_le_old, hbs_le_new⟩,
          Satisfies.mono (by sep_frame) hm'⟩
      · intro sf_re hpc_sfre hrun_sfre hsp_sfre hcs_sfre
        refine SepWP.done hpc_sfre hrun_sfre fun hcl_sfre => ?_
        dsimp only [rustBudgetReallocSpec]; wp_conv_pre => simp only [sepConj_assoc]
        apply SepWP.pure_elim; intro hacp_re
        have hsp_sfre_eq : sf_re.sp = s0.sp - 32#64 := hsp_sfre.trans hsp_re_eq
        have hx19_sfre : sf_re.readReg64 (.gpr 19#5) = BitVec.ofNat 64 newCap := hcs_sfre.readReg64_x19.trans hx19_re
        have hx20_sfre : sf_re.readReg64 (.gpr 20#5) = outPtr := hcs_sfre.readReg64_x20.trans hx20_re
        have hgprs_sfre : BudgetGrowHighGprs s0 sf_re := hgprs_re.trans (BudgetGrowHighGprs.of_calleeSaved hcs_sfre)
        have hvregs_sfre : calleeSavedVRegs sf_re = calleeSavedVRegs s0 := hcs_sfre.vregs.trans hvregs_re
        by_cases hx0_re0 : sf_re.readReg64 .x0 = 0#64
        · wp_conv_pre =>
            simp only [show (0 : BitVec 64) = 0#64 from rfl, hx0_re0, ↓reduceIte, hsp_re_eq, sepConj_assoc]
            rw [sepConj_left_comm (Rust.hookFrame _) ⌜NullAllowed newCap 1⌝,
              sepConj_left_comm (A.pool st sf_re) ⌜NullAllowed newCap 1⌝]
          apply SepWP.pure_elim; intro hnull_re
          refine SepWP.weaken_pre (by
            dsimp only [budgetFinishGrowSavedSlots, vecHeader, fmtBufVecAt]
            simp only [hold0, ↓reduceIte]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_old, hold_lt, holdPtr_ne⟩]; exact Entails.refl _)))))
            sep_entail) <|
            budgetFinishGrow_post_err A hk2 hext2 hcl_sfre (Or.inr hpc_sfre) hrun_sfre hsp0 hsp_sfre_eq
              hx0_re0 hx19_sfre hx20_sfre hgprs_sfre hvregs_sfre
              (allocCallPreserved_trans hacp_0re hacp_re) hnull_re
              fun sf hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩
        · wp_conv_pre => simp only [show (0 : BitVec 64) = 0#64 from rfl, hx0_re0, ↓reduceIte, hsp_re_eq,
            pure_sepConj_of_true (Nat.mod_one (sf_re.readReg64 .x0).toNat), sepConj_assoc]
          refine SepWP.weaken_pre (by
            dsimp only [budgetFinishGrowSavedSlots, vecHeader, fmtBufVecAt, stringGrowStepEvents]
            simp only [hold0, hnew_ne0, ↓reduceIte, hnew_toNat]
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
                (by rw [pure_sepConj_of_true ⟨hbs_le_new, hnew_lt63, hx0_re0⟩]; exact Entails.refl _)))))
            sep_entail) <|
            budgetFinishGrow_post_ok A hk2 hext2 hcl_sfre (Or.inr hpc_sfre) hrun_sfre hsp0 hsp_sfre_eq
              rfl hx0_re0 hx19_sfre hx20_sfre hgprs_sfre hvregs_sfre
              (allocCallPreserved_trans hacp_0re hacp_re) hnew_lt63
              fun sf hsp_f hcs_f {_Pre_f} hent =>
                ⟨fun hm_out => Satisfies.mono (sepConj_mono_left hent) hm_out, hsp_f, hcs_f⟩

end FinishGrowProof

end VerifiedLibraries.RustStd
