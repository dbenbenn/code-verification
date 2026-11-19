/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.AsciiNum
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.Join
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.StringWriterBudget
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteProof
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Placed `core::fmt::write` Contracts and CLI Specializations

Composes `VerifiedLibraries.RustStd.coreFmtWrite_ok` (`coreMultiLib` block `0`) with
`stringBudgetFmtWriterOk` / `budgetWriteStr_fmtWriteStrCall_ok` (`allocMultiLib` blocks `1`, `2`,
`6`, `7` + `allocStringWriteAddrs mplAlloc`) over `toRustAllocBudget M A lim`, discharging every
CLI `core::fmt::write` call shape without adding formatting hooks to `Specifications/`:

- **General placed contracts (`cliCoreFmtWrite_vecU8At_placed_ok`, `cliCoreFmtWrite_string_placed_ok`):**
  parametric in `stackBytes` (tight `0x70 + stringWriterStack = 4352` B) and specialized to
  `extHookStack = 16384` B, returning `(sf.readReg64 .x0).setWidth 32 = 0#32`,
  `AllocCallPreserved s0 sf`, `sf.fs = s0.fs`, `sf.trace = s0.trace`, `Env evs`, exact concatenated
  bytes `vecU8 A.repAlloc v (bs ++ ...)`, and entailing the `.post` of `fmtWriteBudgetEnvSpec`.
- **0-arg literal / empty / `from_str` specializations** (`FmtWriteLitEnv`, `0` callbacks).
- **Single-arg integer `Display::fmt`** (`u8`, `u32`, `u64`, `usize` via `CoreFmt.*_fmtArg_placed_ok`,
  covering `<DeviceId as Display>` and `<KyberPreKeyId as Display>` including `"kyber:"` at
  `cap = 14`, `FmtWriteU8Env`, `FmtWriteU32Env`, `FmtWriteAnyU32Env`).
- **Single-arg `&str` / `String` `Display::fmt` and two-arg `"{}.{}"` `String` + `u8` / `u32`
  composition** (matching `<ProtocolAddress as Display>::fmt`, `FmtWriteAddrEnv`).
- **1- and 2-hop `b`-stub linker-alias corollaries** at `lsFmtWriteSym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open Arm64.Program (HooksUnfetched)
open ProofLib.AsciiNum
  (formatDecimalNat_div_10000 formatDecimalNat_of_1000_lt_10000 formatDecimalNat_of_lt_10
   formatDecimalNat_three_digits formatDecimalNat_two_digits fourDecimalDigits_length)
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustAllocAddrs
   RustCliAllocBudget RustCliAllocBudgetEntriesBase rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (checkBranchStub2 subroutine_ok_of_branchStub subroutine_ok_of_branchStub2
   subroutine_ok_of_branchStub2_wordTree subroutine_ok_of_branchStub_wordTree)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv fmtWriteBudgetEnvSpec)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (CliBufShape PoolMemTransport allocCallPreserved_of_ioCallFrame budgetAllocShim_of_hasInstrs
   budgetMemcpy_all_of_hasWords callBytes callLens cliBufShapeOf
   fmtOpsAbort_str_inv fmtOpsRun_str_inv fmtWriteKnownEvents knownArgOom knownArgPanic
   knownArgStep knownOom_iff lsFmtWriteSym not_appendPanics_of_fits pool_of_setPC
   reaches_fmtWriteEvents_prefix run_known rustBudgetAlloc_of_entriesBase
   rustBudgetRealloc_of_entriesBase stringGrowStepEvents toCliAllocEvent toRustAllocBudget
   toRustAllocBudget_fitsEvents toRustAllocBudget_stepEvents
   vecHeader_fmtBufVecAt_entails_vecU8 vecHeader_fmtBufVecAt_eq_vecU8At
   vecU8At_entails_vecHeader_fmtBufVecAt)
open VerifiedLibraries.Mallocng.Proofs (memcpySymWords)
open VerifiedLibraries.RustStd
  (FmtBuf FmtCall FmtCallbacks FmtInnerBudgetArgsOk FmtOptions FmtReaches FmtRun FmtWriteFrame
   FmtWriterOk IoCallFrame RustAllocBudget StringBufAppendPanics StringBufCharStep
   StringBufStrStep StringBufWriterOom StringBufWriterPanic StringWriteAddrs
   allocBudgetHandleErrorSym allocMultiLib allocRustAllocSym allocRustNoAllocShimSym
   allocRustReallocSym allocStringWriteAddrs allocStringWriteCharSym allocStringWriteStrSym
   budgetAllocShimSpec budgetMemcpySpec budgetWriteStr_fmtWriteStrCall_ok
   checkStrRefDisplayShimBlock checkStringDisplayShimBlock coreFmtDecDigitsLutSym coreFmtMultiLib
   coreFmtWriteSpec coreFmtWriteSym coreFmtWrite_ok coreMultiLib decDigitsLutBytes
   decodeFmtArguments decodeFmtArguments_dotted_pair decodeFmtArguments_single_default
   decodeFmtTemplate defaultFmtOptions defaultFmtOptions_noAlt displayShimTargetSym fmtArgCallSpec fmtArgumentsAt
   fmtBufVecAt fmtInnerBudgetOom fmtInnerBudgetPanic fmtInnerBudgetStep fmtInnerBudgetW
   fmtPadFastOpts_default fmtRef32 fmtRef64 fmtRef8 fmtRefStr fmtRefString fmtSrcBytes
   fmtWriteStrCallSpec padIntegralNoAltOps_default rustBudgetAllocSpec rustBudgetReallocSpec
   strDisplayFmtSpec strDisplayFmt_of_writerOk strRefDisplayFmtSpec strRefDisplayFmtSym
   strRefDisplayFmt_fmtArg_ok strRefDisplayFmt_of_codeLoaded strRefDisplayShim_of_codeLoaded
   stringAppendEvents stringBudgetFmtWriterOk stringDisplayFmtSpec stringDisplayFmt_fmtArg_ok
   stringDisplayShim_of_codeLoaded stringGrowCap stringWriteVtableAt stringWriterKeep
   stringWriterStack subroutine_ok_drop_codeLoadedWhere u32DisplayFmtSym u64DisplayFmtSym
   u8DisplayFmtSym usizeDisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern strDisplayKeep strRefDisplayKeep
   u32DisplayFmt_fmtArg_placed_ok u32DisplayKeep
   u64DisplayFmt_fmtArg_placed_ok u64DisplayKeep u8DisplayFmt_fmtArg_placed_ok
   u8DisplayKeep usizeDisplayFmt_fmtArg_placed_ok)

/-! ## Linkage Bundle & Writer Helpers -/

theorem allocStringWriteAddrs_writeStr_eq_resolve (mpl : MultiPlacement) :
    (allocStringWriteAddrs mpl).writeStr = allocMultiLib.resolve mpl allocStringWriteStrSym := by
  have h : lookupBlockSym allocStringWriteStrSym allocMultiLib.blocks = some (7, 0) := by decide
  simp [allocStringWriteAddrs, MultiPlacedLib.resolve, h]

theorem allocStringWriteAddrs_writeChar_eq_resolve (mpl : MultiPlacement) :
    (allocStringWriteAddrs mpl).writeChar = allocMultiLib.resolve mpl allocStringWriteCharSym := by
  have h : lookupBlockSym allocStringWriteCharSym allocMultiLib.blocks = some (6, 0) := by decide
  simp [allocStringWriteAddrs, MultiPlacedLib.resolve, h]

theorem stringWriteVtableAt_dup_writeStr (va : StringWriteAddrs) :
    stringWriteVtableAt va = ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va := by
  unfold stringWriteVtableAt
  conv => rhs; rw [← sepConj_assoc, pointsTo64RO_dup]

theorem fmtInnerBudgetW_split_R (B : RustAllocBudget) (st0 : B.σ) (va : StringWriteAddrs)
    (F R : SepProp) (t0 : State) (out : BitVec 64) (st : FmtBuf) (s : State) :
    fmtInnerBudgetW B st0 va (F ∗ R) t0 out st s =
      F ∗ fmtInnerBudgetW B st0 va R t0 out st s := by
  dsimp only [fmtInnerBudgetW]
  sep_ac_rfl

private theorem fmtInnerBudgetW_transport_local (B : RustAllocBudget) (st0 : B.σ)
    (va : StringWriteAddrs) (R : SepProp) (t0 : State) (out : BitVec 64) (st : FmtBuf)
    (s s' : State) (hf : FmtWriteFrame s s') :
    fmtInnerBudgetW B st0 va R t0 out st s ⊢ fmtInnerBudgetW B st0 va R t0 out st s' := by
  dsimp only [fmtInnerBudgetW]
  rw [B.pool_of_fmtWriteFrame _ hf]
  refine Entails.pure_left fun ⟨hio, hfs, htr⟩ => ?_
  have hio' : IoCallFrame t0 s' :=
    ⟨hf.2.2.1.trans hio.1, hf.2.2.2.1.trans hio.2.1, hf.2.2.2.2.2.1.trans hio.2.2.1,
     hf.2.2.2.2.2.2.2.1.trans hio.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1.trans hio.2.2.2.2⟩
  exact Entails.pure_right ⟨hio', hf.2.1.trans hfs, hf.1.trans htr⟩ (Entails.refl _)

private theorem subroutine_ok_of_multiCodeLoaded {α : Type} {lib : MultiPlacedLib}
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

private theorem subroutine_ok_of_withCodeLoadedWhere {α : Type} {lib : MultiPlacedLib}
    {keep : Nat → Bool} {mpl : MultiPlacement} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (hcl : ∀ m, P.CodeLoaded m → lib.CodeLoadedWhere keep mpl m)
    (hok : subroutine_ok P addr (lib.withCodeLoadedWhere keep mpl spec)) :
    subroutine_ok P addr spec :=
  subroutine_ok_drop_codeLoadedWhere hcl hok

/-- Placement and callee-discharge bundle for placed `core::fmt::write` (`coreMultiLib` block `0`)
    and `<String as fmt::Write>::{write_str, write_char}` (`allocMultiLib` blocks `1`, `2`, `6`,
    `7`) over `toRustAllocBudget M A lim`. -/
structure CliFmtWriteLink (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (P : Program)
    (mplCore mplAlloc : MultiPlacement) : Prop where
  plCore : coreMultiLib.Placeable mplCore
  clCore : ∀ m, P.CodeLoaded m → coreMultiLib.CodeLoaded mplCore m
  noExtCore0 : ∀ off : Nat, off < 436 → P.externAt? (mplCore.base 0 + BitVec.ofNat 64 off) = none
  plAlloc : allocMultiLib.Placeable mplAlloc
  clAllocWriter : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoadedWhere stringWriterKeep mplAlloc m
  noExtAlloc1 : LibBlockNoExtern allocMultiLib mplAlloc P 1
  noExtAlloc2 : LibBlockNoExtern allocMultiLib mplAlloc P 2
  noExtAlloc6 : LibBlockNoExtern allocMultiLib mplAlloc P 6
  noExtAlloc7 : LibBlockNoExtern allocMultiLib mplAlloc P 7
  panicHandleErr :
    P.externAt? (allocMultiLib.resolve mplAlloc allocBudgetHandleErrorSym) = some Rust.panicked
  memcpyAll : ∀ ro, subroutine_ok P (allocMultiLib.resolve mplAlloc "memcpy") (budgetMemcpySpec ro)
  allocShim : subroutine_ok P (allocMultiLib.resolve mplAlloc allocRustNoAllocShimSym)
    budgetAllocShimSpec
  rustAlloc : subroutine_ok P (allocMultiLib.resolve mplAlloc allocRustAllocSym)
    (rustBudgetAllocSpec (toRustAllocBudget M A lim))
  rustRealloc : subroutine_ok P (allocMultiLib.resolve mplAlloc allocRustReallocSym)
    (rustBudgetReallocSpec (toRustAllocBudget M A lim))

/-- Construct `CliFmtWriteLink` directly from `RustCliAllocBudgetEntriesBase`, `memcpySymWords`, and
    a 1-instruction `ret` `__rust_no_alloc_shim_is_unstable_v2` stub. -/
theorem CliFmtWriteLink.of_entriesBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] (lim : BudgetLimits) {P : Program} {mplCore mplAlloc : MultiPlacement}
    {addrs : RustAllocAddrs}
    (hplCore : coreMultiLib.Placeable mplCore)
    (hclCore : ∀ m, P.CodeLoaded m → coreMultiLib.CodeLoaded mplCore m)
    (hnoExtCore0 : ∀ off : Nat, off < 436 →
      P.externAt? (mplCore.base 0 + BitVec.ofNat 64 off) = none)
    (hplAlloc : allocMultiLib.Placeable mplAlloc)
    (hclAlloc : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoadedWhere stringWriterKeep mplAlloc m)
    (hnoExt1 : LibBlockNoExtern allocMultiLib mplAlloc P 1)
    (hnoExt2 : LibBlockNoExtern allocMultiLib mplAlloc P 2)
    (hnoExt6 : LibBlockNoExtern allocMultiLib mplAlloc P 6)
    (hnoExt7 : LibBlockNoExtern allocMultiLib mplAlloc P 7)
    (hpanic : P.externAt? (allocMultiLib.resolve mplAlloc allocBudgetHandleErrorSym) =
      some Rust.panicked)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (hmemcpyWords : P.hasWords (allocMultiLib.resolve mplAlloc "memcpy") memcpySymWords)
    (hshimInstr : hasInstrs P (allocMultiLib.resolve mplAlloc allocRustNoAllocShimSym) [.ret .x30])
    (hAllocEq : allocMultiLib.resolve mplAlloc allocRustAllocSym = addrs.alloc)
    (hReallocEq : allocMultiLib.resolve mplAlloc allocRustReallocSym = addrs.realloc)
    (hEntries : RustCliAllocBudgetEntriesBase M A P addrs) :
    CliFmtWriteLink M A lim P mplCore mplAlloc where
  plCore := hplCore
  clCore := hclCore
  noExtCore0 := hnoExtCore0
  plAlloc := hplAlloc
  clAllocWriter := hclAlloc
  noExtAlloc1 := hnoExt1
  noExtAlloc2 := hnoExt2
  noExtAlloc6 := hnoExt6
  noExtAlloc7 := hnoExt7
  panicHandleErr := hpanic
  memcpyAll := budgetMemcpy_all_of_hasWords P _ hsvc hhooks hmemcpyWords
  allocShim := budgetAllocShim_of_hasInstrs hshimInstr
  rustAlloc := hAllocEq ▸ rustBudgetAlloc_of_entriesBase lim hEntries
  rustRealloc := hReallocEq ▸ rustBudgetRealloc_of_entriesBase lim hEntries

/-- Assemble `FmtWriterOk` over `fmtInnerBudgetW (toRustAllocBudget M A lim)` from `CliFmtWriteLink`. -/
theorem cliStringBudgetFmtWriterOk {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (st0 : M.σ) (R : SepProp) (t0 : State) (stackBytes : Nat) (out : BitVec 64)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    FmtWriterOk P
      (fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc) R t0 out)
      StringBufStrStep StringBufCharStep
      (StringBufWriterPanic t0) (StringBufWriterOom (toRustAllocBudget M A lim) st0)
      stackBytes out (allocStringWriteAddrs mplAlloc).vtable
      (allocStringWriteAddrs mplAlloc).writeStr
      (allocStringWriteAddrs mplAlloc).writeChar :=
  stringBudgetFmtWriterOk (toRustAllocBudget M A lim)
    (keep := stringWriterKeep) (by decide) (by decide) (by decide) (by decide)
    L.plAlloc L.clAllocWriter st0 (allocStringWriteAddrs mplAlloc) R t0 stackBytes out
    (allocStringWriteAddrs_writeStr_eq_resolve mplAlloc)
    (allocStringWriteAddrs_writeChar_eq_resolve mplAlloc)
    L.noExtAlloc6 L.noExtAlloc7 L.noExtAlloc1 L.noExtAlloc2 hstk
    L.panicHandleErr L.memcpyAll L.allocShim L.rustAlloc L.rustRealloc

/-- Placed `fmtWriteStrCallSpec` for `<String as fmt::Write>::write_str` from `CliFmtWriteLink`. -/
theorem cliStringBudgetWriteStrCall_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (st0 : M.σ) (R : SepProp)
    (ArgStep : FmtCall → FmtBuf → Bool → FmtBuf → Prop)
    (ArgPanic ArgOom : FmtCall → FmtBuf → State → Prop)
    (t0 : State) (stackBytes : Nat) (out ptr : BitVec 64) (sbs : List (BitVec 8))
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    subroutine_ok P (allocStringWriteAddrs mplAlloc).writeStr
      (fmtWriteStrCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc) R t0 out)
        (fmtInnerBudgetStep ArgStep) (fmtInnerBudgetPanic t0 ArgPanic)
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0 ArgOom)
        stackBytes out ptr sbs) := by
  rw [allocStringWriteAddrs_writeStr_eq_resolve mplAlloc]
  exact subroutine_ok_of_withCodeLoadedWhere L.clAllocWriter
    (budgetWriteStr_fmtWriteStrCall_ok (toRustAllocBudget M A lim)
      (keep := stringWriterKeep) (by decide) (by decide) (by decide)
      L.plAlloc st0 (allocStringWriteAddrs mplAlloc) R ArgStep ArgPanic ArgOom t0 stackBytes
      out ptr sbs L.noExtAlloc7 L.noExtAlloc1 L.noExtAlloc2 hstk
      L.panicHandleErr (L.memcpyAll true) L.allocShim L.rustAlloc L.rustRealloc)

/-! ## Headline Placed `core::fmt::write` Specifications & Proofs -/

/-- Tight-stack placed contract for `core::fmt::write` on an explicit `vecU8At` `String` header
    `(v, cap0, ptr0, bs)` (`0x70 + stackBytes` stack, with `stringWriterStack ≤ stackBytes`). -/
@[expose] def cliCoreFmtWriteVecAtSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argBytes : Nat → List (BitVec 8))
    (stackBytes : Nat) (P : Program) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Bool × List (BitVec 8) ×
      List (BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (v, cap0, ptr0, bs, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = va.vtable ∧
      stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64 ∧
      FitsEnv M lim st0 Env ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x2) (s.readReg64 .x3) tpl args = some cs ∧
        Env (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)) ∧
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (knownArgStep argBytes) (knownArgPanic argBytes)
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s cs⌝ ∗
      vecU8At A.repAlloc v cap0 ptr0 bs ∗
      fmtArgumentsAt argsRo (s.readReg64 .x2) (s.readReg64 .x3) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
  post := fun (v, cap0, _, bs, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs' : List (BitVec 8),
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
        sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
          evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
          bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
      vecU8 A.repAlloc v bs' ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes)

/-- `extHookStack`-framed placed contract for `core::fmt::write` on an existential `vecU8` `String`
    (`16384` B stack, matching `fmtWriteBudgetEnvSpec` plus preserved `fmtArgumentsAt`,
    `stringWriteVtableAt`, and `R_client`). -/
@[expose] def cliCoreFmtWriteSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argBytes : Nat → List (BitVec 8))
    (stackBytes : Nat) (P : Program) :
    Spec (BitVec 64 × List (BitVec 8) × Bool × List (BitVec 8) ×
      List (BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (v, bs, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = va.vtable ∧
      stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ extHookStack ∧
      FitsEnv M lim st0 Env ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x2) (s.readReg64 .x3) tpl args = some cs ∧
        (∀ cap : BitVec 64, bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 →
          Env (fmtWriteKnownEvents bs.length cap (callLens argBytes cs))) ∧
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (knownArgStep argBytes) (knownArgPanic argBytes)
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s cs⌝ ∗
      vecU8 A.repAlloc v bs ∗
      fmtArgumentsAt argsRo (s.readReg64 .x2) (s.readReg64 .x3) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim st0 s ∗ stackAt s.sp extHookStack
  post := fun (v, bs, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs' : List (BitVec 8),
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
        sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
          bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
      vecU8 A.repAlloc v bs' ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack

/-- The normal-return postcondition of `cliCoreFmtWriteSpec` directly entails the postcondition of
    `fmtWriteBudgetEnvSpec M A lim Env` (plus preserved `fmtArgumentsAt`, `stringWriteVtableAt`,
    and `R_client`, and `AllocCallPreserved s0 sf`). -/
theorem cliCoreFmtWriteSpec_post_entails_budgetEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argBytes : Nat → List (BitVec 8))
    (stackBytes : Nat) (P : Program)
    (v : BitVec 64) (bs : List (BitVec 8)) (argsRo : Bool) (tpl : List (BitVec 8))
    (args : List (BitVec 64 × BitVec 64)) (st0 : M.σ) (s0 sf : State) :
    (cliCoreFmtWriteSpec M A lim Env va R_client argBytes stackBytes P).post
      (v, bs, argsRo, tpl, args, st0) s0 sf ⊢
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      (fmtWriteBudgetEnvSpec M A lim Env).post (v, bs, st0) s0 sf ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
      stringWriteVtableAt va ∗ R_client := by
  dsimp only [cliCoreFmtWriteSpec, fmtWriteBudgetEnvSpec]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_elim fun bs' => ?_
  refine Entails.pure_left fun ⟨hw0, hacp, hfs, htr, hEnv, _⟩ => ?_
  refine Entails.pure_right ⟨hacp, hfs⟩ ?_
  have hex : vecU8 A.repAlloc v bs' ⊢ ∃∗ b : List (BitVec 8), vecU8 A.repAlloc v b :=
    Entails.sepExists_right bs' (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hex) ?_
  have hinner :
      (∃∗ b : List (BitVec 8), vecU8 A.repAlloc v b) ∗
        (fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
          (stringWriteVtableAt va ∗ (R_client ∗
            (A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack)))) ⊢
      (⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
        (∃∗ b : List (BitVec 8), vecU8 A.repAlloc v b) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
        stringWriteVtableAt va ∗ R_client := by
    rw [pure_sepConj_of_true ⟨hw0, htr, hEnv⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans hinner ?_
  exact sepConj_mono_left (Entails.sepExists_right evs (Entails.refl _))

/-- Placed correctness of `core::fmt::write` (`coreMultiLib` block `0`) composed with
    `<String as fmt::Write>` (`allocMultiLib` blocks `1`, `2`, `6`, `7`) on an explicit `vecU8At`
    `String` header `(v, cap0, ptr0, bs)`. -/
theorem cliCoreFmtWrite_vecU8At_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc) :
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      (cliCoreFmtWriteVecAtSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) := by
  let B := toRustAllocBudget M A lim
  let va := allocStringWriteAddrs mplAlloc
  apply subroutine_ok.of_codeLoaded
  rintro ⟨v, cap0, ptr0, bs, argsRo, tpl, args, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  dsimp only [cliCoreFmtWriteVecAtSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = va.vtable ∧
        stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64 ∧
        FitsEnv M lim st0 Env ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
          Env (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)) ∧
          FmtInnerBudgetArgsOk P B st0 va R_client
            (knownArgStep argBytes) (knownArgPanic argBytes)
            (knownArgOom B st0 argBytes) stackBytes s0 cs⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
          stringWriteVtableAt va ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0, hx1, hstk1, hstk2, hFitEnv, cs, hdec, hEnvCs, hArgsOk⟩, hm0⟩
  let stInit : FmtBuf := { bytes := bs, cap := cap0, ptr := ptr0, evs := [] }
  have hcb :
      FmtCallbacks P (fmtInnerBudgetW B st0 va R_client s0 v)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic s0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
        stackBytes v va.vtable va.writeStr cs :=
    { transport := fun st s s' hf =>
        fmtInnerBudgetW_transport_local B st0 va R_client s0 v st s s' hf
      write_str := fun ptr sbs _ =>
        cliStringBudgetWriteStrCall_ok L st0 R_client
          (knownArgStep argBytes) (knownArgPanic argBytes) (knownArgOom B st0 argBytes)
          s0 stackBytes v ptr sbs ⟨hstk1, by omega⟩
      fmt_arg := fun idx val fn opts hmem => hArgsOk idx val fn opts hmem v }
  have hcore := subroutine_ok_of_multiCodeLoaded L.clCore
    (coreFmtWrite_ok L.plCore L.noExtCore0
      (fmtInnerBudgetW B st0 va R_client s0 v)
      (fmtInnerBudgetStep (knownArgStep argBytes))
      (fmtInnerBudgetPanic s0 (knownArgPanic argBytes))
      (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
      stackBytes)
  have hpreCore :
      s0.mem ⊨
        (coreFmtWriteSpec P (fmtInnerBudgetW B st0 va R_client s0 v)
          (fmtInnerBudgetStep (knownArgStep argBytes))
          (fmtInnerBudgetPanic s0 (knownArgPanic argBytes))
          (fmtInnerBudgetOom B st0 (knownArgOom B st0 argBytes))
          stackBytes).pre (v, va.vtable, va.writeStr, argsRo, tpl, args, stInit) s0 ∗ R₀ := by
    dsimp only [coreFmtWriteSpec, fmtInnerBudgetW, stInit]
    have hio0 : IoCallFrame s0 s0 ∧ s0.fs = s0.fs ∧ s0.trace = s0.trace :=
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk2, cs, hdec, hcb⟩, pure_sepConj_of_true hio0]
    rw [← vecHeader_fmtBufVecAt_eq_vecU8At M A lim v cap0 ptr0 bs,
      stringWriteVtableAt_dup_writeStr va] at hm0
    refine Satisfies.mono ?_ hm0
    exact Entails.of_eq (by dsimp only [B, va, toRustAllocBudget, RustAllocBudget.stepEvents]; sep_ac_rfl)
  refine hcore.mono_outcome (v, va.vtable, va.writeStr, argsRo, tpl, args, stInit)
    R₀ s0 hpc hrun hpreCore hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨_ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [coreFmtWriteSpec] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨ok, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨st', hpost⟩
    have hpost1 :
        sf.mem ⊨ ⌜(sf.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
          ∃ cs', decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs' ∧
            FmtRun (fmtInnerBudgetStep (knownArgStep argBytes)) cs' stInit ok st'⌝ ∗
          ((((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
            fmtInnerBudgetW B st0 va R_client s0 v st' sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hw0, cs', hdec', hrun'⟩, hmf⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    obtain ⟨hok, hsh, hby⟩ := run_known hrun'
    subst hok
    have hw0_eq : (sf.readReg64 .x0).setWidth 32 = 0#32 := by
      simpa [State.readReg32, State.readReg64] using hw0
    have hevsEq :
        st'.evs.map toCliAllocEvent = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) := by
      have hev := congrArg CliBufShape.evs hsh
      simpa [cliBufShapeOf, stInit, fmtWriteKnownEvents] using hev
    dsimp only [fmtInnerBudgetW] at hmf
    have hmf1 :
        sf.mem ⊨ ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗
          (((((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ stringWriteVtableAt va) ∗
            (Arm64.Rust.vecHeader v st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
              fmtBufVecAt B st'.cap st'.ptr st'.bytes) ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
            R_client ∗ B.pool (B.stepEvents st'.evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
    rw [satisfies_pure_sepConj] at hmf1
    rcases hmf1 with ⟨⟨hio, hfs, htr⟩, hmf2⟩
    rw [← stringWriteVtableAt_dup_writeStr va] at hmf2
    have hpoolEq :
        B.pool (B.stepEvents st'.evs st0) sf =
          A.pool lim (M.stepEvents (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)) st0) sf := by
      dsimp only [B]
      rw [toRustAllocBudget_stepEvents M A lim st'.evs st0, hevsEq]
      rfl
    rw [hpoolEq] at hmf2
    dsimp only [cliCoreFmtWriteVecAtSpec]
    refine Satisfies.mono (sepConj_mono_left ?_) hmf2
    refine Entails.trans
      (Entails.of_eq (show _ =
        (Arm64.Rust.vecHeader v st'.cap st'.ptr (BitVec.ofNat 64 st'.bytes.length) ∗
          fmtBufVecAt B st'.cap st'.ptr st'.bytes) ∗
          (fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
            stringWriteVtableAt va ∗ R_client ∗
            A.pool lim (M.stepEvents (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)) st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) by sep_ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_left (vecHeader_fmtBufVecAt_entails_vecU8 M A lim v st'.cap st'.ptr st'.bytes)) ?_
    let evsOut := fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)
    refine Entails.sepExists_right evsOut (Entails.sepExists_right st'.bytes ?_)
    rw [pure_sepConj_of_true ⟨hw0_eq, allocCallPreserved_of_ioCallFrame hio hfs htr,
      hfs, htr, hEnvCs, cs, hdec, rfl, hby⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  · exfalso
    dsimp only [coreFmtWriteSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan.1 with ⟨cs', c, st, hdec', hreach, hpanC⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    obtain ⟨suf, hsuf⟩ := reaches_fmtWriteEvents_prefix (st₀ := stInit) rfl hreach
    have hall := hFitEnv _ hEnvCs
    rw [hsuf, LibsignalBinary.Heap.fitsEvents_append] at hall
    have hfitAppend : B.FitsEvents st0 (stringAppendEvents st (callBytes argBytes c).length) :=
      (toRustAllocBudget_fitsEvents M A lim st0 _).mpr hall.1
    have hnoPan := not_appendPanics_of_fits B hfitAppend
    cases c with
    | writeStr _ _ => exact hnoPan hpanC.2.2
    | fmtArg _ _ _ _ => exact hnoPan hpanC
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [coreFmtWriteSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    rcases hoom.1 with ⟨cs', c, st, hdec', hreach, hoomC⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    obtain ⟨suf, hsuf⟩ := reaches_fmtWriteEvents_prefix (st₀ := stInit) rfl hreach
    have hall := hFitEnv _ hEnvCs
    rw [hsuf, LibsignalBinary.Heap.fitsEvents_append] at hall
    have hfitAppend : B.FitsEvents st0 (stringAppendEvents st (callBytes argBytes c).length) :=
      (toRustAllocBudget_fitsEvents M A lim st0 _).mpr hall.1
    exact ((knownOom_iff B st0 argBytes c st sf).mp hoomC) hfitAppend

/-- Headline `extHookStack`-framed placed correctness of `core::fmt::write` on an existential
    `vecU8 A.repAlloc v bs` `String`. -/
theorem cliCoreFmtWrite_string_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc) :
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      (cliCoreFmtWriteSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) := by
  let va := allocStringWriteAddrs mplAlloc
  have hvecAt := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  apply subroutine_ok.of_codeLoaded
  rintro ⟨v, bs, argsRo, tpl, args, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  dsimp only [cliCoreFmtWriteSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = va.vtable ∧
        stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ extHookStack ∧
        FitsEnv M lim st0 Env ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs ∧
          (∀ cap : BitVec 64, bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 →
            Env (fmtWriteKnownEvents bs.length cap (callLens argBytes cs))) ∧
          FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
            (knownArgStep argBytes) (knownArgPanic argBytes)
            (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs⌝ ∗
        (vecU8 A.repAlloc v bs ∗
          (fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
            stringWriteVtableAt va ∗ R_client ∗
            A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack ∗ R₀)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0, hx1, hstk1, hstkExt, hFitEnv, cs, hdec, hEnvAll, hArgsOk⟩, hm0⟩
  unfold vecU8 at hm0
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm0
  rcases hm0 with ⟨cap0, hm0⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm0
  rcases hm0 with ⟨ptr0, hm0⟩
  have hinv_extract :
      vecU8At A.repAlloc v cap0 ptr0 bs ⊢
        ⌜bs.length ≤ cap0.toNat ∧ cap0.toNat < 2 ^ 63⌝ ∗ vecU8At A.repAlloc v cap0 ptr0 bs := by
    refine Entails.trans (vecU8At_entails_vecHeader_fmtBufVecAt M A lim v cap0 ptr0 bs) ?_
    refine Entails.pure_left fun ⟨h1, h2, _⟩ => Entails.pure_right ⟨h1, h2⟩ ?_
    rw [vecHeader_fmtBufVecAt_eq_vecU8At M A lim v cap0 ptr0 bs]
    exact Entails.refl _
  have hm0' := Satisfies.mono (sepConj_mono_left hinv_extract) hm0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm0'
  rcases hm0' with ⟨⟨hlen_le, hcap_lt⟩, hm0''⟩
  have hEnvCs : Env (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs)) :=
    hEnvAll cap0 hlen_le hcap_lt
  let remStack : Nat := extHookStack - (0x70 + stackBytes)
  have hstkSplit :
      stackAt s0.sp extHookStack =
        stackFrameAt s0.sp (0x70 + stackBytes) ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 (0x70 + stackBytes)) remStack := by
    rw [stackAt_eq_stackFrameAt s0.sp extHookStack (by decide)]
    conv => lhs; rw [show extHookStack = (0x70 + stackBytes) + remStack by dsimp [remStack, extHookStack] at *; omega]
    exact stackFrameAt_split s0.sp (0x70 + stackBytes) remStack (by dsimp [remStack, extHookStack] at *; omega)
  let R_frame := stackFrameAt (s0.sp - BitVec.ofNat 64 (0x70 + stackBytes)) remStack ∗ R₀
  have hpreVec :
      s0.mem ⊨
        (cliCoreFmtWriteVecAtSpec M A lim Env va R_client argBytes stackBytes P).pre
          (v, cap0, ptr0, bs, argsRo, tpl, args, st0) s0 ∗ R_frame := by
    dsimp only [cliCoreFmtWriteVecAtSpec, R_frame]
    rw [hstkSplit] at hm0''
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk1, by dsimp [extHookStack] at hstkExt; omega,
      hFitEnv, cs, hdec, hEnvCs, hArgsOk⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0''
  refine hvecAt.mono_outcome (v, cap0, ptr0, bs, argsRo, tpl, args, st0)
    R_frame s0 hpc hrun hpreVec hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliCoreFmtWriteVecAtSpec, R_frame] at hpost
    dsimp only [cliCoreFmtWriteSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hpost1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs', decodeFmtArguments (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args = some cs' ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs') ∧
            bs' = bs ++ cs'.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x2) (s0.readReg64 .x3) tpl args ∗
            stringWriteVtableAt va ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            (stackFrameAt s0.sp (0x70 + stackBytes) ∗
              stackFrameAt (s0.sp - BitVec.ofNat 64 (0x70 + stackBytes)) remStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hw0, hacp, hfs, htr, hEnv, cs', hdec', _, hbs'⟩, hmf⟩
    rw [← hstkSplit] at hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs (Entails.sepExists_right bs' ?_)
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnv, cs', hdec', hbs'⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact hpan.1.elim
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-! ## Concrete CLI Specializations -/

/-! ### 1. 0-Argument Static Literal, Empty, and `from_str` Templates -/

/-- Exact allocation-event envelope of appending a single slice of length `addLen` onto a `String`
    of capacity `cap0` and length `len0`. -/
@[expose] def FmtWriteLitEnv (cap0 len0 addLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = if len0 + addLen ≤ cap0 then []
        else stringGrowStepEvents cap0 (stringGrowCap cap0 len0 addLen)

theorem fmtWriteKnownEvents_nil (len0 : Nat) (cap0 : BitVec 64) :
    fmtWriteKnownEvents len0 cap0 [] = [] :=
  rfl

theorem fmtWriteKnownEvents_singleton (len0 : Nat) (cap0 : BitVec 64) (addLen : Nat) :
    fmtWriteKnownEvents len0 cap0 [addLen] =
      if len0 + addLen ≤ cap0.toNat then []
      else stringGrowStepEvents cap0.toNat (stringGrowCap cap0.toNat len0 addLen) := by
  unfold fmtWriteKnownEvents CliBufShape.run List.foldl CliBufShape.append
  split <;> simp

theorem fmtWriteLitEnv_knownEvents (len0 : Nat) (cap0 : BitVec 64) (addLen : Nat) :
    FmtWriteLitEnv cap0.toNat len0 addLen (fmtWriteKnownEvents len0 cap0 [addLen]) :=
  fmtWriteKnownEvents_singleton len0 cap0 addLen

theorem decodeFmtArguments_empty (x2 : BitVec 64) :
    decodeFmtArguments x2 0#64 [0x00#8] [] = some [] :=
  rfl

theorem decodeFmtArguments_shortLiteral (x2 : BitVec 64) {litBs : List (BitVec 8)}
    (hlo : 1 ≤ litBs.length) (hhi : litBs.length ≤ 127) :
    decodeFmtArguments x2 0#64 ([BitVec.ofNat 8 litBs.length] ++ litBs ++ [0x00#8]) [] =
      some [FmtCall.writeStr (x2 + 1#64) litBs] := by
  have h0_even : (0#64 : BitVec 64).getLsbD 0 = false := by decide
  have hn0 : BitVec.ofNat 8 litBs.length ≠ 0#8 := by
    intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ht
    rw [Nat.mod_eq_of_lt (by omega)] at ht
    omega
  have hlt80 : litBs.length < 0x80 := by omega
  have hto : (BitVec.ofNat 8 litBs.length).toNat = litBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_rest : ¬ (litBs ++ [0x00#8]).length < litBs.length := by simp
  have htake : (litBs ++ [0x00#8]).take litBs.length = litBs := by simp
  have hdrop : (litBs ++ [0x00#8]).drop litBs.length = [0x00#8] := by simp
  simp only [decodeFmtArguments, h0_even, Bool.false_eq_true, ↓reduceIte,
    List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil,
    Nat.zero_add]
  unfold decodeFmtTemplate
  simp only [hn0, ↓reduceIte, hto, hlt80, hlen_rest, hdrop, htake]
  unfold decodeFmtTemplate
  simp

theorem decodeFmtArguments_fromStr (x2 x3 : BitVec 64) (litBs : List (BitVec 8))
    (hodd : x3.getLsbD 0 = true) (hlen : litBs.length = (x3 >>> 1).toNat) :
    decodeFmtArguments x2 x3 litBs [] = some [FmtCall.writeStr x2 litBs] := by
  simp [decodeFmtArguments, hodd, hlen]

/-- Empty-template (`tpl = [0x00#8]`, `args = []`) `core::fmt::write` specialization: `0` callbacks,
    `0` allocations (`FmtWriteEnv`), tight stack `0x70 + stringWriterStack = 4352` B. -/
theorem cliCoreFmtWrite_empty_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {R_client : SepProp}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (v cap0 ptr0 x2 : BitVec 64) (bs : List (BitVec 8)) (argsRo : Bool) (st0 : M.σ) :
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = 0#64 ∧ FitsEnv M lim st0 FmtWriteEnv⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 0#64 [0x00#8] [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stringWriterStack)
        post := fun () s0 sf =>
          ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
            sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗
          vecU8 A.repAlloc v bs ∗
          fmtArgumentsAt argsRo x2 0#64 [0x00#8] [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 sf ∗ stackFrameAt s0.sp (0x70 + stringWriterStack) } := by
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := FmtWriteEnv) (R_client := R_client)
    (argBytes := fun _ => []) (stackBytes := stringWriterStack) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = 0#64 ∧ FitsEnv M lim st0 FmtWriteEnv⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 0#64 [0x00#8] [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stringWriterStack)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  refine ⟨(v, cap0, ptr0, bs, argsRo, [0x00#8], [], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep fun _ => [])
        (knownArgPanic fun _ => [])
        (knownArgOom (toRustAllocBudget M A lim) st0 fun _ => []) stringWriterStack s0 [] :=
      fun _ _ _ _ hmem => False.elim (List.not_mem_nil hmem)
    rw [pure_sepConj_of_true ⟨hx0, hx1, Nat.le_refl _, by decide, hFit,
      [], decodeFmtArguments_empty x2, rfl, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ FmtWriteEnv evs ∧
          ∃ cs, decodeFmtArguments x2 0#64 [0x00#8] [] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens (fun _ => []) cs) ∧
            bs' = bs ++ cs.flatMap (callBytes fun _ => [])⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 0#64 [0x00#8] [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stringWriterStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, _, cs, hdec, hevs, hbs'⟩, hmf⟩
    have hcs : cs = [] := Option.some.inj (hdec.symm.trans (decodeFmtArguments_empty x2))
    subst hcs
    simp only [callLens, List.map_nil, fmtWriteKnownEvents_nil, List.flatMap_nil,
      List.append_nil] at hevs hbs'
    subst hevs hbs'
    simp only [AllocCostModel.stepEvents_nil] at hmf
    dsimp only
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- 0-argument single-literal `core::fmt::write` specialization (`decodeFmtArguments x2 x3 tpl [] =
    some [.writeStr litPtr litBs]`, covering both static bytecode literals and `Arguments::from_str`),
    with explicit `FmtWriteLitEnv cap0.toNat bs.length litBs.length` and `0` callbacks. -/
theorem cliCoreFmtWrite_lit0_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (v cap0 ptr0 x2 x3 litPtr : BitVec 64) (bs tpl litBs : List (BitVec 8))
    (argsRo : Bool) (st0 : M.σ)
    (hdec : decodeFmtArguments x2 x3 tpl [] = some [FmtCall.writeStr litPtr litBs])
    (hEnv : FmtWriteLitEnv cap0.toNat bs.length litBs.length
      (fmtWriteKnownEvents bs.length cap0 [litBs.length]) →
      Env (fmtWriteKnownEvents bs.length cap0 [litBs.length]))
    (hstk : stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 tpl [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteLitEnv cap0.toNat bs.length litBs.length evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ litBs) ∗
            fmtArgumentsAt argsRo x2 x3 tpl [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := fun _ => []) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 tpl [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  refine ⟨(v, cap0, ptr0, bs, argsRo, tpl, [], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep fun _ => [])
        (knownArgPanic fun _ => [])
        (knownArgOom (toRustAllocBudget M A lim) st0 fun _ => []) stackBytes s0
        [FmtCall.writeStr litPtr litBs] := by
      intro _ _ _ _ hmem
      simp at hmem
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0
        (callLens (fun _ => []) [FmtCall.writeStr litPtr litBs])) :=
      hEnv (fmtWriteLitEnv_knownEvents bs.length cap0 litBs.length)
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk.1, hstk.2, hFit,
      [FmtCall.writeStr litPtr litBs], hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 tpl [] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens (fun _ => []) cs) ∧
            bs' = bs ++ cs.flatMap (callBytes fun _ => [])⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 tpl [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = [FmtCall.writeStr litPtr litBs] := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [callLens, List.map_cons, List.map_nil, callBytes, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hevs hbs'
    subst hbs'
    have hLit : FmtWriteLitEnv cap0.toNat bs.length litBs.length evs := by
      rw [hevs]; exact fmtWriteLitEnv_knownEvents bs.length cap0 litBs.length
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hLit⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 2. Single-Argument Integer `Display::fmt` (`u8`, `u32`, `u64`, `usize`) -/

/-- Decimal digit length bounds for `u8` (`1 ≤ len ≤ 3`). -/
theorem formatDecimalNat_u8_length (v : BitVec 8) :
    1 ≤ (formatDecimalNat v.toNat).length ∧ (formatDecimalNat v.toNat).length ≤ 3 := by
  have hv : v.toNat < 256 := v.isLt
  by_cases h10 : v.toNat < 10
  · rw [formatDecimalNat_of_lt_10 h10]; simp
  · by_cases h100 : v.toNat < 100
    · rw [formatDecimalNat_two_digits (by omega) h100]; simp
    · rw [formatDecimalNat_three_digits (by omega) (by omega)]; simp

/-- Decimal digit length bounds for `u32` (`1 ≤ len ≤ 10`). -/
theorem formatDecimalNat_u32_length (v : BitVec 32) :
    1 ≤ (formatDecimalNat v.toNat).length ∧ (formatDecimalNat v.toNat).length ≤ 10 := by
  have hv : v.toNat < 4294967296 := v.isLt
  have hlt10k : ∀ {m : Nat}, m < 10000 →
      1 ≤ (formatDecimalNat m).length ∧ (formatDecimalNat m).length ≤ 4 := by
    intro m hm
    by_cases h1 : m < 10
    · rw [formatDecimalNat_of_lt_10 h1]; simp
    · by_cases h2 : m < 100
      · rw [formatDecimalNat_two_digits (by omega) h2]; simp
      · by_cases h3 : m < 1000
        · rw [formatDecimalNat_three_digits (by omega) h3]; simp
        · rw [formatDecimalNat_of_1000_lt_10000 (by omega) hm]; simp
  by_cases h1 : v.toNat < 10000
  · have ⟨hlo, hhi⟩ := hlt10k h1; omega
  · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
    by_cases h2 : v.toNat / 10000 < 10000
    · have ⟨hlo, hhi⟩ := hlt10k h2; omega
    · rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
      have h3 : v.toNat / 10000 / 10000 < 100 := by omega
      by_cases h4 : v.toNat / 10000 / 10000 < 10
      · rw [formatDecimalNat_of_lt_10 h4]; simp
      · rw [formatDecimalNat_two_digits (by omega) h3]; simp

/-- Exact allocation-event envelope of appending `<u8 as Display>::fmt` onto `(cap0, len0)`. -/
@[expose] def FmtWriteU8Env (cap0 len0 : Nat) (v : BitVec 8) (evs : List AllocEvent) : Prop :=
  FmtWriteLitEnv cap0 len0 (formatDecimalNat v.toNat).length evs

/-- Value-independent `u8` decimal `Display` envelope (`1..3` digits). -/
@[expose] def FmtWriteAnyU8Env (cap0 len0 : Nat) (evs : List AllocEvent) : Prop :=
  ∃ dLen : Nat, 1 ≤ dLen ∧ dLen ≤ 3 ∧ FmtWriteLitEnv cap0 len0 dLen evs

/-- Exact allocation-event envelope of appending `<u32 as Display>::fmt` onto `(cap0, len0)`. -/
@[expose] def FmtWriteU32Env (cap0 len0 : Nat) (v : BitVec 32) (evs : List AllocEvent) : Prop :=
  FmtWriteLitEnv cap0 len0 (formatDecimalNat v.toNat).length evs

/-- Value-independent `u32` decimal `Display` envelope (`1..10` digits, e.g. `<KyberPreKeyId as Display>`). -/
@[expose] def FmtWriteAnyU32Env (cap0 len0 : Nat) (evs : List AllocEvent) : Prop :=
  ∃ dLen : Nat, 1 ≤ dLen ∧ dLen ≤ 10 ∧ FmtWriteLitEnv cap0 len0 dLen evs

theorem fmtWriteAnyU8Env_of_u8 (cap0 len0 : Nat) (v : BitVec 8) {evs : List AllocEvent}
    (h : FmtWriteU8Env cap0 len0 v evs) : FmtWriteAnyU8Env cap0 len0 evs :=
  ⟨(formatDecimalNat v.toNat).length, (formatDecimalNat_u8_length v).1,
   (formatDecimalNat_u8_length v).2, h⟩

theorem fmtWriteAnyU32Env_of_u32 (cap0 len0 : Nat) (v : BitVec 32) {evs : List AllocEvent}
    (h : FmtWriteU32Env cap0 len0 v evs) : FmtWriteAnyU32Env cap0 len0 evs :=
  ⟨(formatDecimalNat v.toNat).length, (formatDecimalNat_u32_length v).1,
   (formatDecimalNat_u32_length v).2, h⟩

/-- Explicit `"kyber:"` (`cap0 = 14`, `len0 = 6`) characterization of `FmtWriteU32Env`: `evs = []`
    when `(formatDecimalNat v.toNat).length ≤ 8` (`v < 10^8`), and `evs = [.realloc 1 14 28]` when
    `9 ≤ (formatDecimalNat v.toNat).length` (`10^8 ≤ v`). -/
theorem fmtWriteU32_kyber14_events (v : BitVec 32) :
    fmtWriteKnownEvents 6 14#64 [(formatDecimalNat v.toNat).length] =
      if (formatDecimalNat v.toNat).length ≤ 8 then []
      else [.realloc 1 14 28] := by
  have ⟨hlo, hhi⟩ := formatDecimalNat_u32_length v
  rw [fmtWriteKnownEvents_singleton]
  have h14 : (14#64 : BitVec 64).toNat = 14 := by decide
  rw [h14]
  by_cases hle8 : (formatDecimalNat v.toNat).length ≤ 8
  · have hle14 : 6 + (formatDecimalNat v.toNat).length ≤ 14 := by omega
    simp [hle8, hle14]
  · have hnle14 : ¬ (6 + (formatDecimalNat v.toNat).length ≤ 14) := by omega
    have hgrow : stringGrowCap 14 6 (formatDecimalNat v.toNat).length = 28 := by
      unfold stringGrowCap; omega
    simp [hle8, hnle14, hgrow, stringGrowStepEvents, rustReallocEvents]

theorem decodeFmtArguments_single_even (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(v0, fn0)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]
  exact decodeFmtArguments_single_default x2 v0 fn0

theorem decodeFmtArguments_dotted_even (x2 x3 v0 fn0 v1 fn1 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8] [(v0, fn0), (v1, fn1)] =
      some [FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions,
            FmtCall.writeStr (x2 + 2#64) [0x2e#8],
            FmtCall.fmtArg 1 v1 fn1 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]
  exact decodeFmtArguments_dotted_pair x2 v0 fn0 v1 fn1

/-- Placed callback lift for `<u8 as Display>::fmt` at `defaultFmtOptions` over `fmtInnerBudgetW`. -/
theorem cliU8Display_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (st0 : M.σ) (R_rest : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr : BitVec 64)
    (valRo : Bool) (val : BitVec 8)
    (harg : argBytes idx = formatDecimalNat val.toNat)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : 192 + writerStack ≤ argStack) :
    let R_client :=
      (fmtRef8 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym)
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr
        (coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym) defaultFmtOptions) := by
  intro R_client
  have hw := cliStringBudgetFmtWriterOk L st0 R_rest t0 writerStack out hwStk
  refine u8DisplayFmt_fmtArg_placed_ok (ro := valRo) (v := val) hplFmt hextFmt hclFmt hw
    defaultFmtOptions_noAlt
    (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) haStk (fun st s => ?_)
  · rw [padIntegralNoAltOps_default] at hr
    have hs := fmtOpsRun_str_inv hr
    dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · rw [padIntegralNoAltOps_default] at hp
    have hab := fmtOpsAbort_str_inv hp
    dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hab.2.2
  · rw [padIntegralNoAltOps_default] at ho
    have hab := fmtOpsAbort_str_inv ho
    dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rw [harg]
    exact hab
  · dsimp only [R_client, fmtInnerBudgetW]
    sep_ac_rfl

/-- Placed callback lift for `<u32 as Display>::fmt` at `defaultFmtOptions` over `fmtInnerBudgetW`. -/
theorem cliU32Display_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mplFmt m)
    (st0 : M.σ) (R_rest : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr : BitVec 64)
    (valRo : Bool) (val : BitVec 32)
    (harg : argBytes idx = formatDecimalNat val.toNat)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : 192 + writerStack ≤ argStack) :
    let R_client :=
      (fmtRef32 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym)
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr
        (coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym) defaultFmtOptions) := by
  intro R_client
  have hw := cliStringBudgetFmtWriterOk L st0 R_rest t0 writerStack out hwStk
  refine u32DisplayFmt_fmtArg_placed_ok (ro := valRo) (v := val) hplFmt hextFmt hclFmt hw
    defaultFmtOptions_noAlt
    (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) haStk (fun st s => ?_)
  · rw [padIntegralNoAltOps_default] at hr
    have hs := fmtOpsRun_str_inv hr
    dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · rw [padIntegralNoAltOps_default] at hp
    have hab := fmtOpsAbort_str_inv hp
    dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hab.2.2
  · rw [padIntegralNoAltOps_default] at ho
    have hab := fmtOpsAbort_str_inv ho
    dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rw [harg]
    exact hab
  · dsimp only [R_client, fmtInnerBudgetW]
    sep_ac_rfl

/-- Placed callback lift for `<u64 as Display>::fmt` at `defaultFmtOptions` over `fmtInnerBudgetW`. -/
theorem cliU64Display_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mplFmt m)
    (st0 : M.σ) (R_rest : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr : BitVec 64)
    (valRo : Bool) (val : BitVec 64)
    (harg : argBytes idx = formatDecimalNat val.toNat)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : 240 + writerStack ≤ argStack) :
    let R_client :=
      (fmtRef64 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt u64DisplayFmtSym)
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr
        (coreFmtMultiLib.fnAddr mplFmt u64DisplayFmtSym) defaultFmtOptions) := by
  intro R_client
  have hw := cliStringBudgetFmtWriterOk L st0 R_rest t0 writerStack out hwStk
  refine u64DisplayFmt_fmtArg_placed_ok (ro := valRo) (v := val) hplFmt hextFmt hclFmt hw
    defaultFmtOptions_noAlt
    (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) haStk (fun st s => ?_)
  · rw [padIntegralNoAltOps_default] at hr
    have hs := fmtOpsRun_str_inv hr
    dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · rw [padIntegralNoAltOps_default] at hp
    have hab := fmtOpsAbort_str_inv hp
    dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hab.2.2
  · rw [padIntegralNoAltOps_default] at ho
    have hab := fmtOpsAbort_str_inv ho
    dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rw [harg]
    exact hab
  · dsimp only [R_client, fmtInnerBudgetW]
    sep_ac_rfl

/-- Placed callback lift for `<usize as Display>::fmt` at `defaultFmtOptions` over `fmtInnerBudgetW`. -/
theorem cliUsizeDisplay_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mplFmt m)
    (st0 : M.σ) (R_rest : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr : BitVec 64)
    (valRo : Bool) (val : BitVec 64)
    (harg : argBytes idx = formatDecimalNat val.toNat)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : 240 + writerStack ≤ argStack) :
    let R_client :=
      (fmtRef64 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt usizeDisplayFmtSym)
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr
        (coreFmtMultiLib.fnAddr mplFmt usizeDisplayFmtSym) defaultFmtOptions) := by
  intro R_client
  have hw := cliStringBudgetFmtWriterOk L st0 R_rest t0 writerStack out hwStk
  refine usizeDisplayFmt_fmtArg_placed_ok (ro := valRo) (v := val) hplFmt hextFmt hclFmt hw
    defaultFmtOptions_noAlt
    (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) haStk (fun st s => ?_)
  · rw [padIntegralNoAltOps_default] at hr
    have hs := fmtOpsRun_str_inv hr
    dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · rw [padIntegralNoAltOps_default] at hp
    have hab := fmtOpsAbort_str_inv hp
    dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hab.2.2
  · rw [padIntegralNoAltOps_default] at ho
    have hab := fmtOpsAbort_str_inv ho
    dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rw [harg]
    exact hab
  · dsimp only [R_client, fmtInnerBudgetW]
    sep_ac_rfl

/-- Single-argument `<u8 as Display>::fmt` (`"{}"`, `tpl = [0xc0#8, 0x00#8]`) `core::fmt::write`
    contract (covering `<DeviceId as Display>::fmt`; peak stack `0x70 + 192 + stringWriterStack =
    4544` B `≤ extHookStack`). -/
theorem cliCoreFmtWrite_u8Display_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (v cap0 ptr0 x2 x3 valPtr : BitVec 64) (bs : List (BitVec 8))
    (argsRo valRo : Bool) (val : BitVec 8) (st0 : M.σ)
    (heven : x3.getLsbD 0 = false)
    (hEnv : FmtWriteU8Env cap0.toNat bs.length val
      (fmtWriteKnownEvents bs.length cap0 [(formatDecimalNat val.toNat).length]) →
      Env (fmtWriteKnownEvents bs.length cap0 [(formatDecimalNat val.toNat).length]))
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    let u8Fn := coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
    let R_client :=
      (fmtRef8 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteU8Env cap0.toNat bs.length val evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ formatDecimalNat val.toNat) ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  intro u8Fn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  have hdec : decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] =
      some [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions] :=
    decodeFmtArguments_single_even x2 x3 valPtr u8Fn heven
  refine ⟨(v, cap0, ptr0, bs, argsRo, [0xc0#8, 0x00#8], [(valPtr, u8Fn)], st0), ?_,
    fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0
        [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions] := by
      intro idx value fmtFn opts hmem out
      simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliU8Display_fmtArg_ok L hplFmt hextFmt hclFmt st0 R_rest argBytes s0
        stringWriterStack stackBytes 0 out valPtr valRo val rfl ⟨Nat.le_refl _, by decide⟩ hstk.1
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0
        (callLens argBytes [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions])) :=
      hEnv (fmtWriteLitEnv_knownEvents bs.length cap0 (formatDecimalNat val.toNat).length)
    have hstk1 : stringWriterStack ≤ stackBytes := by omega
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk1, hstk.2, hFit,
      [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions], hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
            bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions] :=
      Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [callLens, List.map_cons, List.map_nil, callBytes, argBytes, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hevs hbs'
    subst hbs'
    have hU8 : FmtWriteU8Env cap0.toNat bs.length val evs := by
      rw [hevs]; exact fmtWriteLitEnv_knownEvents bs.length cap0 (formatDecimalNat val.toNat).length
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hU8⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Single-argument `<u32 as Display>::fmt` (`"{}"`, `tpl = [0xc0#8, 0x00#8]`) `core::fmt::write`
    contract (covering `<KyberPreKeyId as Display>::fmt`, including `"kyber:"` with `cap0 = 14#64`
    via `fmtWriteU32_kyber14_events`; peak stack `0x70 + 192 + stringWriterStack = 4544` B
    `≤ extHookStack`). -/
theorem cliCoreFmtWrite_u32Display_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mplFmt m)
    (v cap0 ptr0 x2 x3 valPtr : BitVec 64) (bs : List (BitVec 8))
    (argsRo valRo : Bool) (val : BitVec 32) (st0 : M.σ)
    (heven : x3.getLsbD 0 = false)
    (hEnv : FmtWriteU32Env cap0.toNat bs.length val
      (fmtWriteKnownEvents bs.length cap0 [(formatDecimalNat val.toNat).length]) →
      Env (fmtWriteKnownEvents bs.length cap0 [(formatDecimalNat val.toNat).length]))
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    let u32Fn := coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym
    let R_client :=
      (fmtRef32 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteU32Env cap0.toNat bs.length val evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ formatDecimalNat val.toNat) ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  intro u32Fn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  have hdec : decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] =
      some [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions] :=
    decodeFmtArguments_single_even x2 x3 valPtr u32Fn heven
  refine ⟨(v, cap0, ptr0, bs, argsRo, [0xc0#8, 0x00#8], [(valPtr, u32Fn)], st0), ?_,
    fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0
        [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions] := by
      intro idx value fmtFn opts hmem out
      simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliU32Display_fmtArg_ok L hplFmt hextFmt hclFmt st0 R_rest argBytes s0
        stringWriterStack stackBytes 0 out valPtr valRo val rfl ⟨Nat.le_refl _, by decide⟩ hstk.1
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0
        (callLens argBytes [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions])) :=
      hEnv (fmtWriteLitEnv_knownEvents bs.length cap0 (formatDecimalNat val.toNat).length)
    have hstk1 : stringWriterStack ≤ stackBytes := by omega
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk1, hstk.2, hFit,
      [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions], hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
            bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions] :=
      Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [callLens, List.map_cons, List.map_nil, callBytes, argBytes, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hevs hbs'
    subst hbs'
    have hU32 : FmtWriteU32Env cap0.toNat bs.length val evs := by
      rw [hevs]; exact fmtWriteLitEnv_knownEvents bs.length cap0 (formatDecimalNat val.toNat).length
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hU32⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 3. `<&str as Display>::fmt`, `<String as Display>::fmt`, and Two-Arg `"{}.{}"` -/

/-- Lift any `strRefDisplayFmtSpec` implementation over `fmtInnerBudgetW` (either `coreFmtMultiLib`
    block `7` or a crate-local 20-byte `checkStrRefDisplayShimBlock` shim) to `fmtArgCallSpec` at
    `defaultFmtOptions`. -/
theorem cliStrRefDisplay_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {mplAlloc : MultiPlacement}
    (st0 : M.σ) (R_client R_inner : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr ptr fmtFn : BitVec 64)
    (refRo srcRo : Bool) (sbs : List (BitVec 8))
    (hfmt : subroutine_ok P fmtFn
      (strRefDisplayFmtSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_inner t0 out)
        StringBufStrStep (StringBufWriterPanic t0)
        (StringBufWriterOom (toRustAllocBudget M A lim) st0)
        writerStack out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions
        refRo srcRo valPtr ptr sbs))
    (hlen : sbs.length < 2 ^ 60)
    (harg : argBytes idx = sbs)
    (hwStk : 80 ≤ writerStack ∧ writerStack ≤ argStack)
    (hR : R_client =
      fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 sbs.length) ∗ fmtSrcBytes srcRo ptr sbs ∗ R_inner) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr fmtFn defaultFmtOptions) := by
  refine strRefDisplayFmt_fmtArg_ok hfmt hlen fmtPadFastOpts_default
    (fun st ok st' hs => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_)
    (by omega) (fun st s => ?_)
  · dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hp.2.2
  · dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rwa [harg]
  · rw [hR]
    dsimp only [fmtInnerBudgetW]
    sep_ac_rfl

/-- Placed callback lift for `coreFmtMultiLib` block `7` (`strRefDisplayFmtSym`, `<&str as Display>::fmt`)
    at `defaultFmtOptions`. -/
theorem cliStrRefDisplay_coreFmt_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strRefDisplayKeep mplFmt m)
    (st0 : M.σ) (R_client R_inner : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr ptr : BitVec 64)
    (refRo srcRo : Bool) (sbs : List (BitVec 8))
    (hlen : sbs.length < 2 ^ 60)
    (harg : argBytes idx = sbs)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : writerStack ≤ argStack)
    (hR : R_client =
      fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 sbs.length) ∗ fmtSrcBytes srcRo ptr sbs ∗ R_inner) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt strRefDisplayFmtSym)
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr
        (coreFmtMultiLib.fnAddr mplFmt strRefDisplayFmtSym) defaultFmtOptions) := by
  have hw := cliStringBudgetFmtWriterOk L st0 R_inner t0 writerStack out hwStk
  have hfmt := strRefDisplayFmt_of_codeLoaded hplFmt hextFmt hclFmt
    hw.transport hw.slot_write_str (hw.write_str srcRo ptr sbs) (opts := defaultFmtOptions)
    (refRo := refRo) (valPtr := valPtr)
  have h80 : 80 ≤ writerStack := le_trans (by decide : 80 ≤ stringWriterStack) hwStk.1
  exact cliStrRefDisplay_fmtArg_ok st0 R_client R_inner argBytes t0 writerStack argStack idx
    out valPtr ptr (coreFmtMultiLib.fnAddr mplFmt strRefDisplayFmtSym) refRo srcRo sbs
    hfmt hlen harg ⟨h80, haStk⟩ hR

/-- Placed callback lift for a crate-local 20-byte `<&str as Display>::fmt` shim block `bi` of `lib`
    jumping to `coreFmtMultiLib` block `10` (`strDisplayFmtSym`). -/
theorem cliStrRefDisplayShim_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m)
    (hplShim : lib.Placeable mplShim) (bi : Nat)
    (hkeep : keep bi = true) (hshim : checkStrRefDisplayShimBlock lib bi = true)
    (hextShim : LibBlockNoExtern lib mplShim P bi)
    (hclShim : ∀ m, P.CodeLoaded m → lib.CodeLoadedWhere keep mplShim m)
    (htarget : lib.resolve mplShim (displayShimTargetSym lib bi) =
      coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym)
    (st0 : M.σ) (R_client R_inner : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr ptr fmtFn : BitVec 64)
    (refRo srcRo : Bool) (sbs : List (BitVec 8))
    (hentry : fmtFn = mplShim.base bi)
    (hlen : sbs.length < 2 ^ 60)
    (harg : argBytes idx = sbs)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : writerStack ≤ argStack)
    (hR : R_client =
      fmtRefStr refRo valPtr ptr (BitVec.ofNat 64 sbs.length) ∗ fmtSrcBytes srcRo ptr sbs ∗ R_inner) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr fmtFn defaultFmtOptions) := by
  have hw := cliStringBudgetFmtWriterOk L st0 R_inner t0 writerStack out hwStk
  have hstr := subroutine_ok_of_withCodeLoadedWhere hclFmt
    (strDisplayFmt_of_writerOk hplFmt hextFmt hw (opts := defaultFmtOptions)
      (ro := srcRo) (ptr := ptr) (bs := sbs))
  have hfmt := strRefDisplayShim_of_codeLoaded hplShim bi hkeep hshim hextShim hclShim
    hw.transport hstr hentry htarget (refRo := refRo) (valPtr := valPtr)
  have h80 : 80 ≤ writerStack := le_trans (by decide : 80 ≤ stringWriterStack) hwStk.1
  exact cliStrRefDisplay_fmtArg_ok st0 R_client R_inner argBytes t0 writerStack argStack idx
    out valPtr ptr fmtFn refRo srcRo sbs hfmt hlen harg ⟨h80, haStk⟩ hR

/-- Lift any `stringDisplayFmtSpec` implementation over `fmtInnerBudgetW` (such as a crate-local
    20-byte `checkStringDisplayShimBlock` shim) to `fmtArgCallSpec` at `defaultFmtOptions`. -/
theorem cliStringDisplay_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program} {mplAlloc : MultiPlacement}
    (st0 : M.σ) (R_client R_inner : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr cap ptr fmtFn : BitVec 64)
    (refRo srcRo : Bool) (sbs : List (BitVec 8))
    (hfmt : subroutine_ok P fmtFn
      (stringDisplayFmtSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_inner t0 out)
        StringBufStrStep (StringBufWriterPanic t0)
        (StringBufWriterOom (toRustAllocBudget M A lim) st0)
        writerStack out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions
        refRo srcRo valPtr cap ptr sbs))
    (hlen : sbs.length < 2 ^ 60)
    (harg : argBytes idx = sbs)
    (hwStk : 80 ≤ writerStack ∧ writerStack ≤ argStack)
    (hR : R_client =
      fmtRefString refRo valPtr cap ptr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo ptr sbs ∗ R_inner) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr fmtFn defaultFmtOptions) := by
  refine stringDisplayFmt_fmtArg_ok hfmt hlen fmtPadFastOpts_default
    (fun st ok st' hs => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_)
    (by omega) (fun st s => ?_)
  · dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes]
    rwa [harg]
  · dsimp only [fmtInnerBudgetPanic, knownArgPanic, callBytes]
    rw [harg]
    exact hp.2.2
  · dsimp only [fmtInnerBudgetOom, knownArgOom, callBytes]
    rwa [harg]
  · rw [hR]
    dsimp only [fmtInnerBudgetW]
    sep_ac_rfl

/-- Placed callback lift for a crate-local 20-byte `<String as Display>::fmt` shim block `bi` of
    `lib` jumping to `coreFmtMultiLib` block `10` (`strDisplayFmtSym`). -/
theorem cliStringDisplayShim_fmtArg_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m)
    (hplShim : lib.Placeable mplShim) (bi : Nat)
    (hkeep : keep bi = true) (hshim : checkStringDisplayShimBlock lib bi = true)
    (hextShim : LibBlockNoExtern lib mplShim P bi)
    (hclShim : ∀ m, P.CodeLoaded m → lib.CodeLoadedWhere keep mplShim m)
    (htarget : lib.resolve mplShim (displayShimTargetSym lib bi) =
      coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym)
    (st0 : M.σ) (R_client R_inner : SepProp) (argBytes : Nat → List (BitVec 8))
    (t0 : State) (writerStack argStack idx : Nat) (out valPtr cap ptr fmtFn : BitVec 64)
    (refRo srcRo : Bool) (sbs : List (BitVec 8))
    (hentry : fmtFn = mplShim.base bi)
    (hlen : sbs.length < 2 ^ 60)
    (harg : argBytes idx = sbs)
    (hwStk : stringWriterStack ≤ writerStack ∧ writerStack ≤ 2 ^ 64)
    (haStk : writerStack ≤ argStack)
    (hR : R_client =
      fmtRefString refRo valPtr cap ptr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo ptr sbs ∗ R_inner) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec
        (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
          (allocStringWriteAddrs mplAlloc) R_client t0 out)
        (fmtInnerBudgetStep (knownArgStep argBytes))
        (fmtInnerBudgetPanic t0 (knownArgPanic argBytes))
        (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes))
        argStack out (allocStringWriteAddrs mplAlloc).vtable idx valPtr fmtFn defaultFmtOptions) := by
  have hw := cliStringBudgetFmtWriterOk L st0 R_inner t0 writerStack out hwStk
  have hstr := subroutine_ok_of_withCodeLoadedWhere hclFmt
    (strDisplayFmt_of_writerOk hplFmt hextFmt hw (opts := defaultFmtOptions)
      (ro := srcRo) (ptr := ptr) (bs := sbs))
  have hfmt := stringDisplayShim_of_codeLoaded hplShim bi hkeep hshim hextShim hclShim
    hw.transport hstr hentry htarget (refRo := refRo) (valPtr := valPtr) (cap := cap)
  have h80 : 80 ≤ writerStack := le_trans (by decide : 80 ≤ stringWriterStack) hwStk.1
  exact cliStringDisplay_fmtArg_ok st0 R_client R_inner argBytes t0 writerStack argStack idx
    out valPtr cap ptr fmtFn refRo srcRo sbs hfmt hlen harg ⟨h80, haStk⟩ hR

/-- Single-argument `<&str as Display>::fmt` (`"{}"`, `tpl = [0xc0#8, 0x00#8]`) `core::fmt::write`
    specialization (peak stack `0x70 + stringWriterStack = 4352` B `≤ extHookStack`). -/
theorem cliCoreFmtWrite_strRefDisplay_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strRefDisplayKeep mplFmt m)
    (v cap0 ptr0 x2 x3 valPtr strPtr : BitVec 64) (bs sbs : List (BitVec 8))
    (argsRo refRo srcRo : Bool) (st0 : M.σ)
    (heven : x3.getLsbD 0 = false)
    (hlen : sbs.length < 2 ^ 60)
    (hEnv : FmtWriteLitEnv cap0.toNat bs.length sbs.length
      (fmtWriteKnownEvents bs.length cap0 [sbs.length]) →
      Env (fmtWriteKnownEvents bs.length cap0 [sbs.length]))
    (hstk : stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    let strFn := coreFmtMultiLib.fnAddr mplFmt strRefDisplayFmtSym
    let R_client :=
      fmtRefStr refRo valPtr strPtr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo strPtr sbs ∗ R_rest
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteLitEnv cap0.toNat bs.length sbs.length evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ sbs) ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  intro strFn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => sbs
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  have hdec : decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] =
      some [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions] :=
    decodeFmtArguments_single_even x2 x3 valPtr strFn heven
  refine ⟨(v, cap0, ptr0, bs, argsRo, [0xc0#8, 0x00#8], [(valPtr, strFn)], st0), ?_,
    fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0
        [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions] := by
      intro idx value fmtFn opts hmem out
      simp only [List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliStrRefDisplay_coreFmt_fmtArg_ok L hplFmt hextFmt hclFmt st0 R_client R_rest
        argBytes s0 stringWriterStack stackBytes 0 out valPtr strPtr refRo srcRo sbs
        hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk.1 rfl
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0
        (callLens argBytes [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions])) :=
      hEnv (fmtWriteLitEnv_knownEvents bs.length cap0 sbs.length)
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk.1, hstk.2, hFit,
      [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions], hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
            bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions] :=
      Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [callLens, List.map_cons, List.map_nil, callBytes, argBytes, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hevs hbs'
    subst hbs'
    have hLit : FmtWriteLitEnv cap0.toNat bs.length sbs.length evs := by
      rw [hevs]; exact fmtWriteLitEnv_knownEvents bs.length cap0 sbs.length
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hLit⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Exact allocation-event envelope of the two-argument `"{}.{}"` (`String` + `u8`/`u32`)
    `core::fmt::write` call shape (matching `<ProtocolAddress as Display>::fmt`'s
    `write!(f, "{}.{}", self.name, self.device_id)`). -/
@[expose] def FmtWriteAddrEnv (cap0 len0 nameLen devDigits : Nat) (evs : List AllocEvent) : Prop :=
  evs = fmtWriteKnownEvents len0 (BitVec.ofNat 64 cap0) [nameLen, 1, devDigits]

/-- Empty-buffer (`cap0 = 0`, `len0 = 0`) specialization of `FmtWriteAddrEnv`. -/
@[expose] def FmtWriteEmptyAddrEnv (nameLen devDigits : Nat) (evs : List AllocEvent) : Prop :=
  FmtWriteAddrEnv 0 0 nameLen devDigits evs

/-- Two-argument `"{}.{}"` (`tpl = [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]`) `String` + `u8`
    `core::fmt::write` composition (matching `<ProtocolAddress as Display>::fmt` when `DeviceId`
    wraps `u8`; peak stack `0x70 + 192 + stringWriterStack = 4544` B `≤ extHookStack`). -/
theorem cliCoreFmtWrite_dottedStringU8_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextStrFmt : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P)
    (hclStrFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m)
    (hextU8Fmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclU8Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (hplShim : lib.Placeable mplShim) (bi : Nat)
    (hkeep : keep bi = true) (hshim : checkStringDisplayShimBlock lib bi = true)
    (hextShim : LibBlockNoExtern lib mplShim P bi)
    (hclShim : ∀ m, P.CodeLoaded m → lib.CodeLoadedWhere keep mplShim m)
    (htarget : lib.resolve mplShim (displayShimTargetSym lib bi) =
      coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym)
    (v cap0 ptr0 x2 x3 namePtr nameCap nameDataPtr strFn devPtr : BitVec 64)
    (bs nameBs : List (BitVec 8))
    (argsRo strRefRo strSrcRo devRo : Bool) (dev : BitVec 8) (st0 : M.σ)
    (hstrEntry : strFn = mplShim.base bi)
    (heven : x3.getLsbD 0 = false)
    (hlen : nameBs.length < 2 ^ 60)
    (hEnv : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length (formatDecimalNat dev.toNat).length
      (fmtWriteKnownEvents bs.length cap0
        [nameBs.length, 1, (formatDecimalNat dev.toNat).length]) →
      Env (fmtWriteKnownEvents bs.length cap0
        [nameBs.length, 1, (formatDecimalNat dev.toNat).length]))
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    let u8Fn := coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
    let F_str := fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
      fmtSrcBytes strSrcRo nameDataPtr nameBs
    let F_dev := fmtRef8 devRo devPtr dev ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)
    let R_client := F_str ∗ F_dev ∗ R_rest
    let dotTpl : List (BitVec 8) := [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
                (formatDecimalNat dev.toNat).length evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat) ∗
            fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  intro u8Fn F_str F_dev R_client dotTpl
  let argBytes : Nat → List (BitVec 8) :=
    fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  let cs0 : List FmtCall :=
    [FmtCall.fmtArg 0 namePtr strFn defaultFmtOptions,
     FmtCall.writeStr (x2 + 2#64) [0x2e#8],
     FmtCall.fmtArg 1 devPtr u8Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] = some cs0 :=
    decodeFmtArguments_dotted_even x2 x3 namePtr strFn devPtr u8Fn heven
  have hstk1 : stringWriterStack ≤ stackBytes := by omega
  have hcap_id : BitVec.ofNat 64 cap0.toNat = cap0 := by simp
  refine ⟨(v, cap0, ptr0, bs, argsRo, dotTpl, [(namePtr, strFn), (devPtr, u8Fn)], st0), ?_,
    fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_cons, List.not_mem_nil, or_false, false_or, FmtCall.fmtArg.injEq,
        reduceCtorEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩ | ⟨rfl, hval, hfn, hopts⟩
      · rw [hval, hfn, hopts]
        exact cliStringDisplayShim_fmtArg_ok L hplFmt hextStrFmt hclStrFmt hplShim bi hkeep hshim
          hextShim hclShim htarget st0 R_client (F_dev ∗ R_rest) argBytes s0
          stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr strFn
          strRefRo strSrcRo nameBs hstrEntry hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk1
          (by dsimp only [R_client, F_str]; sep_ac_rfl)
      · rw [hval, hfn, hopts]
        have hw := cliStringBudgetFmtWriterOk L st0 (F_str ∗ R_rest) s0 stringWriterStack out
          ⟨Nat.le_refl _, by decide⟩
        refine u8DisplayFmt_fmtArg_placed_ok (ro := devRo) (v := dev) hplFmt hextU8Fmt hclU8Fmt hw
          defaultFmtOptions_noAlt
          (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) hstk.1
          (fun st s => ?_)
        · rw [padIntegralNoAltOps_default] at hr
          exact fmtOpsRun_str_inv hr
        · rw [padIntegralNoAltOps_default] at hp
          exact (fmtOpsAbort_str_inv hp).2.2
        · rw [padIntegralNoAltOps_default] at ho
          exact fmtOpsAbort_str_inv ho
        · dsimp only [R_client, F_str, F_dev, fmtInnerBudgetW]
          sep_ac_rfl
    have hAddr0 : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
        (formatDecimalNat dev.toNat).length
        (fmtWriteKnownEvents bs.length cap0
          [nameBs.length, 1, (formatDecimalNat dev.toNat).length]) := by
      unfold FmtWriteAddrEnv
      rw [hcap_id]
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs0)) :=
      hEnv hAddr0
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk1, hstk.2, hFit, cs0, hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
            bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [cs0, callLens, List.map_cons, List.map_nil, callBytes, argBytes, ↓reduceIte,
      Nat.one_ne_zero, List.length_singleton, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hevs hbs'
    have hbsEq : bs' = bs ++ nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat := by
      rw [hbs']; simp only [List.append_assoc]
    subst hbsEq
    have hAddr : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
        (formatDecimalNat dev.toNat).length evs := by
      unfold FmtWriteAddrEnv
      rw [hevs, hcap_id]
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hAddr⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Two-argument `"{}.{}"` (`tpl = [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]`) `String` + `u32`
    `core::fmt::write` composition (matching `<ProtocolAddress as Display>::fmt` when `DeviceId`
    wraps `u32`; peak stack `0x70 + 192 + stringWriterStack = 4544` B `≤ extHookStack`). -/
theorem cliCoreFmtWrite_dottedStringU32_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextStrFmt : LibKeepNoExtern coreFmtMultiLib strDisplayKeep mplFmt P)
    (hclStrFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strDisplayKeep mplFmt m)
    (hextU32Fmt : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mplFmt P)
    (hclU32Fmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mplFmt m)
    (hplShim : lib.Placeable mplShim) (bi : Nat)
    (hkeep : keep bi = true) (hshim : checkStringDisplayShimBlock lib bi = true)
    (hextShim : LibBlockNoExtern lib mplShim P bi)
    (hclShim : ∀ m, P.CodeLoaded m → lib.CodeLoadedWhere keep mplShim m)
    (htarget : lib.resolve mplShim (displayShimTargetSym lib bi) =
      coreFmtMultiLib.fnAddr mplFmt VerifiedLibraries.RustStd.strDisplayFmtSym)
    (v cap0 ptr0 x2 x3 namePtr nameCap nameDataPtr strFn devPtr : BitVec 64)
    (bs nameBs : List (BitVec 8))
    (argsRo strRefRo strSrcRo devRo : Bool) (dev : BitVec 32) (st0 : M.σ)
    (hstrEntry : strFn = mplShim.base bi)
    (heven : x3.getLsbD 0 = false)
    (hlen : nameBs.length < 2 ^ 60)
    (hEnv : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length (formatDecimalNat dev.toNat).length
      (fmtWriteKnownEvents bs.length cap0
        [nameBs.length, 1, (formatDecimalNat dev.toNat).length]) →
      Env (fmtWriteKnownEvents bs.length cap0
        [nameBs.length, 1, (formatDecimalNat dev.toNat).length]))
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ 0x70 + stackBytes ≤ 2 ^ 64) :
    let u32Fn := coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym
    let F_str := fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
      fmtSrcBytes strSrcRo nameDataPtr nameBs
    let F_dev := fmtRef32 devRo devPtr dev ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)
    let R_client := F_str ∗ F_dev ∗ R_rest
    let dotTpl : List (BitVec 8) := [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]
    subroutine_ok P (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
            s.readReg64 .x2 = x2 ∧ s.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
          vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
              sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
                (formatDecimalNat dev.toNat).length evs⌝ ∗
            vecU8 A.repAlloc v (bs ++ nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat) ∗
            fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp (0x70 + stackBytes) } := by
  intro u32Fn F_str F_dev R_client dotTpl
  let argBytes : Nat → List (BitVec 8) :=
    fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
  have hbase := cliCoreFmtWrite_vecU8At_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = v ∧ s0.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable ∧
        s0.readReg64 .x2 = x2 ∧ s0.readReg64 .x3 = x3 ∧ FitsEnv M lim st0 Env⌝ ∗
        ((vecU8At A.repAlloc v cap0 ptr0 bs ∗
          fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx0, hx1, hx2, hx3, hFit⟩, hm2⟩
  let cs0 : List FmtCall :=
    [FmtCall.fmtArg 0 namePtr strFn defaultFmtOptions,
     FmtCall.writeStr (x2 + 2#64) [0x2e#8],
     FmtCall.fmtArg 1 devPtr u32Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] = some cs0 :=
    decodeFmtArguments_dotted_even x2 x3 namePtr strFn devPtr u32Fn heven
  have hstk1 : stringWriterStack ≤ stackBytes := by omega
  have hcap_id : BitVec.ofNat 64 cap0.toNat = cap0 := by simp
  refine ⟨(v, cap0, ptr0, bs, argsRo, dotTpl, [(namePtr, strFn), (devPtr, u32Fn)], st0), ?_,
    fun sf hpost => ?_⟩
  · dsimp only [cliCoreFmtWriteVecAtSpec]
    rw [hx2, hx3]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_cons, List.not_mem_nil, or_false, false_or, FmtCall.fmtArg.injEq,
        reduceCtorEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩ | ⟨rfl, hval, hfn, hopts⟩
      · rw [hval, hfn, hopts]
        exact cliStringDisplayShim_fmtArg_ok L hplFmt hextStrFmt hclStrFmt hplShim bi hkeep hshim
          hextShim hclShim htarget st0 R_client (F_dev ∗ R_rest) argBytes s0
          stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr strFn
          strRefRo strSrcRo nameBs hstrEntry hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk1
          (by dsimp only [R_client, F_str]; sep_ac_rfl)
      · rw [hval, hfn, hopts]
        have hw := cliStringBudgetFmtWriterOk L st0 (F_str ∗ R_rest) s0 stringWriterStack out
          ⟨Nat.le_refl _, by decide⟩
        refine u32DisplayFmt_fmtArg_placed_ok (ro := devRo) (v := dev) hplFmt hextU32Fmt hclU32Fmt hw
          defaultFmtOptions_noAlt
          (fun st ok st' hr => ?_) (fun st sf hp => ?_) (fun st sf ho => ?_) hstk.1
          (fun st s => ?_)
        · rw [padIntegralNoAltOps_default] at hr
          exact fmtOpsRun_str_inv hr
        · rw [padIntegralNoAltOps_default] at hp
          exact (fmtOpsAbort_str_inv hp).2.2
        · rw [padIntegralNoAltOps_default] at ho
          exact fmtOpsAbort_str_inv ho
        · dsimp only [R_client, F_str, F_dev, fmtInnerBudgetW]
          sep_ac_rfl
    have hAddr0 : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
        (formatDecimalNat dev.toNat).length
        (fmtWriteKnownEvents bs.length cap0
          [nameBs.length, 1, (formatDecimalNat dev.toNat).length]) := by
      unfold FmtWriteAddrEnv
      rw [hcap_id]
    have hEnv1 : Env (fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs0)) :=
      hEnv hAddr0
    rw [pure_sepConj_of_true ⟨hx0, hx1, hstk1, hstk.2, hFit, cs0, hdec, hEnv1, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliCoreFmtWriteVecAtSpec] at hpost
    rw [hx2, hx3] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs', hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ AllocCallPreserved s0 sf ∧
          sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] = some cs ∧
            evs = fmtWriteKnownEvents bs.length cap0 (callLens argBytes cs) ∧
            bs' = bs ++ cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc v bs' ∗
            fmtArgumentsAt argsRo x2 x3 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hw0, hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs'⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [cs0, callLens, List.map_cons, List.map_nil, callBytes, argBytes, ↓reduceIte,
      Nat.one_ne_zero, List.length_singleton, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hevs hbs'
    have hbsEq : bs' = bs ++ nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat := by
      rw [hbs']; simp only [List.append_assoc]
    subst hbsEq
    have hAddr : FmtWriteAddrEnv cap0.toNat bs.length nameBs.length
        (formatDecimalNat dev.toNat).length evs := by
      unfold FmtWriteAddrEnv
      rw [hevs, hcap_id]
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hw0, hacp, hfs, htr, hEnvOut, hAddr⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 4. 1- and 2-Hop Linker-Alias Stubs at `lsFmtWriteSym` -/

/-- Lift `cliCoreFmtWrite_string_placed_ok` across a 1-instruction `b` linker-alias stub
    (e.g. `lsFmtWriteSym` → `coreFmtWriteSym`). -/
theorem cliCoreFmtWrite_alias_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    {aliasAddr : BitVec 64}
    (hstub : hasInstrs P aliasAddr
      [.b (coreMultiLib.fnAddr mplCore coreFmtWriteSym - aliasAddr)]) :
    subroutine_ok P aliasAddr
      (cliCoreFmtWriteSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub aliasAddr (coreMultiLib.fnAddr mplCore coreFmtWriteSym) hstub
    (by
      rintro ⟨_, _, _, _, _, st0⟩ s pc'
      dsimp only [cliCoreFmtWriteSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliCoreFmtWrite_string_placed_ok L)

/-- Lift `cliCoreFmtWrite_string_placed_ok` across a 2-hop `b` linker-alias chain
    (`snapstubAddr → aliasAddr → coreFmtWriteSym`). -/
theorem cliCoreFmtWrite_alias2_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    {snapstubAddr aliasAddr : BitVec 64}
    (hSnap : hasInstrs P snapstubAddr [.b (aliasAddr - snapstubAddr)])
    (hAlias : hasInstrs P aliasAddr
      [.b (coreMultiLib.fnAddr mplCore coreFmtWriteSym - aliasAddr)]) :
    subroutine_ok P snapstubAddr
      (cliCoreFmtWriteSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub2 snapstubAddr aliasAddr (coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hSnap hAlias
    (by
      rintro ⟨_, _, _, _, _, st0⟩ s pc'
      dsimp only [cliCoreFmtWriteSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliCoreFmtWrite_string_placed_ok L)

/-- `WordTree` (`checkBranchStub2`) variant of `cliCoreFmtWrite_alias2_ok` for `LinkedImage` proofs. -/
theorem cliCoreFmtWrite_alias2_wordTree_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {t : WordTree} (n : Nat) {mplCore mplAlloc : MultiPlacement}
    (L : CliFmtWriteLink M A lim P mplCore mplAlloc)
    (snapstubAddr aliasAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr
      (coreMultiLib.fnAddr mplCore coreFmtWriteSym) = true) :
    subroutine_ok P snapstubAddr
      (cliCoreFmtWriteSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr
    (coreMultiLib.fnAddr mplCore coreFmtWriteSym) hcode hwf hhookSnap hhookAlias hok
    (by
      rintro ⟨_, _, _, _, _, st0⟩ s pc'
      dsimp only [cliCoreFmtWriteSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliCoreFmtWrite_string_placed_ok L)

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof

