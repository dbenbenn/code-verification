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
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.FormatInnerBudget
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.Join
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Placed `alloc::fmt::format::format_inner` Contracts and CLI Specializations

Composes `VerifiedLibraries.RustStd.allocFormatInnerBudget_placed_ok` (`allocMultiLib` block `3`,
`_RNvNvNtCshlmZ2E5RoO1_5alloc3fmt6format12format_inner`) over `toRustAllocBudget M A lim`,
discharging every CLI `alloc::fmt::format::format_inner` call shape without adding formatting
hooks or formatting specifications to `Specifications/`:

- **General placed contracts (`cliAllocFormatInner_tight_placed_ok`,
  `cliAllocFormatInner_placed_ok`):** parametric in `stackBytes` (tight
  `formatInnerFrame + 0x70 + stringWriterStack = 4448` B) and specialized to
  `extHookStack = 16384` B, returning `AllocCallPreserved s0 sf`, `sf.fs = s0.fs`,
  `sf.trace = s0.trace`, `Env evs`, exact concatenated bytes `vecU8 A.repAlloc ret bs`, and
  entailing the `.post` of `formatInnerBudgetEnvSpec`.
- **0-arg static fast paths:** empty template (`FormatInnerEnv`, `0` allocations), `from_str`
  (odd `x1`, `FormatInnerFromStrEnv`), and short static literals (`FormatInnerShortLitEnv`).
- **Single-arg `Display::fmt` (`u8`, `u32`, `&str`)** and **two-arg `"{}.{}"` `String` + `u8` /
  `u32` composition** (`<ProtocolAddress as Display>::fmt`, `FormatInnerAddrEnv`).
- **1- and 2-hop `b`-stub linker-alias corollaries** at `lsFormatInnerSym`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open Arm64.Program (HooksUnfetched)
open ProofLib.ProgramReflection (WordTree)
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustAllocAddrs
   RustCliAllocBudget RustCliAllocBudgetEntriesBase rustAllocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (checkBranchStub2 subroutine_ok_of_branchStub subroutine_ok_of_branchStub2
   subroutine_ok_of_branchStub2_wordTree)
open LibsignalBinary.Heap.SpecBudget (FormatInnerEnv formatInnerBudgetEnvSpec)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (CliBufShape PoolMemTransport allocCallPreserved_of_ioCallFrame callBytes callLens cliBufShapeOf
   cliBufShape_of_start fitsEnv_toRustAllocBudget_of_cli fmtOpsAbort_str_inv fmtOpsRun_str_inv
   formatInnerKnownEvents knownArgOom knownArgPanic knownArgStep knownFmt_safe_of_env
   lsFormatInnerSym pool_of_setPC run_known startCliBufShape toCliAllocEvent toRustAllocBudget
   toRustAllocBudget_stepEvents toRustStdEnv vecHeader_fmtBufVecAt_entails_vecU8)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof
  (CliFmtWriteLink cliStrRefDisplay_coreFmt_fmtArg_ok cliStringBudgetFmtWriterOk
   cliStringDisplayShim_fmtArg_ok cliU32Display_fmtArg_ok cliU8Display_fmtArg_ok
   decodeFmtArguments_dotted_even decodeFmtArguments_empty decodeFmtArguments_fromStr
   decodeFmtArguments_shortLiteral decodeFmtArguments_single_even formatDecimalNat_u32_length
   formatDecimalNat_u8_length)
open VerifiedLibraries.Mallocng.Proofs (memcpySymWords)
open VerifiedLibraries.RustStd
  (FmtBuf FmtCall FmtInnerBudgetArgsOk IoCallFrame StringWriteAddrs allocBudgetHandleErrorSym
   allocFormatInnerBudgetSpec allocFormatInnerBudget_placed_ok allocFormatInnerSym allocMultiLib
   allocRustAllocSym allocRustNoAllocShimSym allocRustReallocSym allocStringWriteAddrs
   checkStringDisplayShimBlock coreFmtDecDigitsLutSym coreFmtMultiLib coreFmtWriteSym coreMultiLib
   decDigitsLutBytes decodeFmtArguments defaultFmtOptions defaultFmtOptions_noAlt
   displayShimTargetSym fmtArgumentsAt fmtEstimatedCapacity fmtInnerBudgetOom fmtInnerBudgetPanic
   fmtInnerBudgetStep fmtInnerBudgetW fmtInnerCoreFmtWriteRawSym fmtLiteralLen fmtRef32 fmtRef8
   fmtRefStr fmtRefString fmtSrcBytes fmtStartsWithPlaceholder formatInnerFrame
   padIntegralNoAltOps_default strRefDisplayFmtSym stringGrowCap stringWriteVtableAt
   stringWriterStack u32DisplayFmtSym u8DisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern strDisplayKeep strRefDisplayKeep u32DisplayFmt_fmtArg_placed_ok
   u32DisplayKeep u8DisplayFmt_fmtArg_placed_ok u8DisplayKeep)

/-! ## Stack Bounds & Linkage Bundle -/

/-- Exact peak stack of `alloc::fmt::format::format_inner` with `0`-extra-frame callbacks
    (`0x60 + 0x70 + (0x90 + 4096) = 4448` B). -/
@[expose] def allocFormatInnerStack : Nat :=
  formatInnerFrame + 0x70 + stringWriterStack

theorem allocFormatInnerStack_eq : allocFormatInnerStack = 4448 :=
  rfl

theorem allocFormatInnerStack_le_extHookStack : allocFormatInnerStack ≤ extHookStack := by
  decide

/-- Placement and callee-discharge bundle for placed `alloc::fmt::format::format_inner`
    (`allocMultiLib` block `3`), `core::fmt::write` (`coreMultiLib` block `0`), and
    `<String as fmt::Write>` (`allocMultiLib` blocks `1`, `2`, `6`, `7`) over
    `toRustAllocBudget M A lim`. -/
structure CliFormatInnerLink (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (P : Program)
    (mplCore mplAlloc : MultiPlacement) : Prop extends
    CliFmtWriteLink M A lim P mplCore mplAlloc where
  clAlloc : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoaded mplAlloc m
  noExtAlloc3 : LibBlockNoExtern allocMultiLib mplAlloc P 3
  fmtWriteTie :
    allocMultiLib.resolve mplAlloc fmtInnerCoreFmtWriteRawSym =
      coreMultiLib.fnAddr mplCore coreFmtWriteSym

/-- Construct `CliFormatInnerLink` directly from `RustCliAllocBudgetEntriesBase`, `memcpySymWords`,
    and a 1-instruction `ret` `__rust_no_alloc_shim_is_unstable_v2` stub. -/
theorem CliFormatInnerLink.of_entriesBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] (lim : BudgetLimits) {P : Program} {mplCore mplAlloc : MultiPlacement}
    {addrs : RustAllocAddrs}
    (hplCore : coreMultiLib.Placeable mplCore)
    (hclCore : ∀ m, P.CodeLoaded m → coreMultiLib.CodeLoaded mplCore m)
    (hnoExtCore0 : ∀ off : Nat, off < 436 →
      P.externAt? (mplCore.base 0 + BitVec.ofNat 64 off) = none)
    (hplAlloc : allocMultiLib.Placeable mplAlloc)
    (hclAlloc : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoaded mplAlloc m)
    (hnoExt1 : LibBlockNoExtern allocMultiLib mplAlloc P 1)
    (hnoExt2 : LibBlockNoExtern allocMultiLib mplAlloc P 2)
    (hnoExt3 : LibBlockNoExtern allocMultiLib mplAlloc P 3)
    (hnoExt6 : LibBlockNoExtern allocMultiLib mplAlloc P 6)
    (hnoExt7 : LibBlockNoExtern allocMultiLib mplAlloc P 7)
    (hfmtTie : allocMultiLib.resolve mplAlloc fmtInnerCoreFmtWriteRawSym =
      coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (hpanic : P.externAt? (allocMultiLib.resolve mplAlloc allocBudgetHandleErrorSym) =
      some Rust.panicked)
    (hsvc : P.svc = Syscall.standard)
    (hhooks : ∀ m : Memory, P.CodeLoaded m → HooksUnfetched P m)
    (hmemcpyWords : P.hasWords (allocMultiLib.resolve mplAlloc "memcpy") memcpySymWords)
    (hshimInstr : hasInstrs P (allocMultiLib.resolve mplAlloc allocRustNoAllocShimSym) [.ret .x30])
    (hAllocEq : allocMultiLib.resolve mplAlloc allocRustAllocSym = addrs.alloc)
    (hReallocEq : allocMultiLib.resolve mplAlloc allocRustReallocSym = addrs.realloc)
    (hEntries : RustCliAllocBudgetEntriesBase M A P addrs) :
    CliFormatInnerLink M A lim P mplCore mplAlloc where
  toCliFmtWriteLink := CliFmtWriteLink.of_entriesBase lim hplCore hclCore hnoExtCore0 hplAlloc
    (fun m hm => (hclAlloc m hm).toWhere _) hnoExt1 hnoExt2 hnoExt6 hnoExt7 hpanic hsvc hhooks
    hmemcpyWords hshimInstr hAllocEq hReallocEq hEntries
  clAlloc := hclAlloc
  noExtAlloc3 := hnoExt3
  fmtWriteTie := hfmtTie

/-! ## Headline Placed `alloc::fmt::format::format_inner` Specifications & Proofs -/

/-- Tight-stack placed contract for `alloc::fmt::format::format_inner` (`formatInnerFrame + 0x70 +
    stackBytes` stack, with `stringWriterStack ≤ stackBytes`). -/
@[expose] def cliAllocFormatInnerTightSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argBytes : Nat → List (BitVec 8))
    (stackBytes : Nat) (P : Program) :
    Spec (BitVec 64 × Bool × List (BitVec 8) × List (BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (ret, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ FitsEnv M lim st0 Env ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x0) (s.readReg64 .x1) tpl args = some cs ∧
        fmtLiteralLen cs < 2 ^ 60 ∧
        Env (formatInnerKnownEvents (fmtEstimatedCapacity (s.readReg64 .x1) cs)
          (callLens argBytes cs)) ∧
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (knownArgStep argBytes) (knownArgPanic argBytes)
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s cs⌝ ∗
      fmtArgumentsAt argsRo (s.readReg64 .x0) (s.readReg64 .x1) tpl args ∗
      memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
      A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
  post := fun (ret, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs : List (BitVec 8),
      ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          evs = formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (callLens argBytes cs) ∧
          bs = cs.flatMap (callBytes argBytes)⌝ ∗
      vecU8 A.repAlloc ret bs ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim (M.stepEvents evs st0) sf ∗
      stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)

/-- `extHookStack`-framed placed contract for `alloc::fmt::format::format_inner` (`16384` B stack,
    matching `formatInnerBudgetEnvSpec` plus preserved `fmtArgumentsAt`, `stringWriteVtableAt`,
    and `R_client`). -/
@[expose] def cliAllocFormatInnerSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argBytes : Nat → List (BitVec 8))
    (stackBytes : Nat) (P : Program) :
    Spec (BitVec 64 × Bool × List (BitVec 8) × List (BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (ret, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ extHookStack ∧ FitsEnv M lim st0 Env ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x0) (s.readReg64 .x1) tpl args = some cs ∧
        fmtLiteralLen cs < 2 ^ 60 ∧
        Env (formatInnerKnownEvents (fmtEstimatedCapacity (s.readReg64 .x1) cs)
          (callLens argBytes cs)) ∧
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (knownArgStep argBytes) (knownArgPanic argBytes)
          (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s cs⌝ ∗
      fmtArgumentsAt argsRo (s.readReg64 .x0) (s.readReg64 .x1) tpl args ∗
      memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
      A.pool lim st0 s ∗ stackAt s.sp extHookStack
  post := fun (ret, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs : List (BitVec 8),
      ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          evs = formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (callLens argBytes cs) ∧
          bs = cs.flatMap (callBytes argBytes)⌝ ∗
      vecU8 A.repAlloc ret bs ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack

/-- The normal-return postcondition of `cliAllocFormatInnerSpec` directly entails the postcondition
    of `formatInnerBudgetEnvSpec M A lim Env` (plus preserved `fmtArgumentsAt`,
    `stringWriteVtableAt`, and `R_client`, and `AllocCallPreserved s0 sf`). -/
theorem cliAllocFormatInnerSpec_post_entails_budgetEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) [PoolMemTransport A] (lim : BudgetLimits)
    (Env : List AllocEvent → Prop) (va : StringWriteAddrs) (R_client : SepProp)
    (argBytes : Nat → List (BitVec 8)) (stackBytes : Nat) (P : Program)
    (ret : BitVec 64) (argsRo : Bool) (tpl : List (BitVec 8))
    (args : List (BitVec 64 × BitVec 64)) (st0 : M.σ) (s0 sf : State) :
    (cliAllocFormatInnerSpec M A lim Env va R_client argBytes stackBytes P).post
      (ret, argsRo, tpl, args, st0) s0 sf ⊢
    ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      (formatInnerBudgetEnvSpec M A lim Env).post (ret, st0) s0 sf ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      stringWriteVtableAt va ∗ R_client := by
  dsimp only [cliAllocFormatInnerSpec, formatInnerBudgetEnvSpec]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_elim fun bs => ?_
  refine Entails.pure_left fun ⟨hacp, hfs, htr, hEnv, _⟩ => ?_
  refine Entails.pure_right ⟨hacp, hfs⟩ ?_
  have hex : vecU8 A.repAlloc ret bs ⊢ ∃∗ b : List (BitVec 8), vecU8 A.repAlloc ret b :=
    Entails.sepExists_right bs (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hex) ?_
  have hinner :
      (∃∗ b : List (BitVec 8), vecU8 A.repAlloc ret b) ∗
        (fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          (stringWriteVtableAt va ∗ (R_client ∗
            (A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack)))) ⊢
      (⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
        (∃∗ b : List (BitVec 8), vecU8 A.repAlloc ret b) ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp extHookStack) ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗ R_client := by
    rw [pure_sepConj_of_true ⟨htr, hEnv⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans hinner ?_
  exact sepConj_mono_left (Entails.sepExists_right evs (Entails.refl _))

/-- Tight-stack placed correctness of `alloc::fmt::format::format_inner` (`allocMultiLib` block `3`)
    composed with `core::fmt::write` (`coreMultiLib` block `0`) and `<String as fmt::Write>`
    (`allocMultiLib` blocks `1`, `2`, `6`, `7`). -/
theorem cliAllocFormatInner_tight_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      (cliAllocFormatInnerTightSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) := by
  let B := toRustAllocBudget M A lim
  let va := allocStringWriteAddrs mplAlloc
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ret, argsRo, tpl, args, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  have hplaced := allocFormatInnerBudget_placed_ok P B (toRustStdEnv Env) R_client
    (knownArgStep argBytes) (knownArgPanic argBytes) (knownArgOom B st0 argBytes)
    stackBytes mplAlloc L.plAlloc L.clAlloc L.noExtAlloc3 L.noExtAlloc7 L.noExtAlloc1
    L.noExtAlloc2 L.panicHandleErr (L.memcpyAll true) L.allocShim L.rustAlloc L.rustRealloc
    mplCore L.plCore L.clCore L.fmtWriteTie L.noExtCore0
  dsimp only [cliAllocFormatInnerTightSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
        formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ FitsEnv M lim st0 Env ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          fmtLiteralLen cs < 2 ^ 60 ∧
          Env (formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (callLens argBytes cs)) ∧
          FmtInnerBudgetArgsOk P B st0 va R_client (knownArgStep argBytes)
            (knownArgPanic argBytes) (knownArgOom B st0 argBytes) stackBytes s0 cs⌝ ∗
        ((fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
          A.pool lim st0 s0 ∗
          stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx8, hstk1, hstkFit, hFitCli, cs, hdec, hlit, hEnvCs, hArgsOk⟩, hm0⟩
  have hFitB : VerifiedLibraries.RustStd.FitsEnv B st0 (toRustStdEnv Env) :=
    fitsEnv_toRustAllocBudget_of_cli M A lim hFitCli
  have hSafe : VerifiedLibraries.RustStd.FormatInnerBudgetSafe B st0 (toRustStdEnv Env)
      (knownArgStep argBytes) (knownArgPanic argBytes) (knownArgOom B st0 argBytes)
      (s0.readReg64 .x1) cs :=
    knownFmt_safe_of_env M A lim st0 Env argBytes (s0.readReg64 .x1) cs hlit hEnvCs
  have hpreRaw :
      s0.mem ⊨ (allocFormatInnerBudgetSpec P B (toRustStdEnv Env) va R_client
        (knownArgStep argBytes) (knownArgPanic argBytes) (knownArgOom B st0 argBytes)
        stackBytes).pre (ret, argsRo, tpl, args, st0) s0 ∗ R₀ := by
    dsimp only [allocFormatInnerBudgetSpec]
    have hpoolEq : B.pool st0 s0 = A.pool lim st0 s0 := rfl
    rw [hpoolEq, pure_sepConj_of_true ⟨hx8, hstk1, hstkFit, hFitB, cs, hdec, hSafe, hArgsOk⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  refine hplaced.mono_outcome (ret, argsRo, tpl, args, st0) R₀ s0 hpc hrun hpreRaw hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocFormatInnerBudgetSpec] at hpost
    dsimp only [cliAllocFormatInnerTightSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨stF, hpost⟩
    have hpost1 :
        sf.mem ⊨ ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
          toRustStdEnv Env stF.evs ∧
          ∃ cs', ∃ st₀,
            decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs' ∧
            VerifiedLibraries.RustStd.FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs') st₀ ∧
            VerifiedLibraries.RustStd.FmtRun (fmtInnerBudgetStep (knownArgStep argBytes))
              cs' st₀ true stF⌝ ∗
          (((Arm64.Rust.vecHeader ret stF.cap stF.ptr (BitVec.ofNat 64 stF.bytes.length) ∗
            VerifiedLibraries.RustStd.fmtBufVecAt B stF.cap stF.ptr stF.bytes) ∗
            B.pool (B.stepEvents stF.evs st0) sf ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
            stringWriteVtableAt va ∗ R_client ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hio, hfs, htr, hEnvOut, cs', st₀, hdec', hstart, hrunCs⟩, hmf⟩
    have hacp : AllocCallPreserved s0 sf := allocCallPreserved_of_ioCallFrame hio hfs htr
    obtain ⟨_, hshF, hbsF⟩ := run_known hrunCs
    have hsh0 := cliBufShape_of_start hstart
    have hevsEq :
        stF.evs.map toCliAllocEvent =
          formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs')
            (callLens argBytes cs') := by
      have h1 := congrArg CliBufShape.evs hshF
      rw [hsh0] at h1
      exact h1
    have hbsEq : stF.bytes = cs'.flatMap (callBytes argBytes) := by
      rw [hbsF, hstart.1, List.nil_append]
    have hstepEq : B.pool (B.stepEvents stF.evs st0) sf =
        A.pool lim (M.stepEvents (stF.evs.map toCliAllocEvent) st0) sf := by
      rw [toRustAllocBudget_stepEvents M A lim stF.evs st0]
      rfl
    rw [hstepEq] at hmf
    have hmfVec := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left
        (vecHeader_fmtBufVecAt_entails_vecU8 M A lim ret stF.cap stF.ptr stF.bytes))) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmfVec
    refine Entails.sepExists_right (stF.evs.map toCliAllocEvent)
      (Entails.sepExists_right stF.bytes ?_)
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, cs', hdec', hevsEq, hbsEq⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [allocFormatInnerBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact hpan.1.elim
  · dsimp only [allocFormatInnerBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [allocFormatInnerBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-- Headline `extHookStack`-framed placed correctness of `alloc::fmt::format::format_inner`
    (`16384` B stack). -/
theorem cliAllocFormatInner_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      (cliAllocFormatInnerSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) := by
  let va := allocStringWriteAddrs mplAlloc
  let usedStack : Nat := formatInnerFrame + 0x70 + stackBytes
  have htight := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ret, argsRo, tpl, args, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  dsimp only [cliAllocFormatInnerSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
        formatInnerFrame + 0x70 + stackBytes ≤ extHookStack ∧ FitsEnv M lim st0 Env ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          fmtLiteralLen cs < 2 ^ 60 ∧
          Env (formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (callLens argBytes cs)) ∧
          FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
            (knownArgStep argBytes) (knownArgPanic argBytes)
            (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs⌝ ∗
        ((fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp extHookStack) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx8, hstk1, hstkExt, hFit, cs, hdec, hlit, hEnvCs, hArgsOk⟩, hm0⟩
  let remStack : Nat := extHookStack - usedStack
  have hstkSplit :
      stackAt s0.sp extHookStack =
        stackFrameAt s0.sp usedStack ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 usedStack) remStack := by
    rw [stackAt_eq_stackFrameAt s0.sp extHookStack (by decide)]
    conv => lhs; rw [show extHookStack = usedStack + remStack by
      dsimp [remStack, usedStack, extHookStack] at *; omega]
    exact stackFrameAt_split s0.sp usedStack remStack
      (by dsimp [remStack, usedStack, extHookStack] at *; omega)
  let R_frame := stackFrameAt (s0.sp - BitVec.ofNat 64 usedStack) remStack ∗ R₀
  have hpreTight :
      s0.mem ⊨ (cliAllocFormatInnerTightSpec M A lim Env va R_client argBytes stackBytes P).pre
        (ret, argsRo, tpl, args, st0) s0 ∗ R_frame := by
    dsimp only [cliAllocFormatInnerTightSpec, R_frame, usedStack]
    rw [hstkSplit] at hm0
    rw [pure_sepConj_of_true ⟨hx8, hstk1, by dsimp [extHookStack] at hstkExt; omega,
      hFit, cs, hdec, hlit, hEnvCs, hArgsOk⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  refine htight.mono_outcome (ret, argsRo, tpl, args, st0) R_frame s0 hpc hrun hpreTight hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliAllocFormatInnerTightSpec, R_frame] at hpost
    dsimp only [cliAllocFormatInnerSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs', decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs' ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs')
              (callLens argBytes cs') ∧
            bs = cs'.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
            stringWriteVtableAt va ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            (stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) ∗
              stackFrameAt (s0.sp - BitVec.ofNat 64 usedStack) remStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨hpure, hmf⟩
    change sf.mem ⊨
      ((vecU8 A.repAlloc ret bs ∗
        fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
        stringWriteVtableAt va ∗ R_client ∗
        A.pool lim (M.stepEvents evs st0) sf ∗
        (stackFrameAt s0.sp usedStack ∗
          stackFrameAt (s0.sp - BitVec.ofNat 64 usedStack) remStack)) ∗ R₀) at hmf
    rw [← hstkSplit] at hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs (Entails.sepExists_right bs ?_)
    rw [pure_sepConj_of_true hpure]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [cliAllocFormatInnerTightSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact hpan.1.elim
  · dsimp only [cliAllocFormatInnerTightSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [cliAllocFormatInnerTightSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-! ## Concrete CLI Specializations -/

/-! ### 1. Allocation-Event Envelopes & `formatInnerKnownEvents` Reductions -/

/-- Exact allocation-event envelope of `format_inner` on `Arguments::from_str` (`x1` odd):
    `0` allocations when `len = 0`, else a single `rustAllocEvents len 1` (`[.alloc len]`). -/
@[expose] def FormatInnerFromStrEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  evs = if len = 0 then [] else rustAllocEvents len 1

/-- Exact allocation-event envelope of `format_inner` on a short 0-arg static literal (`1 ≤ len ≤ 127`,
    `x1 = 0#64`): initial `String::with_capacity(2 * len)` (`[.alloc (2 * len)]`) with `0` growths. -/
@[expose] def FormatInnerShortLitEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  evs = formatInnerKnownEvents (2 * len) [len]

/-- Exact allocation-event envelope of `format_inner` on a single placeholder `"{}"` (`x1` even):
    initial capacity is `0`, followed by `0` allocations if `argLen = 0` or a single
    `rustAllocEvents (max argLen 8) 1` (`[.alloc (max argLen 8)]`). -/
@[expose] def FormatInnerSingleEnv (argLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = formatInnerKnownEvents 0 [argLen]

/-- Exact allocation-event envelope of `format!("{val}")` for `val : u8` (`[.alloc 8]`). -/
@[expose] def FormatInnerU8Env (v : BitVec 8) (evs : List AllocEvent) : Prop :=
  FormatInnerSingleEnv (formatDecimalNat v.toNat).length evs

/-- Value-independent `u8` `format!("{val}")` envelope (`1..3` digits, always `[.alloc 8]`). -/
@[expose] def FormatInnerAnyU8Env (evs : List AllocEvent) : Prop :=
  ∃ dLen : Nat, 1 ≤ dLen ∧ dLen ≤ 3 ∧ FormatInnerSingleEnv dLen evs

/-- Exact allocation-event envelope of `format!("{val}")` for `val : u32`
    (`[.alloc (max dLen 8)]` where `dLen ∈ [1, 10]`, i.e. `[.alloc 8]`, `[.alloc 9]`, or
    `[.alloc 10]`). -/
@[expose] def FormatInnerU32Env (v : BitVec 32) (evs : List AllocEvent) : Prop :=
  FormatInnerSingleEnv (formatDecimalNat v.toNat).length evs

/-- Value-independent `u32` `format!("{val}")` envelope (`1..10` digits). -/
@[expose] def FormatInnerAnyU32Env (evs : List AllocEvent) : Prop :=
  ∃ dLen : Nat, 1 ≤ dLen ∧ dLen ≤ 10 ∧ FormatInnerSingleEnv dLen evs

/-- Exact allocation-event envelope of `format!("{name}.{dev}")` (`<ProtocolAddress as Display>::fmt`
    invoked from `format_inner`): `fmtEstimatedCapacity` is `0` (`starts_with_placeholder = true` and
    literal length `1 < 16`), followed by appending `[nameLen, 1, devDigits]`. -/
@[expose] def FormatInnerAddrEnv (nameLen devDigits : Nat) (evs : List AllocEvent) : Prop :=
  evs = formatInnerKnownEvents 0 [nameLen, 1, devDigits]

theorem formatInnerKnownEvents_zero_nil :
    formatInnerKnownEvents 0 [] = [] :=
  rfl

theorem formatInnerKnownEvents_zero_singleton (n : Nat) :
    formatInnerKnownEvents 0 [n] =
      if n = 0 then [] else rustAllocEvents (max n 8) 1 := by
  unfold formatInnerKnownEvents startCliBufShape CliBufShape.run List.foldl CliBufShape.append
  have hcap0 : (BitVec.ofNat 64 0).toNat = 0 := by decide
  by_cases hn : n = 0
  · subst hn; simp
  · have hgrow : stringGrowCap 0 0 n = max n 8 := by
      unfold stringGrowCap; omega
    simp [hn, hcap0, hgrow, FmtPlacedObj.stringGrowStepEvents]

theorem formatInnerKnownEvents_fromStr (n : Nat) (hlt : n < 2 ^ 60) :
    formatInnerKnownEvents n [n] =
      if n = 0 then [] else rustAllocEvents n 1 := by
  unfold formatInnerKnownEvents startCliBufShape CliBufShape.run List.foldl CliBufShape.append
  by_cases hn : n = 0
  · subst hn; simp
  · have hmod : n % 18446744073709551616 = n := Nat.mod_eq_of_lt (by omega)
    simp [hn, hmod]

theorem formatInnerU8_events_eq_alloc8 (v : BitVec 8) :
    formatInnerKnownEvents 0 [(formatDecimalNat v.toNat).length] = [.alloc 8] := by
  have ⟨hlo, hhi⟩ := formatDecimalNat_u8_length v
  rw [formatInnerKnownEvents_zero_singleton]
  have hne : (formatDecimalNat v.toNat).length ≠ 0 := by omega
  have hmax : max (formatDecimalNat v.toNat).length 8 = 8 := by omega
  simp [hne, hmax, rustAllocEvents]

theorem formatInnerAnyU8Env_of_u8 (v : BitVec 8) {evs : List AllocEvent}
    (h : FormatInnerU8Env v evs) : FormatInnerAnyU8Env evs :=
  ⟨(formatDecimalNat v.toNat).length, (formatDecimalNat_u8_length v).1,
   (formatDecimalNat_u8_length v).2, h⟩

theorem formatInnerAnyU32Env_of_u32 (v : BitVec 32) {evs : List AllocEvent}
    (h : FormatInnerU32Env v evs) : FormatInnerAnyU32Env evs :=
  ⟨(formatDecimalNat v.toNat).length, (formatDecimalNat_u32_length v).1,
   (formatDecimalNat_u32_length v).2, h⟩

/-! ### 2. 0-Argument Fast Paths (`""`, `Arguments::from_str`, Short Static Literal) -/

/-- Empty-template (`tpl = [0x00#8]`, `x1 = 0#64`) `format_inner` specialization: `0` callbacks,
    `0` heap allocations (`FormatInnerEnv`), tight stack `allocFormatInnerStack = 4448` B. -/
theorem cliAllocFormatInner_empty_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {R_client : SepProp}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (ret x0 : BitVec 64) (argsRo : Bool) (st0 : M.σ) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = 0#64 ∧
            FitsEnv M lim st0 FormatInnerEnv⌝ ∗
          fmtArgumentsAt argsRo x0 0#64 [0x00#8] [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp allocFormatInnerStack
        post := fun () s0 sf =>
          ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗
          vecU8 A.repAlloc ret [] ∗
          fmtArgumentsAt argsRo x0 0#64 [0x00#8] [] ∗
          stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 sf ∗ stackFrameAt s0.sp allocFormatInnerStack } := by
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := FormatInnerEnv) (R_client := R_client)
    (argBytes := fun _ => []) (stackBytes := stringWriterStack) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = 0#64 ∧
        FitsEnv M lim st0 FormatInnerEnv⌝ ∗
        ((fmtArgumentsAt argsRo x0 0#64 [0x00#8] [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp allocFormatInnerStack) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  refine ⟨(ret, argsRo, [0x00#8], [], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hm2 ⊢
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep fun _ => [])
        (knownArgPanic fun _ => [])
        (knownArgOom (toRustAllocBudget M A lim) st0 fun _ => []) stringWriterStack s0 [] :=
      fun _ _ _ _ hmem => False.elim (List.not_mem_nil hmem)
    have hest : fmtEstimatedCapacity 0#64 [] = 0 := by decide
    have hEnv0 : FormatInnerEnv (formatInnerKnownEvents (fmtEstimatedCapacity 0#64 [])
        (callLens (fun _ => []) [])) := by
      rw [hest]; rfl
    rw [pure_sepConj_of_true ⟨hx8, Nat.le_refl _, by decide, hFit,
      [], decodeFmtArguments_empty x0, by decide, hEnv0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hpost ⊢
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
          FormatInnerEnv evs ∧
          ∃ cs, decodeFmtArguments x0 0#64 [0x00#8] [] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity 0#64 cs)
              (callLens (fun _ => []) cs) ∧
            bs = cs.flatMap (callBytes fun _ => [])⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 0#64 [0x00#8] [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stringWriterStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', _, hbs⟩, hmf⟩
    have hcs : cs = [] := Option.some.inj (hdec'.symm.trans (decodeFmtArguments_empty x0))
    subst hcs
    have hevs0 : evs = [] := hEnvOut
    subst hevs0
    simp only [List.flatMap_nil] at hbs
    subst hbs
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf

/-- `Arguments::from_str` (`x1` odd, `litBs.length = (x1 >>> 1).toNat < 2 ^ 60`) `format_inner`
    fast-path specialization (`FormatInnerFromStrEnv litBs.length`, `4448` B stack). -/
theorem cliAllocFormatInner_fromStr_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (ret x0 x1 : BitVec 64) (litBs : List (BitVec 8)) (argsRo : Bool) (st0 : M.σ)
    (hodd : x1.getLsbD 0 = true)
    (hlen : litBs.length = (x1 >>> 1).toNat)
    (hlt : litBs.length < 2 ^ 60)
    (hEnv : ∀ evs, FormatInnerFromStrEnv litBs.length evs → Env evs) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 litBs [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp allocFormatInnerStack
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerFromStrEnv litBs.length evs⌝ ∗
            vecU8 A.repAlloc ret litBs ∗
            fmtArgumentsAt argsRo x0 x1 litBs [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp allocFormatInnerStack } := by
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := fun _ => []) (stackBytes := stringWriterStack) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 litBs [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp allocFormatInnerStack) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall := [FmtCall.writeStr x0 litBs]
  have hdec : decodeFmtArguments x0 x1 litBs [] = some cs0 :=
    decodeFmtArguments_fromStr x0 x1 litBs hodd hlen
  have hest : fmtEstimatedCapacity x1 cs0 = litBs.length := by
    simp [cs0, fmtEstimatedCapacity, hodd, fmtLiteralLen]
  have hlit : fmtLiteralLen cs0 < 2 ^ 60 := by
    simpa [cs0, fmtLiteralLen] using hlt
  have hFrom0 : FormatInnerFromStrEnv litBs.length
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens (fun _ => []) cs0)) := by
    unfold FormatInnerFromStrEnv
    simp only [hest, cs0, callLens, List.map_cons, List.map_nil, callBytes]
    exact formatInnerKnownEvents_fromStr litBs.length hlt
  refine ⟨(ret, argsRo, litBs, [], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hm2 ⊢
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep fun _ => [])
        (knownArgPanic fun _ => [])
        (knownArgOom (toRustAllocBudget M A lim) st0 fun _ => []) stringWriterStack s0 cs0 := by
      intro _ _ _ _ hmem
      simp [cs0] at hmem
    rw [pure_sepConj_of_true ⟨hx8, Nat.le_refl _, by decide, hFit,
      cs0, hdec, hlit, hEnv _ hFrom0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hpost ⊢
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 litBs [] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs)
              (callLens (fun _ => []) cs) ∧
            bs = cs.flatMap (callBytes fun _ => [])⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 litBs [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stringWriterStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hbsEq : bs = litBs := by simp [cs0, callBytes] at hbs; exact hbs
    rw [hbsEq] at hmf
    have hFrom : FormatInnerFromStrEnv litBs.length evs := by rw [hevs]; exact hFrom0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hFrom⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 3. Single-Argument `Display::fmt` (`u8`, `u32`, `&str`) -/

/-- Single-argument `<u8 as Display>::fmt` (`tpl = [0xc0#8, 0x00#8]`, `x1` even) `format_inner`
    specialization (`FormatInnerU8Env val`, `[.alloc 8]`, stack `4448 + 192 = 4640 ≤ 16384` B). -/
theorem cliAllocFormatInner_u8Display_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mplFmt m)
    (ret x0 x1 valPtr : BitVec 64) (argsRo valRo : Bool) (val : BitVec 8) (st0 : M.σ)
    (heven : x1.getLsbD 0 = false)
    (hEnv : ∀ evs, FormatInnerU8Env val evs → Env evs)
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let u8Fn := coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
    let R_client :=
      (fmtRef8 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerU8Env val evs⌝ ∗
            vecU8 A.repAlloc ret (formatDecimalNat val.toNat) ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro u8Fn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall := [FmtCall.fmtArg 0 valPtr u8Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] = some cs0 :=
    decodeFmtArguments_single_even x0 x1 valPtr u8Fn heven
  have hest : fmtEstimatedCapacity x1 cs0 = 0 := by
    simp [cs0, fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen]
  have hU8_0 : FormatInnerU8Env val
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens argBytes cs0)) := by
    unfold FormatInnerU8Env FormatInnerSingleEnv
    simp [hest, cs0, callLens, callBytes, argBytes]
  refine ⟨(ret, argsRo, [0xc0#8, 0x00#8], [(valPtr, u8Fn)], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec]
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliU8Display_fmtArg_ok L.toCliFmtWriteLink hplFmt hextFmt hclFmt st0 R_rest argBytes
        s0 stringWriterStack stackBytes 0 out valPtr valRo val rfl ⟨Nat.le_refl _, by decide⟩
        hstk.1
    rw [pure_sepConj_of_true ⟨hx8, by omega, hstk.2, hFit, cs0, hdec,
      by simp [cs0, fmtLiteralLen], hEnv _ hU8_0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) ∧
            bs = cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hbsEq : bs = formatDecimalNat val.toNat := by
      simp [cs0, callBytes, argBytes] at hbs; exact hbs
    subst hbsEq
    have hU8 : FormatInnerU8Env val evs := by rw [hevs]; exact hU8_0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hU8⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Single-argument `<u32 as Display>::fmt` (`tpl = [0xc0#8, 0x00#8]`, `x1` even) `format_inner`
    specialization (`FormatInnerU32Env val`, stack `4448 + 192 = 4640 ≤ 16384` B). -/
theorem cliAllocFormatInner_u32Display_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mplFmt m)
    (ret x0 x1 valPtr : BitVec 64) (argsRo valRo : Bool) (val : BitVec 32) (st0 : M.σ)
    (heven : x1.getLsbD 0 = false)
    (hEnv : ∀ evs, FormatInnerU32Env val evs → Env evs)
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let u32Fn := coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym
    let R_client :=
      (fmtRef32 valRo valPtr val ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerU32Env val evs⌝ ∗
            vecU8 A.repAlloc ret (formatDecimalNat val.toNat) ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro u32Fn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => formatDecimalNat val.toNat
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall := [FmtCall.fmtArg 0 valPtr u32Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] = some cs0 :=
    decodeFmtArguments_single_even x0 x1 valPtr u32Fn heven
  have hest : fmtEstimatedCapacity x1 cs0 = 0 := by
    simp [cs0, fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen]
  have hU32_0 : FormatInnerU32Env val
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens argBytes cs0)) := by
    unfold FormatInnerU32Env FormatInnerSingleEnv
    simp [hest, cs0, callLens, callBytes, argBytes]
  refine ⟨(ret, argsRo, [0xc0#8, 0x00#8], [(valPtr, u32Fn)], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec]
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliU32Display_fmtArg_ok L.toCliFmtWriteLink hplFmt hextFmt hclFmt st0 R_rest argBytes
        s0 stringWriterStack stackBytes 0 out valPtr valRo val rfl ⟨Nat.le_refl _, by decide⟩
        hstk.1
    rw [pure_sepConj_of_true ⟨hx8, by omega, hstk.2, hFit, cs0, hdec,
      by simp [cs0, fmtLiteralLen], hEnv _ hU32_0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) ∧
            bs = cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hbsEq : bs = formatDecimalNat val.toNat := by
      simp [cs0, callBytes, argBytes] at hbs; exact hbs
    subst hbsEq
    have hU32 : FormatInnerU32Env val evs := by rw [hevs]; exact hU32_0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hU32⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Single-argument `<&str as Display>::fmt` (`tpl = [0xc0#8, 0x00#8]`, `x1` even) `format_inner`
    specialization (`FormatInnerSingleEnv sbs.length`, stack `4448` B). -/
theorem cliAllocFormatInner_strRefDisplay_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (hplFmt : coreFmtMultiLib.Placeable mplFmt)
    (hextFmt : LibKeepNoExtern coreFmtMultiLib strRefDisplayKeep mplFmt P)
    (hclFmt : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere strRefDisplayKeep mplFmt m)
    (ret x0 x1 valPtr strPtr : BitVec 64) (sbs : List (BitVec 8))
    (argsRo refRo srcRo : Bool) (st0 : M.σ)
    (heven : x1.getLsbD 0 = false)
    (hlen : sbs.length < 2 ^ 60)
    (hEnv : ∀ evs, FormatInnerSingleEnv sbs.length evs → Env evs)
    (hstk : stringWriterStack ≤ stackBytes ∧ formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let strFn := coreFmtMultiLib.fnAddr mplFmt strRefDisplayFmtSym
    let R_client :=
      fmtRefStr refRo valPtr strPtr (BitVec.ofNat 64 sbs.length) ∗
        fmtSrcBytes srcRo strPtr sbs ∗ R_rest
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerSingleEnv sbs.length evs⌝ ∗
            vecU8 A.repAlloc ret sbs ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro strFn R_client
  let argBytes : Nat → List (BitVec 8) := fun _ => sbs
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall := [FmtCall.fmtArg 0 valPtr strFn defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] = some cs0 :=
    decodeFmtArguments_single_even x0 x1 valPtr strFn heven
  have hest : fmtEstimatedCapacity x1 cs0 = 0 := by
    simp [cs0, fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen]
  have hSingle0 : FormatInnerSingleEnv sbs.length
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens argBytes cs0)) := by
    unfold FormatInnerSingleEnv
    simp [hest, cs0, callLens, callBytes, argBytes]
  refine ⟨(ret, argsRo, [0xc0#8, 0x00#8], [(valPtr, strFn)], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec]
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_singleton, FmtCall.fmtArg.injEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩
      rw [hval, hfn, hopts]
      exact cliStrRefDisplay_coreFmt_fmtArg_ok L.toCliFmtWriteLink hplFmt hextFmt hclFmt st0
        R_client R_rest argBytes s0 stringWriterStack stackBytes 0 out valPtr strPtr refRo srcRo
        sbs hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk.1 rfl
    rw [pure_sepConj_of_true ⟨hx8, hstk.1, hstk.2, hFit, cs0, hdec,
      by simp [cs0, fmtLiteralLen], hEnv _ hSingle0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) ∧
            bs = cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 [0xc0#8, 0x00#8] [(valPtr, strFn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hbsEq : bs = sbs := by simp [cs0, callBytes, argBytes] at hbs; exact hbs
    rw [hbsEq] at hmf
    have hSingle : FormatInnerSingleEnv sbs.length evs := by rw [hevs]; exact hSingle0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hSingle⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 4. Short Static Literal & Two-Argument `"{}.{}"` (`<ProtocolAddress as Display>::fmt`) -/

/-- Short 0-arg static literal (`1 ≤ litBs.length ≤ 127`, `x1 = 0#64`) `format_inner`
    specialization (`FormatInnerShortLitEnv litBs.length`, stack `4448` B). -/
theorem cliAllocFormatInner_lit0_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (ret x0 : BitVec 64) (litBs : List (BitVec 8)) (argsRo : Bool) (st0 : M.σ)
    (hlo : 1 ≤ litBs.length) (hhi : litBs.length ≤ 127)
    (hEnv : ∀ evs, FormatInnerShortLitEnv litBs.length evs → Env evs) :
    let tpl := [BitVec.ofNat 8 litBs.length] ++ litBs ++ [0x00#8]
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = 0#64 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 0#64 tpl [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp allocFormatInnerStack
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerShortLitEnv litBs.length evs⌝ ∗
            vecU8 A.repAlloc ret litBs ∗
            fmtArgumentsAt argsRo x0 0#64 tpl [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackFrameAt s0.sp allocFormatInnerStack } := by
  intro tpl
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := fun _ => []) (stackBytes := stringWriterStack) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = 0#64 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 0#64 tpl [] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp allocFormatInnerStack) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall := [FmtCall.writeStr (x0 + 1#64) litBs]
  have hdec : decodeFmtArguments x0 0#64 tpl [] = some cs0 :=
    decodeFmtArguments_shortLiteral x0 hlo hhi
  have hest : fmtEstimatedCapacity 0#64 cs0 = 2 * litBs.length := by
    have h0_even : (0#64 : BitVec 64).getLsbD 0 = false := by decide
    have hstart : fmtStartsWithPlaceholder cs0 = false := by
      simp [cs0, fmtStartsWithPlaceholder]
    have hlitEq : fmtLiteralLen cs0 = litBs.length := by
      simp [cs0, fmtLiteralLen]
    simp only [fmtEstimatedCapacity, h0_even, Bool.false_eq_true, ↓reduceIte, hstart,
      Bool.false_and, hlitEq]
    exact Nat.mod_eq_of_lt (by omega)
  have hlit : fmtLiteralLen cs0 < 2 ^ 60 := by
    simp only [cs0, fmtLiteralLen]; omega
  have hLit0 : FormatInnerShortLitEnv litBs.length
      (formatInnerKnownEvents (fmtEstimatedCapacity 0#64 cs0) (callLens (fun _ => []) cs0)) := by
    unfold FormatInnerShortLitEnv
    simp [hest, cs0, callLens, callBytes]
  refine ⟨(ret, argsRo, tpl, [], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hm2 ⊢
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep fun _ => [])
        (knownArgPanic fun _ => [])
        (knownArgOom (toRustAllocBudget M A lim) st0 fun _ => []) stringWriterStack s0 cs0 := by
      intro _ _ _ _ hmem
      simp [cs0] at hmem
    rw [pure_sepConj_of_true ⟨hx8, Nat.le_refl _, by decide, hFit,
      cs0, hdec, hlit, hEnv _ hLit0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec, allocFormatInnerStack] at hpost ⊢
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 0#64 tpl [] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity 0#64 cs)
              (callLens (fun _ => []) cs) ∧
            bs = cs.flatMap (callBytes fun _ => [])⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 0#64 tpl [] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stringWriterStack)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hbsEq : bs = litBs := by simp [cs0, callBytes] at hbs; exact hbs
    rw [hbsEq] at hmf
    have hLit : FormatInnerShortLitEnv litBs.length evs := by rw [hevs]; exact hLit0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hLit⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Two-argument `"{}.{}"` (`tpl = [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]`) `String` + `u8`
    `alloc::fmt::format::format_inner` composition (`<ProtocolAddress as Display>::fmt` with `u8`
    device ID; peak stack `formatInnerFrame + 0x70 + 192 + stringWriterStack = 4640 ≤ extHookStack`). -/
theorem cliAllocFormatInner_dottedStringU8_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
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
    (ret x0 x1 namePtr nameCap nameDataPtr strFn devPtr : BitVec 64)
    (nameBs : List (BitVec 8))
    (argsRo strRefRo strSrcRo devRo : Bool) (dev : BitVec 8) (st0 : M.σ)
    (hstrEntry : strFn = mplShim.base bi)
    (heven : x1.getLsbD 0 = false)
    (hlen : nameBs.length < 2 ^ 60)
    (hEnv : ∀ evs,
      FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs → Env evs)
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let u8Fn := coreFmtMultiLib.fnAddr mplFmt u8DisplayFmtSym
    let F_str := fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
      fmtSrcBytes strSrcRo nameDataPtr nameBs
    let F_dev := fmtRef8 devRo devPtr dev ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)
    let R_client := F_str ∗ F_dev ∗ R_rest
    let dotTpl : List (BitVec 8) := [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs⌝ ∗
            vecU8 A.repAlloc ret (nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat) ∗
            fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro u8Fn F_str F_dev R_client dotTpl
  let argBytes : Nat → List (BitVec 8) :=
    fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall :=
    [FmtCall.fmtArg 0 namePtr strFn defaultFmtOptions,
     FmtCall.writeStr (x0 + 2#64) [0x2e#8],
     FmtCall.fmtArg 1 devPtr u8Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] = some cs0 :=
    decodeFmtArguments_dotted_even x0 x1 namePtr strFn devPtr u8Fn heven
  have hest : fmtEstimatedCapacity x1 cs0 = 0 := by
    unfold fmtEstimatedCapacity
    rw [heven]
    simp [cs0, fmtStartsWithPlaceholder, fmtLiteralLen]
  have hAddr0 : FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens argBytes cs0)) := by
    unfold FormatInnerAddrEnv
    simp [hest, cs0, callLens, callBytes, argBytes]
  have hstk1 : stringWriterStack ≤ stackBytes := by omega
  refine ⟨(ret, argsRo, dotTpl, [(namePtr, strFn), (devPtr, u8Fn)], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec]
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_cons, List.not_mem_nil, or_false, false_or, FmtCall.fmtArg.injEq,
        reduceCtorEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩ | ⟨rfl, hval, hfn, hopts⟩
      · rw [hval, hfn, hopts]
        exact cliStringDisplayShim_fmtArg_ok L.toCliFmtWriteLink hplFmt hextStrFmt hclStrFmt
          hplShim bi hkeep hshim hextShim hclShim htarget st0 R_client (F_dev ∗ R_rest) argBytes s0
          stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr strFn
          strRefRo strSrcRo nameBs hstrEntry hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk1
          (by dsimp only [R_client, F_str]; sep_ac_rfl)
      · rw [hval, hfn, hopts]
        have hw := cliStringBudgetFmtWriterOk L.toCliFmtWriteLink st0 (F_str ∗ R_rest) s0
          stringWriterStack out ⟨Nat.le_refl _, by decide⟩
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
    rw [pure_sepConj_of_true ⟨hx8, hstk1, hstk.2, hFit, cs0, hdec,
      by simp [cs0, fmtLiteralLen], hEnv _ hAddr0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) ∧
            bs = cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u8Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [cs0, callBytes, argBytes, ↓reduceIte, Nat.one_ne_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hbs
    have hbsEq : bs = nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat := by
      rw [hbs]; simp only [List.append_assoc]
    subst hbsEq
    have hAddr : FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs := by
      rw [hevs]; exact hAddr0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hAddr⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Two-argument `"{}.{}"` (`tpl = [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]`) `String` + `u32`
    `alloc::fmt::format::format_inner` composition (`<ProtocolAddress as Display>::fmt` when
    `DeviceId` wraps `u32`; peak stack `4640 ≤ extHookStack` B). -/
theorem cliAllocFormatInner_dottedStringU32_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {lib : MultiPlacedLib} {keep : Nat → Bool}
    {mplCore mplAlloc mplFmt mplShim : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
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
    (ret x0 x1 namePtr nameCap nameDataPtr strFn devPtr : BitVec 64)
    (nameBs : List (BitVec 8))
    (argsRo strRefRo strSrcRo devRo : Bool) (dev : BitVec 32) (st0 : M.σ)
    (hstrEntry : strFn = mplShim.base bi)
    (heven : x1.getLsbD 0 = false)
    (hlen : nameBs.length < 2 ^ 60)
    (hEnv : ∀ evs,
      FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs → Env evs)
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let u32Fn := coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym
    let F_str := fmtRefString strRefRo namePtr nameCap nameDataPtr (BitVec.ofNat 64 nameBs.length) ∗
      fmtSrcBytes strSrcRo nameDataPtr nameBs
    let F_dev := fmtRef32 devRo devPtr dev ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)
    let R_client := F_str ∗ F_dev ∗ R_rest
    let dotTpl : List (BitVec 8) := [0xc0#8, 0x01#8, 0x2e#8, 0xc0#8, 0x00#8]
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env⌝ ∗
          fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs⌝ ∗
            vecU8 A.repAlloc ret (nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat) ∗
            fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro u32Fn F_str F_dev R_client dotTpl
  let argBytes : Nat → List (BitVec 8) :=
    fun i => if i = 0 then nameBs else formatDecimalNat dev.toNat
  have hbase := cliAllocFormatInner_tight_placed_ok (Env := Env) (R_client := R_client)
    (argBytes := argBytes) (stackBytes := stackBytes) L
  refine subroutine_ok_refine hbase fun () R₀ s0 hm => ?_
  dsimp only at hm
  have hm1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm1
  rcases hm1 with ⟨⟨hx8, hx0, hx1, hFit⟩, hm2⟩
  let cs0 : List FmtCall :=
    [FmtCall.fmtArg 0 namePtr strFn defaultFmtOptions,
     FmtCall.writeStr (x0 + 2#64) [0x2e#8],
     FmtCall.fmtArg 1 devPtr u32Fn defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] = some cs0 :=
    decodeFmtArguments_dotted_even x0 x1 namePtr strFn devPtr u32Fn heven
  have hest : fmtEstimatedCapacity x1 cs0 = 0 := by
    unfold fmtEstimatedCapacity
    rw [heven]
    simp [cs0, fmtStartsWithPlaceholder, fmtLiteralLen]
  have hAddr0 : FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length
      (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (callLens argBytes cs0)) := by
    unfold FormatInnerAddrEnv
    simp [hest, cs0, callLens, callBytes, argBytes]
  have hstk1 : stringWriterStack ≤ stackBytes := by omega
  refine ⟨(ret, argsRo, dotTpl, [(namePtr, strFn), (devPtr, u32Fn)], st0), ?_, fun sf hpost => ?_⟩
  · dsimp only [cliAllocFormatInnerTightSpec]
    rw [hx0, hx1]
    have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
        (allocStringWriteAddrs mplAlloc) R_client (knownArgStep argBytes)
        (knownArgPanic argBytes)
        (knownArgOom (toRustAllocBudget M A lim) st0 argBytes) stackBytes s0 cs0 := by
      intro idx value fmtFn opts hmem out
      simp only [cs0, List.mem_cons, List.not_mem_nil, or_false, false_or, FmtCall.fmtArg.injEq,
        reduceCtorEq] at hmem
      rcases hmem with ⟨rfl, hval, hfn, hopts⟩ | ⟨rfl, hval, hfn, hopts⟩
      · rw [hval, hfn, hopts]
        exact cliStringDisplayShim_fmtArg_ok L.toCliFmtWriteLink hplFmt hextStrFmt hclStrFmt
          hplShim bi hkeep hshim hextShim hclShim htarget st0 R_client (F_dev ∗ R_rest) argBytes s0
          stringWriterStack stackBytes 0 out namePtr nameCap nameDataPtr strFn
          strRefRo strSrcRo nameBs hstrEntry hlen rfl ⟨Nat.le_refl _, by decide⟩ hstk1
          (by dsimp only [R_client, F_str]; sep_ac_rfl)
      · rw [hval, hfn, hopts]
        have hw := cliStringBudgetFmtWriterOk L.toCliFmtWriteLink st0 (F_str ∗ R_rest) s0
          stringWriterStack out ⟨Nat.le_refl _, by decide⟩
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
    rw [pure_sepConj_of_true ⟨hx8, hstk1, hstk.2, hFit, cs0, hdec,
      by simp [cs0, fmtLiteralLen], hEnv _ hAddr0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  · dsimp only [cliAllocFormatInnerTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (callLens argBytes cs) ∧
            bs = cs.flatMap (callBytes argBytes)⌝ ∗
          ((vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 dotTpl [(namePtr, strFn), (devPtr, u32Fn)] ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_client ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf⟩
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    simp only [cs0, callBytes, argBytes, ↓reduceIte, Nat.one_ne_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hbs
    have hbsEq : bs = nameBs ++ [0x2e#8] ++ formatDecimalNat dev.toNat := by
      rw [hbs]; simp only [List.append_assoc]
    subst hbsEq
    have hAddr : FormatInnerAddrEnv nameBs.length (formatDecimalNat dev.toNat).length evs := by
      rw [hevs]; exact hAddr0
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hAddr⟩]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ### 5. 1- and 2-Hop Linker-Alias Stubs at `lsFormatInnerSym` -/

/-- Lift `cliAllocFormatInner_placed_ok` across a 1-instruction `b` linker-alias stub
    (e.g. `lsFormatInnerSym` → `allocFormatInnerSym`). -/
theorem cliAllocFormatInner_alias_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    {aliasAddr : BitVec 64}
    (hstub : hasInstrs P aliasAddr
      [.b (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym - aliasAddr)]) :
    subroutine_ok P aliasAddr
      (cliAllocFormatInnerSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub aliasAddr (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym) hstub
    (by
      rintro ⟨_, _, _, _, st0⟩ s pc'
      dsimp only [cliAllocFormatInnerSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliAllocFormatInner_placed_ok L)

/-- Lift `cliAllocFormatInner_placed_ok` across a 2-hop `b` linker-alias chain
    (`snapstubAddr → aliasAddr → allocFormatInnerSym`). -/
theorem cliAllocFormatInner_alias2_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    {snapstubAddr aliasAddr : BitVec 64}
    (hSnap : hasInstrs P snapstubAddr [.b (aliasAddr - snapstubAddr)])
    (hAlias : hasInstrs P aliasAddr
      [.b (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym - aliasAddr)]) :
    subroutine_ok P snapstubAddr
      (cliAllocFormatInnerSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub2 snapstubAddr aliasAddr
    (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym) hSnap hAlias
    (by
      rintro ⟨_, _, _, _, st0⟩ s pc'
      dsimp only [cliAllocFormatInnerSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliAllocFormatInner_placed_ok L)

/-- `WordTree` (`checkBranchStub2`) variant of `cliAllocFormatInner_alias2_ok` for `LinkedImage`
    proofs. -/
theorem cliAllocFormatInner_alias2_wordTree_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argBytes : Nat → List (BitVec 8)} {stackBytes : Nat}
    {P : Program} {t : WordTree} (n : Nat) {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc)
    (snapstubAddr aliasAddr : BitVec 64)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr
      (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym) = true) :
    subroutine_ok P snapstubAddr
      (cliAllocFormatInnerSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argBytes stackBytes P) :=
  subroutine_ok_of_branchStub2_wordTree n snapstubAddr aliasAddr
    (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym) hcode hwf hhookSnap hhookAlias hok
    (by
      rintro ⟨_, _, _, _, st0⟩ s pc'
      dsimp only [cliAllocFormatInnerSpec]
      simp only [pool_of_setPC]
      cases s; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (by intros; rfl)
    (by intro _ s0 _ _; cases s0; rfl)
    (cliAllocFormatInner_placed_ok L)

end LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
