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
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.PadIntegralPrefix
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteProof
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag -- proof-setup: allow-public-import
public import GeneratedLean.LibsignalSessionPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Placed.GenLsBlockFast
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import GeneratedLean.LibsignalSessionPlacedObjShard19

/-!
# Multi-Piece `format_inner` Algebra & Placed Sub-Formatters for `<spqr::Error as Display>::fmt`

Auxiliary foundation for real-code `<spqr::Error as core::fmt::Display>::fmt` (`libsignalSessionLib`
Block `412`) on the 0-hook CLI placed-budget path:

1. **Multi-Piece `FmtBuf` Algebra (`StringBufAppendMany`, `manyFmt_safe_of_env`,
   `cliAllocFormatInnerMany_placed_ok`, `formatInnerKnownEvents_coalesce_prefixed`):**
   Handles nested `core::fmt::write` callbacks (`<&EncodingError as Display>::fmt` in Block `392`
   and 7 arms of `<spqr::Error as Display>::fmt` in Block `412`) that append multiple slices
   `[p₁, p₂, ...]` onto an arbitrary `st : FmtBuf`, and proves that for any literal prefix of
   `24..40` bytes (`cap0 = 2 * prefixLen`), all `1..5` pieces emitted by `spqr::Error` (total
   `14..71` bytes) coalesce into `formatInnerKnownEvents (2 * prefixLen) [prefixLen, total]` inside
   `FormatInnerPrefixedEnv` (`CliFormatInnerEnv` unchanged).
2. **By-Name `.rodata` Bundle (`spqrErrorRoSep`) & Pure Output Piece Spec (`spqrErrorPieces`):**
   Packages all `22` `spqr:.rodata.*` objects referenced by Blocks `412, 392, 393, 394` with
   kernel-checked `lsroCheck` discharge from `LibsignalRoLoaded lsmpl` and 0 raw layout offsets.
3. **Placed Sub-Formatter Proofs (`Blocks 396, 397, 394, 393, 392`):**
   Relocatable `[LibsignalPlacement]` `fmtArgCallSpec` contracts for `<&u32 as Display>::fmt`
   (`396`), `<&u64 as Display>::fmt` (`397`), `<&PolynomialError as Display>::fmt` (`394`),
   `<&serialize::Error as Display>::fmt` (`393`), and `<&EncodingError as Display>::fmt` (`392`).
-/

set_option autoImplicit false
set_option maxRecDepth 2000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic SepProp
open ProofLib.AsciiNum
  (formatDecimalNat_div_10000 formatDecimalNat_of_1000_lt_10000
   formatDecimalNat_of_lt_10 formatDecimalNat_three_digits formatDecimalNat_two_digits
   fourDecimalDigits_length)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement LibsignalRoLoaded libsignalSessionLib
   libsignalSessionLib_blocks_length ls_resolve_data_ultra lsroCheck lsro_intro_chk lsmpl)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (CliBufShape PoolMemTransport allocCallPreserved_of_ioCallFrame callBytes cliBufShapeOf
   cliBufShape_append cliBufShape_of_start cliBufShape_run_append cliBufShape_run_cons
   cliBufShape_run_evs_prefix fitsEnv_toRustAllocBudget_of_cli formatInnerKnownEvents
   knownArgOom knownArgPanic knownArgStep lsFmtWriteSym map_stringAppendEvents_eq_cliBufShape
   map_toCliAllocEvent_ofCliAllocEvent not_appendPanics_of_fits ofCliAllocEvent startCliBufShape
   stringGrowStepEvents toCliAllocEvent toRustAllocBudget toRustAllocBudget_fitsEvents
   toRustAllocBudget_stepEvents toRustStdEnv vecHeader_fmtBufVecAt_entails_vecU8)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof
  (CliFmtWriteLink cliStringBudgetFmtWriterOk cliStringBudgetWriteStrCall_ok
   cliU32Display_fmtArg_ok cliU64Display_fmtArg_ok formatDecimalNat_u32_length
   stringWriteVtableAt_dup_writeStr)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
  (CliFormatInnerLink)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFormatInnerEnv FormatInnerPrefixedEnv cliFormatInnerEnv_iff)
open VerifiedLibraries.RustStd
  (FmtBuf FmtBufStart FmtCall FmtCallbacks FmtInnerBudgetArgsOk FmtOptions FmtReaches FmtRun
   FmtWriteFrame FormatInnerBudgetSafe IoCallFrame RustAllocBudget StringBufAppend
   StringBufAppendPanics StringWriteAddrs allocFormatInnerBudgetSpec allocFormatInnerBudget_placed_ok
   allocFormatInnerSym allocMultiLib allocStringWriteAddrs call_wpp_where
   coreFmtDecDigitsLutSym coreFmtMultiLib coreFmtWriteSpec coreFmtWriteSym coreFmtWrite_ok
   coreMultiLib decDigitsLutBytes decodeFmtArguments defaultFmtOptions fmtArgCallSpec
   fmtArgEntriesAt fmtArgumentsAt fmtBufVecAt fmtEstimatedCapacity fmtInnerBudgetOom
   fmtInnerBudgetPanic fmtInnerBudgetStep fmtInnerBudgetW fmtLiteralLen fmtRef32 fmtRef64
   fmtSrcBytes fmtWriteFrame_of_pureSeg formatInnerFrame formatterAt formatterWriteStrSpec
   formatterWriteStrSym formatterWriteStr_ok stringAppendEvents stringGrowCap stringWriteVtableAt
   stringWriterStack subroutine_ok_drop_codeLoadedWhere u32DisplayFmtSym u64DisplayFmtSym)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern PureSegPreserved
   sepWPp_seg_lib_block_pureWhere u32DisplayKeep u64DisplayKeep writeStrKeep)

/-! ## 1. `u64` Decimal Length Bounds & Alignment Helpers -/

private theorem formatDecimalNat_len_le_of_lt_pow {m k : Nat} (hk : 1 ≤ k)
    (hm : m < 10000 ^ k) :
    1 ≤ (formatDecimalNat m).length ∧ (formatDecimalNat m).length ≤ 4 * k := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
    by_cases hlt : m < 10000
    · by_cases h1 : m < 10
      · rw [formatDecimalNat_of_lt_10 h1]; simp; omega
      · by_cases h2 : m < 100
        · rw [formatDecimalNat_two_digits (by omega) h2]; simp; omega
        · by_cases h3 : m < 1000
          · rw [formatDecimalNat_three_digits (by omega) h3]; simp; omega
          · rw [formatDecimalNat_of_1000_lt_10000 (by omega) hlt]; simp
    · cases k with
      | zero => simp at hm; omega
      | succ k' =>
        rw [formatDecimalNat_div_10000 (by omega), List.length_append, fourDecimalDigits_length]
        have hdiv : m / 10000 < 10000 ^ (k' + 1) := by
          rw [Nat.pow_succ] at hm
          exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hm)
        have ⟨hlo, hhi⟩ := ih (by omega) hdiv
        omega

/-- Decimal digit length bounds for `u64` (`1 ≤ len ≤ 20`). -/
theorem formatDecimalNat_u64_length (v : BitVec 64) :
    1 ≤ (formatDecimalNat v.toNat).length ∧ (formatDecimalNat v.toNat).length ≤ 20 := by
  have hv : v.toNat < 10000 ^ 5 := Nat.lt_trans v.isLt (by decide)
  exact formatDecimalNat_len_le_of_lt_pow (k := 5) (by decide) hv

/-- Subtracting any multiple of `16` preserves `State.spAligned` (`sp &&& 15#64 = 0#64`). -/
theorem spAligned_sub_16k {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true)
    (k : Nat) (hk : k % 16 = 0) (hklt : k < 2 ^ 64 := by omega) :
    ((sp0 - BitVec.ofNat 64 k) &&& 15#64 == 0#64) = true := by
  rw [beq_iff_eq] at h ⊢
  have h0 : (sp0 &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  have hm2 : ((sp0 - BitVec.ofNat 64 k) &&& 15#64).toNat =
      (sp0 - BitVec.ofNat 64 k).toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod (sp0 - BitVec.ofNat 64 k).toNat 4
  rw [hm1] at h0
  apply BitVec.eq_of_toNat_eq
  rw [hm2, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt, BitVec.toNat_ofNat]
  have := sp0.isLt
  omega

/-- Subtracting any even offset from a 16-byte aligned `sp0` yields an even pointer
    (`getLsbD 0 = false`), so `decodeFmtArguments` takes the bytecode-template branch. -/
theorem getLsbD0_sub_even_of_spAligned {sp0 : BitVec 64}
    (h : (sp0 &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 2 = 0)
    (hklt : k < 2 ^ 64 := by omega) :
    (sp0 - BitVec.ofNat 64 k).getLsbD 0 = false := by
  rw [beq_iff_eq] at h
  have h0 : (sp0 &&& 15#64).toNat = 0 := by rw [h]; rfl
  have hm1 : (sp0 &&& 15#64).toNat = sp0.toNat % 16 :=
    Nat.and_two_pow_sub_one_eq_mod sp0.toNat 4
  rw [hm1] at h0
  have hk_toNat : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]; omega
  have hmod2 : (sp0 - BitVec.ofNat 64 k).toNat % 2 = 0 := by
    rw [BitVec.toNat_sub, hk_toNat]
    have := sp0.isLt
    omega
  rw [Bool.eq_false_iff]
  intro ht
  change (sp0 - BitVec.ofNat 64 k).toNat.testBit 0 = true at ht
  simp only [Nat.testBit_zero, decide_eq_true_eq] at ht
  omega

/-! ## 2. Multi-Piece `StringBufAppendMany` Algebra & Coalescing -/

/-- Sequential `StringBufAppend` of zero or more byte slices onto a `FmtBuf`. -/
inductive StringBufAppendMany : FmtBuf → List (List (BitVec 8)) → FmtBuf → Prop
  | nil (st : FmtBuf) : StringBufAppendMany st [] st
  | cons {st st1 st2 : FmtBuf} {p : List (BitVec 8)} {ps : List (List (BitVec 8))} :
      StringBufAppend st p st1 → StringBufAppendMany st1 ps st2 →
      StringBufAppendMany st (p :: ps) st2

theorem appendMany_append {st st1 st2 : FmtBuf} {ps1 ps2 : List (List (BitVec 8))}
    (h1 : StringBufAppendMany st ps1 st1) (h2 : StringBufAppendMany st1 ps2 st2) :
    StringBufAppendMany st (ps1 ++ ps2) st2 := by
  induction h1 with
  | nil _ => exact h2
  | cons hp _ ih => exact .cons hp (ih h2)

theorem appendMany_singleton_iff {st st' : FmtBuf} {bs : List (BitVec 8)} :
    StringBufAppendMany st [bs] st' ↔ StringBufAppend st bs st' := by
  constructor
  · intro h
    cases h with
    | cons hp hnil =>
      cases hnil
      exact hp
  · exact fun h => .cons h (.nil _)

theorem cliBufShape_appendMany {st st' : FmtBuf} {ps : List (List (BitVec 8))}
    (h : StringBufAppendMany st ps st') :
    cliBufShapeOf st' = (cliBufShapeOf st).run (ps.map List.length) ∧
      st'.bytes = st.bytes ++ ps.flatten := by
  induction h with
  | nil _ => exact ⟨rfl, by simp⟩
  | cons hp _ ih =>
    refine ⟨?_, ?_⟩
    · rw [ih.1, cliBufShape_append hp, List.map_cons, cliBufShape_run_cons]
    · rw [ih.2, hp.1, List.flatten_cons, List.append_assoc]

/-- Multi-piece panic relation: some intermediate slice `p` in `ps` triggers `StringBufAppendPanics`. -/
@[expose] def StringBufManyPanic (st : FmtBuf) (ps : List (List (BitVec 8))) (_ : State) : Prop :=
  ∃ pre p post st_m, ps = pre ++ p :: post ∧
    StringBufAppendMany st pre st_m ∧ StringBufAppendPanics st_m p.length

/-- Multi-piece out-of-memory relation: some intermediate slice `p` in `ps` exceeds `B.FitsEvents`. -/
@[expose] def StringBufManyOom (B : RustAllocBudget) (st0 : B.σ) (st : FmtBuf)
    (ps : List (List (BitVec 8))) (_ : State) : Prop :=
  ∃ pre p post st_m, ps = pre ++ p :: post ∧
    StringBufAppendMany st pre st_m ∧ ¬ B.FitsEvents st0 (stringAppendEvents st_m p.length)

/-- Slice list appended by a single `FmtCall` under multi-piece callback map `argPieces`. -/
@[expose] def callPieces (argPieces : Nat → List (List (BitVec 8))) :
    FmtCall → List (List (BitVec 8))
  | .writeStr _ bs => [bs]
  | .fmtArg idx _ _ _ => argPieces idx

/-- Flattened list of appended slice lengths across `cs`. -/
abbrev manyLens (argPieces : Nat → List (List (BitVec 8))) (cs : List FmtCall) : List Nat :=
  (cs.flatMap (callPieces argPieces)).map List.length

/-- Multi-piece `ArgStep` relation for `fmtInnerBudgetStep`. -/
@[expose] def manyArgStep (argPieces : Nat → List (List (BitVec 8))) (c : FmtCall) (st : FmtBuf)
    (ok : Bool) (st' : FmtBuf) : Prop :=
  ok = true ∧ StringBufAppendMany st (callPieces argPieces c) st'

/-- Multi-piece `ArgPanic` relation for `fmtInnerBudgetPanic`. -/
@[expose] def manyArgPanic (argPieces : Nat → List (List (BitVec 8))) (c : FmtCall) (st : FmtBuf)
    (sf : State) : Prop :=
  StringBufManyPanic st (callPieces argPieces c) sf

/-- Multi-piece `ArgOom` relation for `fmtInnerBudgetOom`. -/
@[expose] def manyArgOom (B : RustAllocBudget) (st0 : B.σ)
    (argPieces : Nat → List (List (BitVec 8))) (c : FmtCall) (st : FmtBuf) (sf : State) : Prop :=
  StringBufManyOom B st0 st (callPieces argPieces c) sf

theorem manyStep_iff (argPieces : Nat → List (List (BitVec 8))) (c : FmtCall) (st : FmtBuf)
    (ok : Bool) (st' : FmtBuf) :
    fmtInnerBudgetStep (manyArgStep argPieces) c st ok st' ↔
      ok = true ∧ StringBufAppendMany st (callPieces argPieces c) st' := by
  cases c with
  | writeStr _ bs =>
    dsimp only [fmtInnerBudgetStep, callPieces]
    exact and_congr_right' appendMany_singleton_iff.symm
  | fmtArg _ _ _ _ => rfl

theorem manyPanic_of_budgetPanic {t0 : State} {argPieces : Nat → List (List (BitVec 8))}
    {c : FmtCall} {st : FmtBuf} {sf : State}
    (h : fmtInnerBudgetPanic t0 (manyArgPanic argPieces) c st sf) :
    StringBufManyPanic st (callPieces argPieces c) sf := by
  cases c with
  | writeStr _ bs => exact ⟨[], bs, [], st, rfl, .nil st, h.2.2⟩
  | fmtArg _ _ _ _ => exact h

theorem manyOom_of_budgetOom {B : RustAllocBudget} {st0 : B.σ}
    {argPieces : Nat → List (List (BitVec 8))} {c : FmtCall} {st : FmtBuf} {sf : State}
    (h : fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces) c st sf) :
    StringBufManyOom B st0 st (callPieces argPieces c) sf := by
  cases c with
  | writeStr _ bs => exact ⟨[], bs, [], st, rfl, .nil st, h⟩
  | fmtArg _ _ _ _ => exact h

theorem run_many {argPieces : Nat → List (List (BitVec 8))} {cs : List FmtCall}
    {st : FmtBuf} {b : Bool} {st' : FmtBuf}
    (h : FmtRun (fmtInnerBudgetStep (manyArgStep argPieces)) cs st b st') :
    b = true ∧ StringBufAppendMany st (cs.flatMap (callPieces argPieces)) st' := by
  induction h with
  | nil st => exact ⟨rfl, .nil st⟩
  | cons_ok hstep _ ih =>
    obtain ⟨-, happ⟩ := (manyStep_iff argPieces _ _ _ _).mp hstep
    exact ⟨ih.1, appendMany_append happ ih.2⟩
  | cons_err hstep =>
    exact absurd ((manyStep_iff argPieces _ _ _ _).mp hstep).1 Bool.false_ne_true

theorem reaches_manyPanic {t0 : State} {argPieces : Nat → List (List (BitVec 8))}
    {cs : List FmtCall} {st₀ st : FmtBuf} {c : FmtCall} {sf : State}
    (hr : FmtReaches (fmtInnerBudgetStep (manyArgStep argPieces)) cs st₀ c st)
    (hp : fmtInnerBudgetPanic t0 (manyArgPanic argPieces) c st sf) :
    StringBufManyPanic st₀ (cs.flatMap (callPieces argPieces)) sf := by
  obtain ⟨pre_c, post_c, rfl, hrun⟩ := hr
  obtain ⟨-, hpre⟩ := run_many hrun
  obtain ⟨pre_p, p, post_p, st_m, hcp, hmid, hpan⟩ := manyPanic_of_budgetPanic hp
  refine ⟨pre_c.flatMap (callPieces argPieces) ++ pre_p, p,
    post_p ++ post_c.flatMap (callPieces argPieces), st_m, ?_,
    appendMany_append hpre hmid, hpan⟩
  simp [List.flatMap_append, List.flatMap_cons, hcp, List.append_assoc]

theorem reaches_manyOom {B : RustAllocBudget} {st0 : B.σ}
    {argPieces : Nat → List (List (BitVec 8))}
    {cs : List FmtCall} {st₀ st : FmtBuf} {c : FmtCall} {sf : State}
    (hr : FmtReaches (fmtInnerBudgetStep (manyArgStep argPieces)) cs st₀ c st)
    (ho : fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces) c st sf) :
    StringBufManyOom B st0 st₀ (cs.flatMap (callPieces argPieces)) sf := by
  obtain ⟨pre_c, post_c, rfl, hrun⟩ := hr
  obtain ⟨-, hpre⟩ := run_many hrun
  obtain ⟨pre_p, p, post_p, st_m, hcp, hmid, hoom⟩ := manyOom_of_budgetOom ho
  refine ⟨pre_c.flatMap (callPieces argPieces) ++ pre_p, p,
    post_p ++ post_c.flatMap (callPieces argPieces), st_m, ?_,
    appendMany_append hpre hmid, hoom⟩
  simp [List.flatMap_append, List.flatMap_cons, hcp, List.append_assoc]

/-- Discharge `FormatInnerBudgetSafe` for multi-piece callbacks `argPieces` whenever `Env` contains
    `formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (manyLens argPieces cs)`. -/
theorem manyFmt_safe_of_env (M : AllocCostModel) (A : RustCliAllocBudget M) [PoolMemTransport A]
    (lim : BudgetLimits) (st0 : M.σ) (Env : List AllocEvent → Prop)
    (argPieces : Nat → List (List (BitVec 8))) (x1 : BitVec 64) (cs : List FmtCall)
    (hlit : fmtLiteralLen cs < 2 ^ 60)
    (hEnv : Env (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (manyLens argPieces cs))) :
    FormatInnerBudgetSafe (toRustAllocBudget M A lim) st0 (toRustStdEnv Env)
      (manyArgStep argPieces) (manyArgPanic argPieces)
      (manyArgOom (toRustAllocBudget M A lim) st0 argPieces) x1 cs := by
  let B := toRustAllocBudget M A lim
  let cap0 := fmtEstimatedCapacity x1 cs
  refine ⟨hlit, ?_, ?_, ?_, ?_⟩
  · intro st₀ hstart
    obtain ⟨suf, hsuf⟩ :=
      cliBufShape_run_evs_prefix (startCliBufShape cap0) (manyLens argPieces cs)
    refine ⟨suf.map ofCliAllocEvent, ?_⟩
    unfold toRustStdEnv
    rw [List.map_append, map_toCliAllocEvent_ofCliAllocEvent]
    have h0 := congrArg CliBufShape.evs (cliBufShape_of_start hstart)
    simp only [cliBufShapeOf] at h0
    rw [h0, ← hsuf]
    exact hEnv
  · intro st₀ st hstart hrun
    have hm := (cliBufShape_appendMany (run_many hrun).2).1
    rw [cliBufShape_of_start hstart] at hm
    have hev := congrArg CliBufShape.evs hm
    simp only [cliBufShapeOf] at hev
    unfold toRustStdEnv
    rw [hev]
    exact hEnv
  · rintro ⟨st₀, st, -, hrun⟩
    exact absurd (run_many hrun).1 Bool.false_ne_true
  · intro hfitE st₀ c st sf hstart hreach
    have hevMem : toRustStdEnv Env
        ((formatInnerKnownEvents cap0 (manyLens argPieces cs)).map ofCliAllocEvent) := by
      unfold toRustStdEnv
      rw [map_toCliAllocEvent_ofCliAllocEvent]
      exact hEnv
    have hall0 := (toRustAllocBudget_fitsEvents M A lim st0 _).mp (hfitE _ hevMem)
    rw [map_toCliAllocEvent_ofCliAllocEvent] at hall0
    have hfitSlice : ∀ {pre_p p post_p st_m},
        callPieces argPieces c = pre_p ++ p :: post_p →
        StringBufAppendMany st pre_p st_m →
        B.FitsEvents st0 (stringAppendEvents st_m p.length) := by
      intro pre_p p post_p st_m hcp hmid
      obtain ⟨pre_c, post_c, hcs, hrun_pre⟩ := hreach
      have hall_pre := appendMany_append (run_many hrun_pre).2 hmid
      have hsh := (cliBufShape_appendMany hall_pre).1
      rw [cliBufShape_of_start hstart] at hsh
      let lensPre := (pre_c.flatMap (callPieces argPieces) ++ pre_p).map List.length
      let lensPost := (post_p ++ post_c.flatMap (callPieces argPieces)).map List.length
      have hsplit : manyLens argPieces cs = lensPre ++ p.length :: lensPost := by
        dsimp only [manyLens, lensPre, lensPost]
        rw [hcs]
        simp [List.flatMap_append, List.flatMap_cons, hcp, List.map_append, List.append_assoc]
      obtain ⟨suf, hsuf⟩ :=
        cliBufShape_run_evs_prefix (((startCliBufShape cap0).run lensPre).append p.length) lensPost
      have hpref : formatInnerKnownEvents cap0 (manyLens argPieces cs) =
          (stringAppendEvents st_m p.length).map toCliAllocEvent ++ suf := by
        rw [map_stringAppendEvents_eq_cliBufShape, hsh, ← hsuf, formatInnerKnownEvents,
          hsplit, cliBufShape_run_append, cliBufShape_run_cons]
      have hall1 := hall0
      rw [hpref, LibsignalBinary.Heap.fitsEvents_append] at hall1
      exact (toRustAllocBudget_fitsEvents M A lim st0 _).mpr hall1.1
    refine ⟨?_, ?_⟩
    · rintro idx val fn opts rfl ⟨pre_p, p, post_p, st_m, hcp, hmid, hpan⟩
      exact not_appendPanics_of_fits B (hfitSlice hcp hmid) hpan
    · intro hoom
      obtain ⟨pre_p, p, post_p, st_m, hcp, hmid, hnotFit⟩ := manyOom_of_budgetOom hoom
      exact hnotFit (hfitSlice hcp hmid)

/-- Tight-stack placed contract for `alloc::fmt::format::format_inner` with multi-piece callbacks
    `argPieces`. -/
@[expose] def cliAllocFormatInnerManyTightSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (Env : List AllocEvent → Prop)
    (va : StringWriteAddrs) (R_client : SepProp) (argPieces : Nat → List (List (BitVec 8)))
    (stackBytes : Nat) (P : Program) :
    Spec (BitVec 64 × Bool × List (BitVec 8) × List (BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (ret, argsRo, tpl, args, st0) s =>
    ⌜s.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ FitsEnv M lim st0 Env ∧
      ∃ cs, decodeFmtArguments (s.readReg64 .x0) (s.readReg64 .x1) tpl args = some cs ∧
        fmtLiteralLen cs < 2 ^ 60 ∧
        Env (formatInnerKnownEvents (fmtEstimatedCapacity (s.readReg64 .x1) cs)
          (manyLens argPieces cs)) ∧
        FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0 va R_client
          (manyArgStep argPieces) (manyArgPanic argPieces)
          (manyArgOom (toRustAllocBudget M A lim) st0 argPieces) stackBytes s cs⌝ ∗
      fmtArgumentsAt argsRo (s.readReg64 .x0) (s.readReg64 .x1) tpl args ∗
      memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
      A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
  post := fun (ret, argsRo, tpl, args, st0) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ bs : List (BitVec 8),
      ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          evs = formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (manyLens argPieces cs) ∧
          bs = (cs.flatMap (callPieces argPieces)).flatten⌝ ∗
      CryptoVerification.RustHeap.vecU8 A.repAlloc ret bs ∗
      fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
      stringWriteVtableAt va ∗ R_client ∗
      A.pool lim (M.stepEvents evs st0) sf ∗
      stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)

/-- Multi-piece placed correctness of `alloc::fmt::format::format_inner` (`allocMultiLib` block `3`). -/
theorem cliAllocFormatInnerMany_tight_placed_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    [PoolMemTransport A] {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_client : SepProp} {argPieces : Nat → List (List (BitVec 8))} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc : MultiPlacement}
    (L : CliFormatInnerLink M A lim P mplCore mplAlloc) :
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      (cliAllocFormatInnerManyTightSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argPieces stackBytes P) := by
  let B := toRustAllocBudget M A lim
  let va := allocStringWriteAddrs mplAlloc
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ret, argsRo, tpl, args, st0⟩ R₀ s0 hpc hrun hpre hsp0 _hclP
  have hplaced := allocFormatInnerBudget_placed_ok P B (toRustStdEnv Env) R_client
    (manyArgStep argPieces) (manyArgPanic argPieces) (manyArgOom B st0 argPieces)
    stackBytes mplAlloc L.plAlloc L.clAlloc L.noExtAlloc3 L.noExtAlloc7 L.noExtAlloc1
    L.noExtAlloc2 L.panicHandleErr (L.memcpyAll true) L.allocShim L.rustAlloc L.rustRealloc
    mplCore L.plCore L.clCore L.fmtWriteTie L.noExtCore0
  dsimp only [cliAllocFormatInnerManyTightSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ stringWriterStack ≤ stackBytes ∧
        formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64 ∧ FitsEnv M lim st0 Env ∧
        ∃ cs, decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs ∧
          fmtLiteralLen cs < 2 ^ 60 ∧
          Env (formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs)
            (manyLens argPieces cs)) ∧
          FmtInnerBudgetArgsOk P B st0 va R_client (manyArgStep argPieces)
            (manyArgPanic argPieces) (manyArgOom B st0 argPieces) stackBytes s0 cs⌝ ∗
        ((fmtArgumentsAt argsRo (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt va ∗ R_client ∗
          A.pool lim st0 s0 ∗
          stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx8, hstk1, hstkFit, hFitCli, cs, hdec, hlit, hEnvCs, hArgsOk⟩, hm0⟩
  have hFitB : VerifiedLibraries.RustStd.FitsEnv B st0 (toRustStdEnv Env) :=
    fitsEnv_toRustAllocBudget_of_cli M A lim hFitCli
  have hSafe : FormatInnerBudgetSafe B st0 (toRustStdEnv Env)
      (manyArgStep argPieces) (manyArgPanic argPieces) (manyArgOom B st0 argPieces)
      (s0.readReg64 .x1) cs :=
    manyFmt_safe_of_env M A lim st0 Env argPieces (s0.readReg64 .x1) cs hlit hEnvCs
  have hpreRaw :
      s0.mem ⊨ (allocFormatInnerBudgetSpec P B (toRustStdEnv Env) va R_client
        (manyArgStep argPieces) (manyArgPanic argPieces) (manyArgOom B st0 argPieces)
        stackBytes).pre (ret, argsRo, tpl, args, st0) s0 ∗ R₀ := by
    dsimp only [allocFormatInnerBudgetSpec]
    have hpoolEq : B.pool st0 s0 = A.pool lim st0 s0 := rfl
    rw [hpoolEq, pure_sepConj_of_true ⟨hx8, hstk1, hstkFit, hFitB, cs, hdec, hSafe, hArgsOk⟩]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  refine hplaced.mono_outcome (ret, argsRo, tpl, args, st0) R₀ s0 hpc hrun hpreRaw hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocFormatInnerBudgetSpec] at hpost
    dsimp only [cliAllocFormatInnerManyTightSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨stF, hpost⟩
    have hpost1 :
        sf.mem ⊨ ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
          toRustStdEnv Env stF.evs ∧
          ∃ cs', ∃ st₀,
            decodeFmtArguments (s0.readReg64 .x0) (s0.readReg64 .x1) tpl args = some cs' ∧
            FmtBufStart (fmtEstimatedCapacity (s0.readReg64 .x1) cs') st₀ ∧
            FmtRun (fmtInnerBudgetStep (manyArgStep argPieces)) cs' st₀ true stF⌝ ∗
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
    obtain ⟨hshF, hbsF⟩ := cliBufShape_appendMany (run_many hrunCs).2
    have hsh0 := cliBufShape_of_start hstart
    have hevsEq :
        stF.evs.map toCliAllocEvent =
          formatInnerKnownEvents (fmtEstimatedCapacity (s0.readReg64 .x1) cs')
            (manyLens argPieces cs') := by
      have h1 := congrArg CliBufShape.evs hshF
      rw [hsh0] at h1
      exact h1
    have hbsEq : stF.bytes = (cs'.flatMap (callPieces argPieces)).flatten := by
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
    rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [allocFormatInnerBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [allocFormatInnerBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

private theorem cliBufShape_run_fits (sh : CliBufShape) (ns : List Nat)
    (hfit : sh.len + ns.sum ≤ sh.cap.toNat) :
    sh.run ns = ⟨sh.len + ns.sum, sh.cap, sh.evs⟩ := by
  induction ns generalizing sh with
  | nil => simp [CliBufShape.run]
  | cons n rest ih =>
    simp only [List.sum_cons] at hfit
    have h1 : sh.len + n ≤ sh.cap.toNat := by omega
    have happ : sh.append n = ⟨sh.len + n, sh.cap, sh.evs⟩ := by
      simp [CliBufShape.append, h1]
    rw [cliBufShape_run_cons, happ, ih _ (by dsimp only; omega)]
    simp [Nat.add_assoc]

/-- Whenever `4 ≤ sh.cap.toNat`, `2 * sh.cap.toNat < 2 ^ 64`, `sh.len ≤ sh.cap.toNat`, and
    `sh.len + ns.sum ≤ 2 * sh.cap.toNat`, running any multi-piece sequence `ns` grows at most once
    (by `2 * sh.cap.toNat`), producing the exact same `CliBufShape` as appending `ns.sum` at once. -/
theorem cliBufShape_run_at_most_one_double (sh : CliBufShape) (ns : List Nat)
    (hcap4 : 4 ≤ sh.cap.toNat) (hcapMax : 2 * sh.cap.toNat < 2 ^ 64)
    (hlen : sh.len ≤ sh.cap.toNat) (hsum : sh.len + ns.sum ≤ 2 * sh.cap.toNat) :
    sh.run ns = sh.append ns.sum := by
  induction ns generalizing sh with
  | nil =>
    simp [CliBufShape.run, CliBufShape.append, hlen]
  | cons n rest ih =>
    simp only [List.sum_cons] at hsum ⊢
    rw [cliBufShape_run_cons]
    by_cases h1 : sh.len + n ≤ sh.cap.toNat
    · have happ : sh.append n = ⟨sh.len + n, sh.cap, sh.evs⟩ := by
        simp [CliBufShape.append, h1]
      rw [happ, ih ⟨sh.len + n, sh.cap, sh.evs⟩ hcap4 hcapMax h1 (by dsimp only; omega)]
      by_cases h2 : sh.len + n + rest.sum ≤ sh.cap.toNat
      · have h2' : sh.len + (n + rest.sum) ≤ sh.cap.toNat := by omega
        simp [CliBufShape.append, h2', Nat.add_assoc]
      · have h2' : ¬ (sh.len + (n + rest.sum) ≤ sh.cap.toNat) := by omega
        have hg1 : stringGrowCap sh.cap.toNat (sh.len + n) rest.sum = 2 * sh.cap.toNat := by
          unfold stringGrowCap; omega
        have hg2 : stringGrowCap sh.cap.toNat sh.len (n + rest.sum) = 2 * sh.cap.toNat := by
          unfold stringGrowCap; omega
        simp [CliBufShape.append, h2', hg1, hg2, Nat.add_assoc]
    · have h2' : ¬ (sh.len + (n + rest.sum) ≤ sh.cap.toNat) := by omega
      have hg1 : stringGrowCap sh.cap.toNat sh.len n = 2 * sh.cap.toNat := by
        unfold stringGrowCap; omega
      have hg2 : stringGrowCap sh.cap.toNat sh.len (n + rest.sum) = 2 * sh.cap.toNat := by
        unfold stringGrowCap; omega
      let cap2 : BitVec 64 := BitVec.ofNat 64 (2 * sh.cap.toNat)
      have hcap2 : cap2.toNat = 2 * sh.cap.toNat := by
        dsimp only [cap2]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcapMax]
      have happ : sh.append n =
          ⟨sh.len + n, cap2, sh.evs ++ stringGrowStepEvents sh.cap.toNat (2 * sh.cap.toNat)⟩ := by
        simp [CliBufShape.append, h1, hg1, cap2]
      rw [happ, cliBufShape_run_fits _ rest (by dsimp only; rw [hcap2]; omega)]
      simp [CliBufShape.append, h2', hg2, cap2, Nat.add_assoc]

/-- Coalescing theorem for literal-prefixed `format_inner` calls (`cap0 = 2 * prefixLen`,
    `4 ≤ prefixLen`, `4 * prefixLen < 2 ^ 64`, and `ns.sum ≤ 3 * prefixLen`):
    appending `prefixLen` followed by arbitrary pieces `ns` produces the exact same `AllocEvent`
    trace as `[prefixLen, ns.sum]`. -/
theorem formatInnerKnownEvents_coalesce_prefixed {prefixLen : Nat} {ns : List Nat}
    (hlo : 4 ≤ prefixLen) (hhi : 4 * prefixLen < 2 ^ 64) (hsum : ns.sum ≤ 3 * prefixLen) :
    formatInnerKnownEvents (2 * prefixLen) (prefixLen :: ns) =
      formatInnerKnownEvents (2 * prefixLen) [prefixLen, ns.sum] := by
  unfold formatInnerKnownEvents
  rw [cliBufShape_run_cons, cliBufShape_run_cons]
  have hcap0 : (BitVec.ofNat 64 (2 * prefixLen)).toNat = 2 * prefixLen := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsh1 : (startCliBufShape (2 * prefixLen)).append prefixLen =
      ⟨prefixLen, BitVec.ofNat 64 (2 * prefixLen), rustAllocEvents (2 * prefixLen) 1⟩ := by
    have hnz : 2 * prefixLen ≠ 0 := by omega
    have hle : prefixLen ≤ 2 * prefixLen := by omega
    unfold startCliBufShape CliBufShape.append
    simp only [hnz, ↓reduceIte, hcap0, hle, Nat.zero_add]
  rw [hsh1, cliBufShape_run_at_most_one_double _ ns
    (by dsimp only; rw [hcap0]; omega) (by dsimp only; rw [hcap0]; omega)
    (by dsimp only; rw [hcap0]; omega) (by dsimp only; rw [hcap0]; omega)]
  rfl

/-- Any `24 ≤ prefixLen ≤ 40` and `ns.sum ≤ 71` satisfies both `FormatInnerPrefixedEnv` and
    `CliFormatInnerEnv` at `cap0 = 2 * prefixLen`. -/
theorem formatInnerPrefixedEnv_of_spqrPieces {prefixLen : Nat} {ns : List Nat}
    (hlo : 24 ≤ prefixLen) (hhi : prefixLen ≤ 40) (hsum : ns.sum ≤ 71) :
    FormatInnerPrefixedEnv (formatInnerKnownEvents (2 * prefixLen) (prefixLen :: ns)) := by
  rw [formatInnerKnownEvents_coalesce_prefixed (by omega) (by omega) (by omega)]
  exact ⟨2 * prefixLen, prefixLen, by omega, by omega, [ns.sum], by simp, by simp; omega, rfl⟩

theorem cliFormatInnerEnv_of_spqrPieces {prefixLen : Nat} {ns : List Nat}
    (hlo : 24 ≤ prefixLen) (hhi : prefixLen ≤ 40) (hsum : ns.sum ≤ 71) :
    CliFormatInnerEnv (formatInnerKnownEvents (2 * prefixLen) (prefixLen :: ns)) :=
  cliFormatInnerEnv_iff.mpr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (formatInnerPrefixedEnv_of_spqrPieces hlo hhi hsum))))))))

/-! ## 3. `.rodata` Symbol Bundle (`spqrErrorRoSep`), Payload Cells, & Output Pieces -/

/-- Convert an ASCII string literal into its `List (BitVec 8)` UTF-8 bytes (pure kernel-reducible). -/
@[expose] def asciiBytes (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

abbrev lsFormatterWriteStrSym : String :=
  "_RNvMsa_NtCskxtBwYRO61I_4core3fmtNtB5_9Formatter9write_str"
abbrev lsU32DisplayFmtSym : String :=
  "_RNvXs8_NtNtNtCskxtBwYRO61I_4core3fmt3num3impmNtB9_7Display3fmt"
abbrev lsU64DisplayFmtSym : String :=
  "_RNvXsd_NtNtNtCskxtBwYRO61I_4core3fmt3num3impyNtB9_7Display3fmt"

abbrev spqrPolyDiv2Sym : String := "spqr:.rodata..Lanon.280"
abbrev spqrPolyTooLongSym : String := "spqr:.rodata..Lanon.281"
abbrev spqrPolyInvalidSym : String := "spqr:.rodata..Lanon.282"
abbrev spqrSerGeneralSym : String := "spqr:.rodata..Lanon.257"
abbrev spqrSerCodecSym : String := "spqr:.rodata..Lanon.258"
abbrev spqrEncIndexSym : String := "spqr:.rodata..Lanon.255"
abbrev spqrEncDataSym : String := "spqr:.rodata..Lanon.256"
abbrev spqrEncPolyTplSym : String := "spqr:.rodata.str1.1+0xa30"

abbrev spqrJumpTableSym : String := "spqr:.rodata.<spqr::Error as core::fmt::Display>::fmt"
abbrev spqrArm0Sym : String := "spqr:.rodata..Lanon.347"
abbrev spqrArm1Sym : String := "spqr:.rodata..Lanon.348"
abbrev spqrArm2Sym : String := "spqr:.rodata..Lanon.349"
abbrev spqrArm3Sym : String := "spqr:.rodata..Lanon.350"
abbrev spqrArm4TplSym : String := "spqr:.rodata.str1.1+0xafc"
abbrev spqrArm5TplSym : String := "spqr:.rodata.str1.1+0xb19"
abbrev spqrArm6TplSym : String := "spqr:.rodata.str1.1+0xb2c"
abbrev spqrArm7Sym : String := "spqr:.rodata..Lanon.354"
abbrev spqrArm8Sym : String := "spqr:.rodata..Lanon.355"
abbrev spqrArm9TplSym : String := "spqr:.rodata.str1.1+0xb3e"
abbrev spqrArm10TplSym : String := "spqr:.rodata.str1.1+0xb50"
abbrev spqrArm11TplSym : String := "spqr:.rodata.str1.1+0xb60"
abbrev spqrArm12Sym : String := "spqr:.rodata..Lanon.359"
abbrev spqrArm13TplSym : String := "spqr:.rodata.str1.1+0xb7a"
abbrev spqrArm15Sym : String := "spqr:.rodata..Lanon.362"

@[expose] def spqrPolyDiv2Bs : List (BitVec 8) := asciiBytes "Message length must be divisible by 2"
@[expose] def spqrPolyTooLongBs : List (BitVec 8) := asciiBytes "Message length is too long"
@[expose] def spqrPolyInvalidBs : List (BitVec 8) := asciiBytes "Serialization invalid"
@[expose] def spqrSerGeneralBs : List (BitVec 8) := asciiBytes "General deserialization error"
@[expose] def spqrSerCodecBs : List (BitVec 8) := asciiBytes "Error with encoder/decoder serialization"
@[expose] def spqrEncIndexBs : List (BitVec 8) := asciiBytes "Index decoding error"
@[expose] def spqrEncDataBs : List (BitVec 8) := asciiBytes "Data decoding error"
@[expose] def spqrEncPolyPreBs : List (BitVec 8) := asciiBytes "Polynomial error: "
@[expose] def spqrEncPolyTplBs : List (BitVec 8) := [0x12#8] ++ spqrEncPolyPreBs ++ [0xc0#8, 0x00#8]

@[expose] def spqrJumpTableBs : List (BitVec 8) :=
  [0x00#8, 0x6c#8, 0x4c#8, 0x5c#8, 0x24#8, 0x74#8, 0x94#8, 0x64#8,
   0xb0#8, 0x3a#8, 0xa2#8, 0x16#8, 0x32#8, 0x82#8, 0x08#8, 0x54#8]

@[expose] def spqrArm0Bs : List (BitVec 8) := asciiBytes "state decode failed"
@[expose] def spqrArm1Bs : List (BitVec 8) := asciiBytes "not yet implemented"
@[expose] def spqrArm2Bs : List (BitVec 8) := asciiBytes "message decode failed"
@[expose] def spqrArm3Bs : List (BitVec 8) := asciiBytes "MAC verification failed"
@[expose] def spqrArm4PreBs : List (BitVec 8) := asciiBytes "epoch not in valid range: "
@[expose] def spqrArm4TplBs : List (BitVec 8) := [0x1a#8] ++ spqrArm4PreBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm5PreBs : List (BitVec 8) := asciiBytes "Encoding error: "
@[expose] def spqrArm5TplBs : List (BitVec 8) := [0x10#8] ++ spqrArm5PreBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm6PreBs : List (BitVec 8) := asciiBytes "Serialization: "
@[expose] def spqrArm6TplBs : List (BitVec 8) := [0x0f#8] ++ spqrArm6PreBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm7Bs : List (BitVec 8) := asciiBytes "Version mismatch after negotiation"
@[expose] def spqrArm8Bs : List (BitVec 8) := asciiBytes "Minimum version"
@[expose] def spqrArm9PreBs : List (BitVec 8) := asciiBytes "Key jump: "
@[expose] def spqrArm9MidBs : List (BitVec 8) := asciiBytes " - "
@[expose] def spqrArm9TplBs : List (BitVec 8) :=
  [0x0a#8] ++ spqrArm9PreBs ++ [0xc0#8, 0x03#8] ++ spqrArm9MidBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm10PreBs : List (BitVec 8) := asciiBytes "Key trimmed: "
@[expose] def spqrArm10TplBs : List (BitVec 8) := [0x0d#8] ++ spqrArm10PreBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm11PreBs : List (BitVec 8) := asciiBytes "Key already requested: "
@[expose] def spqrArm11TplBs : List (BitVec 8) := [0x17#8] ++ spqrArm11PreBs ++ [0xc0#8, 0x00#8]
@[expose] def spqrArm12Bs : List (BitVec 8) := asciiBytes "Erroneous data received from remote party"
@[expose] def spqrArm13PreBs : List (BitVec 8) := asciiBytes "Send key epoch decreased ("
@[expose] def spqrArm13MidBs : List (BitVec 8) := asciiBytes " -> "
@[expose] def spqrArm13SufBs : List (BitVec 8) := asciiBytes ")"
@[expose] def spqrArm13TplBs : List (BitVec 8) :=
  [0x1a#8] ++ spqrArm13PreBs ++ [0xc0#8, 0x04#8] ++ spqrArm13MidBs ++
    [0xc0#8, 0x01#8] ++ spqrArm13SufBs ++ [0x00#8]
@[expose] def spqrArm15Bs : List (BitVec 8) := asciiBytes "Chain not available"

/-- All `22` read-only `.rodata` slices in `libsignalSessionLib` accessed by Blocks `412, 392..394`. -/
@[expose] def spqrErrorRoList : List (String × List (BitVec 8)) :=
  [(spqrPolyDiv2Sym, spqrPolyDiv2Bs),
   (spqrPolyTooLongSym, spqrPolyTooLongBs),
   (spqrPolyInvalidSym, spqrPolyInvalidBs),
   (spqrSerGeneralSym, spqrSerGeneralBs),
   (spqrSerCodecSym, spqrSerCodecBs),
   (spqrEncIndexSym, spqrEncIndexBs),
   (spqrEncDataSym, spqrEncDataBs),
   (spqrEncPolyTplSym, spqrEncPolyTplBs),
   (spqrJumpTableSym, spqrJumpTableBs),
   (spqrArm0Sym, spqrArm0Bs),
   (spqrArm1Sym, spqrArm1Bs),
   (spqrArm2Sym, spqrArm2Bs),
   (spqrArm3Sym, spqrArm3Bs),
   (spqrArm4TplSym, spqrArm4TplBs),
   (spqrArm5TplSym, spqrArm5TplBs),
   (spqrArm6TplSym, spqrArm6TplBs),
   (spqrArm7Sym, spqrArm7Bs),
   (spqrArm8Sym, spqrArm8Bs),
   (spqrArm9TplSym, spqrArm9TplBs),
   (spqrArm10TplSym, spqrArm10TplBs),
   (spqrArm11TplSym, spqrArm11TplBs),
   (spqrArm12Sym, spqrArm12Bs),
   (spqrArm13TplSym, spqrArm13TplBs),
   (spqrArm15Sym, spqrArm15Bs)]

/-- Separating conjunction of read-only `.rodata` slices `(pl.ρ sym ↦ᵣ bs)`. -/
@[expose] def roEntriesAt (pl : MultiPlacement) : List (String × List (BitVec 8)) → SepProp
  | [] => emp
  | (sym, bs) :: rest => (pl.ρ sym ↦ᵣ bs) ∗ roEntriesAt pl rest

/-- Read-only `.rodata` footprint of `<spqr::Error as Display>::fmt` and its sub-formatters. -/
def spqrErrorRoSep (pl : MultiPlacement) : SepProp :=
  roEntriesAt pl spqrErrorRoList

theorem roEntriesAt_dup_mem (pl : MultiPlacement) {entries : List (String × List (BitVec 8))}
    {sym : String} {bs : List (BitVec 8)} (hmem : (sym, bs) ∈ entries) :
    roEntriesAt pl entries = (pl.ρ sym ↦ᵣ bs) ∗ roEntriesAt pl entries := by
  induction entries with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · dsimp only [roEntriesAt]
      rw [← sepConj_assoc, pointsToBytesRO_dup]
    · dsimp only [roEntriesAt]
      conv => lhs; rw [ih htl]
      sep_ac_rfl

theorem spqrErrorRoSep_dup_mem (pl : MultiPlacement) {sym : String} {bs : List (BitVec 8)}
    (hmem : (sym, bs) ∈ spqrErrorRoList := by decide) :
    spqrErrorRoSep pl = (pl.ρ sym ↦ᵣ bs) ∗ spqrErrorRoSep pl :=
  roEntriesAt_dup_mem pl hmem

theorem spqrErrorRoSep_dup (pl : MultiPlacement) :
    spqrErrorRoSep pl = spqrErrorRoSep pl ∗ spqrErrorRoSep pl := by
  unfold spqrErrorRoSep
  generalize spqrErrorRoList = entries
  induction entries with
  | nil => simp [roEntriesAt]
  | cons hd tl ih =>
    dsimp only [roEntriesAt]
    conv => lhs; rw [← pointsToBytesRO_dup, ih]
    sep_ac_rfl

private theorem spqrErrorRoList_chk :
    spqrErrorRoList.all (fun p => lsroCheck p.1 p.2) = true := by
  exact eagerReduce (Eq.refl true)

private theorem sat_roEntriesAt {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {entries : List (String × List (BitVec 8))}
    (hall : entries.all (fun p => lsroCheck p.1 p.2) = true)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ roEntriesAt pl entries ∗ P := by
  induction entries with
  | nil => simpa [roEntriesAt] using hP
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    dsimp only [roEntriesAt]
    rw [sepConj_assoc]
    exact lsro_intro_chk hro hall.1 (ih hall.2)

/-- Introduce `spqrErrorRoSep pl` from `LibsignalRoLoaded pl m` with zero heap consumption. -/
theorem sat_spqrErrorRoSep {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ spqrErrorRoSep pl ∗ P :=
  sat_roEntriesAt hro spqrErrorRoList_chk hP

/-- Inline 24-byte `spqr::Error` formattee cell bundle matching `spqrErrorPayload24_split`. -/
@[expose] def spqrErrorCellsAt (errPtr : BitVec 64) (d b1 : BitVec 8) (u1 : BitVec 32)
    (q1 q2 : BitVec 64) : SepProp :=
  (errPtr ↦₈ d) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
    ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2)

/-- Output slice of `<&PolynomialError as Display>::fmt` (`Block 394`). -/
@[expose] def spqrPolyBytes (b1 : BitVec 8) : List (BitVec 8) :=
  if b1 = 0#8 then spqrPolyDiv2Bs
  else if b1 = 1#8 then spqrPolyTooLongBs
  else spqrPolyInvalidBs

/-- Output slice list of `<&EncodingError as Display>::fmt` (`Block 392`). -/
@[expose] def spqrEncPieces (b1 : BitVec 8) : List (List (BitVec 8)) :=
  if b1.toNat ≤ 2 then [spqrEncPolyPreBs, spqrPolyBytes b1]
  else if b1 = 3#8 then [spqrEncIndexBs]
  else [spqrEncDataBs]

/-- Output slice of `<&serialize::Error as Display>::fmt` (`Block 393`). -/
@[expose] def spqrSerBytes (b1 : BitVec 8) : List (BitVec 8) :=
  if b1 = 1#8 then spqrSerCodecBs else spqrSerGeneralBs

/-- Exact sequence of `write_str` slices appended by `<spqr::Error as Display>::fmt` (`Block 412`)
    for any valid discriminant `d` (`SpqrErrorValidTag d`). -/
@[expose] def spqrErrorPieces (d b1 : BitVec 8) (u1 : BitVec 32)
    (q1 q2 : BitVec 64) : List (List (BitVec 8)) :=
  match d.toNat with
  | 0 => [spqrArm0Bs]
  | 1 => [spqrArm1Bs]
  | 2 => [spqrArm2Bs]
  | 3 => [spqrArm3Bs]
  | 4 => [spqrArm4PreBs, formatDecimalNat q1.toNat]
  | 5 => spqrArm5PreBs :: spqrEncPieces b1
  | 6 => [spqrArm6PreBs, spqrSerBytes b1]
  | 7 => [spqrArm7Bs]
  | 8 => [spqrArm8Bs]
  | 9 => [spqrArm9PreBs, formatDecimalNat u1.toNat, spqrArm9MidBs,
          formatDecimalNat (q1.setWidth 32).toNat]
  | 10 => [spqrArm10PreBs, formatDecimalNat u1.toNat]
  | 11 => [spqrArm11PreBs, formatDecimalNat u1.toNat]
  | 12 => [spqrArm12Bs]
  | 13 => [spqrArm13PreBs, formatDecimalNat q1.toNat, spqrArm13MidBs,
           formatDecimalNat q2.toNat, spqrArm13SufBs]
  | _ => [spqrArm15Bs]

theorem spqrPolyBytes_len_bounds (b1 : BitVec 8) :
    21 ≤ (spqrPolyBytes b1).length ∧ (spqrPolyBytes b1).length ≤ 37 := by
  unfold spqrPolyBytes
  split
  · decide
  · split <;> decide

theorem spqrEncPieces_sum_bounds (b1 : BitVec 8) :
    19 ≤ ((spqrEncPieces b1).map List.length).sum ∧
      ((spqrEncPieces b1).map List.length).sum ≤ 55 := by
  have ⟨hlo, hhi⟩ := spqrPolyBytes_len_bounds b1
  unfold spqrEncPieces
  split
  · have hpre : spqrEncPolyPreBs.length = 18 := by decide
    simp [hpre]; omega
  · split <;> decide

theorem spqrSerBytes_len_bounds (b1 : BitVec 8) :
    29 ≤ (spqrSerBytes b1).length ∧ (spqrSerBytes b1).length ≤ 40 := by
  unfold spqrSerBytes
  split <;> decide

/-- Total formatted byte length of `<spqr::Error as Display>::fmt` lies in `[14, 71]` across all
    `d`, `b1`, `u1`, `q1`, `q2`. -/
theorem spqrErrorPieces_sum_bounds (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64) :
    14 ≤ ((spqrErrorPieces d b1 u1 q1 q2).map List.length).sum ∧
      ((spqrErrorPieces d b1 u1 q1 q2).map List.length).sum ≤ 71 ∧
      ((spqrErrorPieces d b1 u1 q1 q2).flatten).length =
        ((spqrErrorPieces d b1 u1 q1 q2).map List.length).sum := by
  have hu1 := formatDecimalNat_u32_length u1
  have hu2 := formatDecimalNat_u32_length (q1.setWidth 32)
  have hq1 := formatDecimalNat_u64_length q1
  have hq2 := formatDecimalNat_u64_length q2
  have henc := spqrEncPieces_sum_bounds b1
  have hser := spqrSerBytes_len_bounds b1
  have hflat := List.length_flatten (L := spqrErrorPieces d b1 u1 q1 q2)
  have h4 : spqrArm4PreBs.length = 26 := by decide
  have h5 : spqrArm5PreBs.length = 16 := by decide
  have h6 : spqrArm6PreBs.length = 15 := by decide
  have h9a : spqrArm9PreBs.length = 10 := by decide
  have h9b : spqrArm9MidBs.length = 3 := by decide
  have h10 : spqrArm10PreBs.length = 13 := by decide
  have h11 : spqrArm11PreBs.length = 23 := by decide
  have h13a : spqrArm13PreBs.length = 26 := by decide
  have h13b : spqrArm13MidBs.length = 4 := by decide
  have h13c : spqrArm13SufBs.length = 1 := by decide
  refine ⟨?_, ?_, hflat⟩ <;> (
    unfold spqrErrorPieces
    split
    · decide
    · decide
    · decide
    · decide
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h4]; omega
    · simp only [List.map_cons, List.sum_cons, h5]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h6]; omega
    · decide
    · decide
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h9a, h9b]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h10]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h11]; omega
    · decide
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h13a, h13b, h13c]; omega
    · decide)

/-! ## 4. Linkage Bundle (`spqrErrorDispKeep`, `SpqrErrorDisplayLink`) & Shared Stepping Bridges -/

/-- Keep predicate for `<spqr::Error as Display>::fmt` (`Block 412`) and its crate-local
    sub-formatters (`Blocks 392, 393, 394, 396, 397`) in `libsignalSessionLib`. -/
@[expose] def spqrErrorDispKeep (j : Nat) : Bool :=
  decide (j = 392 ∨ j = 393 ∨ j = 394 ∨ j = 396 ∨ j = 397 ∨ j = 412)

/-- Complete linkage bundle for real-code `<spqr::Error as Display>::fmt` inside `format_inner`. -/
structure SpqrErrorDisplayLink [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    [PoolMemTransport A] (lim : BudgetLimits) (P : Program)
    (mplCore mplAlloc mplFmt : MultiPlacement) : Prop extends
    CliFormatInnerLink M A lim P mplCore mplAlloc where
  plFmt : coreFmtMultiLib.Placeable mplFmt
  noExtFmtWriteStr : LibBlockNoExtern coreFmtMultiLib mplFmt P 2
  clFmtWriteStr : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere writeStrKeep mplFmt m
  noExtFmtU32 : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mplFmt P
  clFmtU32 : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mplFmt m
  noExtFmtU64 : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mplFmt P
  clFmtU64 : ∀ m, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mplFmt m
  noExtLs : LibKeepNoExtern libsignalSessionLib spqrErrorDispKeep lsmpl P
  clLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl m
  tieWriteStr :
    lsmpl.ρ lsFormatterWriteStrSym =
      coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym
  tieFmtWrite :
    lsmpl.ρ lsFmtWriteSym =
      coreMultiLib.fnAddr mplCore coreFmtWriteSym
  tieU32 :
    lsmpl.ρ lsU32DisplayFmtSym =
      coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym
  tieU64 :
    lsmpl.ρ lsU64DisplayFmtSym =
      coreFmtMultiLib.fnAddr mplFmt u64DisplayFmtSym

theorem formatterAt_entails_memRegion24 (f outPtr vtPtr : BitVec 64) (opts : FmtOptions) :
    formatterAt f outPtr vtPtr opts ⊢ memRegion f 24 := by
  unfold formatterAt
  have h16 := (show f + 20#64 + 2#64 = f + 22#64 by bv_omega) ▸
    pointsTo16_pair (f + 20#64) opts.width opts.precision
  have h32 := (show f + 16#64 + 4#64 = f + 20#64 by bv_omega) ▸
    pointsTo32_pair (f + 16#64) opts.flags (opts.precision ++ opts.width)
  rw [h16, h32, memRegion_cells f 3 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right, show f + 8#64 + 8#64 = f + 16#64 by bv_omega]
  exact Entails.sepExists_right outPtr (Entails.sepExists_right vtPtr
    (Entails.sepExists_right ((opts.precision ++ opts.width) ++ opts.flags) (Entails.refl _)))

theorem panic_frame_anyHeap {φ : Prop} {F : SepProp} :
    ((⌜φ⌝ ∗ anyHeap) ∗ F) ⊢ ⌜φ⌝ ∗ anyHeap := by
  rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _)

theorem fmtInnerBudgetW_transport (B : RustAllocBudget) (st0 : B.σ)
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

/-- Placed `<core::fmt::Formatter>::write_str` (`coreFmtMultiLib` block `2`) over `fmtInnerBudgetW`. -/
theorem cliFormatterWriteStr_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) (R : SepProp) (t0 : State) (stackBytes : Nat) (f out : BitVec 64)
    (opts : FmtOptions) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
      (formatterWriteStrSpec (fmtInnerBudgetW B st0 va R t0 out)
        VerifiedLibraries.RustStd.StringBufStrStep
        (VerifiedLibraries.RustStd.StringBufWriterPanic t0)
        (VerifiedLibraries.RustStd.StringBufWriterOom B st0)
        stackBytes f out va.vtable opts true ptr bs) := by
  intro B va
  have hw := cliStringBudgetFmtWriterOk L.toCliFmtWriteLink st0 R t0 stackBytes out hstk
  exact subroutine_ok_drop_codeLoadedWhere L.clFmtWriteStr
    (formatterWriteStr_ok L.plFmt L.noExtFmtWriteStr hw.transport hw.slot_write_str
      (hw.write_str true ptr bs))

/-- Lift any single-piece `knownArgStep` `fmtArgCallSpec` (`cliU32Display_fmtArg_ok`,
    `cliU64Display_fmtArg_ok`) directly to `manyArgStep` when `argPieces idx = [bs]`. -/
theorem fmtArgCallSpec_many_of_known {B : RustAllocBudget} {st0 : B.σ} {va : StringWriteAddrs}
    {R : SepProp} {t0 : State} {P : Program}
    {argPieces : Nat → List (List (BitVec 8))} {bs : List (BitVec 8)}
    {stackBytes idx : Nat} {out valPtr fmtFn : BitVec 64} {opts : FmtOptions}
    (hpcs : argPieces idx = [bs])
    (hk : subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R t0 out)
        (fmtInnerBudgetStep (knownArgStep fun _ => bs))
        (fmtInnerBudgetPanic t0 (knownArgPanic fun _ => bs))
        (fmtInnerBudgetOom B st0 (knownArgOom B st0 fun _ => bs))
        stackBytes out va.vtable idx valPtr fmtFn opts)) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx valPtr fmtFn opts) := by
  refine subroutine_ok_mono hk
    (fun _ _ _ h => h)
    (fun (st, f) _ _ sf hpost => by
      dsimp only [fmtArgCallSpec] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine Entails.sepExists_mono fun ok => Entails.sepExists_mono fun st' => ?_
      refine Entails.pure_left fun ⟨hw0, hstep⟩ => ?_
      dsimp only [fmtInnerBudgetStep, knownArgStep, callBytes] at hstep
      dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces]
      rw [hpcs]
      exact Entails.pure_right ⟨hw0, hstep.1, appendMany_singleton_iff.mpr hstep.2⟩
        (Entails.refl _))
    (fun (st, _) _ _ sf hpan => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, knownArgPanic, callBytes] at hpan
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces]
      rw [hpcs]
      refine Satisfies.mono (sepConj_mono_left ?_) hpan
      exact Entails.pure_left fun hp =>
        Entails.pure_right ⟨[], bs, [], st, rfl, .nil st, hp⟩ (Entails.refl _))
    (hoom := fun (st, _) _ _ sf hoom => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, knownArgOom, callBytes] at hoom
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces]
      rw [hpcs]
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨⟨[], bs, [], st, rfl, .nil st, hoom.1⟩, hoom.2⟩)

theorem fmtInnerBudgetW_split_R_eq (B : RustAllocBudget) (st0 : B.σ)
    (va : StringWriteAddrs) (F R : SepProp) (t0 : State) (out : BitVec 64)
    (st : FmtBuf) (s : State) :
    fmtInnerBudgetW B st0 va (F ∗ R) t0 out st s =
      F ∗ fmtInnerBudgetW B st0 va R t0 out st s := by
  dsimp only [fmtInnerBudgetW]
  sep_ac_rfl

private theorem fmtInnerBudgetW_dup_R {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {P_dup R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} (hdup : R = P_dup ∗ R) :
    fmtInnerBudgetW B st0 va R t0 out st s =
      P_dup ∗ fmtInnerBudgetW B st0 va R t0 out st s :=
  (congrArg (fun X => fmtInnerBudgetW B st0 va X t0 out st s) hdup).trans
    (fmtInnerBudgetW_split_R_eq B st0 va P_dup R t0 out st s)

private theorem fmtInnerBudgetW_dup_vtable {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} :
    fmtInnerBudgetW B st0 va R t0 out st s =
      ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
        fmtInnerBudgetW B st0 va R t0 out st s := by
  let F : SepProp → SepProp := fun V =>
    ⌜IoCallFrame t0 s ∧ s.fs = t0.fs ∧ s.trace = t0.trace⌝ ∗
      Rust.vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      fmtBufVecAt B st.cap st.ptr st.bytes ∗
      B.pool (B.stepEvents st.evs st0) s ∗ V ∗ R
  change F (stringWriteVtableAt va) =
    ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ F (stringWriteVtableAt va)
  refine (congrArg F (stringWriteVtableAt_dup_writeStr va)).trans ?_
  dsimp only [F]
  sep_ac_rfl

private theorem fmtInnerBudgetW_dup_vtable_and_R {B : RustAllocBudget} {st0 : B.σ}
    {va : StringWriteAddrs} {P_dup R : SepProp} {t0 : State} {out : BitVec 64}
    {st : FmtBuf} {s : State} (hdup : R = P_dup ∗ R) :
    fmtInnerBudgetW B st0 va R t0 out st s =
      ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ P_dup ∗
        fmtInnerBudgetW B st0 va R t0 out st s := by
  refine fmtInnerBudgetW_dup_vtable.trans ?_
  refine (congrArg (fun X => ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ X)
    (fmtInnerBudgetW_dup_R hdup)).trans ?_
  sep_ac_rfl

/-- Extract any `.rodata` slice `(sym, bs) ∈ spqrErrorRoList` as a duplicate atom in front of
    `R_client = F ∗ (spqrErrorRoSep lsmpl ∗ R_rest)`. -/
theorem spqrErrorRoSep_dup_in_R [LibsignalPlacement] {F R_client R_rest : SepProp}
    {sym : String} {bs : List (BitVec 8)}
    (hmem : (sym, bs) ∈ spqrErrorRoList := by decide)
    (hR : R_client = F ∗ (spqrErrorRoSep lsmpl ∗ R_rest)) :
    R_client = (lsmpl.ρ sym ↦ᵣ bs) ∗ R_client := by
  rw [hR]
  refine (congrArg (fun X => F ∗ (X ∗ R_rest)) (spqrErrorRoSep_dup_mem lsmpl hmem)).trans ?_
  sep_ac_rfl

/-- Collapse `sepWPp_seg_lib_block_pureWhere`'s `(libsignalSessionLib.blockProgram lsmpl j).rebase`
    directly to a `gen_ls_blk_ultra` rebased block program `prog` (avoiding double `Program.rebase`). -/
theorem blockProgram_rebase_eq_lsProg [LibsignalPlacement] {j : Nat} {prog : Program}
    [hprog : IsLsBlockProg prog j (fun _ => none)] :
    (libsignalSessionLib.blockProgram lsmpl j).rebase (lsmpl.base j) (fun _ => none) = prog := by
  change libsignalSessionLib.blockProgram lsmpl j (fun _ => none) = prog
  exact hprog.eq_blockProgram.symm

private theorem subroutine_ok_of_multiCodeLoaded_local {α : Type} {lib : MultiPlacedLib}
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

/-- Initialize a `SepWPp` proof of `subroutine_ok P entry spec` with
    `libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl s0.mem` extracted from `L.clLs`. -/
theorem subroutine_ok_of_sepWPp_clLs [LibsignalPlacement] {α : Type} {P : Program}
    {entry : BitVec 64} {spec : Spec α}
    (hclLs : ∀ m, P.CodeLoaded m → libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl m)
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.spAligned = true →
      libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl s0.mem →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
        SepWPp P (s0.readReg64 Reg.lr) s0 P_init
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.onPanic x s0 sf ∗ R)
          (spec.onOom x s0)) :
    subroutine_ok P entry spec := by
  refine subroutine_ok_drop_codeLoadedWhere hclLs ?_
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨
    (spec.pre x s0 ∗ ⌜libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl s0.mem⌝) ∗ R
    at hpre
  have hpre' :
      s0.mem ⊨ ⌜libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl s0.mem⌝ ∗
        (spec.pre x s0 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'
  exact h x R s0 hpc0 hrun0 hsp0 hpre'.1 hpre'.2

/-- Reusable tail-call discharge at `coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym` from an
    intermediate state `sm` of any `fmtFn` callback whose `argPieces idx = [bs]` (`bs.length < 2^60`),
    extracting `(ptr ↦ᵣ bs)` from `R_client` via `hdup`. -/
theorem tailcall_formatterWriteStr_many [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client : SepProp} (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out valPtr fmtFn f : BitVec 64)
    (opts : FmtOptions) (ptr : BitVec 64) (bs : List (BitVec 8))
    (st : FmtBuf) (R : SepProp) (s0 sm : State)
    (hpcs : argPieces idx = [bs])
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hdup : R_client = (ptr ↦ᵣ bs) ∗ R_client)
    (hframe : FmtWriteFrame s0 sm)
    (hpc_sm : sm.pc = coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
    (hrun_sm : sm.status = .Running)
    (hsp_sm : sm.sp = s0.sp)
    (hsp_al : s0.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (hx0_sm : sm.readReg64 .x0 = f)
    (hx1_sm : sm.readReg64 .x1 = ptr)
    (hx2_sm : (sm.readReg64 .x2).toNat = bs.length)
    (hlen_lt : bs.length < 2 ^ 60)
    (hcs_sm : CalleeSavedPreserved s0 sm) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    SepWPp P (s0.readReg64 Reg.lr) sm
      (formatterAt f out va.vtable opts ∗
        fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
        stackFrameAt s0.sp stackBytes)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable idx valPtr fmtFn opts).post (st, f) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable idx valPtr fmtFn opts).onPanic (st, f) s0 sf ∗ R)
      (fun sf =>
        (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
          (fmtInnerBudgetStep (manyArgStep argPieces))
          (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
          (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
          stackBytes out va.vtable idx valPtr fmtFn opts).onOom (st, f) s0 sf) := by
  intro B va
  have hws := cliFormatterWriteStr_placed_ok L st0 R_client t0 stackBytes
    f out opts ptr bs hstk
  refine SepWPp.tailcall (x := st) (F := emp) hws hpc_sm hrun_sm
    (by unfold State.spAligned at hsp_al ⊢; rwa [hsp_sm]) hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ hm_pan => ?_)
    (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => ?_, hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩)
    (fun sf R' _ hoom => ?_)
  · refine Satisfies.mono ?_ hm
    have htr := fmtInnerBudgetW_transport B st0 va R_client t0 out st s0 sm hframe
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left htr))) ?_
    have hdupW := fmtInnerBudgetW_dup_R (B := B) (st0 := st0) (va := va)
      (t0 := t0) (out := out) (st := st) (s := sm) hdup
    refine Entails.trans (Entails.of_eq (show
      (formatterAt f out va.vtable opts ∗
        fmtInnerBudgetW B st0 va R_client t0 out st sm ∗
        stackFrameAt s0.sp stackBytes) ∗ R' =
      (formatterAt f out va.vtable opts ∗ (ptr ↦ᵣ bs) ∗
        fmtInnerBudgetW B st0 va R_client t0 out st sm ∗
        stackFrameAt sm.sp stackBytes) ∗ (emp ∗ R') by
      dsimp only [toRustAllocBudget, B] at hdupW ⊢
      conv => lhs; rw [hdupW]
      rw [hsp_sm, emp_sepConj]
      sep_ac_rfl)) ?_
    refine sepConj_mono_left ?_
    dsimp only [formatterWriteStrSpec, fmtSrcBytes, ↓reduceIte]
    exact Entails.pure_right ⟨hx0_sm, hx1_sm, hx2_sm, hlen_lt⟩ (Entails.refl _)
  · dsimp only [formatterWriteStrSpec, fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic,
      callPieces, VerifiedLibraries.RustStd.StringBufWriterPanic] at hm_pan ⊢
    rw [hpcs]
    rw [sepConj_emp] at hm_pan
    refine Satisfies.mono (sepConj_mono_left ?_) hm_pan
    exact Entails.pure_left fun ⟨_, _, hp⟩ =>
      Entails.pure_right ⟨[], bs, [], st, rfl, .nil st, hp⟩ (Entails.refl _)
  · dsimp only [formatterWriteStrSpec, fmtSrcBytes, ↓reduceIte, fmtArgCallSpec] at hm_post ⊢
    rw [sepConj_emp, hsp_sm] at hm_post
    refine Satisfies.mono (sepConj_mono_left ?_) hm_post
    refine Entails.sepExists_mono fun ok => Entails.sepExists_mono fun st' => ?_
    refine Entails.pure_left fun ⟨hw0, hstep⟩ => ?_
    dsimp only [VerifiedLibraries.RustStd.StringBufStrStep] at hstep
    have hw0_and : sf.readReg32 .x0 &&& 1#32 = if ok then 0#32 else 1#32 := by
      rw [hw0, hstep.1]; decide
    dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces]
    rw [hpcs]
    have hdupW' := (fmtInnerBudgetW_dup_R (B := B) (st0 := st0) (va := va)
      (t0 := t0) (out := out) (st := st') (s := sf) hdup).symm
    refine Entails.pure_right ⟨hw0_and, hstep.1, appendMany_singleton_iff.mpr hstep.2⟩ ?_
    refine Entails.trans (Entails.of_eq (show
      formatterAt f out va.vtable opts ∗ (ptr ↦ᵣ bs) ∗
        fmtInnerBudgetW B st0 va R_client t0 out st' sf ∗
        stackFrameAt s0.sp stackBytes =
      formatterAt f out va.vtable opts ∗
        fmtInnerBudgetW B st0 va R_client t0 out st' sf ∗
        stackFrameAt s0.sp stackBytes by
      dsimp only [toRustAllocBudget, B] at hdupW' ⊢
      conv => lhs; arg 2; rw [← sepConj_assoc, hdupW'])) ?_
    exact sepConj_mono_left (formatterAt_entails_memRegion24 f out va.vtable opts)
  · dsimp only [formatterWriteStrSpec, fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom,
      callPieces, VerifiedLibraries.RustStd.StringBufWriterOom] at hoom ⊢
    rw [hpcs]
    rw [satisfies_pure_sepConj] at hoom ⊢
    exact ⟨⟨[], bs, [], st, rfl, .nil st, hoom.1⟩, Satisfies.drop_left hoom.2⟩

/-- Reusable `call_wpp_where` discharge for a nested `bl lsFmtWriteSym` (`core::fmt::write`) inside
    any `libsignalSessionLib` `fmtFn` callback over `fmtInnerBudgetW`, preserving
    `libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl` across the call and lifting
    nested `FmtRun` / `FmtReaches` into `manyArgStep` / `manyArgPanic` / `manyArgOom`. -/
theorem nested_coreFmtWrite_many_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_sub F_frame : SepProp}
    (argPieces subPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes subStack outerIdx : Nat)
    (out valPtr fmtFn f ret_pc tplPtr argsPtr : BitVec 64)
    (opts : FmtOptions) (tpl : List (BitVec 8)) (args : List (BitVec 64 × BitVec 64))
    (cs : List FmtCall) (st : FmtBuf) (R : SepProp) (s0 sm : State)
    (hpcs : argPieces outerIdx = cs.flatMap (callPieces subPieces))
    (hsubStk : stringWriterStack ≤ subStack ∧ 0x70 + subStack ≤ 2 ^ 64)
    (heven : argsPtr.getLsbD 0 = false)
    (hdec : decodeFmtArguments tplPtr argsPtr tpl args = some cs)
    (htpl_dup : R_sub = (tplPtr ↦ᵣ tpl) ∗ R_sub)
    (hargsOk : ∀ idx val fn opt, FmtCall.fmtArg idx val fn opt ∈ cs →
      subroutine_ok P fn
        (fmtArgCallSpec
          (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
            (allocStringWriteAddrs mplAlloc) R_sub t0 out)
          (fmtInnerBudgetStep (manyArgStep subPieces))
          (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
          (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
            (manyArgOom (toRustAllocBudget M A lim) st0 subPieces))
          subStack out (allocStringWriteAddrs mplAlloc).vtable idx val fn opt))
    (hcl_sm : libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl sm.mem)
    (hframe : FmtWriteFrame s0 sm)
    (hpc_sm : sm.pc = coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    (hrun_sm : sm.status = .Running)
    (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = ret_pc)
    (hx0_sm : sm.readReg64 .x0 = out)
    (hx1_sm : sm.readReg64 .x1 = (allocStringWriteAddrs mplAlloc).vtable)
    (hx2_sm : sm.readReg64 .x2 = tplPtr)
    (hx3_sm : sm.readReg64 .x3 = argsPtr)
    (hnext : ∀ (sf_call : State) (st' : FmtBuf),
      sf_call.pc = ret_pc → sf_call.status = .Running →
      sf_call.sp = sm.sp → CalleeSavedPreserved sm sf_call →
      libsignalSessionLib.CodeLoadedWhere spqrErrorDispKeep lsmpl sf_call.mem →
      sf_call.readReg32 .x0 = 0#32 →
      manyArgStep argPieces (.fmtArg outerIdx valPtr fmtFn opts) st true st' →
      SepWPp P (s0.readReg64 Reg.lr) sf_call
        (fmtArgEntriesAt false argsPtr args ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0
            (allocStringWriteAddrs mplAlloc) R_sub t0 out st' sf_call ∗
          stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (fmtArgCallSpec
              (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
                (allocStringWriteAddrs mplAlloc) R_client t0 out)
              (fmtInnerBudgetStep (manyArgStep argPieces))
              (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
              (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
                (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
              stackBytes out (allocStringWriteAddrs mplAlloc).vtable
              outerIdx valPtr fmtFn opts).post (st, f) s0 sf ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (fmtArgCallSpec
              (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
                (allocStringWriteAddrs mplAlloc) R_client t0 out)
              (fmtInnerBudgetStep (manyArgStep argPieces))
              (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
              (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
                (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
              stackBytes out (allocStringWriteAddrs mplAlloc).vtable
              outerIdx valPtr fmtFn opts).onPanic (st, f) s0 sf ∗ R)
        (fun sf =>
          (fmtArgCallSpec
            (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
              (allocStringWriteAddrs mplAlloc) R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
              (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
            stackBytes out (allocStringWriteAddrs mplAlloc).vtable
            outerIdx valPtr fmtFn opts).onOom (st, f) s0 sf)) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    SepWPp P (s0.readReg64 Reg.lr) sm
      (fmtArgEntriesAt false argsPtr args ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
        stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable outerIdx valPtr fmtFn opts).post (st, f) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
            (fmtInnerBudgetStep (manyArgStep argPieces))
            (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
            (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
            stackBytes out va.vtable outerIdx valPtr fmtFn opts).onPanic (st, f) s0 sf ∗ R)
      (fun sf =>
        (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
          (fmtInnerBudgetStep (manyArgStep argPieces))
          (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
          (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
          stackBytes out va.vtable outerIdx valPtr fmtFn opts).onOom (st, f) s0 sf) := by
  intro B va
  have hcb :
      FmtCallbacks P (fmtInnerBudgetW B st0 va R_sub t0 out)
        (fmtInnerBudgetStep (manyArgStep subPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 subPieces))
        subStack out va.vtable va.writeStr cs :=
    { transport := fun st_i s_i s_i' hf =>
        fmtInnerBudgetW_transport B st0 va R_sub t0 out st_i s_i s_i' hf
      write_str := fun ptr sbs _ =>
        cliStringBudgetWriteStrCall_ok L.toCliFmtWriteLink st0 R_sub
          (manyArgStep subPieces) (manyArgPanic subPieces) (manyArgOom B st0 subPieces)
          t0 subStack out ptr sbs ⟨hsubStk.1, by omega⟩
      fmt_arg := hargsOk }
  have hcore := subroutine_ok_of_multiCodeLoaded_local L.clCore
    (coreFmtWrite_ok L.plCore L.noExtCore0
      (fmtInnerBudgetW B st0 va R_sub t0 out)
      (fmtInnerBudgetStep (manyArgStep subPieces))
      (fmtInnerBudgetPanic t0 (manyArgPanic subPieces))
      (fmtInnerBudgetOom B st0 (manyArgOom B st0 subPieces))
      subStack)
  refine call_wpp_where (x := (out, va.vtable, va.writeStr, false, tpl, args, st))
    (F := F_frame) hcore hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ _ hm_pan => ?_)
    (fun sf_call hpcf hrunf hspf hcsf hcl_sf => ?_)
    (fun sf R' _ hoom => ?_)
  · refine Satisfies.mono ?_ hm
    have htr := fmtInnerBudgetW_transport B st0 va R_sub t0 out st s0 sm hframe
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left htr))) ?_
    have hdupW := fmtInnerBudgetW_dup_vtable_and_R (B := B) (st0 := st0) (va := va)
      (t0 := t0) (out := out) (st := st) (s := sm) htpl_dup
    refine Entails.trans (Entails.of_eq (show
      (fmtArgEntriesAt false argsPtr args ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st sm ∗
        stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R' =
      (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗
        ((tplPtr ↦ᵣ tpl) ∗ fmtArgEntriesAt false argsPtr args) ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st sm ∗
        stackFrameAt sm.sp (0x70 + subStack)) ∗ (F_frame ∗ R') by
      dsimp only [toRustAllocBudget, B] at hdupW ⊢
      conv => lhs; rw [hdupW]
      sep_ac_rfl)) ?_
    refine sepConj_mono_left ?_
    dsimp only [coreFmtWriteSpec, fmtArgumentsAt]
    rw [hx2_sm, hx3_sm, heven]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.pure_right ⟨hx0_sm, hx1_sm, hsubStk.2, cs, hdec, hcb⟩ (Entails.refl _)
  · dsimp only [coreFmtWriteSpec, fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic,
      callPieces] at hm_pan ⊢
    rw [hx2_sm, hx3_sm] at hm_pan
    rw [hpcs]
    refine Satisfies.mono (sepConj_mono_left ?_) hm_pan
    refine Entails.trans panic_frame_anyHeap ?_
    refine Entails.pure_left fun ⟨cs', c, st_m, hdec', hreach, hpC⟩ => ?_
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    exact Entails.pure_right (reaches_manyPanic hreach hpC) (Entails.refl _)
  · dsimp only [coreFmtWriteSpec, fmtArgumentsAt]
    rw [hx2_sm, hx3_sm, heven]
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro R' hm_after hL_P
    rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
    rcases hm_after with ⟨ok, hm_after⟩
    rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm_after
    rcases hm_after with ⟨st', hm_after⟩
    have hm1 :
        sf_call.mem ⊨ ⌜(sf_call.readReg32 .x0 = if ok then 0#32 else 1#32) ∧
          ∃ cs', decodeFmtArguments tplPtr argsPtr tpl args = some cs' ∧
            FmtRun (fmtInnerBudgetStep (manyArgStep subPieces)) cs' st ok st'⌝ ∗
          (((fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗
            (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl))) ∗ R') := by
      refine Satisfies.mono ?_ hm_after
      exact Entails.of_eq (by sep_ac_rfl)
    rw [satisfies_pure_sepConj] at hm1
    rcases hm1 with ⟨⟨hw0, cs', hdec', hrun'⟩, hm2⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    obtain ⟨hok, happ⟩ := run_many hrun'
    subst hok
    have hstep_outer :
        manyArgStep argPieces (.fmtArg outerIdx valPtr fmtFn opts) st true st' := by
      dsimp only [manyArgStep, callPieces]
      rw [hpcs]
      exact ⟨rfl, happ⟩
    have hm3 :
        sf_call.mem ⊨
          (fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R' := by
      have hdrop :
          ((fmtArgEntriesAt false argsPtr args ∗
            fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
            stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗
            (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl))) ∗ R' =
          (((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ (tplPtr ↦ᵣ tpl)) ∗
            ((fmtArgEntriesAt false argsPtr args ∗
              fmtInnerBudgetW B st0 va R_sub t0 out st' sf_call ∗
              stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame) ∗ R') := by
        sep_ac_rfl
      rw [hdrop] at hm2
      exact Satisfies.drop_left hm2
    exact hnext sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0 hstep_outer R' hm3 hL_P
  · dsimp only [coreFmtWriteSpec, fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom,
      callPieces] at hoom ⊢
    rw [hx2_sm, hx3_sm] at hoom
    rw [hpcs]
    rw [satisfies_pure_sepConj] at hoom ⊢
    rcases hoom.1 with ⟨cs', c, st_m, hdec', hreach, hoC⟩
    have hcsEq : cs' = cs := Option.some.inj (hdec'.symm.trans hdec)
    subst cs'
    exact ⟨reaches_manyOom hreach hoC, Satisfies.drop_left hoom.2⟩

/-! ## 5. Placed Sub-Formatter Proofs (`Blocks 396, 397, 394, 393, 392`) -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 396

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 397

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 394

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 393

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 392

private theorem ls_checkNoSvc0_396 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 396).text = true := by
  rw [← blkLib_eq_396]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_397 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 397).text = true := by
  rw [← blkLib_eq_397]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_394 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 394).text = true := by
  rw [← blkLib_eq_394]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_393 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 393).text = true := by
  rw [← blkLib_eq_393]; exact eagerReduce (Eq.refl true)

private theorem ls_checkNoSvc0_392 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 392).text = true := by
  rw [← blkLib_eq_392]; exact eagerReduce (Eq.refl true)

/-- Unfold read-write `fmtRef32 false` to `↦₃₂`. -/
theorem fmtRef32_false (p : BitVec 64) (v : BitVec 32) :
    fmtRef32 false p v = (p ↦₃₂ v) := by
  simp only [fmtRef32, Bool.false_eq_true, ↓reduceIte]

/-- Unfold read-write `fmtRef64 false` to `↦₆₄`. -/
theorem fmtRef64_false (p v : BitVec 64) :
    fmtRef64 false p v = (p ↦₆₄ v) := by
  simp only [fmtRef64, Bool.false_eq_true, ↓reduceIte]

/-- Unfold read-write 1-element `fmtArgEntriesAt false`. -/
theorem fmtArgEntriesAt_false_singleton (p v0 fn0 : BitVec 64) :
    fmtArgEntriesAt false p [(v0, fn0)] =
      ((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ fn0)) := by
  simp only [fmtArgEntriesAt, Bool.false_eq_true, ↓reduceIte, sepConj_emp]

/-- Unfold read-write 2-element `fmtArgEntriesAt false`. -/
theorem fmtArgEntriesAt_false_pair (p v0 fn0 v1 fn1 : BitVec 64) :
    fmtArgEntriesAt false p [(v0, fn0), (v1, fn1)] =
      (((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ fn0)) ∗
        (((p + 16#64) ↦₆₄ v1) ∗ ((p + 16#64 + 8#64) ↦₆₄ fn1))) := by
  simp only [fmtArgEntriesAt, Bool.false_eq_true, ↓reduceIte, sepConj_emp]

/-- Placed `fmtArgCallSpec` for `<&u32 as core::fmt::Display>::fmt` (`Block 396`, `8` B). -/
theorem spqrRefU32Display_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out refPtr valPtr : BitVec 64) (val : BitVec 32)
    (hpcs : argPieces idx = [formatDecimalNat val.toNat])
    (hstk : 192 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (refPtr ↦₆₄ valPtr) ∗
        ((valPtr ↦₃₂ val) ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 396)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx refPtr (lsmpl.base 396) defaultFmtOptions) := by
  intro B va
  let R_inner :=
    ((valPtr ↦₃₂ val) ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
  have hR_eq : R_client = (refPtr ↦₆₄ valPtr) ∗ R_inner := hR
  have hu32 := fmtArgCallSpec_many_of_known (argPieces := argPieces) hpcs
    (cliU32Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU32 L.clFmtU32
      st0 R_rest (fun _ => formatDecimalNat val.toNat) t0 stringWriterStack stackBytes
      idx out valPtr false val rfl ⟨Nat.le_refl _, by omega⟩ hstk.1)
  rw [fmtRef32_false] at hu32
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = refPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        (((refPtr ↦₆₄ valPtr) ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 396
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 396 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_396
    (mid := coreFmtMultiLib.fnAddr mplFmt u32DisplayFmtSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_396).rebase (blkPl_396).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_396).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  iterate 2 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieU32])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  have hsp_sm : sm.sp = s0.sp := by
    rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
  have hframe : FmtWriteFrame s0 sm :=
    fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  have hcs_sm : CalleeSavedPreserved s0 sm :=
    hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
  exact SepWPp.tailcall (x := (st, f)) (F := refPtr ↦₆₄ valPtr) hu32
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieU32])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (fun R' hm => by
      refine Satisfies.mono ?_ hm
      have htr := fmtInnerBudgetW_transport B st0 va R_inner t0 out st s0 sm hframe
      refine Entails.trans
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left htr)))) ?_
      have hx0_sm : sm.readReg64 .x0 = valPtr := by
        rw [hcpu_out.readReg64]; simp [arm64_norm]
      have hx1_sm : sm.readReg64 .x1 = f := by
        rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0
      refine Entails.trans (Entails.of_eq (show
        ((refPtr ↦₆₄ valPtr) ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st sm ∗
          stackFrameAt s0.sp stackBytes) ∗ R' =
        (formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st sm ∗
          stackFrameAt sm.sp stackBytes) ∗ ((refPtr ↦₆₄ valPtr) ∗ R') by
        dsimp only [fmtInnerBudgetW, toRustAllocBudget, B, R_inner]
        rw [hsp_sm]
        sep_ac_rfl)) ?_
      refine sepConj_mono_left ?_
      dsimp only [fmtArgCallSpec, fmtRef32, Bool.false_eq_true, ↓reduceIte, R_inner]
      exact Entails.pure_right ⟨hx0_sm, hx1_sm⟩ (Entails.refl _))
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ hm_pan => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces] at hm_pan ⊢
      exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan)
    (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => by
      dsimp only [fmtArgCallSpec, fmtRef32, Bool.false_eq_true, ↓reduceIte] at hm_post ⊢
      rw [hsp_sm] at hm_post
      refine Satisfies.mono (sepConj_mono_left ?_) hm_post
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_mono fun ok => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_mono fun st' => ?_
      dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces]
      exact Entails.of_eq (by
        rw [hR_eq]
        dsimp only [fmtInnerBudgetW, toRustAllocBudget, B, R_inner]
        sep_ac_rfl),
      hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩)
    (fun sf R' _ hoom => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces] at hoom ⊢
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩)

/-- Placed `fmtArgCallSpec` for `<&u64 as core::fmt::Display>::fmt` (`Block 397`, `8` B). -/
theorem spqrRefU64Display_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out refPtr valPtr val : BitVec 64)
    (hpcs : argPieces idx = [formatDecimalNat val.toNat])
    (hstk : 240 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (refPtr ↦₆₄ valPtr) ∗
        ((valPtr ↦₆₄ val) ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 397)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx refPtr (lsmpl.base 397) defaultFmtOptions) := by
  intro B va
  let R_inner :=
    ((valPtr ↦₆₄ val) ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗ R_rest
  have hR_eq : R_client = (refPtr ↦₆₄ valPtr) ∗ R_inner := hR
  have hu64 := fmtArgCallSpec_many_of_known (argPieces := argPieces) hpcs
    (cliU64Display_fmtArg_ok L.toCliFmtWriteLink L.plFmt L.noExtFmtU64 L.clFmtU64
      st0 R_rest (fun _ => formatDecimalNat val.toNat) t0 stringWriterStack stackBytes
      idx out valPtr false val rfl ⟨Nat.le_refl _, by omega⟩ hstk.1)
  rw [fmtRef64_false] at hu64
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = refPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        (((refPtr ↦₆₄ valPtr) ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 397
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 397 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_397
    (mid := coreFmtMultiLib.fnAddr mplFmt u64DisplayFmtSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_397).rebase (blkPl_397).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_397).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  iterate 2 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieU64])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  have hsp_sm : sm.sp = s0.sp := by
    rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq
  have hframe : FmtWriteFrame s0 sm :=
    fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq)
  have hcs_sm : CalleeSavedPreserved s0 sm :=
    hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
  exact SepWPp.tailcall (x := (st, f)) (F := refPtr ↦₆₄ valPtr) hu64
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieU64])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rwa [hsp_sm])
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (fun R' hm => by
      refine Satisfies.mono ?_ hm
      have htr := fmtInnerBudgetW_transport B st0 va R_inner t0 out st s0 sm hframe
      refine Entails.trans
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left htr)))) ?_
      have hx0_sm : sm.readReg64 .x0 = valPtr := by
        rw [hcpu_out.readReg64]; simp [arm64_norm]
      have hx1_sm : sm.readReg64 .x1 = f := by
        rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0
      refine Entails.trans (Entails.of_eq (show
        ((refPtr ↦₆₄ valPtr) ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st sm ∗
          stackFrameAt s0.sp stackBytes) ∗ R' =
        (formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st sm ∗
          stackFrameAt sm.sp stackBytes) ∗ ((refPtr ↦₆₄ valPtr) ∗ R') by
        dsimp only [fmtInnerBudgetW, toRustAllocBudget, B, R_inner]
        rw [hsp_sm]
        sep_ac_rfl)) ?_
      refine sepConj_mono_left ?_
      dsimp only [fmtArgCallSpec, fmtRef64, Bool.false_eq_true, ↓reduceIte, R_inner]
      exact Entails.pure_right ⟨hx0_sm, hx1_sm⟩ (Entails.refl _))
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ hm_pan => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetPanic, manyArgPanic, callPieces] at hm_pan ⊢
      exact Satisfies.mono (sepConj_mono_left panic_frame_anyHeap) hm_pan)
    (fun sf _ _ hspf hcs_sf => ⟨fun hm_post => by
      dsimp only [fmtArgCallSpec, fmtRef64, Bool.false_eq_true, ↓reduceIte] at hm_post ⊢
      rw [hsp_sm] at hm_post
      refine Satisfies.mono (sepConj_mono_left ?_) hm_post
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_mono fun ok => ?_
      rw [sepExists_sepConj_left]
      refine Entails.sepExists_mono fun st' => ?_
      dsimp only [fmtInnerBudgetStep, manyArgStep, callPieces]
      exact Entails.of_eq (by
        rw [hR_eq]
        dsimp only [fmtInnerBudgetW, toRustAllocBudget, B, R_inner]
        sep_ac_rfl),
      hspf.trans hsp_sm, hcs_sm.trans hcs_sf⟩)
    (fun sf R' _ hoom => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetOom, manyArgOom, callPieces] at hoom ⊢
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨hoom.1, Satisfies.drop_left hoom.2⟩)

/-- Placed `fmtArgCallSpec` for `<&spqr::encoding::polynomial::PolynomialError as Display>::fmt`
    (`Block 394`, `72` B). -/
theorem spqrPolyErrorDisplay_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out refPtr bytePtr : BitVec 64) (b1 : BitVec 8)
    (hpcs : argPieces idx = [spqrPolyBytes b1])
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1) ∗ spqrErrorRoSep lsmpl ∗ R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 394)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx refPtr (lsmpl.base 394) defaultFmtOptions) := by
  intro B va
  let F_cells := (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1)
  let R_inner := spqrErrorRoSep lsmpl ∗ R_rest
  have hR_eq : R_client = F_cells ∗ R_inner := by
    rw [hR]; dsimp only [F_cells, R_inner]; sep_ac_rfl
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = refPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 394
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 394 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_394
    (mid := coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_394).rebase (blkPl_394).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_394).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  dsimp only [F_cells]
  by_cases hb0 : b1 = 0#8
  · subst hb0
    iterate 7 wp_step
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out _hcl_sm hpseg => ?_
    refine SepWPp.congr_pre (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
        stackFrameAt s0.sp stackBytes by
      rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
    exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
      (lsmpl.base 394) f defaultFmtOptions (lsmpl.ρ spqrPolyDiv2Sym) spqrPolyDiv2Bs st R s0 sm
      (by simpa [spqrPolyBytes] using hpcs) hstk
      (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
      hsp0
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
      (by decide)
      (hcpu_in.calleeSavedPreserved hcpu_out (by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
  · by_cases hb1 : b1 = 1#8
    · subst hb1
      iterate 9 wp_step
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out _hcl_sm hpseg => ?_
      refine SepWPp.congr_pre (show _ =
        formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes by
        rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
      exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
        (lsmpl.base 394) f defaultFmtOptions (lsmpl.ρ spqrPolyTooLongSym) spqrPolyTooLongBs st R s0 sm
        (by simpa [spqrPolyBytes] using hpcs) hstk
        (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
        hsp0
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
        (by decide)
        (hcpu_in.calleeSavedPreserved hcpu_out (by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
    · iterate 9 wp_step
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out _hcl_sm hpseg => ?_
      refine SepWPp.congr_pre (show _ =
        formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes by
        rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
      exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
        (lsmpl.base 394) f defaultFmtOptions (lsmpl.ρ spqrPolyInvalidSym) spqrPolyInvalidBs st R s0 sm
        (by simpa [spqrPolyBytes, hb0, hb1] using hpcs) hstk
        (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
        hsp0
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
        (by decide)
        (hcpu_in.calleeSavedPreserved hcpu_out (by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

/-- Placed `fmtArgCallSpec` for `<&spqr::serialize::Error as Display>::fmt` (`Block 393`, `52` B). -/
theorem spqrSerErrorDisplay_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out refPtr bytePtr : BitVec 64) (b1 : BitVec 8)
    (hpcs : argPieces idx = [spqrSerBytes b1])
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1) ∗ spqrErrorRoSep lsmpl ∗ R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 393)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx refPtr (lsmpl.base 393) defaultFmtOptions) := by
  intro B va
  let F_cells := (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1)
  let R_inner := spqrErrorRoSep lsmpl ∗ R_rest
  have hR_eq : R_client = F_cells ∗ R_inner := by
    rw [hR]; dsimp only [F_cells, R_inner]; sep_ac_rfl
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = refPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  refine ⟨_, hm0, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 393
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 393 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_393
    (mid := coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_393).rebase (blkPl_393).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_393).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  dsimp only [F_cells]
  by_cases hb1 : b1 = 1#8
  · subst hb1
    iterate 8 wp_step
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out _hcl_sm hpseg => ?_
    refine SepWPp.congr_pre (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
        stackFrameAt s0.sp stackBytes by
      rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
    exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
      (lsmpl.base 393) f defaultFmtOptions (lsmpl.ρ spqrSerCodecSym) spqrSerCodecBs st R s0 sm
      (by simpa [spqrSerBytes] using hpcs) hstk
      (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
      hsp0
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
      (by decide)
      (hcpu_in.calleeSavedPreserved hcpu_out (by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
  · iterate 8 wp_step
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out _hcl_sm hpseg => ?_
    refine SepWPp.congr_pre (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
        stackFrameAt s0.sp stackBytes by
      rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
    exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
      (lsmpl.base 393) f defaultFmtOptions (lsmpl.ρ spqrSerGeneralSym) spqrSerGeneralBs st R s0 sm
      (by simpa [spqrSerBytes, hb1] using hpcs) hstk
      (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
      hsp0
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
      (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
      (by decide)
      (hcpu_in.calleeSavedPreserved hcpu_out (by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem stack48_split (sp0 : BitVec 64) (stackBytes : Nat)
    (hfit : 48 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp0 stackBytes =
      (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
        ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
        ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5)) ∗
        stackFrameAt (sp0 - 48#64) (stackBytes - 48) := by
  have h1 : stackBytes = 48 + (stackBytes - 48) := by omega
  conv => lhs; rw [h1]
  rw [stackFrameAt_split sp0 48 (stackBytes - 48) (by omega)]
  have h48 : stackFrameAt sp0 48 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
        ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
        ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
        ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5) := by
    simp only [arm64_norm]
  rw [h48]

private theorem stack48_fold (sp0 v0 v1 v2 v3 v4 v5 : BitVec 64) (stackBytes : Nat)
    (hfit : 48 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    ((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
      ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
      ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5) ∗
      stackFrameAt (sp0 - 48#64) (stackBytes - 48) ⊢
    stackFrameAt sp0 stackBytes := by
  rw [stack48_split sp0 stackBytes hfit]
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp0 - 48#64) ↦₆₄ v0) ∗ ((sp0 - 40#64) ↦₆₄ v1) ∗
      ((sp0 - 32#64) ↦₆₄ v2) ∗ ((sp0 - 24#64) ↦₆₄ v3) ∗
      ((sp0 - 16#64) ↦₆₄ v4) ∗ ((sp0 - 8#64) ↦₆₄ v5)) ∗
      stackFrameAt (sp0 - 48#64) (stackBytes - 48) by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

private theorem decode_spqrEncPolyTpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrEncPolyTplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrEncPolyPreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Compose `CalleeSavedPreserved s0 sf` across a `stp x29,x30 → bl → ldp x29,x30` frame:
    `x19..x28` and `calleeSavedVRegs` are preserved across `s0 → sm → sf_call → sf` while
    `Reg.fp` (`x29`) is restored directly in the epilogue. -/
theorem calleeSavedPreserved_across_fp_frame {s0 s1' sm' sm sf_call s2' sf' sf : State}
    (h1_in : VerifiedLibraries.RustStd.SameCpuState s1' s0)
    (h1_out : VerifiedLibraries.RustStd.SameCpuState sm sm')
    (hcall : CalleeSavedPreserved sm sf_call)
    (h2_in : VerifiedLibraries.RustStd.SameCpuState s2' sf_call)
    (h2_out : VerifiedLibraries.RustStd.SameCpuState sf sf')
    (hpro :
      sm'.readReg64 (.gpr 19#5) = s1'.readReg64 (.gpr 19#5) ∧
      sm'.readReg64 (.gpr 20#5) = s1'.readReg64 (.gpr 20#5) ∧
      sm'.readReg64 (.gpr 21#5) = s1'.readReg64 (.gpr 21#5) ∧
      sm'.readReg64 (.gpr 22#5) = s1'.readReg64 (.gpr 22#5) ∧
      sm'.readReg64 (.gpr 23#5) = s1'.readReg64 (.gpr 23#5) ∧
      sm'.readReg64 (.gpr 24#5) = s1'.readReg64 (.gpr 24#5) ∧
      sm'.readReg64 (.gpr 25#5) = s1'.readReg64 (.gpr 25#5) ∧
      sm'.readReg64 (.gpr 26#5) = s1'.readReg64 (.gpr 26#5) ∧
      sm'.readReg64 (.gpr 27#5) = s1'.readReg64 (.gpr 27#5) ∧
      sm'.readReg64 (.gpr 28#5) = s1'.readReg64 (.gpr 28#5) ∧
      calleeSavedVRegs sm' = calleeSavedVRegs s1')
    (hepi :
      sf'.readReg64 (.gpr 19#5) = s2'.readReg64 (.gpr 19#5) ∧
      sf'.readReg64 (.gpr 20#5) = s2'.readReg64 (.gpr 20#5) ∧
      sf'.readReg64 (.gpr 21#5) = s2'.readReg64 (.gpr 21#5) ∧
      sf'.readReg64 (.gpr 22#5) = s2'.readReg64 (.gpr 22#5) ∧
      sf'.readReg64 (.gpr 23#5) = s2'.readReg64 (.gpr 23#5) ∧
      sf'.readReg64 (.gpr 24#5) = s2'.readReg64 (.gpr 24#5) ∧
      sf'.readReg64 (.gpr 25#5) = s2'.readReg64 (.gpr 25#5) ∧
      sf'.readReg64 (.gpr 26#5) = s2'.readReg64 (.gpr 26#5) ∧
      sf'.readReg64 (.gpr 27#5) = s2'.readReg64 (.gpr 27#5) ∧
      sf'.readReg64 (.gpr 28#5) = s2'.readReg64 (.gpr 28#5) ∧
      sf'.readReg64 Reg.fp = s0.readReg64 Reg.fp ∧
      calleeSavedVRegs sf' = calleeSavedVRegs s2') :
    CalleeSavedPreserved s0 sf := by
  rcases hpro with ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, av⟩
  rcases (CalleeSavedPreserved.iff_regs sm sf_call).mp hcall with
    ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, _, bv⟩
  rcases hepi with ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩
  rw [CalleeSavedPreserved.iff_regs]
  exact ⟨(h2_out.readReg64 _).trans (c19.trans ((h2_in.readReg64 _).trans
      (b19.trans ((h1_out.readReg64 _).trans (a19.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c20.trans ((h2_in.readReg64 _).trans
      (b20.trans ((h1_out.readReg64 _).trans (a20.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c21.trans ((h2_in.readReg64 _).trans
      (b21.trans ((h1_out.readReg64 _).trans (a21.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c22.trans ((h2_in.readReg64 _).trans
      (b22.trans ((h1_out.readReg64 _).trans (a22.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c23.trans ((h2_in.readReg64 _).trans
      (b23.trans ((h1_out.readReg64 _).trans (a23.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c24.trans ((h2_in.readReg64 _).trans
      (b24.trans ((h1_out.readReg64 _).trans (a24.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c25.trans ((h2_in.readReg64 _).trans
      (b25.trans ((h1_out.readReg64 _).trans (a25.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c26.trans ((h2_in.readReg64 _).trans
      (b26.trans ((h1_out.readReg64 _).trans (a26.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c27.trans ((h2_in.readReg64 _).trans
      (b27.trans ((h1_out.readReg64 _).trans (a27.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans (c28.trans ((h2_in.readReg64 _).trans
      (b28.trans ((h1_out.readReg64 _).trans (a28.trans (h1_in.readReg64 _)))))),
    (h2_out.readReg64 _).trans cfp,
    h2_out.calleeSavedVRegs.trans (cv.trans (h2_in.calleeSavedVRegs.trans
      (bv.trans (h1_out.calleeSavedVRegs.trans (av.trans h1_in.calleeSavedVRegs)))))⟩

/-- Placed `fmtArgCallSpec` for `<&spqr::encoding::EncodingError as Display>::fmt`
    (`Block 392`, `144` B). -/
theorem spqrEncErrorDisplay_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out refPtr bytePtr : BitVec 64) (b1 : BitVec 8)
    (hpcs : argPieces idx = spqrEncPieces b1)
    (hstk : 0x30 + 0x70 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1) ∗ spqrErrorRoSep lsmpl ∗ R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 392)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx refPtr (lsmpl.base 392) defaultFmtOptions) := by
  intro B va
  let F_cells := (refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1)
  let R_inner := spqrErrorRoSep lsmpl ∗ R_rest
  have hR_eq : R_client = F_cells ∗ R_inner := by
    rw [hR]; dsimp only [F_cells, R_inner]; sep_ac_rfl
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = refPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  by_cases hle2 : b1.toNat ≤ 2
  · rw [stack48_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
    have hm1 :
        s0.mem ⊨
          (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5,
            ((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
            ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
            ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
          ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
            fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
            stackFrameAt (s0.sp - 48#64) (stackBytes - 48)) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
    iterate 6 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
    rename_i v0 v1 v2 v3 v4 v5
    rw [← sepConj_assoc] at hm1
    refine ⟨_, hm1, ?_⟩
    refine sepWPp_seg_lib_block_pureWhere 392
      ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
      (L.noExtLs 392 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
      ls_checkNoSvc0_392
      (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
      hcl0 fun s' hcpu_in => ?_
    rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_392).rebase (blkPl_392).base (fun _ => none))]
    have hpc' : s'.pc = (blkPl_392).base := hcpu_in.pc_eq.trans hpc0
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
    have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
    have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
    have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
    dsimp only [F_cells]
    wp_conv_pre => unfold formatterAt
    iterate 17 wp_step
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
      (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hpseg => ?_
    let subStack := stackBytes - 0x30 - 0x70
    let subPieces : Nat → List (List (BitVec 8)) := fun _ => [spqrPolyBytes b1]
    let R_sub : SepProp :=
      ((s0.sp - 40#64) ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1) ∗ spqrErrorRoSep lsmpl ∗ R_rest
    let F_frame : SepProp :=
      (refPtr ↦₆₄ bytePtr) ∗ formatterAt f out va.vtable defaultFmtOptions ∗
        ((s0.sp - 48#64) ↦₆₄ v0) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
    have hsp_sm : sm.sp = s0.sp - 48#64 := by
      rw [hcpu_out.sp_eq]; simp [arm64_norm]
    have heven32 : (s0.sp - 32#64).getLsbD 0 = false :=
      getLsbD0_sub_even_of_spAligned hsp0 32 (by decide)
    have hstk_sm : 0x70 + subStack = stackBytes - 48 := by
      dsimp only [subStack]; omega
    refine SepWPp.congr_pre (show _ =
      fmtArgEntriesAt false (s0.sp - 32#64) [(s0.sp - 40#64, lsmpl.base 394)] ∗
        fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
        stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
      have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) :=
        hcpu_in.readReg64 (.gpr 29#5)
      have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr :=
        hcpu_in.readReg64 Reg.lr
      have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
      rw [fmtArgEntriesAt_false_singleton]
      dsimp only [R_sub, R_inner, F_frame, formatterAt, fmtInnerBudgetW]
      rw [hsp_sm, hstk_sm, hfp, hlr_in, ha24]
      sep_ac_rfl) ?_
    refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
      out refPtr (lsmpl.base 392) f (lsmpl.base 392 + 0x6c#64)
      (lsmpl.ρ spqrEncPolyTplSym) (s0.sp - 32#64) defaultFmtOptions spqrEncPolyTplBs
      [(s0.sp - 40#64, lsmpl.base 394)]
      [FmtCall.writeStr (lsmpl.ρ spqrEncPolyTplSym + 1#64) spqrEncPolyPreBs,
       FmtCall.fmtArg 0 (s0.sp - 40#64) (lsmpl.base 394) defaultFmtOptions]
      st R s0 sm
      (by simpa [spqrEncPieces, hle2, subPieces, callPieces] using hpcs)
      ⟨by dsimp only [subStack]; omega, by omega⟩
      heven32
      (decode_spqrEncPolyTpl _ _ _ _ heven32)
      (spqrErrorRoSep_dup_in_R (F := ((s0.sp - 40#64) ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1))
        (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
      (fun idx_i val_i fn_i opt_i hmem_i => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          FmtCall.fmtArg.injEq] at hmem_i
        rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
        exact spqrPolyErrorDisplay_fmtArg_ok L st0 subPieces t0 subStack 0 out
          (s0.sp - 40#64) bytePtr b1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
      hcl_sm
      (fmtWriteFrame_of_pureSeg hpseg
        (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
        (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
      (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
      (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
      (by
        unfold State.spAligned at hsp0 ⊢
        rw [hsp_sm]
        exact spAligned_sub_16k hsp0 48 (by decide))
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
      (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
      fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
    have hsp_sf : sf_call.sp = s0.sp - 48#64 := hspf.trans hsp_sm
    refine sepWPp_seg_lib_block_pureWhere 392
      ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
      (L.noExtLs 392 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
      ls_checkNoSvc0_392
      (mid := s0.readReg64 Reg.lr)
      hcl_sf fun s2' hcpu2_in => ?_
    rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_392).rebase (blkPl_392).base (fun _ => none))]
    have hpc2' : s2'.pc = (blkPl_392).base + 108#64 := hcpu2_in.pc_eq.trans hpcf
    have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
    have hsp2' : s2'.sp = s0.sp - 48#64 := hcpu2_in.sp_eq.trans hsp_sf
    have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
    have ha24 : s0.sp - 32#64 + 8#64 = s0.sp - 24#64 := by bv_omega
    have hstk_sm' : 0x70 + subStack = stackBytes - 48 := by
      dsimp only [subStack]; omega
    dsimp only [F_frame, R_sub]
    wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha24, hsp_sm, hstk_sm']
    iterate 3 wp_step
    refine SepWP.done
      (by simp only [arm64_norm])
      (by simpa [arm64_norm] using hrun2')
      fun sf hcpu2_out _hcl_end hpseg2 => ?_
    have hpc_end : sf.pc = s0.readReg64 Reg.lr := by
      rw [hcpu2_out.pc_eq]; simp [arm64_norm]
    have hrun_end : sf.status = .Running := by
      rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
    have hsp_end : sf.sp = s0.sp := by
      rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
    have hw0_end : sf.readReg32 .x0 &&& 1#32 = 0#32 := by
      have h := (hcpu2_out.readReg32 .x0).trans (by simpa [arm64_norm] using hx0_2')
      rw [h]; decide
    have hframe2 : FmtWriteFrame sf_call sf :=
      fmtWriteFrame_of_pureSeg hpseg2
        (by rw [hcpu2_out.sigActions_eq]; simpa [arm64_norm] using hcpu2_in.sigActions_eq)
        (by rw [hcpu2_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu2_in.tpidrEl0_eq)
    have hcs_end : CalleeSavedPreserved s0 sf :=
      calleeSavedPreserved_across_fp_frame hcpu_in hcpu_out hcsf hcpu2_in hcpu2_out
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
    exact fun R' hm_end _ => ⟨sf, .refl sf, Or.inl ⟨hpc_end, hrun_end, _, hm_end, ⟨fun hm_post => by
      dsimp only [fmtArgCallSpec, fmtInnerBudgetStep]
      refine Satisfies.mono (sepConj_mono_left ?_) hm_post
      refine Entails.sepExists_right true (Entails.sepExists_right st' ?_)
      refine Entails.pure_right ⟨hw0_end, hstep_outer⟩ ?_
      have htr2 := fmtInnerBudgetW_transport B st0 va R_inner t0 out st' sf_call sf hframe2
      have hfmt24 := formatterAt_entails_memRegion24 f out va.vtable defaultFmtOptions
      have hfold48 := stack48_fold s0.sp v0 bytePtr (s0.sp - 40#64) (lsmpl.base 394)
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes ⟨by omega, hstk.2⟩
      refine Entails.trans (Entails.of_eq (show _ =
        formatterAt f out va.vtable defaultFmtOptions ∗
          ((refPtr ↦₆₄ bytePtr) ∗ (bytePtr ↦₈ b1) ∗
            fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
          (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ bytePtr) ∗
            ((s0.sp - 32#64) ↦₆₄ (s0.sp - 40#64)) ∗ ((s0.sp - 24#64) ↦₆₄ lsmpl.base 394) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
            stackFrameAt (s0.sp - 48#64) (stackBytes - 48)) by
        dsimp only [fmtInnerBudgetW, R_inner, B, va]; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hfmt24
        (sepConj_mono (sepConj_mono_right (sepConj_mono_right htr2)) hfold48)) ?_
      exact Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl),
      hsp_end, hcs_end⟩⟩⟩
  · refine ⟨_, hm0, ?_⟩
    refine sepWPp_seg_lib_block_pureWhere 392
      ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
      (L.noExtLs 392 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
      ls_checkNoSvc0_392
      (mid := coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
      hcl0 fun s' hcpu_in => ?_
    rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_392).rebase (blkPl_392).base (fun _ => none))]
    have hpc' : s'.pc = (blkPl_392).base := hcpu_in.pc_eq.trans hpc0
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
    have hx0' : s'.readReg64 .x0 = refPtr := (hcpu_in.readReg64 .x0).trans hx0_0
    dsimp only [F_cells]
    by_cases hb3 : b1 = 3#8
    · subst hb3
      iterate 13 wp_step
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out _hcl_sm hpseg => ?_
      refine SepWPp.congr_pre (show _ =
        formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes by
        rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
      exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
        (lsmpl.base 392) f defaultFmtOptions (lsmpl.ρ spqrEncIndexSym) spqrEncIndexBs st R s0 sm
        (by simpa [spqrEncPieces] using hpcs) ⟨by omega, hstk.2⟩
        (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
        hsp0
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
        (by decide)
        (hcpu_in.calleeSavedPreserved hcpu_out (by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))
    · have hb_ge4 : 4 ≤ b1.toNat := by
        have : b1.toNat ≠ 3 := fun h => hb3 (BitVec.eq_of_toNat_eq h)
        omega
      iterate 13 wp_step
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out _hcl_sm hpseg => ?_
      refine SepWPp.congr_pre (show _ =
        formatterAt f out va.vtable defaultFmtOptions ∗
          fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes by
        rw [hR_eq]; dsimp only [fmtInnerBudgetW, F_cells]; sep_ac_rfl) ?_
      exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out refPtr
        (lsmpl.base 392) f defaultFmtOptions (lsmpl.ρ spqrEncDataSym) spqrEncDataBs st R s0 sm
        (by simpa [spqrEncPieces, hle2, hb3] using hpcs) ⟨by omega, hstk.2⟩
        (spqrErrorRoSep_dup_in_R (by decide) hR_eq)
        (fmtWriteFrame_of_pureSeg hpseg
          (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
          (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
        (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simpa [arm64_norm] using hcpu_in.sp_eq)
        hsp0
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
        (by rw [hcpu_out.readReg64]; simpa [arm64_norm, hcpu_in.readReg64] using hx1_0)
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
        (by decide)
        (hcpu_in.calleeSavedPreserved hcpu_out (by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
