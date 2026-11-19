/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import GeneratedLean.LibsignalSessionPlacedObjShard20

/-!
# Real-Code Proof of `<spqr::Error as core::fmt::Display>::fmt` (`Block 412`) & `format_inner` Discharge

Completes the real-code proof of `<spqr::Error as core::fmt::Display>::fmt`
(`libsignalSessionLib` Block `412`, `776` B = `194` instructions) across all `15` reachable
non-pointer discriminants `d ∈ {0..13, 15}` (`SpqrErrorValidTag d`):
- `8` direct `<Formatter>::write_str` tail-call arms (`d ∈ {0, 1, 2, 3, 7, 8, 12, 15}`);
- `5` 1-argument nested `core::fmt::write` arms (`d = 4` `EpochOutOfRange(u64)` → Block `397`,
  `d = 5` `EncodingDecoding` → Block `392`, `d = 6` `Serialization` → Block `393`,
  `d = 10` `KeyTrimmed(u32)` → Block `396`, `d = 11` `KeyAlreadyRequested(u32)` → Block `396`);
- `2` 2-argument nested `core::fmt::write` arms (`d = 9` `KeyJump(u32, u32)` → Block `396`,
  `d = 13` `SendKeyEpochDecreased(u64, u64)` → Block `397`).

Exports:
- `spqrErrorDisplay_fmtArg_ok`: `fmtArgCallSpec` callback correctness for `lsmpl.base 412`;
- `cliAllocFormatInner_spqrErrorDisplayPrefixed_cells_placed_ok`: exact-event cell-level placed
  `format_inner` correctness (zero `libsignalSessionLib` `.rodata` obligations, ready for
  `ExactOrNilEnv c.exactEvs` in `CliFmtGhostSpecs`);
- `cliAllocFormatInner_spqrErrorDisplayPrefixed_placed_ok`: payload-level (`(errPtr ↦₈ d) ∗
  memRegion (errPtr + 1) 23`) placed `format_inner` correctness establishing
  `FormatInnerPrefixedEnv evs ∧ CliFormatInnerEnv evs`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.Step
open CryptoVerification
  (LibsignalPlacement LibsignalRoLoaded libsignalSessionLib libsignalSessionLib_blocks_length lsmpl)
open CryptoVerification.RustHeap (vecU8)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj
  (PoolMemTransport formatInnerKnownEvents toRustAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
  (CliFormatInnerEnv FormatInnerPrefixedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux
  (SpqrErrorDisplayLink blockProgram_rebase_eq_lsProg callPieces
   calleeSavedPreserved_across_fp_frame cliAllocFormatInnerManyTightSpec
   cliAllocFormatInnerMany_tight_placed_ok cliFormatInnerEnv_of_spqrPieces
   fmtArgEntriesAt_false_pair fmtArgEntriesAt_false_singleton
   fmtInnerBudgetW_transport formatInnerPrefixedEnv_of_spqrPieces formatterAt_entails_memRegion24
   getLsbD0_sub_even_of_spAligned manyArgOom manyArgPanic manyArgStep manyLens
   nested_coreFmtWrite_many_ok sat_spqrErrorRoSep spAligned_sub_16k spqrArm0Bs spqrArm0Sym
   spqrArm1Bs spqrArm1Sym spqrArm2Bs spqrArm2Sym spqrArm3Bs spqrArm3Sym spqrArm4PreBs
   spqrArm4TplBs spqrArm4TplSym spqrArm5PreBs spqrArm5TplBs spqrArm5TplSym spqrArm6PreBs
   spqrArm6TplBs spqrArm6TplSym spqrArm7Bs spqrArm7Sym spqrArm8Bs spqrArm8Sym spqrArm9MidBs
   spqrArm9PreBs spqrArm9TplBs spqrArm9TplSym spqrArm10PreBs spqrArm10TplBs spqrArm10TplSym
   spqrArm11PreBs spqrArm11TplBs spqrArm11TplSym spqrArm12Bs spqrArm12Sym spqrArm13MidBs
   spqrArm13PreBs spqrArm13SufBs spqrArm13TplBs spqrArm13TplSym spqrArm15Bs spqrArm15Sym
   spqrEncErrorDisplay_fmtArg_ok spqrEncPieces spqrErrorCellsAt spqrErrorPieces
   spqrErrorPieces_sum_bounds spqrErrorRoSep spqrErrorRoSep_dup_in_R spqrErrorRoSep_dup_mem
   spqrJumpTableBs spqrJumpTableSym spqrRefU32Display_fmtArg_ok spqrRefU64Display_fmtArg_ok
   spqrSerBytes spqrSerErrorDisplay_fmtArg_ok subroutine_ok_of_sepWPp_clLs
   tailcall_formatterWriteStr_many)
open LibsignalBinary.Proofs.SpqrV1.ErrorDisplayTag
  (SpqrErrorValidTag spqrErrorPayload24_split spqrErrorPayload24_unsplit)
open VerifiedLibraries.RustStd
  (FmtBuf FmtCall FmtInnerBudgetArgsOk FmtWriteFrame allocFormatInnerSym allocMultiLib
   allocStringWriteAddrs coreFmtDecDigitsLutSym coreFmtMultiLib coreFmtWriteSym coreMultiLib
   decDigitsLutBytes decodeFmtArguments decodeFmtPlaceholder decodeFmtTemplate defaultFmtOptions
   fmtArgCallSpec fmtArgEntriesAt fmtArgumentsAt fmtEstimatedCapacity fmtInnerBudgetOom
   fmtInnerBudgetPanic fmtInnerBudgetStep fmtInnerBudgetW fmtLiteralLen fmtStartsWithPlaceholder
   fmtWriteFrame_of_pureSeg formatInnerFrame formatterAt formatterWriteStrSym stringWriteVtableAt
   stringWriterStack)
open VerifiedLibraries.RustStd.CoreFmt (sepWPp_seg_lib_block_pureWhere)

/-! ## 1. Block `412` Rebased Program, `80`-Byte Stack Frame, & Template Decoders -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 4000000 in
gen_ls_blk_ultra 412

private theorem ls_checkNoSvc0_412 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (libsignalSessionLib.blockLib 412).text = true := by
  rw [← blkLib_eq_412]; exact eagerReduce (Eq.refl true)

private theorem stack80_split (sp0 : BitVec 64) (stackBytes : Nat)
    (hfit : 80 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    stackFrameAt sp0 stackBytes =
      (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
        ((sp0 - 80#64) ↦₆₄ v0) ∗ ((sp0 - 72#64) ↦₆₄ v1) ∗
        ((sp0 - 64#64) ↦₆₄ v2) ∗ ((sp0 - 56#64) ↦₆₄ v3) ∗
        ((sp0 - 48#64) ↦₆₄ v4) ∗ ((sp0 - 40#64) ↦₆₄ v5) ∗
        ((sp0 - 32#64) ↦₆₄ v6) ∗ ((sp0 - 24#64) ↦₆₄ v7) ∗
        ((sp0 - 16#64) ↦₆₄ v8) ∗ ((sp0 - 8#64) ↦₆₄ v9)) ∗
        stackFrameAt (sp0 - 80#64) (stackBytes - 80) := by
  have h1 : stackBytes = 80 + (stackBytes - 80) := by omega
  conv => lhs; rw [h1]
  rw [stackFrameAt_split sp0 80 (stackBytes - 80) (by omega)]
  have h80 : stackFrameAt sp0 80 =
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
        ((sp0 - 80#64) ↦₆₄ v0) ∗ ((sp0 - 72#64) ↦₆₄ v1) ∗
        ((sp0 - 64#64) ↦₆₄ v2) ∗ ((sp0 - 56#64) ↦₆₄ v3) ∗
        ((sp0 - 48#64) ↦₆₄ v4) ∗ ((sp0 - 40#64) ↦₆₄ v5) ∗
        ((sp0 - 32#64) ↦₆₄ v6) ∗ ((sp0 - 24#64) ↦₆₄ v7) ∗
        ((sp0 - 16#64) ↦₆₄ v8) ∗ ((sp0 - 8#64) ↦₆₄ v9) := by
    simp only [arm64_norm]
  rw [h80]

private theorem stack80_fold (sp0 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) (stackBytes : Nat)
    (hfit : 80 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64) :
    ((sp0 - 80#64) ↦₆₄ v0) ∗ ((sp0 - 72#64) ↦₆₄ v1) ∗
      ((sp0 - 64#64) ↦₆₄ v2) ∗ ((sp0 - 56#64) ↦₆₄ v3) ∗
      ((sp0 - 48#64) ↦₆₄ v4) ∗ ((sp0 - 40#64) ↦₆₄ v5) ∗
      ((sp0 - 32#64) ↦₆₄ v6) ∗ ((sp0 - 24#64) ↦₆₄ v7) ∗
      ((sp0 - 16#64) ↦₆₄ v8) ∗ ((sp0 - 8#64) ↦₆₄ v9) ∗
      stackFrameAt (sp0 - 80#64) (stackBytes - 80) ⊢
    stackFrameAt sp0 stackBytes := by
  rw [stack80_split sp0 stackBytes hfit]
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp0 - 80#64) ↦₆₄ v0) ∗ ((sp0 - 72#64) ↦₆₄ v1) ∗
      ((sp0 - 64#64) ↦₆₄ v2) ∗ ((sp0 - 56#64) ↦₆₄ v3) ∗
      ((sp0 - 48#64) ↦₆₄ v4) ∗ ((sp0 - 40#64) ↦₆₄ v5) ∗
      ((sp0 - 32#64) ↦₆₄ v6) ∗ ((sp0 - 24#64) ↦₆₄ v7) ∗
      ((sp0 - 16#64) ↦₆₄ v8) ∗ ((sp0 - 8#64) ↦₆₄ v9)) ∗
      stackFrameAt (sp0 - 80#64) (stackBytes - 80) by sep_ac_rfl)) ?_
  refine sepConj_mono_left ?_
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.refl _))))))))))

private theorem decode_spqrArm4Tpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm4TplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm4PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm5Tpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm5TplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm5PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm6Tpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm6TplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm6PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm9Tpl (x2 x3 v0 fn0 v1 fn1 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm9TplBs [(v0, fn0), (v1, fn1)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm9PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions,
            FmtCall.writeStr (x2 + 13#64) spqrArm9MidBs,
            FmtCall.fmtArg 1 v1 fn1 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm10Tpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm10TplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm10PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm11Tpl (x2 x3 v0 fn0 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm11TplBs [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm11PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem decode_spqrArm13Tpl (x2 x3 v0 fn0 v1 fn1 : BitVec 64)
    (heven : x3.getLsbD 0 = false) :
    decodeFmtArguments x2 x3 spqrArm13TplBs [(v0, fn0), (v1, fn1)] =
      some [FmtCall.writeStr (x2 + 1#64) spqrArm13PreBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions,
            FmtCall.writeStr (x2 + 29#64) spqrArm13MidBs,
            FmtCall.fmtArg 1 v1 fn1 defaultFmtOptions,
            FmtCall.writeStr (x2 + 35#64) spqrArm13SufBs] := by
  simp only [decodeFmtArguments, heven, Bool.false_eq_true, ↓reduceIte]; rfl

/-- Decode any literal-prefixed 1-argument template `[len] ++ pfxBs ++ [0xc0, 0x00]`
    (`1 ≤ pfxBs.length ≤ 127`, `x3` even). -/
theorem decodeFmtArguments_prefixedOneArg (x2 x3 v0 fn0 : BitVec 64) (pfxBs : List (BitVec 8))
    (heven : x3.getLsbD 0 = false) (hlo : 1 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 127) :
    decodeFmtArguments x2 x3 ([BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8])
      [(v0, fn0)] =
      some [FmtCall.writeStr (x2 + 1#64) pfxBs,
            FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] := by
  have hlen_tpl :
      ([BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8]).length =
        (pfxBs.length + 2) + 1 := by simp
  have hcons :
      ([BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8]) =
        BitVec.ofNat 8 pfxBs.length :: (pfxBs ++ [0xc0#8, 0x00#8]) := rfl
  have hn_toNat : (BitVec.ofNat 8 pfxBs.length).toNat = pfxBs.length := by
    rw [BitVec.toNat_ofNat]; omega
  have hn_ne0 : BitVec.ofNat 8 pfxBs.length ≠ 0#8 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [hn_toNat] at this
    change pfxBs.length = 0 at this
    omega
  have hlt128 : pfxBs.length < 128 := by omega
  have hrest_len : ¬ ((pfxBs ++ [0xc0#8, 0x00#8]).length < pfxBs.length) := by simp
  have htake : (pfxBs ++ [0xc0#8, 0x00#8]).take pfxBs.length = pfxBs :=
    List.take_left
  have hdrop : (pfxBs ++ [0xc0#8, 0x00#8]).drop pfxBs.length = [0xc0#8, 0x00#8] :=
    List.drop_left
  unfold decodeFmtArguments
  rw [heven]
  simp only [Bool.false_eq_true, ↓reduceIte, hlen_tpl]
  rw [hcons]
  unfold decodeFmtTemplate
  simp only [hn_ne0, ↓reduceIte, hn_toNat, hlt128, hrest_len, htake, hdrop, Nat.zero_add]
  have hfuel2 : pfxBs.length + 2 = (pfxBs.length + 1) + 1 := by omega
  rw [hfuel2]
  unfold decodeFmtTemplate
  have hc0_ne0 : (0xc0#8 : BitVec 8) ≠ 0#8 := by decide
  have hc0_nlt80 : ¬ ((0xc0#8 : BitVec 8).toNat < 0x80) := by decide
  have hc0_ne80 : (0xc0#8 : BitVec 8) ≠ 0x80#8 := by decide
  have hc0_nltc0 : ¬ ((0xc0#8 : BitVec 8).toNat < 0xc0) := by decide
  have hph :
      decodeFmtPlaceholder 0xc0#8 [0x00#8] [(v0, fn0)] 0 =
        some (defaultFmtOptions, 0, 1, 0) := rfl
  simp only [hc0_ne0, hc0_nlt80, hc0_ne80, hc0_nltc0, ↓reduceIte, hph,
    List.getElem?_cons_zero, List.drop_zero]
  unfold decodeFmtTemplate
  simp only [↓reduceIte, Option.map_some]

private theorem fmtEstimatedCapacity_prefixedOneArg (x1 x2 v0 fn0 : BitVec 64)
    (pfxBs : List (BitVec 8))
    (heven : x1.getLsbD 0 = false) (hlo : 1 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 127) :
    fmtEstimatedCapacity x1
      [FmtCall.writeStr (x2 + 1#64) pfxBs, FmtCall.fmtArg 0 v0 fn0 defaultFmtOptions] =
      2 * pfxBs.length := by
  have hne : pfxBs.isEmpty = false := by
    cases pfxBs with
    | nil => simp at hlo
    | cons _ _ => rfl
  dsimp only [fmtEstimatedCapacity, fmtStartsWithPlaceholder, fmtLiteralLen]
  simp only [heven, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

/-! ## 2. Shared Fold Helpers for Block `412` Arms -/

private theorem fmtInnerBudgetW_dup_R {B : VerifiedLibraries.RustStd.RustAllocBudget} {st0 : B.σ}
    {va : VerifiedLibraries.RustStd.StringWriteAddrs} {R R' : SepProp} {F : SepProp}
    {t0 : State} {out : BitVec 64} {st : FmtBuf} {s : State}
    (hdup : R = F ∗ R') :
    fmtInnerBudgetW B st0 va R t0 out st s =
      F ∗ fmtInnerBudgetW B st0 va R' t0 out st s := by
  dsimp only [fmtInnerBudgetW]
  conv => lhs; rw [hdup]
  sep_ac_rfl

private theorem dup_jumpTable_in_inner [LibsignalPlacement] {R_tail : SepProp} :
    (spqrErrorRoSep lsmpl ∗ R_tail) =
      (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗ (spqrErrorRoSep lsmpl ∗ R_tail) := by
  refine (congrArg (· ∗ R_tail)
    (spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
      (by decide))).trans ?_
  sep_ac_rfl

/-- Precondition weakening before `tailcall_formatterWriteStr_many` on all `8` `write_str`
    tail-call arms (`d ∈ {0, 1, 2, 3, 7, 8, 12, 15}`): folds the `80`-byte stack frame back into
    `stackFrameAt s0.sp stackBytes` and absorbs both `(lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs)`
    and `spqrErrorCellsAt` back into `fmtInnerBudgetW B st0 va R_client t0 out st s0`. -/
private theorem fold_writeStr_arm80_pre [LibsignalPlacement]
    (B : VerifiedLibraries.RustStd.RustAllocBudget) (st0 : B.σ)
    (va : VerifiedLibraries.RustStd.StringWriteAddrs)
    (F_cells R_tail R_client : SepProp) (t0 s0 : State) (out : BitVec 64) (st : FmtBuf)
    (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) (stackBytes : Nat)
    (hstk : 80 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR_eq : R_client = F_cells ∗ (spqrErrorRoSep lsmpl ∗ R_tail)) :
    (F_cells ∗
      formatterAt f out va.vtable defaultFmtOptions ∗
      (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
      fmtInnerBudgetW B st0 va (spqrErrorRoSep lsmpl ∗ R_tail) t0 out st s0 ∗
      (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
        ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
        ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
        ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9) ∗
        stackFrameAt (s0.sp - 80#64) (stackBytes - 80))) ⊢
    formatterAt f out va.vtable defaultFmtOptions ∗
      fmtInnerBudgetW B st0 va R_client t0 out st s0 ∗
      stackFrameAt s0.sp stackBytes := by
  have hjtW := (fmtInnerBudgetW_dup_R (B := B) (st0 := st0) (va := va)
    (t0 := t0) (out := out) (st := st) (s := s0)
    (dup_jumpTable_in_inner (R_tail := R_tail))).symm
  have hfold := stack80_fold s0.sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 stackBytes hstk
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right hfold)))) ?_
  refine Entails.of_eq ?_
  conv =>
    lhs; arg 2; arg 2
    rw [← sepConj_assoc, hjtW]
  rw [hR_eq]
  dsimp only [fmtInnerBudgetW]
  sep_ac_rfl

/-- Shared postcondition entailment after the `3`-instruction epilogue (`ldp; add sp; ret`) of
    Block `412`'s nested `core::fmt::write` arms. -/
private theorem fold_epilogue80_post
    (B : VerifiedLibraries.RustStd.RustAllocBudget) (st0 : B.σ)
    (va : VerifiedLibraries.RustStd.StringWriteAddrs)
    (F_cells R_inner R_client : SepProp) (t0 s0 sf_call sf : State)
    (out f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) (st' : FmtBuf) (stackBytes : Nat)
    (hstk : 80 ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hframe2 : FmtWriteFrame sf_call sf)
    (hR_eq : R_client = F_cells ∗ R_inner) :
    formatterAt f out va.vtable defaultFmtOptions ∗
      (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
      (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
        ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
        ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
        ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9) ∗
        stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ⊢
    memRegion f 24 ∗
      fmtInnerBudgetW B st0 va R_client t0 out st' sf ∗
      stackFrameAt s0.sp stackBytes := by
  have htr2 := fmtInnerBudgetW_transport B st0 va R_inner t0 out st' sf_call sf hframe2
  have hfmt24 := formatterAt_entails_memRegion24 f out va.vtable defaultFmtOptions
  have hfold80 := stack80_fold s0.sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 stackBytes hstk
  refine Entails.trans
    (sepConj_mono hfmt24 (sepConj_mono (sepConj_mono_right htr2) hfold80)) ?_
  exact Entails.of_eq (by rw [hR_eq]; dsimp only [fmtInnerBudgetW]; sep_ac_rfl)

/-! ## 3. Per-Arm Proofs (`8` `write_str` Tail-Call Arms + `7` Nested `core::fmt::write` Arms) -/

/-- Shared proof for all `8` `<Formatter>::write_str` tail-call arms of Block `412`:
    given any `d : BitVec 8`, literal symbol `sym` and slice `bs` with `(sym, bs) ∈ spqrErrorRoList`,
    once `iterate 18 wp_step` reaches `coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym` with
    `sp` and `x29, x30` restored, closes `subroutine_ok` via `tailcall_formatterWriteStr_many`. -/
private theorem arm_writeStr_helper [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (sym : String) (bs : List (BitVec 8))
    (_hpcs : argPieces idx = [bs])
    (hstk : 80 ≤ stackBytes ∧ stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (_hmem : (sym, bs) ∈ LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux.spqrErrorRoList)
    (_hlen_lt : bs.length < 2 ^ 60)
    (hR : R_client =
      spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest)
    (hstep : ∀ (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) (st : FmtBuf)
      (R : SepProp) (s0 s' : State),
      VerifiedLibraries.RustStd.SameCpuState s' s0 →
      s'.pc = (blkPl_412).base → s'.status = .Running →
      s'.readReg64 .x0 = errPtr → s'.readReg64 .x1 = f → s'.sp = s0.sp →
      s0.spAligned = true →
      SepWP ((blkPC_412).rebase (blkPl_412).base (fun _ => none))
        (coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym) s'
        ((((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
          spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
          formatterAt f out (allocStringWriteAddrs mplAlloc).vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
            (spqrErrorRoSep lsmpl ∗
              ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
                R_rest))
            t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80))
        (fun sm' P_out => ∀ sm,
          VerifiedLibraries.RustStd.SameCpuState sm sm' →
          libsignalSessionLib.CodeLoadedWhere
            LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplayAux.spqrErrorDispKeep
            lsmpl sm.mem →
          VerifiedLibraries.RustStd.CoreFmt.PureSegPreserved s0 sm →
          SepWPp P (s0.readReg64 Reg.lr) sm P_out
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
                  idx errPtr (lsmpl.base 412) defaultFmtOptions).post (st, f) s0 sf ∗ R) ∧
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
                  idx errPtr (lsmpl.base 412) defaultFmtOptions).onPanic (st, f) s0 sf ∗ R)
            ((fmtArgCallSpec
              (fmtInnerBudgetW (toRustAllocBudget M A lim) st0
                (allocStringWriteAddrs mplAlloc) R_client t0 out)
              (fmtInnerBudgetStep (manyArgStep argPieces))
              (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
              (fmtInnerBudgetOom (toRustAllocBudget M A lim) st0
                (manyArgOom (toRustAllocBudget M A lim) st0 argPieces))
              stackBytes out (allocStringWriteAddrs mplAlloc).vtable
              idx errPtr (lsmpl.base 412) defaultFmtOptions).onOom (st, f) s0))) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr d b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨hstk.1, hstk.2.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreFmtMultiLib.fnAddr mplFmt formatterWriteStrSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  exact hstep f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in
    (hcpu_in.pc_eq.trans hpc0) (hcpu_in.status_eq.trans hrun0)
    ((hcpu_in.readReg64 .x0).trans hx0_0) ((hcpu_in.readReg64 .x1).trans hx1_0)
    hcpu_in.sp_eq hsp0

private theorem arm0_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 0#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 0#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 0#8 b1 u1 q1 q2
    spqrArm0Sym spqrArm0Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 0#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm0Sym) spqrArm0Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm1_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 1#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 1#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 1#8 b1 u1 q1 q2
    spqrArm1Sym spqrArm1Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 1#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm1Sym) spqrArm1Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm2_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 2#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 2#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 2#8 b1 u1 q1 q2
    spqrArm2Sym spqrArm2Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 2#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm2Sym) spqrArm2Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm3_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 3#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 3#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 3#8 b1 u1 q1 q2
    spqrArm3Sym spqrArm3Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 3#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm3Sym) spqrArm3Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm7_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 7#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 7#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 7#8 b1 u1 q1 q2
    spqrArm7Sym spqrArm7Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 7#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm7Sym) spqrArm7Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm8_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 8#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 8#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 8#8 b1 u1 q1 q2
    spqrArm8Sym spqrArm8Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 8#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm8Sym) spqrArm8Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm12_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 12#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 12#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 12#8 b1 u1 q1 q2
    spqrArm12Sym spqrArm12Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 12#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm12Sym) spqrArm12Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

private theorem arm15_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 15#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 15#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  refine arm_writeStr_helper L st0 argPieces t0 stackBytes idx out errPtr 15#8 b1 u1 q1 q2
    spqrArm15Sym spqrArm15Bs (by simpa [spqrErrorPieces] using hpcs)
    ⟨by omega, by omega, hstk.2⟩ (by decide) (by decide) hR ?_
  intro f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 st R s0 s' hcpu_in hpc' hrun' hx0' hx1' hsp' hsp0
  dsimp only [spqrErrorCellsAt]
  iterate 16 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out _hcl_sm hpseg => ?_
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    dsimp only [spqrErrorCellsAt]
    rw [hfp, hlr]
    sep_ac_rfl))
    (fold_writeStr_arm80_pre (toRustAllocBudget M A lim) st0 (allocStringWriteAddrs mplAlloc)
      (spqrErrorCellsAt errPtr 15#8 b1 u1 q1 q2)
      ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest)
      R_client t0 s0 out st f v0 v1 v2 v3 v4 v5 v6 v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) stackBytes
      ⟨by omega, hstk.2⟩ (by rw [hR]))) ?_
  exact tailcall_formatterWriteStr_many L st0 argPieces t0 stackBytes idx out errPtr
    (lsmpl.base 412) f defaultFmtOptions (lsmpl.ρ spqrArm15Sym) spqrArm15Bs st R s0 sm
    (by simpa [spqrErrorPieces] using hpcs) ⟨by omega, hstk.2⟩
    (spqrErrorRoSep_dup_in_R (by decide) (by rw [hR]))
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieWriteStr])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by rw [hcpu_out.sp_eq]; simp only [arm64_norm])
    hsp0
    (by rw [hcpu_out.readReg64]; simpa [arm64_norm] using hcpu_in.readReg64 Reg.lr)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp [arm64_norm]; decide)
    (by decide)
    (hcpu_in.calleeSavedPreserved hcpu_out (by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm]))

/-- Arm `d = 4`: `EpochOutOfRange(u64)` (`+0x0b8 .. +0x0ec`, nested `core::fmt::write` → Block `397`). -/
private theorem arm4_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 4#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 4#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 4#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 18 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => [formatDecimalNat q1.toNat]
  let R_sub : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗
      (((errPtr + 8#64) ↦₆₄ q1) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
      (spqrErrorRoSep lsmpl ∗ R_rest)
  let F_unused : SepProp :=
    (errPtr ↦₈ 4#8) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
      ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64) [(s0.sp - 32#64, lsmpl.base 397)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0xe4#64)
    (lsmpl.ρ spqrArm4TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm4TplBs
    [(s0.sp - 32#64, lsmpl.base 397)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm4TplSym + 1#64) spqrArm4PreBs,
     FmtCall.fmtArg 0 (s0.sp - 32#64) (lsmpl.base 397) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm4Tpl _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗
        (((errPtr + 8#64) ↦₆₄ q1) ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
      exact spqrRefU64Display_fmtArg_ok L st0 subPieces t0 subStack 0 out
        (s0.sp - 32#64) (errPtr + 8#64) q1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 228#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha56, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 397) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 v1 (s0.sp - 32#64) (lsmpl.base 397) v4 v5 (errPtr + 8#64) v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes ⟨by omega, hstk.2⟩
      hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 5`: `EncodingDecoding(EncodingError)` (`+0x1f8 .. +0x22c`, nested `core::fmt::write` → Block `392`). -/
private theorem arm5_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 5#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 5#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 5#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 18 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => spqrEncPieces b1
  let R_sub : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((errPtr + 1#64) ↦₈ b1) ∗
      spqrErrorRoSep lsmpl ∗ R_tail
  let F_unused : SepProp :=
    (errPtr ↦₈ 5#8) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
      ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64) [(s0.sp - 32#64, lsmpl.base 392)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0x224#64)
    (lsmpl.ρ spqrArm5TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm5TplBs
    [(s0.sp - 32#64, lsmpl.base 392)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm5TplSym + 1#64) spqrArm5PreBs,
     FmtCall.fmtArg 0 (s0.sp - 32#64) (lsmpl.base 392) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm5Tpl _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((errPtr + 1#64) ↦₈ b1))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
      exact spqrEncErrorDisplay_fmtArg_ok L st0 subPieces t0 subStack 0 out
        (s0.sp - 32#64) (errPtr + 1#64) b1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 548#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha56, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 392) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 v1 (s0.sp - 32#64) (lsmpl.base 392) v4 v5 (errPtr + 1#64) v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes ⟨by omega, hstk.2⟩
      hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 6`: `Serialization(serialize::Error)` (`+0x278 .. +0x2ac`, nested `core::fmt::write` → Block `393`). -/
private theorem arm6_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 6#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 6#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 6#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 18 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => [spqrSerBytes b1]
  let R_sub : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((errPtr + 1#64) ↦₈ b1) ∗
      spqrErrorRoSep lsmpl ∗ R_tail
  let F_unused : SepProp :=
    (errPtr ↦₈ 6#8) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 4#64) ↦₃₂ u1) ∗ ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
      ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64) [(s0.sp - 32#64, lsmpl.base 393)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0x2a4#64)
    (lsmpl.ρ spqrArm6TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm6TplBs
    [(s0.sp - 32#64, lsmpl.base 393)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm6TplSym + 1#64) spqrArm6PreBs,
     FmtCall.fmtArg 0 (s0.sp - 32#64) (lsmpl.base 393) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm6Tpl _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((errPtr + 1#64) ↦₈ b1))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
      exact spqrSerErrorDisplay_fmtArg_ok L st0 subPieces t0 subStack 0 out
        (s0.sp - 32#64) (errPtr + 1#64) b1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 676#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha56, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 393) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 1#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 v1 (s0.sp - 32#64) (lsmpl.base 393) v4 v5 (errPtr + 1#64) v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes ⟨by omega, hstk.2⟩
      hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 10`: `KeyTrimmed(u32)` (`+0x2b0 .. +0x2e4`, nested `core::fmt::write` → Block `396`). -/
private theorem arm10_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 10#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 10#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 10#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 18 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => [formatDecimalNat u1.toNat]
  let R_sub : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗
      (((errPtr + 4#64) ↦₃₂ u1) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
      (spqrErrorRoSep lsmpl ∗ R_rest)
  let F_unused : SepProp :=
    (errPtr ↦₈ 10#8) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
      ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64) [(s0.sp - 32#64, lsmpl.base 396)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0x2dc#64)
    (lsmpl.ρ spqrArm10TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm10TplBs
    [(s0.sp - 32#64, lsmpl.base 396)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm10TplSym + 1#64) spqrArm10PreBs,
     FmtCall.fmtArg 0 (s0.sp - 32#64) (lsmpl.base 396) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm10Tpl _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗
        (((errPtr + 4#64) ↦₃₂ u1) ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
      exact spqrRefU32Display_fmtArg_ok L st0 subPieces t0 subStack 0 out
        (s0.sp - 32#64) (errPtr + 4#64) u1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 732#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha56, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 396) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 v1 (s0.sp - 32#64) (lsmpl.base 396) v4 v5 (errPtr + 4#64) v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes ⟨by omega, hstk.2⟩
      hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 11`: `KeyAlreadyRequested(u32)` (`+0x080 .. +0x0b4`, nested `core::fmt::write` → Block `396`). -/
private theorem arm11_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 11#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 11#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 11#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 18 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) := fun _ => [formatDecimalNat u1.toNat]
  let R_sub : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗
      (((errPtr + 4#64) ↦₃₂ u1) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)) ∗
      (spqrErrorRoSep lsmpl ∗ R_rest)
  let F_unused : SepProp :=
    (errPtr ↦₈ 11#8) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 8#64) ↦₆₄ q1) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
      ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64) [(s0.sp - 32#64, lsmpl.base 396)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
    rw [fmtArgEntriesAt_false_singleton]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0xac#64)
    (lsmpl.ρ spqrArm11TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm11TplBs
    [(s0.sp - 32#64, lsmpl.base 396)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm11TplSym + 1#64) spqrArm11PreBs,
     FmtCall.fmtArg 0 (s0.sp - 32#64) (lsmpl.base 396) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm11Tpl _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗
        (((errPtr + 4#64) ↦₃₂ u1) ∗
          (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes)))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩
      exact spqrRefU32Display_fmtArg_ok L st0 subPieces t0 subStack 0 out
        (s0.sp - 32#64) (errPtr + 4#64) u1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩ rfl)
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 172#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_singleton, ha56, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 396) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 4#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 v1 (s0.sp - 32#64) (lsmpl.base 396) v4 v5 (errPtr + 4#64) v7
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes ⟨by omega, hstk.2⟩
      hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 9`: `KeyJump(u32, u32)` (`+0x110 .. +0x154`, 2-arg nested `core::fmt::write` → Block `396`). -/
private theorem arm9_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 9#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 9#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 9#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 22 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let u2 : BitVec 32 := q1.setWidth 32
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) :=
    fun i => if i = 0 then [formatDecimalNat u1.toNat] else [formatDecimalNat u2.toNat]
  let R_sub : SepProp :=
    ((s0.sp - 72#64) ↦₆₄ (errPtr + 4#64)) ∗
      ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗
      ((errPtr + 4#64) ↦₃₂ u1) ∗
      ((errPtr + 8#64) ↦₃₂ u2) ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
      (spqrErrorRoSep lsmpl ∗ R_rest)
  let F_unused : SepProp :=
    (errPtr ↦₈ 9#8) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      (((errPtr + 8#64) + 4#64) ↦₃₂ q1.extractLsb' 32 32) ∗ ((errPtr + 16#64) ↦₆₄ q2)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have ha48 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have ha40 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64)
      [(s0.sp - 72#64, lsmpl.base 396), (s0.sp - 32#64, lsmpl.base 396)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    have hq1_split : ((errPtr + 8#64) ↦₆₄ q1) =
        (((errPtr + 8#64) ↦₃₂ u2) ∗ (((errPtr + 8#64) + 4#64) ↦₃₂ q1.extractLsb' 32 32)) :=
      pointsTo64_split32' (errPtr + 8#64) q1
    rw [fmtArgEntriesAt_false_pair, hq1_split]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56, ha48, ha40]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0x14c#64)
    (lsmpl.ρ spqrArm9TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm9TplBs
    [(s0.sp - 72#64, lsmpl.base 396), (s0.sp - 32#64, lsmpl.base 396)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm9TplSym + 1#64) spqrArm9PreBs,
     FmtCall.fmtArg 0 (s0.sp - 72#64) (lsmpl.base 396) defaultFmtOptions,
     FmtCall.writeStr (lsmpl.ρ spqrArm9TplSym + 13#64) spqrArm9MidBs,
     FmtCall.fmtArg 1 (s0.sp - 32#64) (lsmpl.base 396) defaultFmtOptions]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, u2, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm9Tpl _ _ _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 72#64) ↦₆₄ (errPtr + 4#64)) ∗
        ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗
        ((errPtr + 4#64) ↦₃₂ u1) ∗
        ((errPtr + 8#64) ↦₃₂ u2) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact spqrRefU32Display_fmtArg_ok L st0 subPieces t0 subStack 0 out
          (s0.sp - 72#64) (errPtr + 4#64) u1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩
          (by dsimp only [R_sub]; sep_ac_rfl)
      · exact spqrRefU32Display_fmtArg_ok L st0 subPieces t0 subStack 1 out
          (s0.sp - 32#64) (errPtr + 8#64) u2 rfl ⟨by dsimp only [subStack]; omega, by omega⟩
          (by dsimp only [R_sub]; sep_ac_rfl))
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 332#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_pair, ha56, ha48, ha40, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    have hq1_split : ((errPtr + 8#64) ↦₆₄ q1) =
        (((errPtr + 8#64) ↦₃₂ u2) ∗ (((errPtr + 8#64) + 4#64) ↦₃₂ q1.extractLsb' 32 32)) :=
      pointsTo64_split32' (errPtr + 8#64) q1
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ (errPtr + 4#64)) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 72#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 396) ∗
          ((s0.sp - 48#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 40#64) ↦₆₄ lsmpl.base 396) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 8#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      rw [hq1_split]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 (errPtr + 4#64) (s0.sp - 72#64) (lsmpl.base 396) (s0.sp - 32#64) (lsmpl.base 396)
      (errPtr + 8#64) v7 (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes
      ⟨by omega, hstk.2⟩ hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-- Arm `d = 13`: `SendKeyEpochDecreased(u64, u64)` (`+0x230 .. +0x274`, 2-arg nested `core::fmt::write` → Block `397`). -/
private theorem arm13_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hpcs : argPieces idx = spqrErrorPieces 13#8 b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr 13#8 b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  intro B va
  let F_cells := spqrErrorCellsAt errPtr 13#8 b1 u1 q1 q2
  let R_tail :=
    (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest
  let R_inner := spqrErrorRoSep lsmpl ∗ R_tail
  have hR_eq : R_client = F_cells ∗ R_inner := by rw [hR]
  apply subroutine_ok_of_sepWPp_clLs L.clLs
  rintro ⟨st, f⟩ R s0 hpc0 hrun0 hsp0 hcl0 hpre
  dsimp only [fmtArgCallSpec] at hpre
  have hpre1 :
      s0.mem ⊨ ⌜s0.readReg64 .x0 = errPtr ∧ s0.readReg64 .x1 = f⌝ ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt s0.sp stackBytes) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    rw [hR_eq]
    dsimp only [fmtInnerBudgetW, R_inner]
    conv =>
      lhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre1
  rcases hpre1 with ⟨⟨hx0_0, hx1_0⟩, hm0⟩
  rw [stack80_split s0.sp stackBytes ⟨by omega, hstk.2⟩] at hm0
  have hm1 :
      s0.mem ⊨
        (∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8, ∃∗ v9,
          ((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ v1) ∗
          ((s0.sp - 64#64) ↦₆₄ v2) ∗ ((s0.sp - 56#64) ↦₆₄ v3) ∗
          ((s0.sp - 48#64) ↦₆₄ v4) ∗ ((s0.sp - 40#64) ↦₆₄ v5) ∗
          ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ∗
        ((F_cells ∗ formatterAt f out va.vtable defaultFmtOptions ∗
          (lsmpl.ρ spqrJumpTableSym ↦ᵣ spqrJumpTableBs) ∗
          fmtInnerBudgetW B st0 va R_inner t0 out st s0 ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm0
  iterate 10 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨_, hm1⟩)
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  rw [← sepConj_assoc] at hm1
  refine ⟨_, hm1, ?_⟩
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := coreMultiLib.fnAddr mplCore coreFmtWriteSym)
    hcl0 fun s' hcpu_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc' : s'.pc = (blkPl_412).base := hcpu_in.pc_eq.trans hpc0
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun0
  have hx0' : s'.readReg64 .x0 = errPtr := (hcpu_in.readReg64 .x0).trans hx0_0
  have hx1' : s'.readReg64 .x1 = f := (hcpu_in.readReg64 .x1).trans hx1_0
  have hsp' : s'.sp = s0.sp := hcpu_in.sp_eq
  dsimp only [F_cells, spqrErrorCellsAt]
  wp_conv_pre => unfold formatterAt
  iterate 22 wp_step
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hpseg => ?_
  let subStack := stackBytes - 80 - 0x70
  let subPieces : Nat → List (List (BitVec 8)) :=
    fun i => if i = 0 then [formatDecimalNat q1.toNat] else [formatDecimalNat q2.toNat]
  let R_sub : SepProp :=
    ((s0.sp - 72#64) ↦₆₄ (errPtr + 8#64)) ∗
      ((s0.sp - 32#64) ↦₆₄ (errPtr + 16#64)) ∗
      ((errPtr + 8#64) ↦₆₄ q1) ∗
      ((errPtr + 16#64) ↦₆₄ q2) ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
      (spqrErrorRoSep lsmpl ∗ R_rest)
  let F_unused : SepProp :=
    (errPtr ↦₈ 13#8) ∗ ((errPtr + 1#64) ↦₈ b1) ∗ memRegion (errPtr + 2#64) 2 ∗
      ((errPtr + 4#64) ↦₃₂ u1)
  let F_frame : SepProp :=
    F_unused ∗ formatterAt f out va.vtable defaultFmtOptions ∗
      ((s0.sp - 80#64) ↦₆₄ v0) ∗
      ((s0.sp - 24#64) ↦₆₄ v7) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr)
  have hsp_sm : sm.sp = s0.sp - 80#64 := by
    rw [hcpu_out.sp_eq]; simp [arm64_norm]
  have heven64 : (s0.sp - 64#64).getLsbD 0 = false :=
    getLsbD0_sub_even_of_spAligned hsp0 64 (by decide)
  have hstk_sm : 0x70 + subStack = stackBytes - 80 := by
    dsimp only [subStack]; omega
  have ha56 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_omega
  have ha48 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_omega
  have ha40 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_omega
  refine SepWPp.congr_pre (show _ =
    fmtArgEntriesAt false (s0.sp - 64#64)
      [(s0.sp - 72#64, lsmpl.base 397), (s0.sp - 32#64, lsmpl.base 397)] ∗
      fmtInnerBudgetW B st0 va R_sub t0 out st s0 ∗
      stackFrameAt sm.sp (0x70 + subStack) ∗ F_frame by
    have hfp : s'.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := hcpu_in.readReg64 (.gpr 29#5)
    have hlr_in : s'.readReg64 Reg.lr = s0.readReg64 Reg.lr := hcpu_in.readReg64 Reg.lr
    rw [fmtArgEntriesAt_false_pair]
    dsimp only [R_sub, R_inner, R_tail, F_frame, F_unused, formatterAt, fmtInnerBudgetW]
    conv =>
      rhs
      rw [spqrErrorRoSep_dup_mem lsmpl (sym := spqrJumpTableSym) (bs := spqrJumpTableBs)
        (by decide)]
    rw [hsp_sm, hstk_sm, hfp, hlr_in, ha56, ha48, ha40]
    sep_ac_rfl) ?_
  refine nested_coreFmtWrite_many_ok L st0 argPieces subPieces t0 stackBytes subStack idx
    out errPtr (lsmpl.base 412) f (lsmpl.base 412 + 0x26c#64)
    (lsmpl.ρ spqrArm13TplSym) (s0.sp - 64#64) defaultFmtOptions spqrArm13TplBs
    [(s0.sp - 72#64, lsmpl.base 397), (s0.sp - 32#64, lsmpl.base 397)]
    [FmtCall.writeStr (lsmpl.ρ spqrArm13TplSym + 1#64) spqrArm13PreBs,
     FmtCall.fmtArg 0 (s0.sp - 72#64) (lsmpl.base 397) defaultFmtOptions,
     FmtCall.writeStr (lsmpl.ρ spqrArm13TplSym + 29#64) spqrArm13MidBs,
     FmtCall.fmtArg 1 (s0.sp - 32#64) (lsmpl.base 397) defaultFmtOptions,
     FmtCall.writeStr (lsmpl.ρ spqrArm13TplSym + 35#64) spqrArm13SufBs]
    st R s0 sm
    (by simpa [spqrErrorPieces, subPieces, callPieces] using hpcs)
    ⟨by dsimp only [subStack]; omega, by omega⟩
    heven64
    (decode_spqrArm13Tpl _ _ _ _ _ _ heven64)
    (spqrErrorRoSep_dup_in_R
      (F := ((s0.sp - 72#64) ↦₆₄ (errPtr + 8#64)) ∗
        ((s0.sp - 32#64) ↦₆₄ (errPtr + 16#64)) ∗
        ((errPtr + 8#64) ↦₆₄ q1) ∗
        ((errPtr + 16#64) ↦₆₄ q2) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes))
      (by decide) (by dsimp only [R_sub]; sep_ac_rfl))
    (fun idx_i val_i fn_i opt_i hmem_i => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        FmtCall.fmtArg.injEq] at hmem_i
      rcases hmem_i with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact spqrRefU64Display_fmtArg_ok L st0 subPieces t0 subStack 0 out
          (s0.sp - 72#64) (errPtr + 8#64) q1 rfl ⟨by dsimp only [subStack]; omega, by omega⟩
          (by dsimp only [R_sub]; sep_ac_rfl)
      · exact spqrRefU64Display_fmtArg_ok L st0 subPieces t0 subStack 1 out
          (s0.sp - 32#64) (errPtr + 16#64) q2 rfl ⟨by dsimp only [subStack]; omega, by omega⟩
          (by dsimp only [R_sub]; sep_ac_rfl))
    hcl_sm
    (fmtWriteFrame_of_pureSeg hpseg
      (by rw [hcpu_out.sigActions_eq]; simpa [arm64_norm] using hcpu_in.sigActions_eq)
      (by rw [hcpu_out.tpidrEl0_eq]; simpa [arm64_norm] using hcpu_in.tpidrEl0_eq))
    (by rw [hcpu_out.pc_eq]; simp only [arm64_norm, wp_norm, L.tieFmtWrite])
    (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
    (by unfold State.spAligned at hsp0 ⊢; rw [hsp_sm]; exact spAligned_sub_16k hsp0 80 (by decide))
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm]; rfl)
    (by rw [hcpu_out.readReg64]; simp [arm64_norm, wp_norm])
    (by rw [hcpu_out.readReg64]; simp only [arm64_norm])
    fun sf_call st' hpcf hrunf hspf hcsf hcl_sf hw0_sf hstep_outer => ?_
  have hsp_sf : sf_call.sp = s0.sp - 80#64 := hspf.trans hsp_sm
  refine sepWPp_seg_lib_block_pureWhere 412
    ⟨by rw [libsignalSessionLib_blocks_length]; decide, by decide⟩
    (L.noExtLs 412 (by rw [libsignalSessionLib_blocks_length]; decide) (by decide))
    ls_checkNoSvc0_412
    (mid := s0.readReg64 Reg.lr)
    hcl_sf fun s2' hcpu2_in => ?_
  rw [blockProgram_rebase_eq_lsProg (prog := (blkPC_412).rebase (blkPl_412).base (fun _ => none))]
  have hpc2' : s2'.pc = (blkPl_412).base + 620#64 := hcpu2_in.pc_eq.trans hpcf
  have hrun2' : s2'.status = .Running := hcpu2_in.status_eq.trans hrunf
  have hsp2' : s2'.sp = s0.sp - 80#64 := hcpu2_in.sp_eq.trans hsp_sf
  have hx0_2' : s2'.readReg32 .x0 = 0#32 := (hcpu2_in.readReg32 .x0).trans hw0_sf
  dsimp only [F_frame, R_sub]
  wp_conv_pre => rw [fmtArgEntriesAt_false_pair, ha56, ha48, ha40, hsp_sm, hstk_sm]
  iterate 3 wp_step
  refine SepWP.done
    (by simp only [arm64_norm])
    (by simpa [arm64_norm] using hrun2')
    fun sf hcpu2_out _hcl_end hpseg2 => ?_
  have hpc_end : sf.pc = s0.readReg64 Reg.lr := by rw [hcpu2_out.pc_eq]; simp [arm64_norm]
  have hrun_end : sf.status = .Running := by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2'
  have hsp_end : sf.sp = s0.sp := by rw [hcpu2_out.sp_eq]; simp only [arm64_norm]
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
    refine Entails.trans (Entails.of_eq (show _ =
      formatterAt f out va.vtable defaultFmtOptions ∗
        (F_cells ∗ fmtInnerBudgetW B st0 va R_inner t0 out st' sf_call) ∗
        (((s0.sp - 80#64) ↦₆₄ v0) ∗ ((s0.sp - 72#64) ↦₆₄ (errPtr + 8#64)) ∗
          ((s0.sp - 64#64) ↦₆₄ (s0.sp - 72#64)) ∗ ((s0.sp - 56#64) ↦₆₄ lsmpl.base 397) ∗
          ((s0.sp - 48#64) ↦₆₄ (s0.sp - 32#64)) ∗ ((s0.sp - 40#64) ↦₆₄ lsmpl.base 397) ∗
          ((s0.sp - 32#64) ↦₆₄ (errPtr + 16#64)) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.lr) ∗
          stackFrameAt (s0.sp - 80#64) (stackBytes - 80)) by
      dsimp only [fmtInnerBudgetW, F_cells, spqrErrorCellsAt, F_unused, R_inner, R_tail, B, va]
      sep_ac_rfl)) ?_
    exact fold_epilogue80_post B st0 va F_cells R_inner R_client t0 s0 sf_call sf
      out f v0 (errPtr + 8#64) (s0.sp - 72#64) (lsmpl.base 397) (s0.sp - 32#64) (lsmpl.base 397)
      (errPtr + 16#64) v7 (s0.readReg64 (.gpr 29#5)) (s0.readReg64 Reg.lr) st' stackBytes
      ⟨by omega, hstk.2⟩ hframe2 hR_eq,
    hsp_end, hcs_end⟩⟩⟩

/-! ## 4. Unified 15-Arm `spqrErrorDisplay_fmtArg_ok` & `format_inner` Discharges -/

private theorem spqrErrorValidTag_cases {d : BitVec 8} (hd : SpqrErrorValidTag d) :
    d = 0#8 ∨ d = 1#8 ∨ d = 2#8 ∨ d = 3#8 ∨ d = 4#8 ∨ d = 5#8 ∨ d = 6#8 ∨ d = 7#8 ∨
      d = 8#8 ∨ d = 9#8 ∨ d = 10#8 ∨ d = 11#8 ∨ d = 12#8 ∨ d = 13#8 ∨ d = 15#8 := by
  unfold SpqrErrorValidTag at hd
  have hne14 : d.toNat ≠ 14 := fun h => hd.2 (BitVec.eq_of_toNat_eq h)
  have hnat :
      d.toNat = 0 ∨ d.toNat = 1 ∨ d.toNat = 2 ∨ d.toNat = 3 ∨ d.toNat = 4 ∨
      d.toNat = 5 ∨ d.toNat = 6 ∨ d.toNat = 7 ∨ d.toNat = 8 ∨ d.toNat = 9 ∨
      d.toNat = 10 ∨ d.toNat = 11 ∨ d.toNat = 12 ∨ d.toNat = 13 ∨ d.toNat = 15 := by
    omega
  rcases hnat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h))))))))))))))

/-- Placed `fmtArgCallSpec` correctness of `<spqr::Error as core::fmt::Display>::fmt`
    (`libsignalSessionLib` Block `412`, `776` B) across all `15` valid non-pointer discriminants
    `SpqrErrorValidTag d` (`432 + stringWriterStack = 4672` B callback stack). -/
theorem spqrErrorDisplay_fmtArg_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} [PoolMemTransport A] {lim : BudgetLimits} {P : Program}
    {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (st0 : M.σ) {R_client R_rest : SepProp}
    (argPieces : Nat → List (List (BitVec 8)))
    (t0 : State) (stackBytes idx : Nat) (out errPtr : BitVec 64)
    (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64)
    (hd : SpqrErrorValidTag d)
    (hpcs : argPieces idx = spqrErrorPieces d b1 u1 q1 q2)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hR : R_client =
      spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
        spqrErrorRoSep lsmpl ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest) :
    let B := toRustAllocBudget M A lim
    let va := allocStringWriteAddrs mplAlloc
    subroutine_ok P (lsmpl.base 412)
      (fmtArgCallSpec (fmtInnerBudgetW B st0 va R_client t0 out)
        (fmtInnerBudgetStep (manyArgStep argPieces))
        (fmtInnerBudgetPanic t0 (manyArgPanic argPieces))
        (fmtInnerBudgetOom B st0 (manyArgOom B st0 argPieces))
        stackBytes out va.vtable idx errPtr (lsmpl.base 412) defaultFmtOptions) := by
  rcases spqrErrorValidTag_cases hd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact arm0_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm1_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm2_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm3_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm4_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm5_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm6_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm7_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm8_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm9_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm10_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm11_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm12_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm13_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR
  · exact arm15_ok L st0 argPieces t0 stackBytes idx out errPtr b1 u1 q1 q2 hpcs hstk hR

/-- Exact `AllocEvent` list emitted by `format_inner` on `"<pfxBs>{}"` with `<spqr::Error as Display>::fmt`
    at scalar payload cells `(d, b1, u1, q1, q2)`. -/
@[expose] def spqrErrorPrefixedExactEvs (pfxBs : List (BitVec 8))
    (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64) : List AllocEvent :=
  formatInnerKnownEvents (2 * pfxBs.length)
    (pfxBs.length :: (spqrErrorPieces d b1 u1 q1 q2).map List.length)

theorem spqrErrorPrefixedExactEvs_mem_prefixed {pfxBs : List (BitVec 8)}
    {d b1 : BitVec 8} {u1 : BitVec 32} {q1 q2 : BitVec 64}
    (hlo : 24 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 40) :
    FormatInnerPrefixedEnv (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2) :=
  formatInnerPrefixedEnv_of_spqrPieces hlo hhi (spqrErrorPieces_sum_bounds d b1 u1 q1 q2).2.1

theorem spqrErrorPrefixedExactEvs_mem_cli {pfxBs : List (BitVec 8)}
    {d b1 : BitVec 8} {u1 : BitVec 32} {q1 q2 : BitVec 64}
    (hlo : 24 ≤ pfxBs.length) (hhi : pfxBs.length ≤ 40) :
    CliFormatInnerEnv (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2) :=
  cliFormatInnerEnv_of_spqrPieces hlo hhi (spqrErrorPieces_sum_bounds d b1 u1 q1 q2).2.1

/-- Cell-level placed `alloc::fmt::format::format_inner` correctness for `"<pfxBs>{}"` with
    `<spqr::Error as Display>::fmt` (`lsmpl.base 412`), introducing `spqrErrorRoSep lsmpl`
    from `LibsignalRoLoaded lsmpl s.mem` so the caller has **zero `libsignalSessionLib` `.rodata`
    separating-conjunction obligations**, and returning exact events
    `spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2` (ready for `ExactOrNilEnv c.exactEvs` in
    `CliFmtGhostSpecs`). -/
theorem cliAllocFormatInner_spqrErrorDisplayPrefixed_cells_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} [PoolMemTransport A]
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (ret x0 x1 errPtr : BitVec 64) (pfxBs : List (BitVec 8)) (argsRo : Bool)
    (d b1 : BitVec 8) (u1 : BitVec 32) (q1 q2 : BitVec 64) (st0 : M.σ)
    (heven : x1.getLsbD 0 = false)
    (hd : SpqrErrorValidTag d)
    (hpfxLo : 1 ≤ pfxBs.length) (hpfxHi : pfxBs.length ≤ 127)
    (hEnv : Env (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2))
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let tpl := [BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8]
    let args := [(errPtr, lsmpl.base 412)]
    let R_caller :=
      spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗
          fmtArgumentsAt argsRo x0 x1 tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent,
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              evs = spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2⌝ ∗
            vecU8 A.repAlloc ret (pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten) ∗
            fmtArgumentsAt argsRo x0 x1 tpl args ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro tpl args R_caller
  let argPieces : Nat → List (List (BitVec 8)) := fun _ => spqrErrorPieces d b1 u1 q1 q2
  let R_client : SepProp :=
    spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
      spqrErrorRoSep lsmpl ∗
      (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
      R_rest
  have hbase := cliAllocFormatInnerMany_tight_placed_ok (Env := Env) (R_client := R_client)
    (argPieces := argPieces) (stackBytes := stackBytes) L.toCliFormatInnerLink
  apply subroutine_ok.of_codeLoaded
  intro () R₀ s0 hpc0 hrun0 hpre hsp0 _hclP
  dsimp only at hpre
  have hm0 :
      s0.mem ⊨ ⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
        FitsEnv M lim st0 Env ∧ LibsignalRoLoaded lsmpl s0.mem⌝ ∗
        ((fmtArgumentsAt argsRo x0 x1 tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hx8, hx0, hx1, hFit, hro0⟩, hm1⟩
  have hm_ro : s0.mem ⊨ spqrErrorRoSep lsmpl ∗
      ((fmtArgumentsAt argsRo x0 x1 tpl args ∗
        memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
        A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    sat_spqrErrorRoSep hro0 hm1
  let cs0 : List FmtCall :=
    [FmtCall.writeStr (x0 + 1#64) pfxBs,
     FmtCall.fmtArg 0 errPtr (lsmpl.base 412) defaultFmtOptions]
  have hdec : decodeFmtArguments x0 x1 tpl args = some cs0 :=
    decodeFmtArguments_prefixedOneArg x0 x1 errPtr (lsmpl.base 412) pfxBs heven hpfxLo hpfxHi
  have hest : fmtEstimatedCapacity x1 cs0 = 2 * pfxBs.length :=
    fmtEstimatedCapacity_prefixedOneArg x1 x0 errPtr (lsmpl.base 412) pfxBs heven hpfxLo hpfxHi
  have hlit : fmtLiteralLen cs0 < 2 ^ 60 := by
    dsimp only [cs0, fmtLiteralLen]; omega
  have hEnv0 :
      Env (formatInnerKnownEvents (fmtEstimatedCapacity x1 cs0) (manyLens argPieces cs0)) := by
    simpa [hest, cs0, manyLens, callPieces, argPieces, spqrErrorPrefixedExactEvs] using hEnv
  have hargs : FmtInnerBudgetArgsOk P (toRustAllocBudget M A lim) st0
      (allocStringWriteAddrs mplAlloc) R_client (manyArgStep argPieces)
      (manyArgPanic argPieces)
      (manyArgOom (toRustAllocBudget M A lim) st0 argPieces) stackBytes s0 cs0 := by
    intro idx value fmtFn opts hmem out
    simp only [cs0, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      FmtCall.fmtArg.injEq] at hmem
    rcases hmem with ⟨rfl, hval, rfl, rfl⟩
    subst value
    exact spqrErrorDisplay_fmtArg_ok L st0 argPieces s0 stackBytes 0 out errPtr
      d b1 u1 q1 q2 hd rfl ⟨hstk.1, by omega⟩ rfl
  have hpreBase :
      s0.mem ⊨ (cliAllocFormatInnerManyTightSpec M A lim Env (allocStringWriteAddrs mplAlloc)
        R_client argPieces stackBytes P).pre (ret, argsRo, tpl, args, st0) s0 ∗ R₀ := by
    dsimp only [cliAllocFormatInnerManyTightSpec]
    rw [hx0, hx1]
    rw [pure_sepConj_of_true ⟨hx8, by omega, hstk.2, hFit, cs0, hdec, hlit, hEnv0, hargs⟩]
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R_client, R_caller]; sep_ac_rfl)) hm_ro
  refine hbase.mono_outcome (ret, argsRo, tpl, args, st0) R₀ s0 hpc0 hrun0 hpreBase hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [cliAllocFormatInnerManyTightSpec] at hpost
    rw [hx0, hx1] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          ∃ cs, decodeFmtArguments x0 x1 tpl args = some cs ∧
            evs = formatInnerKnownEvents (fmtEstimatedCapacity x1 cs) (manyLens argPieces cs) ∧
            bs = (cs.flatMap (callPieces argPieces)).flatten⌝ ∗
          (spqrErrorRoSep lsmpl ∗
            ((vecU8 A.repAlloc ret bs ∗
              fmtArgumentsAt argsRo x0 x1 tpl args ∗
              stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀)) :=
      Satisfies.mono (Entails.of_eq (by dsimp only [R_client, R_caller]; sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, cs, hdec', hevs, hbs⟩, hmf_ro⟩
    have hmf := Satisfies.drop_left hmf_ro
    have hcs : cs = cs0 := Option.some.inj (hdec'.symm.trans hdec)
    subst hcs
    have hevsEq : evs = spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2 := by
      simpa [hest, cs0, manyLens, callPieces, argPieces, spqrErrorPrefixedExactEvs] using hevs
    have hbsEq : bs = pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten := by
      simpa [cs0, callPieces, argPieces, List.flatten_cons] using hbs
    subst hbsEq
    refine Satisfies.mono (sepConj_mono_left ?_) hmf
    refine Entails.sepExists_right evs ?_
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hevsEq⟩]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [cliAllocFormatInnerManyTightSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [cliAllocFormatInnerManyTightSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [cliAllocFormatInnerManyTightSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Payload-level placed `alloc::fmt::format::format_inner` correctness for `"<pfxBs>{}"`
    (`24 ≤ pfxBs.length ≤ 40`) with `<spqr::Error as Display>::fmt` (`lsmpl.base 412`),
    splitting and re-folding `(errPtr ↦₈ d) ∗ memRegion (errPtr + 1) 23` automatically and
    proving `FormatInnerPrefixedEnv evs ∧ CliFormatInnerEnv evs`. -/
theorem cliAllocFormatInner_spqrErrorDisplayPrefixed_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} [PoolMemTransport A]
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {R_rest : SepProp} {stackBytes : Nat}
    {P : Program} {mplCore mplAlloc mplFmt : MultiPlacement}
    (L : SpqrErrorDisplayLink M A lim P mplCore mplAlloc mplFmt)
    (ret x0 x1 errPtr : BitVec 64) (pfxBs : List (BitVec 8)) (argsRo : Bool)
    (d : BitVec 8) (st0 : M.σ)
    (heven : x1.getLsbD 0 = false)
    (hd : SpqrErrorValidTag d)
    (hpfxLo : 24 ≤ pfxBs.length) (hpfxHi : pfxBs.length ≤ 40)
    (hEnv : ∀ evs, FormatInnerPrefixedEnv evs → Env evs)
    (hstk : 432 + stringWriterStack ≤ stackBytes ∧
      formatInnerFrame + 0x70 + stackBytes ≤ 2 ^ 64) :
    let tpl := [BitVec.ofNat 8 pfxBs.length] ++ pfxBs ++ [0xc0#8, 0x00#8]
    let args := [(errPtr, lsmpl.base 412)]
    let R_caller :=
      ((errPtr ↦₈ d) ∗ memRegion (errPtr + 1#64) 23) ∗
        (coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
        R_rest
    subroutine_ok P (allocMultiLib.fnAddr mplAlloc allocFormatInnerSym)
      { pre := fun () s =>
          ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = x0 ∧ s.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗
          fmtArgumentsAt argsRo x0 x1 tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
          A.pool lim st0 s ∗ stackFrameAt s.sp (formatInnerFrame + 0x70 + stackBytes)
        post := fun () s0 sf =>
          ∃∗ evs : List AllocEvent, ∃∗ bs : List (BitVec 8),
            ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
              FormatInnerPrefixedEnv evs ∧ CliFormatInnerEnv evs⌝ ∗
            vecU8 A.repAlloc ret bs ∗
            fmtArgumentsAt argsRo x0 x1 tpl args ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗ R_caller ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes) } := by
  intro tpl args R_caller
  apply subroutine_ok.of_codeLoaded
  intro () R₀ s0 hpc0 hrun0 hpre hsp0 _hclP
  dsimp only at hpre
  have hm0 :
      s0.mem ⊨
        ((errPtr ↦₈ d) ∗ memRegion (errPtr + 1#64) 23) ∗
        ((⌜s0.readReg64 .x8 = ret ∧ s0.readReg64 .x0 = x0 ∧ s0.readReg64 .x1 = x1 ∧
            FitsEnv M lim st0 Env ∧ LibsignalRoLoaded lsmpl s0.mem⌝ ∗
          fmtArgumentsAt argsRo x0 x1 tpl args ∗
          memRegion ret 24 ∗ stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗
          ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ R_rest) ∗
          A.pool lim st0 s0 ∗ stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [R_caller]; sep_ac_rfl)) hpre
  rw [spqrErrorPayload24_split errPtr d] at hm0
  iterate 4 (rw [sepExists_sepConj_left, satisfies_sepExists] at hm0; rcases hm0 with ⟨_, hm0⟩)
  rename_i b1 u1 q1 q2
  have hPref : FormatInnerPrefixedEnv (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2) :=
    spqrErrorPrefixedExactEvs_mem_prefixed hpfxLo hpfxHi
  have hCli : CliFormatInnerEnv (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2) :=
    spqrErrorPrefixedExactEvs_mem_cli hpfxLo hpfxHi
  have hcells := cliAllocFormatInner_spqrErrorDisplayPrefixed_cells_placed_ok
    (Env := Env) (R_rest := R_rest) (stackBytes := stackBytes) L
    ret x0 x1 errPtr pfxBs argsRo d b1 u1 q1 q2 st0 heven hd
    (by omega) (by omega) (hEnv _ hPref) hstk
  refine hcells.mono_outcome () R₀ s0 hpc0 hrun0
    (Satisfies.mono (Entails.of_eq (by dsimp only [spqrErrorCellsAt]; sep_ac_rfl)) hm0)
    hsp0 ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    have hp1 :
        sf.mem ⊨ ⌜AllocCallPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ Env evs ∧
          evs = spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2⌝ ∗
          ((spqrErrorCellsAt errPtr d b1 u1 q1 q2 ∗
            vecU8 A.repAlloc ret (pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten) ∗
            fmtArgumentsAt argsRo x0 x1 tpl args ∗
            stringWriteVtableAt (allocStringWriteAddrs mplAlloc) ∗
            ((coreFmtMultiLib.resolve mplFmt coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗
              R_rest) ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackFrameAt s0.sp (formatInnerFrame + 0x70 + stackBytes)) ∗ R₀) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hp1
    rcases hp1 with ⟨⟨hacp, hfs, htr, hEnvOut, rfl⟩, hmf⟩
    have hunsplit := spqrErrorPayload24_unsplit errPtr d b1 u1 q1 q2
    have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hunsplit)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf2
    refine Entails.sepExists_right (spqrErrorPrefixedExactEvs pfxBs d b1 u1 q1 q2)
      (Entails.sepExists_right (pfxBs ++ (spqrErrorPieces d b1 u1 q1 q2).flatten) ?_)
    rw [pure_sepConj_of_true ⟨hacp, hfs, htr, hEnvOut, hPref, hCli⟩]
    exact Entails.of_eq (by dsimp only [R_caller]; sep_ac_rfl)
  · dsimp only at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SpqrErrorDisplay
