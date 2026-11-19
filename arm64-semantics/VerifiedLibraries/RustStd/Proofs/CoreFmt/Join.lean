/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.StrDisplay
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.PadIntegral
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplay

/-!
# Integer `Display::fmt` Composition

Discharges the `pad_integral` callee premise of the `u8`, `u32`, `u64`, and `usize`
`core::fmt::Display::fmt` contracts via `formatterPadIntegral_ok`, yielding `withCodeLoadedWhere`,
linked-program `CodeLoaded`, and placed `fmtArgCallSpec` corollaries (`u64` and `usize` share block
`9` and `u64DisplayKeep` / `u64DisplayFmtSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd

theorem u8DisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u8DisplayKeep mpl
        (u8DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
          (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v)) :=
  u8DisplayFmt_of_padIntegralWhere_ok hpl
    (hext 6 (by decide) (by decide)) hw.transport stackBytes _ out vt opts rfl
    (fun f dsPtr ds => formatterPadIntegral_ok hpl
      (fun j hj hk => hext j hj (by simp [u8DisplayKeep, hk])) hw f opts true false dsPtr ds)
    ro valPtr v

theorem u8DisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64) (v : BitVec 8) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (u8DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v) :=
  subroutine_ok_drop_codeLoadedWhere hload (u8DisplayFmt_ok hpl hext hw opts ro valPtr v)

theorem u8DisplayFmt_fmtArg_placed_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u8DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u8DisplayKeep mpl m)
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {Step : FmtCall → σ → Bool → σ → Prop} {PanicArg OomArg : FmtCall → σ → State → Prop}
    {stackBytes argStackBytes idx : Nat} {out vt wsFn wcFn valPtr : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {v : BitVec 8}
    (hw : FmtWriterOk P W_inner StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym) opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym) opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym) opts) st sf)
    (hstack : 192 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef8 ro valPtr v ∗
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ W_inner st s :=
      by intros; ac_rfl) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym)
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr
        (coreFmtMultiLib.fnAddr mpl u8DisplayFmtSym) opts) :=
  u8DisplayFmt_fmtArg_ok (u8DisplayFmt_of_codeLoaded hpl hext hload hw opts ro valPtr v)
    hno_alt hstep hpanic hoom hstack hW

theorem u32DisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u32DisplayKeep mpl
        (u32DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
          (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v)) :=
  u32DisplayFmt_of_padIntegralWhere_ok hpl
    (hext 8 (by decide) (by decide)) hw.transport stackBytes _ out vt opts rfl
    (fun f dsPtr ds => formatterPadIntegral_ok hpl
      (fun j hj hk => hext j hj (by simp [u32DisplayKeep, hk])) hw f opts true false dsPtr ds)
    ro valPtr v

theorem u32DisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr : BitVec 64) (v : BitVec 32) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (u32DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v) :=
  subroutine_ok_drop_codeLoadedWhere hload (u32DisplayFmt_ok hpl hext hw opts ro valPtr v)

theorem u32DisplayFmt_fmtArg_placed_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u32DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u32DisplayKeep mpl m)
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {Step : FmtCall → σ → Bool → σ → Prop} {PanicArg OomArg : FmtCall → σ → State → Prop}
    {stackBytes argStackBytes idx : Nat} {out vt wsFn wcFn valPtr : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {v : BitVec 32}
    (hw : FmtWriterOk P W_inner StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym) opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym) opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym) opts) st sf)
    (hstack : 192 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef32 ro valPtr v ∗
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ W_inner st s :=
      by intros; ac_rfl) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym)
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr
        (coreFmtMultiLib.fnAddr mpl u32DisplayFmtSym) opts) :=
  u32DisplayFmt_fmtArg_ok (u32DisplayFmt_of_codeLoaded hpl hext hload hw opts ro valPtr v)
    hno_alt hstep hpanic hoom hstack hW

theorem u64DisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplayKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
          (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v)) :=
  u64DisplayFmt_of_padIntegralWhere_ok hpl
    (hext 3 (by decide) (by decide)) (hext 9 (by decide) (by decide)) hw.transport stackBytes _
    out vt opts rfl
    (fun f dsPtr ds => formatterPadIntegral_ok hpl
      (fun j hj hk => hext j hj (by simp [u64DisplayKeep, hk])) hw f opts true false dsPtr ds)
    ro valPtr v

theorem u64DisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym)
      (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v) :=
  subroutine_ok_drop_codeLoadedWhere hload (u64DisplayFmt_ok hpl hext hw opts ro valPtr v)

theorem u64DisplayFmt_fmtArg_placed_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mpl m)
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {Step : FmtCall → σ → Bool → σ → Prop} {PanicArg OomArg : FmtCall → σ → State → Prop}
    {stackBytes argStackBytes idx : Nat} {out vt wsFn wcFn valPtr : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {v : BitVec 64}
    (hw : FmtWriterOk P W_inner StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym) opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym) opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym) opts) st sf)
    (hstack : 240 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef64 ro valPtr v ∗
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ W_inner st s :=
      by intros; ac_rfl) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym)
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr
        (coreFmtMultiLib.fnAddr mpl u64DisplayFmtSym) opts) :=
  u64DisplayFmt_fmtArg_ok (u64DisplayFmt_of_codeLoaded hpl hext hload hw opts ro valPtr v)
    hno_alt hstep hpanic hoom hstack hW

theorem usizeDisplayFmt_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym)
      (coreFmtMultiLib.withCodeLoadedWhere u64DisplayKeep mpl
        (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
          (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v)) :=
  usizeDisplayFmt_of_padIntegralWhere_ok hpl
    (hext 3 (by decide) (by decide)) (hext 9 (by decide) (by decide)) hw.transport stackBytes _
    out vt opts rfl
    (fun f dsPtr ds => formatterPadIntegral_ok hpl
      (fun j hj hk => hext j hj (by simp [u64DisplayKeep, hk])) hw f opts true false dsPtr ds)
    ro valPtr v

theorem usizeDisplayFmt_of_codeLoaded {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mpl m)
    {W : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {stackBytes : Nat} {out vt wsFn wcFn : BitVec 64}
    (hw : FmtWriterOk P W StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (opts : FmtOptions) (ro : Bool) (valPtr v : BitVec 64) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym)
      (u64DisplayFmtSpec W StrStep CharStep Panic Oom stackBytes
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym) out vt opts ro valPtr v) :=
  subroutine_ok_drop_codeLoadedWhere hload (usizeDisplayFmt_ok hpl hext hw opts ro valPtr v)

theorem usizeDisplayFmt_fmtArg_placed_ok {σ : Type} {mpl : MultiPlacement}
    (hpl : coreFmtMultiLib.Placeable mpl) {P : Program}
    (hext : LibKeepNoExtern coreFmtMultiLib u64DisplayKeep mpl P)
    (hload : ∀ m : Memory, P.CodeLoaded m → coreFmtMultiLib.CodeLoadedWhere u64DisplayKeep mpl m)
    {W W_inner : σ → State → SepProp} {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop} {Panic Oom : σ → Nat → State → Prop}
    {Step : FmtCall → σ → Bool → σ → Prop} {PanicArg OomArg : FmtCall → σ → State → Prop}
    {stackBytes argStackBytes idx : Nat} {out vt wsFn wcFn valPtr : BitVec 64}
    {opts : FmtOptions} {ro : Bool} {v : BitVec 64}
    (hw : FmtWriterOk P W_inner StrStep CharStep Panic Oom stackBytes out vt wsFn wcFn)
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym) opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym) opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym) opts) st sf)
    (hstack : 240 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef64 ro valPtr v ∗
        (coreFmtMultiLib.resolve mpl coreFmtDecDigitsLutSym ↦ᵣ decDigitsLutBytes) ∗ W_inner st s :=
      by intros; ac_rfl) :
    subroutine_ok P (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym)
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr
        (coreFmtMultiLib.fnAddr mpl usizeDisplayFmtSym) opts) :=
  u64DisplayFmt_fmtArg_ok (usizeDisplayFmt_of_codeLoaded hpl hext hload hw opts ro valPtr v)
    hno_alt hstep hpanic hoom hstack hW

end VerifiedLibraries.RustStd.CoreFmt
