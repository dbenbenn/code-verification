/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayU8
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayU32
public import VerifiedLibraries.RustStd.Proofs.CoreFmt.IntDisplayU64

/-!
# Placement-Generic Unsigned Integer `core::fmt::Display` Proofs

Re-exports the placement-generic `<u8>`, `<u32>`, `<u64>`, and `<usize>`
`core::fmt::Display::fmt` contracts over `coreFmtMultiLib` and lifts the `u8` and `u32`
display specifications to `core::fmt::write` argument callbacks (`fmtArgCallSpec`).
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd.CoreFmt

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.AsciiNum
open VerifiedLibraries.RustStd

/-- Lift `<u8 as core::fmt::Display>::fmt` (`u8DisplayFmtSpec`) to a `core::fmt::write` argument
    callback contract (`fmtArgCallSpec`) when `W` frames `fmtRef8` and the read-only
    `DEC_DIGITS_LUT` around `W_inner` and `opts.flags.getLsbD 23 = false`. -/
theorem u8DisplayFmt_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {lutAddr out vt valPtr fmtFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {v : BitVec 8}
    (hfmt : subroutine_ok P fmtFn
      (u8DisplayFmtSpec W_inner StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v))
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : 192 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef8 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗ W_inner st s := by intros; ac_rfl) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) :=
  IntDisplayAux.intDisplay_fmtArg_ok (frameBytes := 192 + stackBytes)
    (F_ref := fmtRef8 ro valPtr v) (ds := formatDecimalNat v.toNat) hfmt hno_alt hstep hpanic hoom hstack hW

/-- Lift `<u32 as core::fmt::Display>::fmt` (`u32DisplayFmtSpec`) to a `core::fmt::write` argument
    callback contract (`fmtArgCallSpec`) when `W` frames `fmtRef32` and the read-only
    `DEC_DIGITS_LUT` around `W_inner` and `opts.flags.getLsbD 23 = false`. -/
theorem u32DisplayFmt_fmtArg_ok {σ : Type} {P : Program}
    {W W_inner : σ → State → SepProp}
    {StrStep : σ → List (BitVec 8) → Bool → σ → Prop}
    {CharStep : σ → BitVec 32 → Bool → σ → Prop}
    {Panic Oom : σ → Nat → State → Prop} {Step : FmtCall → σ → Bool → σ → Prop}
    {PanicArg OomArg : FmtCall → σ → State → Prop} {stackBytes argStackBytes idx : Nat}
    {lutAddr out vt valPtr fmtFn : BitVec 64} {opts : FmtOptions} {ro : Bool} {v : BitVec 32}
    (hfmt : subroutine_ok P fmtFn
      (u32DisplayFmtSpec W_inner StrStep CharStep Panic Oom stackBytes lutAddr out vt opts ro valPtr v))
    (hno_alt : opts.flags.getLsbD 23 = false)
    (hstep : ∀ st ok st',
      FmtOpsRun StrStep CharStep (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st ok st' →
        Step (.fmtArg idx valPtr fmtFn opts) st ok st')
    (hpanic : ∀ st sf,
      FmtOpsAbort StrStep CharStep Panic (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        PanicArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hoom : ∀ st sf,
      FmtOpsAbort StrStep CharStep Oom (padIntegralNoAltOps opts true (formatDecimalNat v.toNat)) st sf →
        OomArg (.fmtArg idx valPtr fmtFn opts) st sf)
    (hstack : 192 + stackBytes ≤ argStackBytes := by omega)
    (hW : ∀ (st : σ) (s : State),
      W st s = fmtRef32 ro valPtr v ∗ (lutAddr ↦ᵣ decDigitsLutBytes) ∗ W_inner st s := by intros; ac_rfl) :
    subroutine_ok P fmtFn
      (fmtArgCallSpec W Step PanicArg OomArg argStackBytes out vt idx valPtr fmtFn opts) :=
  IntDisplayAux.intDisplay_fmtArg_ok (frameBytes := 192 + stackBytes)
    (F_ref := fmtRef32 ro valPtr v) (ds := formatDecimalNat v.toNat) hfmt hno_alt hstep hpanic hoom hstack hW

end VerifiedLibraries.RustStd.CoreFmt
