/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionExtractedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

public section

set_option autoImplicit false

/-!
# Name labels of the `libsignal-cli` library (proof-side cross-check)

**Checked by Lean.** Certifies that the symbol names of `libsignalSessionLib` (panic externs and
SPQR's CPU-probe statics) match the pre-link relocatable objects extracted by `rust-obj2lean`
(`libsignalSessionExtractedObjs`). Retained as an untrusted proof-side cross-check after the
headline statements moved to ELF-direct `.symtab` resolution (`CliBinaryPq.lean`).
-/

namespace CryptoVerification.SignalSession

open Arm64

/-- The pre-link relocatable objects of the `libsignal-cli` library. -/
abbrev cliLinkObjs : List Obj.ExtractedObj := libsignalSessionExtractedObjs

/-- Demangled names of the panic entry points in `cliPanicSymbolsPlaced` that `Rust.isPanicSymbol`
does not match. -/
@[expose] def cliPanicExtraDemangled : List String :=
  ["<alloc::vec::Vec<_, _>>::remove::assert_failed"]

/-- Data objects `tokenStorageName` and `tokenName` (patched by `Placed.cliTokenPatchPlaced`) are
exactly the byte ranges of `STT_OBJECT` symbols of `cliLinkObjs` with exactly those names. -/
@[expose] def CliProbeLabelsAnchored (dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin) : Prop :=
  ∀ n ∈ [LibsignalSpqrV1.tokenStorageName, LibsignalSpqrV1.tokenName],
    ∃ dj : Fin libsignalSessionLib.data.length, libsignalSessionLib.data[dj].sym = n ∧
      ∃ obj, cliLinkObjs[(dO dj).oi]? = some obj ∧ ∃ sy ∈ obj.symbols,
        Obj.CoversDataSlice (dO dj) sy ∧ sy.name = n

/-- Every extern of `libsignalSessionLib` is referenced in `cliLinkObjs` as an undefined non-local
symbol with exactly that `.strtab` name, no object in `cliLinkObjs` defines it non-locally, and no
symbol of that name is a TLS symbol. -/
@[expose] def CliExternLabelsUndefined : Prop :=
  ∀ b ∈ libsignalSessionLib.blocks, ∀ x ∈ b.externs,
    (∃ o ∈ cliLinkObjs, ∃ sy ∈ o.symbols, sy.rawName = x ∧ sy.sec = .undef ∧ sy.bind ≠ .local) ∧
    (∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols, sy.rawName = x → sy.bind ≠ .local → sy.sec = .undef) ∧
    ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols, sy.rawName = x → sy.kind ≠ .tls

/-- Every non-local `.o` symbol named by an extern `x` with `isCliPanicSymbolPlaced x = true` has a
Rust panic entry point as its demangled name. -/
@[expose] def CliPanicLabelsSound : Prop :=
  ∀ b ∈ libsignalSessionLib.blocks, ∀ x ∈ b.externs, isCliPanicSymbolPlaced x = true →
    ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols, sy.rawName = x → sy.bind ≠ .local →
      Rust.isPanicSymbol sy.name = true ∨ sy.name ∈ cliPanicExtraDemangled

/-- Object-level label cross-check for `libsignalSessionLib`. -/
@[expose] def CliLabelsFromObjects : Prop :=
  (∃ bO dO, Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO ∧
      CliProbeLabelsAnchored dO) ∧
    CliExternLabelsUndefined ∧ CliPanicLabelsSound

end CryptoVerification.SignalSession
