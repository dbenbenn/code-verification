/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# SPQR V1 CPU-Feature Detection Symbol Names (`TOKEN` and `STORAGE.0`)

**Checked by Lean.** Demangled symbol names `tokenStorageName` and `tokenName` for the
`spqr::encoding::gf::check_accelerated` CPU-feature cells, used only by the untrusted placed
proofs (`LibsignalBinary/Proofs/Placed/CliBinaryPqPlaced.lean`, `CliLabels.lean`) and the
ELF-direct bridge (`ElfDirectBridge.lean`). The trusted ELF-direct statements
(`SignalSession/CliBinaryPq.lean`) resolve the mangled `.symtab` names directly. See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-- `spqr::encoding::gf::check_accelerated::use_accelerated::STORAGE.0` (`0x9a038`),
a 1-byte `AtomicU8` storing whether PMULL-accelerated GF(2¹⁶) multiplication is enabled
(`0#8` = `false`, `1#8` = `true`, `0xff#8` = uninitialized). -/
abbrev tokenStorageName : String :=
  "spqr::encoding::gf::check_accelerated::use_accelerated::STORAGE.0"

/-- `spqr::encoding::gf::check_accelerated::TOKEN` (`0x9a040`),
a 16-byte `std::sync::LazyLock<InitToken>` whose `std::sys::sync::once::futex::Once`
`AtomicU32` state word resides at offset `+8` (`0x9a048`, `0#32` = `COMPLETE`). -/
abbrev tokenName : String :=
  "spqr::encoding::gf::check_accelerated::TOKEN"

end CryptoVerification.LibsignalSpqrV1
