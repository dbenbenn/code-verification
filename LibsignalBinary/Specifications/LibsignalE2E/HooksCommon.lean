/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# Common External-Call Hook Helpers for `libsignal-cli`

**Checked by Lean.** `Vec<u8>` header writer (`writeVecHeader`) and the two non-allocating
formatting hooks (`formatInnerHook0`, `fmtWriteHook0`), used only for proof-side replay (`0`
definitions in any headline closure). Related proof-side helpers live in
`LibsignalBinary/Proofs/SpecLemmas/SignalSession/HooksCommonLegacy.lean` (bump-allocator,
`String` cloning, `SystemTime` addition, fixed-image panic) and
`LibsignalBinary/Proofs/E2E/AesHooks0.lean` (AES-256-CBC hooks). See
`Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession

/-! ## `Vec<u8>` header helper -/

/-- Write the `Vec<u8>` header `{cap, ptr, len}` at `v` (`vecHeader`). -/
def writeVecHeader (m : Memory) (v cap ptr len : BitVec 64) : Memory :=
  ((m.write64 v cap).write64 (v + 8#64) ptr).write64 (v + 16#64) len

/-! ## Hooks that allocate nothing -/

/-- `alloc::fmt::format::format_inner`: an empty `String` (capacity 0, dangling pointer 1) at the
sret `x8`. -/
def formatInnerHook0 : State → State :=
  retHook fun s => s.setMem (writeVecHeader s.mem (s.readReg64 .x8) 0#64 1#64 0#64)

/-- `core::fmt::write`: `Ok` (`x0 = 0`), the `String` unchanged. -/
def fmtWriteHook0 : State → State := retHook fun s => s.writeReg64 .x0 0#64

end CryptoVerification.E2E
