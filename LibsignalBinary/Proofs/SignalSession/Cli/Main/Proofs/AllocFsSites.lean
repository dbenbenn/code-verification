/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# `AllocContractsFs` Call-Site Helpers

`.keepsFs` call-site wrappers for `AllocContractsFs`, together with `@[simp, arm64_norm]` `.fs`
preservation lemmas across `State.writeReg` and `setTpidrEl0`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

@[simp, arm64_norm]
theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm]
theorem fs_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).fs = s.fs := by
  cases s; rfl

namespace AllocContractsFs

end AllocContractsFs

/-! ## `TripleRatchet.Alloc.Defs`-style `.keepsFs` Call-Site Helpers -/

end CryptoVerification.SignalSession.Cli.MainHops
