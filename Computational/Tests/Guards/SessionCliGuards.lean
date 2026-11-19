/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel

/-!
# Guard for the `signal-session` CLI Party Identities

**Checked by Lean.** Kernel-checked guard (`decide`) verifying distinctness of the party identity
keys in the `signal-session` CLI specification (`LibsignalBinary/Specifications/LibsignalE2E/`);
see `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

theorem idOfE_ne_cli : CryptoVerification.E2E.partyIdentityKey .A ≠ CryptoVerification.E2E.partyIdentityKey .B := by
  decide

end CryptoVerification.SignalSession
