/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeLow -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeMid -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh -- proof-setup: allow-public-import

/-!
# NEON Inlined `serialize_{1, 4, 5, 10, 11, 12}` (`Poly.Serialize.Encode`)

Re-exports `Common`, `EncodeLow` (`serialize_{1, 4}`), `EncodeMid` (`serialize_{5, 11}`), and
`EncodeHigh` (`serialize_{10, 12}`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Encode
end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Encode
