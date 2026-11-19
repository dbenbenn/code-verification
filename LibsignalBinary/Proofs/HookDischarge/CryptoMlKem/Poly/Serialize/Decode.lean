/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 -- proof-setup: allow-public-import

/-!
# NEON Inlined `deserialize_{1, 10, 12}` (`Poly.Serialize.Decode`)

Re-exports `Decode1` (`deserialize_1` + `decompress_1`), `Decode10`
(`deserialize_10` + `decompress_10`), and `Decode12` (`deserialize_12` raw and
`cmhs 3329`-reduced).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode
