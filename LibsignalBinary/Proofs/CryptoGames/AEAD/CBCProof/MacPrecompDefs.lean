/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs

/-!
# Precomposing a MAC / PRF with an encoding

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Defines `MACScheme.precomp` for evaluating a MAC after an input encoding `g : Y → X`, together with
the PRF reduction `MACScheme.precompRed` used in `Computational/Proofs/CryptoGames/AEAD/MacPrecomp.lean`.
-/

public section

open OracleComp OracleSpec

namespace CryptoGames
namespace MACScheme

variable {K X Y T : Type}

/-- `mac.precomp g`: the MAC / PRF `y ↦ mac.tag k (g y)` on `Y`. -/
@[expose] def precomp (mac : MACScheme K X T) (g : Y → X) : MACScheme K Y T :=
  ⟨fun k y => mac.tag k (g y)⟩

end MACScheme
end CryptoGames
