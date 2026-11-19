/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security

/-!
# OT-CCA and ACD19 Thm 5 with an AD-dependent ideal ciphertext (DEV-FS17)

**Checked by Lean.** No theorem of `Computational/Theorems/` uses anything from this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust the results. See
`Computational/docs/TRUSTED_BASE.md`.

Generalizes `otccaGame` and `Theorem5Statement` from uniform ideal ciphertexts `$ᵗ C` to an
AD-dependent ideal distribution `ideal a` (`otccaGameAdIdeal`, `otccaAdvantageAdIdeal`,
`Theorem5StatementAdIdeal`), avoiding `SampleableType C` for wire formats carrying public headers.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

namespace AEADScheme

variable {Key AD M C : Type}

/-- OT-CCA `encrypt(a, m)` oracle sampling ideal ciphertexts from `ideal a`.

**DEV-FS17 (libsignal): the ideal ciphertext may depend on the AD.** Replaces uniform `$ᵗ C` in
ACD19 Def. 2 with `ideal a` (independent of `m`) for wire formats carrying public headers; when
`ideal = fun _ => $ᵗ C`, `otccaAdvantageWith_uniform` recovers `otccaAdvantage` by `rfl`. -/
def otccaEncryptAdIdeal (ae : AEADScheme Key AD M C) (ideal : AD → ProbComp C) :
    QueryImpl ((AD × M) →ₒ Option C) (StateT (OTCCAState Key AD C) ProbComp) := fun ⟨a, m⟩ => do
  let st ← get
  if st.chal.isSome then return none
  let e ← if st.b then liftM (ideal a) else pure (ae.enc st.key a m)
  set { st with chal := some (a, e) }
  return some e

/-- OT-CCA hidden-bit game with ideal ciphertexts drawn from `ideal`. -/
def otccaGameAdIdeal [SampleableType Key] [DecidableEq AD] [DecidableEq C]
    (ae : AEADScheme Key AD M C) (ideal : AD → ProbComp C) (A : OTCCAAdversary AD M C) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (OTCCAState Key AD C) ProbComp)
    + (ae.otccaEncryptAdIdeal ideal + ae.otccaDecrypt)
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

end AEADScheme

namespace FSAEAD

variable {CK MK AD M C : Type}

end FSAEAD

end CryptoGames
