/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17
import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma18

/-!
# Theorem 1: simplified properties imply SM security

**Checked by Lean.** Hybrid steps and query bounds for ACD19 Theorem 1 (`SM/Game.lean`), providing
`lemma17` and `challSim_queries` for the libsignal security proof.

**DEV-SM20 (paper fix): each hop between hidden-bit games costs a factor 2.** With hidden-bit bias
`2·|Pr[win] − 1/2|` (DEV-SM10), each distinguishing hop incurs factor `2` on the bad-event
probability.
-/

public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Thm1

set_option linter.unusedSectionVars false

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

section Hops

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Key] [SampleableType Coins]

/-- `challSim A` makes at most as many SM oracle queries as `A`. -/
theorem challSim_queries (A : Adversary St Msg Coins C) (q : ℕ) (hq : MakesAtMostQueries A q) :
    MakesAtMostQueries (challSim Δ qep A) q := by
  exact L18.challSim_queries_proof Δ qep A q hq

/-! **DEV-SM17 (paper fix): no Def. 7 (B)–(E) needed.** ACD19 Theorem 1 holds here for every
`SMScheme`: Def. 7 (A) is enforced by the game interface (DEV-SM4, DEV-SM16), guesses are summed
rather than sampled, and uniform-bound corollaries are vacuous unless `ε = 1` (DEV-SM18). -/

end Hops

end CryptoGames.SM.Thm1
