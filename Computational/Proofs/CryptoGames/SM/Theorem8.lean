/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Defs
import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Bucket
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.EvalDist.EvalDistEq
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.EvalDist.AnswerMeasure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.Prelude.Core
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Theorem 8: authenticity of the Fig. 8 SM scheme

**Checked by Lean.**

Proves ACD19 §5.3.2 Theorem 8 (`theorem8`, matching `Theorem8` in `SM/Theorem8And12Statements.lean`)
for the concrete reductions `redCKAAuth`, `redPRNGAuth`, and `redFSAuth` by combining Lemmas 9–11.-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-- Lemma 9 (`H0 →` CKA real world): bounds the authenticity game by the real world of
`redCKAAuth` up to doomed runs. -/
theorem lemma9 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    authAdvantage (scheme cka prng fs lam) (2 + Δcka) qep tL t A ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  exact AuthL9.lemma9_proof cka prng fs lam Δcka qep hc tL t A

/-- Lemma 10 (`H1 →` PRF-PRNG real world): couples `redCKAAuth` under a uniform epoch-`t_heal`
CKA key with `redPRNGAuth` under the real root RNG. -/
theorem lemma10 (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  exact AuthL10.lemma10_proof cka prng fs lam Δcka qep hc tL t A

/-- Lemma 11 (`H2 →` FS-AEAD): bounds a win in the ideal world of `redPRNGAuth` by a sum over at
most `q` epoch-`t*` FS-AEAD sessions. -/
theorem lemma11 (tL : Option ℕ) (t q : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueries A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      ∑ j ∈ Finset.range q, FSAEAD.advantage fs (redFSAuth cka prng fs lam Δcka qep j tL t A) := by
  exact AuthL11.lemma11_proof cka prng fs lam Δcka qep tL t q A hq

/-! ### Stage-2 `canon`-bucket and coin-averaged authenticity reductions -/

section Stage2Auth

end Stage2Auth

end CryptoGames.SM.Construction
