/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Assumptions.Kyber1024Correct
public import Computational.Specifications.LibsignalCli.StatementPqElf

/-!
# Concrete Round-3 CRYSTALS-Kyber-1024 `δ_kem` Correctness Statement (`Kyber1024Delta`)

**Trusted: the statement.** States `Kyber1024KemDeltaCorrect`: at `realPEParams`
(`W.Q.encaps = kyber1024EncapsVec`, `W.Q.decaps = kyber1024DecapsVec`) and
`kemKeyGen = kyber1024KemKeyGen`, the PQXDH model primitives
`modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams` satisfy both the wire-length
validity premise `_hKemValid` (`1568`-byte public keys, `3168`-byte secret keys) and, for any `ε`
with `KyberNoiseGap ε`, the `δ_kem`-correctness premise
`KemDeltaCorrect P (ε + 1 / 2 ^ 112)` of `CliPqxdhSecurityForAnyKem`
(`StatementPqElfAnyKem.lean`), instantiating `δ_kem = ε + 1 / 2 ^ 112` in the Main Theorem
`CliPqxdhSecurityFor` (`StatementPqElf.lean`, DEV-PQ21).

Unlike the heuristic `2^-174` figure in the Kyber v3.02 specification (which treats compression
rounding errors as uniform and independent), `1 / 2 ^ 112` holds rigorously over every `SampleNTT`
(`SHAKE-128`) matrix `Â` (with no uniformity assumption on `SHAKE-128`), concrete `SHA3-256` message
hash, exact `Compress_{11,5,1}` / `Decompress_{11,5,1}` rounding, and Fujisaki–Okamoto
re-encryption, assuming only `KyberNoiseGap ε` (proved by `kyber1024_kem_delta_correct` in
`Computational/Theorems/Lemmas.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open scoped ENNReal
open CryptoVerification.SignalSession (realPEParams)

/-- Concrete Round-3 CRYSTALS-Kyber-1024 key-generation length validity (`(1568B, 3168B)`) and
`δ_kem = ε + 1 / 2 ^ 112` decapsulation-failure bound for
`modelPrims (realUnreachedPrims kyber1024KemKeyGen) realPEParams` under `KyberNoiseGap ε`,
discharging `_hKemValid` and `_hKemBin` of `CliPqxdhSecurityForAnyKem` (`StatementPqElfAnyKem.lean`)
to establish `CliPqxdhSecurityFor` (`StatementPqElf.lean`). -/
def Kyber1024KemDeltaCorrect : Prop :=
  (∀ seed : List UInt8,
    (CryptoGames.MLKEM.kyber1024KemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
    (CryptoGames.MLKEM.kyber1024KemKeyGen seed).2.length = 3168) ∧
  ∀ ε : ℝ≥0∞, SignalPqxdh.KyberNoiseGap ε →
    SignalPqxdh.KemDeltaCorrect
      (modelPrims (realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen) realPEParams)
      (ε + 1 / (2 : ℝ≥0∞) ^ 112)

end CryptoVerification.E2E
