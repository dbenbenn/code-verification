/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq
public import Computational.Specifications.Game.StatementPqOomGame
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519Group
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.LibsignalCli.StatementPqElf

@[expose] public section

set_option autoImplicit false

/-!
# KEM-generic ELF-direct security statements for the PQXDH CLI (`*AnyKem`)

**Checked by Lean.** Defines the KEM-generic counterparts `CliPqxdhSecurityForAnyKem`,
`CliPqxdhElfSecureAnyKem`, and `CliPqxdhBinaryCorrectAndSecureAnyKem` parameterized over an
arbitrary length-valid, collision-bounded, `δ_kem`-correct `kemKeyGen` (`KemDeltaCorrect P δ_kem`).
Instantiating `kemKeyGen := CryptoGames.MLKEM.kyber1024KemKeyGen` via
`kyber1024_kem_delta_correct` yields the top-level Kyber-1024 headline statement
`CliPqxdhBinaryCorrectAndSecure` in `Computational/Specifications/LibsignalCli/StatementPqElf.lean`.
-/

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.RFC7748 CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- KEM-generic CLI PQXDH security statement at `realPEParams` and the concrete Curve25519
prime-order x-only subgroup (`X25519Pt`, `x25519Dh`, `x25519EncPt`, `x25519EncT`, `x25519DecT`,
`x25519Delta = 1 / 2 ^ 250`), parameterized by the run quantifier `ForRuns` over
`(run, kemKeyGen, exc?)`. Asserts cost- and query-bounded reductions and bounds `CliPqxdhAdvantage`
against `KeyInd1KeyRealAdvantage` and (given `KeyIndRoGap`) `pqxdhKeyIndAdvantageBoundActiveδ`.
Cost bounds (`CliAdapterCostBounded`, `CompositionCostedReductionFamilyBounded`) track both total
queries `qTot = b.q_total + qStart + qDR` and per-kind counts (`bhKindCounts b qStart qDR`)
separating online queries (`b.q_on`, `qStart`, `qDR`) from offline random-oracle queries
(`b.q_ro`), while the `KeyInd` bound depends only on `b_ki.q_on`. -/
def CliPqxdhSecurityForAnyKem
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRuns : (CliRun → (List UInt8 → List UInt8 × List UInt8) →
        Option (Inputs → Prop) → Prop) → Prop) :
    Prop :=
  ∃ (L_cli : CliToModelAdapterProg S ℓ x25519DecT x25519EncT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily X25519Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (qep : ℕ),
        CompositionCostedReductionFamily S ℓ P realPEParams.C realPEParams.Q.K qep
          x25519DecT x25519EncT),
    SignalPqxdh.Security.KeyIndCostedReductionBounds S RK ∧
    SignalPqxdh.Security.KeyIndReductionQueryBounds S RK.eval ∧
    SessionCostedReductionFamilyBounded ℓ D ∧
    ((∀ (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
        CliAdapterCostBounded x25519DecT x25519EncT b qStart qDR L_cli) ∧
     (∀ (P : SignalPqxdh.Primitives) (qep : ℕ),
        CompositionCostedReductionFamilyBounded P realPEParams.C realPEParams.Q.K qep
          x25519DecT x25519EncT (reds P qep))) ∧
    ForRuns fun run kemKeyGen exc? =>
      let X := realUnreachedPrims kemKeyGen
      let P := modelPrims X realPEParams
      ∀ (_hKemValid : ∀ seed, (kemKeyGen seed).1.length = SignalPqxdh.kyberPkLen ∧
            (kemKeyGen seed).2.length = 3168)
        (_hKemColl : ∀ targetPk,
            𝒟[do let (pk, _) ← SignalPqxdh.sampleKemKeyGen P; pure (pk == targetPk)] {true}
              ≤ 1 / (2 : ℝ≥0∞) ^ 255)
        (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect P δ_kem)
        (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
        (A : CliGameAdversary S ℓ (BitVec 512))
        (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
        let qDR := ∑ k ∈ Finset.range qStart, qs k
        let qInst := Finset.sup (Finset.range qStart) qs
        let qTot := b.q_total + qStart + qDR
        let B_A := L_cli.eval (fun _ => cliGameAdversaryReassoc A) ()
        let Re := reds P qep b qStart qDR qInst
        let b_ki := keyIndReductionBudget S qStart b
        let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
        ∃ (hK : SignalPqxdh.QueryBounded advK b_ki),
          (∀ k < qStart,
            ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
            ∀ flip,
            SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
          let prefixSum :=
            ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
              bhPrefixFullBoundMixV1With S P ℓ D realPEParams.C realPEParams.Q.K
                x25519Dh x25519EncPt x25519EncT x25519DecT qep qTot (qs k) x25519Delta k flip Re B_A
          CliPqxdhAdvantage S run X realPEParams ℓ qep x25519DecT x25519EncT A ≤
            withExcusedAbortTerm S run X realPEParams ℓ qep x25519DecT x25519EncT A exc?
              (2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
                SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
                2 * CliKemFailProb S run X realPEParams ℓ qep x25519DecT x25519EncT A) ∧
          (∀ ε_ro : ℝ≥0∞, SignalPqxdh.KeyIndRoGap S P advK ε_ro →
            CliPqxdhAdvantage S run X realPEParams ℓ qep x25519DecT x25519EncT A ≤
              withExcusedAbortTerm S run X realPEParams ℓ qep x25519DecT x25519EncT A exc?
                (2 * (let R := RK.eval
                      let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
                      SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
                        (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
                        (SignalPqxdh.KemShCr P (R.shcr _ Ab))
                        (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro)
                  + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem
                  + 2 * CliKemFailProb S run X realPEParams ℓ qep x25519DecT x25519EncT A))

end CryptoVerification.E2E

namespace CryptoVerification.LibsignalCli

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.SignalSession

/-! ## ELF-direct security statements -/

/-- Specializes `CliPqxdhSecurityForAnyKem` to the ELF-direct runner `cliRunElf elf addrs` at the closed
primitive bundle `realPEParams` and the concrete Curve25519 prime-order x-only subgroup (`X25519Pt`,
`x25519Dh`, `x25519Delta = 1 / 2 ^ 250`), with `exc? := some (CliReachesSampleNttStuckElf elf addrs)`
(for the `2 * CliPqxdhFlagProb` `SampleNTT` seed-divergence term, DEV-CLI22) and no `.OutOfMemory`
hypothesis. -/
abbrev CliPqxdhElfSecureAnyKem (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  CliPqxdhSecurityForAnyKem S ℓ fun Bound =>
    ∀ (kemKeyGen : List UInt8 → List UInt8 × List UInt8),
      Bound (cliRunElf elf addrs) kemKeyGen
        (some (CliReachesSampleNttStuckElf elf addrs))

/-- `bytes` parses as `elf`, the 23 `.symtab` addresses resolve via `resolveCliElfAddrs`, and both
`CliPqxdhElfCorrect elf addrs` and `CliPqxdhElfSecureAnyKem S ℓ elf addrs` hold. -/
def CliPqxdhBinaryCorrectAndSecureAnyKem (bytes : List (BitVec 8)) : Prop :=
  ∃ elf addrs, ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliPqxdhElfCorrect elf addrs ∧
    ∀ (S : SignalPqxdh.Setup) (ℓ : ℕ),
      CliPqxdhElfSecureAnyKem S ℓ elf addrs

end CryptoVerification.LibsignalCli
