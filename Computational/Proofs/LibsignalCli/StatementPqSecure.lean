/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore -- proof-setup: allow-public-import

/-!
# CLI Security Statement on PQXDH Directories with SPQR

**Checked by Lean.** Defines the abstract-group CLI PQXDH security proposition
`CliPqxdhSecurityForAbstract` (matching the abstract-group form of `CliPqxdhSecurityFor`) and its
model-run specialization `LibsignalCliPqSecure`, for arbitrary CLI implementations `run` satisfying
`CliSpecPqxdh run X W` with no excused aborts (`exc? := none`).

**DEV-CLI16 (formalization): the key-indistinguishability term is that of the real handshake.**
Clause 1 bounds `CliPqxdhAdvantage` using `KeyInd1KeyRealAdvantage` (one identity key for X25519
and XEdDSA, real HKDF) with no random oracle; Clause 2 reduces `KeyInd1KeyRealAdvantage` to the
proved one-key PQXDH bound `pqxdhKeyIndAdvantageBoundδ` under the explicit random-oracle gap
hypothesis `KeyIndRoGap` (see `Computational/docs/DEVIATIONS.md`).
-/

public section

set_option autoImplicit false
open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- Per-run body of `CliPqxdhSecurityForAbstract` over abstract group carrier `Pt`, primitives `Wp`,
unreached model operations `X`, and excused-abort predicate `exc?`. -/
abbrev CliPqxdhAbstractBody {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
    (exc? : Option (Inputs → Prop)) : Prop :=
  ∀ (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
    (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
    (_hDh : Dh.Commutes) (_hX : X25519RealizesDh Wp.C Dh encPt encT)
    (_hdec : ∀ T, decT (encT T) = some T)
    (_hdum : ∀ T, encT T ≠ dummyKey) (_hz : ∀ x, Dh.dh x 0 = 0)
    (_hkerAll : DhKerUniform Dh)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (_hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
    let P := modelPrims X Wp
    let qDR := ∑ k ∈ Finset.range qStart, qs k
    let qInst := Finset.sup (Finset.range qStart) qs
    let qTot := b.q_total + qStart + qDR
    let B_A := (L_cli decT encT).eval (fun _ => cliGameAdversaryReassoc A) ()
    let Re := reds P Wp.C Wp.Q.K qep decT encT b qStart qDR qInst
    let b_ki := keyIndReductionBudget S qStart b
    let advK : SignalPqxdh.KeyIndAdversary S := ⟨Re.kindRed.eval (fun _ => B_A) ()⟩
    ∃ (hK : SignalPqxdh.QueryBounded advK b_ki),
      (∀ k < qStart,
        ∀ o ∈ support (stageOneAsProbComp ((Re.prefixRed k).eval1 (fun _ => B_A) () qTot false)),
        ∀ flip,
        SM.MakesAtMostQueries ((Re.prefixRed k).eval2 o.2 flip qTot false) (qs k)) ∧
      let prefixSum :=
        ∑ k ∈ Finset.range qStart, ⨆ flip : Bool,
          bhPrefixFullBoundMixV1With S P ℓ D Wp.C Wp.Q.K
            Dh encPt encT decT qep qTot (qs k) δ k flip Re B_A
      CliPqxdhAdvantage S run X Wp ℓ qep decT encT A ≤
        withExcusedAbortTerm S run X Wp ℓ qep decT encT A exc?
          (2 * SignalPqxdh.KeyInd1KeyRealAdvantage S P advK + prefixSum +
            SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem +
            2 * CliKemFailProb S run X Wp ℓ qep decT encT A) ∧
      (∀ ε_ro : ℝ≥0∞, SignalPqxdh.KeyIndRoGap S P advK ε_ro →
        CliPqxdhAdvantage S run X Wp ℓ qep decT encT A ≤
          withExcusedAbortTerm S run X Wp ℓ qep decT encT A exc?
            (2 * (let R := RK.eval
                  let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
                  SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on δ_kem
                    (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
                    (SignalPqxdh.KemShCr P (R.shcr _ Ab))
                    (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro)
              + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S δ_kem
              + 2 * CliKemFailProb S run X Wp ℓ qep decT encT A))

/-- Abstract-group CLI PQXDH security proposition over arbitrary group carrier `Pt`, primitive bundle
`Wp`, unreached model operations `X`, and excused-abort predicate `exc?`, used by the model-run
theorem `LibsignalCliPqSecure` and the bridge into the concrete X25519 headline
`CliPqxdhSecurityFor`. -/
@[expose] def CliPqxdhSecurityForAbstract {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRuns : (CliRun → UnreachedPqxdhPrimitives → PEParams → Option (Inputs → Prop) → Prop) → Prop) :
    Prop :=
  ∃ (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
    SignalPqxdh.Security.KeyIndCostedReductionBounds S RK ∧
    SignalPqxdh.Security.KeyIndReductionQueryBounds S RK.eval ∧
    SessionCostedReductionFamilyBounded ℓ D ∧
    ((∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
        CliAdapterCostBounded decT encT b qStart qDR (L_cli decT encT)) ∧
     (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT))) ∧
    ForRuns fun run X Wp exc? =>
      CliPqxdhAbstractBody S ℓ L_cli RK D reds run X Wp exc?

/-- Specializes `CliPqxdhSecurityForAbstract` to every `run` satisfying `CliSpecPqxdh run X W` with
no excused aborts (`exc? := none`). -/
abbrev LibsignalCliPqSecure {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) : Prop :=
  CliPqxdhSecurityForAbstract (Pt := Pt) S ℓ fun Bound =>
    ∀ (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) (_hCli : CliSpecPqxdh run X W)
      (_hK_tot : MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds W.Q.K)
      (_hD : ∀ k x, W.C.D k (W.C.E k x) = x),
      Bound run X W none

end CryptoVerification.E2E
