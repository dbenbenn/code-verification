/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.LibsignalCli.StatementPqElfAnyKem
public import Computational.Proofs.LibsignalCli.StatementPqSecure
import Computational.Proofs.LibsignalCli.ConcreteX25519Prims

/-!
# Old-to-New and Concrete-Converse Guards for Concrete X25519 CLI Security

**Checked by Lean.** Verifies kernel-checked relations between the concrete X25519 CLI security
statements (`CliPqxdhElfSecure`, `CliPqxdhBinaryCorrectAndSecure` in `StatementPqElf.lean`, and
their KEM-generic counterparts `CliPqxdhElfSecureAnyKem`, `CliPqxdhBinaryCorrectAndSecureAnyKem` in
`StatementPqElfAnyKem.lean`) and the abstract-group form (`CliPqxdhSecurityForOld`, `rfl`-equal to
`CliPqxdhSecurityForAbstract` in `Computational/Proofs/LibsignalCli/StatementPqSecure.lean`):

1. **Old ⇒ AnyKem (`cliPqxdhElfSecure_of_old`, `cliPqxdhBinaryCorrectAndSecure_of_old`):**
   instantiating `{Pt}` at `X25519Pt`, `X` at `realUnreachedPrims kemKeyGen`, `Dh` at `x25519Dh`,
   `(encPt, encT, decT)` at `(x25519EncPt, x25519EncT, x25519DecT)`, and `δ` at
   `x25519Delta = 1 / 2 ^ 250` discharges every curve and primitive premise as a proved lemma.
2. **AnyKem ⇒ Old at concrete instance (`cliPqxdhElfSecure_converse_at_concrete`):**
   `CliPqxdhElfSecureAnyKem` implies the abstract-group conclusion instantiated at `X25519Pt`,
   `realUnreachedPrims kemKeyGen`, `realPEParams`, `x25519Dh`, and `x25519Delta` (with the
   discharged premises accepted as unused hypotheses), ensuring no conclusion conjunct is weakened
   or dropped on the concrete primitives.
3. **New Kyber-1024 ⇒ AnyKem conclusion at `kyber1024KemKeyGen`
   (`cliPqxdhElfSecure_kyber1024_converse_at_concrete`):**
   `CliPqxdhElfSecure` implies `CliPqxdhOldConclusion` at `kyber1024KemKeyGen` and
   `δ_kem := ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`.
-/

public section

set_option autoImplicit false

namespace Computational.Tests.Guards.ConcreteX25519OldToNew

open OracleComp OracleSpec MeasureTheory ENNReal
open Arm64.Process (ElfImage)
open CryptoGames CryptoGames.RFC7748 CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession
  CryptoVerification.E2E CryptoVerification.LibsignalCli

/-- Shared conclusion body of the abstract-group CLI PQXDH security statement, parameterized by
instantiated adapter `L_cli_inst` and composition reduction family `reds_inst`. -/
abbrev CliPqxdhOldConclusion {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
    (exc? : Option (Inputs → Prop))
    (δ_kem : ℝ≥0∞) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → CryptoVerification.E2E.Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ)
    (L_cli_inst : CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds_inst : ∀ (P : SignalPqxdh.Primitives) (qep : ℕ),
        CompositionCostedReductionFamily S ℓ P Wp.C Wp.Q.K qep decT encT)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ) (δ : ℝ≥0∞)
    (A : CliGameAdversary S ℓ (BitVec 512)) : Prop :=
  let P := modelPrims X Wp
  let qDR := ∑ k ∈ Finset.range qStart, qs k
  let qInst := Finset.sup (Finset.range qStart) qs
  let qTot := b.q_total + qStart + qDR
  let B_A := L_cli_inst.eval (fun _ => cliGameAdversaryReassoc A) ()
  let Re := reds_inst P qep b qStart qDR qInst
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

/-- Abstract-group `ForRuns` body of `CliPqxdhSecurityForOld`. -/
abbrev CliPqxdhOldBody {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT)
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (Wp : PEParams)
    (exc? : Option (Inputs → Prop)) : Prop :=
  ∀ (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X Wp))
    (δ_kem : ℝ≥0∞) (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X Wp) δ_kem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → CryptoVerification.E2E.Bytes) (encT : Pt → PublicKey)
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
    CliPqxdhOldConclusion S ℓ run X Wp exc? δ_kem Dh encPt encT decT qep
      (L_cli decT encT) RK D (fun P qep => reds P Wp.C Wp.Q.K qep decT encT)
      b qStart qs δ A

/-- Abstract-group form of `CliPqxdhSecurityFor`, definitionally equal (`rfl`) to
`CliPqxdhSecurityForAbstract`. -/
@[expose] def CliPqxdhSecurityForOld {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRuns : (CliRun → UnreachedPqxdhPrimitives → PEParams → Option (Inputs → Prop) → Prop) → Prop) :
    Prop :=
  ∃ (L_cli : ∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CliToModelAdapterProg S ℓ decT encT)
    (RK : SignalPqxdh.Security.KeyIndCostedReductionFamily S)
    (D : SessionCostedReductionFamily Pt ℓ)
    (reds : ∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamily S ℓ P C K qep decT encT),
    SignalPqxdh.Security.KeyIndCostedReductionBounds S RK ∧
    SignalPqxdh.Security.KeyIndReductionQueryBounds S RK.eval ∧
    SessionCostedReductionFamilyBounded ℓ D ∧
    ((∀ (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
        (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ),
        CliAdapterCostBounded decT encT b qStart qDR (L_cli decT encT)) ∧
     (∀ (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem) (qep : ℕ)
        (decT : PublicKey → Option Pt) (encT : Pt → PublicKey),
        CompositionCostedReductionFamilyBounded P C K qep decT encT (reds P C K qep decT encT))) ∧
    ForRuns fun run X Wp exc? =>
      CliPqxdhOldBody S ℓ L_cli RK D reds run X Wp exc?

/-- Kernel-checked definitional equality tying `CliPqxdhSecurityForOld` to the untrusted
abstract-group statement `CliPqxdhSecurityForAbstract`. -/
theorem cliPqxdhSecurityForOld_eq_abstract :
    @CliPqxdhSecurityForOld = @CliPqxdhSecurityForAbstract := rfl

/-- Abstract-group form of `CliPqxdhElfSecure`. -/
abbrev CliPqxdhElfSecureOld {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  CliPqxdhSecurityForOld (Pt := Pt) S ℓ fun Bound =>
    ∀ (X : UnreachedPqxdhPrimitives),
      Bound (cliRunElf elf addrs) X realPEParams
        (some (CliReachesSampleNttStuckElf elf addrs))

/-- Abstract-group form of `CliPqxdhBinaryCorrectAndSecure`. -/
def CliPqxdhBinaryCorrectAndSecureOld (bytes : List (BitVec 8)) : Prop :=
  ∃ elf addrs, ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliPqxdhElfCorrect elf addrs ∧
    ∀ {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (S : SignalPqxdh.Setup) (ℓ : ℕ),
      CliPqxdhElfSecureOld (Pt := Pt) S ℓ elf addrs

/-- The concrete X25519 `CliPqxdhElfSecureAnyKem` statement follows from the abstract-group
statement instantiated at `X25519Pt`, `realUnreachedPrims kemKeyGen`, `x25519Dh`, and
`x25519Delta = 1 / 2 ^ 250`. -/
theorem cliPqxdhElfSecure_of_old
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) (addrs : CliElfAddrs)
    (hOld : CliPqxdhElfSecureOld (Pt := X25519Pt) S ℓ elf addrs) :
    CliPqxdhElfSecureAnyKem S ℓ elf addrs :=
  Computational.Proofs.LibsignalCli.ConcreteX25519Prims.cliPqxdhElfSecureAnyKem_of_abstract
    S ℓ elf addrs (by simpa [CliPqxdhElfSecureOld, cliPqxdhSecurityForOld_eq_abstract] using hOld)

/-- The concrete X25519 `CliPqxdhBinaryCorrectAndSecureAnyKem` statement follows from the
abstract-group statement. -/
theorem cliPqxdhBinaryCorrectAndSecure_of_old (bytes : List (BitVec 8))
    (hOld : CliPqxdhBinaryCorrectAndSecureOld bytes) :
    CliPqxdhBinaryCorrectAndSecureAnyKem bytes := by
  rcases hOld with ⟨elf, addrs, hParse, hRes, hCorr, hSec⟩
  exact ⟨elf, addrs, hParse, hRes, hCorr, fun S ℓ =>
    cliPqxdhElfSecure_of_old S ℓ elf addrs (hSec (Pt := X25519Pt) S ℓ)⟩

/-- Converse check at the concrete X25519 instance: `CliPqxdhElfSecureAnyKem` implies the
abstract-group conclusion (`CliPqxdhOldConclusion`) instantiated at `X25519Pt`,
`realUnreachedPrims kemKeyGen`, `realPEParams`, `x25519Dh`, `(x25519EncPt, x25519EncT, x25519DecT)`,
and `x25519Delta`, with the discharged curve and primitive premises accepted as extra hypotheses. -/
theorem cliPqxdhElfSecure_converse_at_concrete
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) (addrs : CliElfAddrs)
    (hNew : CliPqxdhElfSecureAnyKem S ℓ elf addrs) :
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
      ∀ (kemKeyGen : List UInt8 → List UInt8 × List UInt8),
        let X := realUnreachedPrims kemKeyGen
        ∀ (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X realPEParams))
          (δ_kem : ℝ≥0∞)
          (_hKemBin : SignalPqxdh.KemDeltaCorrect (modelPrims X realPEParams) δ_kem)
          (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
          (_hDh : x25519Dh.Commutes)
          (_hX : X25519RealizesDh realPEParams.C x25519Dh x25519EncPt x25519EncT)
          (_hdec : ∀ T, x25519DecT (x25519EncT T) = some T)
          (_hdum : ∀ T, x25519EncT T ≠ dummyKey)
          (_hz : ∀ x, x25519Dh.dh x 0 = 0)
          (_hkerAll : DhKerUniform x25519Dh)
          (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
          (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
          (_hδ : ∀ Q : X25519Pt,
            𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | x25519Dh.dh x x25519Dh.base = Q} ≤
              x25519Delta)
          (A : CliGameAdversary S ℓ (BitVec 512))
          (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
          CliPqxdhOldConclusion S ℓ (cliRunElf elf addrs) X realPEParams
            (some (CliReachesSampleNttStuckElf elf addrs))
            δ_kem x25519Dh x25519EncPt x25519EncT x25519DecT qep
            L_cli RK D reds b qStart qs x25519Delta A := by
  rcases hNew with ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd, hRuns⟩
  refine ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd, fun kemKeyGen => ?_⟩
  intro X hP δ_kem hKemBin qep hℓ _hDh _hX _hdec _hdum _hz _hkerAll b qStart qs hq32 _hδ A hA
  exact hRuns kemKeyGen hP.kemKeyGen_valid hP.kem_coll_bound δ_kem hKemBin qep hℓ b qStart qs
    hq32 A hA

attribute [local irreducible] CryptoGames.MLKEM.kyber1024KemKeyGen

/-- Converse check on the Kyber-1024 headline `CliPqxdhElfSecure`: implies `CliPqxdhOldConclusion`
at `kyber1024KemKeyGen` and `δ_kem := ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`. -/
theorem cliPqxdhElfSecure_kyber1024_converse_at_concrete
    (S : SignalPqxdh.Setup) (ℓ : ℕ) (elf : ElfImage) (addrs : CliElfAddrs)
    (hNew : CliPqxdhElfSecure S ℓ elf addrs) :
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
      let X := realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen
      ∀ (_hP : SignalPqxdh.CryptoWellFormedPrimitivesδ (modelPrims X realPEParams))
        (ε : ℝ≥0∞) (_hGap : SignalPqxdh.KyberNoiseGap ε)
        (qep : ℕ) (_hℓ : ℓ < 10 ^ 6)
        (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
        (_hq32 : ∀ k < qStart, 2 * (qs k + 1) + 25002 < 2 ^ 32)
        (A : CliGameAdversary S ℓ (BitVec 512))
        (_hA : CliGameAdversaryPerInstanceBounded A b qStart qs),
        CliPqxdhOldConclusion S ℓ (cliRunElf elf addrs) X realPEParams
          (some (CliReachesSampleNttStuckElf elf addrs))
          (ε + 1 / 2 ^ 112) x25519Dh x25519EncPt x25519EncT x25519DecT qep
          L_cli RK D reds b qStart qs x25519Delta A := by
  rcases hNew with ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd, hRuns⟩
  refine ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd, ?_⟩
  intro X hP ε hGap qep hℓ b qStart qs hq32 A hA
  exact hRuns hP.kem_coll_bound ε hGap qep hℓ b qStart qs hq32 A hA

end Computational.Tests.Guards.ConcreteX25519OldToNew
