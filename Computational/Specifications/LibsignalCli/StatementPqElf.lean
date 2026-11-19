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
public import Computational.Specifications.Assumptions.Kyber1024Correct
public import LibsignalBinary.Specifications.CryptoGames.DH.X25519Group
public import LibsignalBinary.Specifications.CryptoGames.KEM.Kyber1024KeyGen
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Computational.Specifications.Pqxdh.Security.HeadlineDelta

@[expose] public section

set_option autoImplicit false

/-!
# ELF-direct security statement for the PQXDH CLI

**Trusted: the statement.** Defines `CliPqxdhBinaryCorrectAndSecure`, the top-level correctness and
cryptographic security predicate instantiated at `cliElfBytes` in `Computational/Theorems/Main.lean`.
Read alongside `StatementPq.lean` (`cliPqExp`, `CliPqxdhAdvantage`), `StatementPqOomGame.lean`
(`CliPqxdhFlagProb`, `CliKemFailProb`), `StatementPqReds.lean`,
`Computational/Specifications/Assumptions/Kyber1024Correct.lean` (`KyberNoiseGap`),
`LibsignalBinary/Specifications/CryptoGames/KEM/Kyber1024KeyGen.lean` (`kyber1024KemKeyGen`),
`LibsignalBinary/Specifications/CryptoGames/DH/X25519Group.lean` (`X25519Pt`, `x25519Dh`,
`x25519EncPt`, `x25519EncT`, `x25519DecT`, `x25519Delta`), and
`LibsignalBinary/Specifications/SignalSession/CliBinaryPq.lean` (`CliPqxdhElfCorrect`,
`cliRunElf`, `resolveCliElfAddrs`). See `Computational/docs/TRUSTED_BASE.md` and
`Computational/docs/DEVIATIONS.md`.

`CliPqxdhSecurityFor S ℓ ForRuns` is stated at the closed primitive bundle `realPEParams`
(FIPS 180-4 SHA-256 / SHA-512 compression, FIPS 197 AES-256, RFC 7748 X25519, round-3 Kyber-1024
encapsulation/decapsulation, FIPS 203 ML-KEM-768 incremental), the concrete Curve25519 prime-order
x-only subgroup (`X25519Pt`, `x25519Dh`, `x25519EncPt`, `x25519EncT`, `x25519DecT`, explicit
point-fiber bound `x25519Delta = 1 / 2 ^ 250`), and the concrete Curve25519/XEdDSA and round-3
CRYSTALS-Kyber-1024 unreached model operations
(`realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen`: `x25519Base`, scalar arithmetic mod
`edOrderL`, cofactor-clearing subgroup projection `realPow8`, real XEdDSA signing `realXeddsaSign`,
reference DDH predicate `realIsValidDhTriple`, and concrete Kyber-1024 key generation
`kyber1024KemKeyGen`). It asserts cost- and query-bounded reductions (`L_cli`, `RK`, `D`, `reds`)
and establishes two upper bounds in `ℝ≥0∞` on `CliPqxdhAdvantage` for the runs selected by
`ForRuns`: first against `KeyInd1KeyRealAdvantage`, and second (given the HKDF random-oracle
idealization gap `KeyIndRoGap`, DEV-CLI16) against `pqxdhKeyIndAdvantageBoundActiveδ`
(`GapSigEufCma`, `KemShCr`, `GapDhWithSign`). Both bounds instantiate the Kyber-1024 decapsulation
failure parameter to `ε + 1 / 2 ^ 112` under the `SHA3-512` (`G`) + `SHAKE-256` (`PRF`) CBD-noise
idealization gap `KyberNoiseGap ε` (DEV-PQ21; key-generation wire lengths `(1568, 3168)` are
discharged unconditionally by `kyber1024_kem_delta_correct`), and include the Double Ratchet prefix
sum `prefixSum`, `2 * CliKemFailProb` evaluated directly on the adversary `A` (since
adversary-chosen send randomness controls the SPQR V1 ML-KEM-768 coins), and, when
`exc? = some exc`, `2 * CliPqxdhFlagProb` for excused aborts (`withExcusedAbortTerm`). The only
remaining primitive premise on `kyber1024KemKeyGen` is the `≤ 1 / 2 ^ 255` public-key collision
bound `_hKemColl` (which cannot be proved unconditionally for concrete unkeyed `SHA3-512` `G`
without an idealization on `SHA3-512`; see DEV-PQ21). The KEM-generic counterpart over an arbitrary
`kemKeyGen` and `δ_kem` lives in `StatementPqElfAnyKem.lean` (`CliPqxdhSecurityForAnyKem`).

`CliPqxdhElfSecure` specializes `CliPqxdhSecurityFor` to the ELF-direct runner `cliRunElf elf addrs`
using the 23 `.symtab`-resolved addresses `addrs` (`resolveCliElfAddrs`: 18 Rust panic entry points
and 5 `SampleNTT` entry points), starting directly from plain `ElfImage.loadState` (zero initial
memory patches), with `exc? := some (CliReachesSampleNttStuckElf elf addrs)` (adding the
`2 * CliPqxdhFlagProb` `SampleNTT` seed-divergence term via `withExcusedAbortTerm`, DEV-CLI22) and
no `.OutOfMemory` hypothesis or allocation-failure term on the security clause (under the modelled
1 GiB dynamic physical-memory budget; the correctness conjunct `CliPqxdhElfCorrect` excuses both
`.OutOfMemory`, DEV-CLI15, and `SampleNTT` seed divergence, DEV-CLI22). Every instruction except
the 18 Rust panic entry points (DEV-E7) executes directly from plain loaded ELF memory, including
`aes` and `spqr` CPU-feature probes against the pinned auxv (`AT_HWCAP = 0x1b`, `AT_HWCAP2 = 0`:
FP, ASIMD, AES, and PMULL enabled, ATOMICS/LSE = 0; `AT_RANDOM` = 16 zero bytes); the trust point
is that the ELF `.symtab` labels the 18 panic entry points and 5 `SampleNTT` entries accurately.

Scope follows `Computational/docs/DEVIATIONS.md`: unpartnered first-message payload privacy and
authentication are covered by the `Auth` conjunct of Lemma 1 rather than folded into this game
(DEV-C5), and as in `CliBinaryPq.lean`, the statement applies to the modelled auxv (`AT_HWCAP = 0x1b`,
LSE bit 8 `= 0`, DEV-CLI10) and excludes subsequent calls after an accepted non-matching pre-key
`recv` (DEV-CLI11).
-/

open OracleComp OracleSpec MeasureTheory ENNReal

/-! ## Concrete Curve25519 / XEdDSA unreached PQXDH primitives -/

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.RFC7748 CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-- Cofactor-clearing idempotent subgroup projection on Curve25519 (`gexp_div_8`): raises points on
`E(𝔽_p)` to `3 * edOrderL + 1` (`≡ 0 mod 8`, `≡ 1 mod edOrderL`) and points on the quadratic twist
`E'(𝔽_p)` to `3 * twistOrderL + 1` (`≡ 0 mod 4`, `≡ 1 mod twistOrderL`), mapping non-32-byte inputs
to `0^32`. -/
def realPow8 (pk : List UInt8) : List UInt8 :=
  if pk.length == 32 then
    let bs := ofU8 pk
    let exp :=
      match SignalPqxdh.montLiftEd bs 0#8 with
      | some _ => 3 * VerifiedLibraries.Common.edOrderL + 1
      | none => 3 * twistOrderL + 1
    toU8 (VerifiedLibraries.Common.natToLeBytes 32
      (x25519Ladder exp (decodeU255 bs)))
  else
    List.replicate 32 0

/-- 32-byte little-endian Curve25519 scalar multiplication modulo `edOrderL`. -/
def realScalarMul (a b : List UInt8) : List UInt8 :=
  toU8 (VerifiedLibraries.Common.natToLeBytes 32
    ((VerifiedLibraries.Common.leBytesToNat (u8Vec 32 a).toList *
      VerifiedLibraries.Common.leBytesToNat (u8Vec 32 b).toList) %
      VerifiedLibraries.Common.edOrderL))

/-- 32-byte little-endian Curve25519 scalar addition modulo `edOrderL`. -/
def realScalarAdd (a b : List UInt8) : List UInt8 :=
  toU8 (VerifiedLibraries.Common.natToLeBytes 32
    ((VerifiedLibraries.Common.leBytesToNat (u8Vec 32 a).toList +
      VerifiedLibraries.Common.leBytesToNat (u8Vec 32 b).toList) %
      VerifiedLibraries.Common.edOrderL))

/-- Base `UnreachedPqxdhPrimitives` bundle fixing `sigPkGen`, `scalarMul`, `scalarAdd`, and `pow8`
to Curve25519, with placeholders for `sigSign` and `isValidDhTriple` populated in
`realUnreachedPrims`. -/
def realUnreachedPrimsBase (kemKeyGen : List UInt8 → List UInt8 × List UInt8) :
    UnreachedPqxdhPrimitives where
  sigPkGen := fun a => vecU8 (x25519PubFromSecretRef (Ratchet.clampScalar (u8Vec 32 a)))
  sigSign := fun _ _ _ => []
  scalarMul := realScalarMul
  scalarAdd := realScalarAdd
  kemKeyGen := kemKeyGen
  pow8 := realPow8
  isValidDhTriple := fun _ _ _ => false

/-- Concrete XEdDSA signing over `realPEParams` (SHA-512, Ed25519 scalar multiplication and point
compression, Curve25519 scalar arithmetic mod `edOrderL`), packing the Edwards sign bit of `[a]B`
into bit 7 of byte 63. -/
noncomputable def realXeddsaSign (sk m rand : List UInt8) : List UInt8 :=
  let P := modelPrims (realUnreachedPrimsBase (fun _ => ([], []))) realPEParams
  let zero32 : List UInt8 := List.replicate 32 0
  let edDummy := (P.montToEd (P.x25519Base zero32) 0).getD VerifiedLibraries.Common.edZero
  let edBaseMul := fun x => P.doubleScalarMulBasepoint zero32 edDummy x
  let xeddsaPrefix : List UInt8 := [0xFE] ++ List.replicate 31 0xFF
  let keyData := SignalPqxdh.clampScalar25519 sk
  let a := P.scalarFromBytesModOrder keyData
  let capA := P.compress (edBaseMul a)
  let signBitByte : UInt8 := capA.getD 31 0 &&& 0x80
  let r := P.scalarFromWide
    (P.sha512 (xeddsaPrefix ++ keyData ++ m ++ SignalPqxdh.fitBytesRef 64 rand))
  let capR := P.compress (edBaseMul r)
  let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
  let s := P.scalarAdd (P.scalarMul h a) r
  capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte]

/-- Concrete Curve25519 DDH-oracle predicate matching `SignalPqxdh.isValidDhTripleRef` over
`realPEParams` and `realPow8`. -/
noncomputable def realIsValidDhTriple (A B Z : List UInt8) : Bool :=
  let P := modelPrims (realUnreachedPrimsBase (fun _ => ([], []))) realPEParams
  @decide (SignalPqxdh.isValidDhTripleRef P A B Z) (Classical.propDecidable _)

/-- Concrete `UnreachedPqxdhPrimitives` at `realPEParams`: fixes all 6 Curve25519/XEdDSA fields
(`sigPkGen`, `sigSign`, `scalarMul`, `scalarAdd`, `pow8`, `isValidDhTriple`), leaving only
Kyber-1024 `kemKeyGen` parameterized. -/
noncomputable def realUnreachedPrims (kemKeyGen : List UInt8 → List UInt8 × List UInt8) :
    UnreachedPqxdhPrimitives :=
  { realUnreachedPrimsBase kemKeyGen with
    sigSign := realXeddsaSign
    isValidDhTriple := realIsValidDhTriple }

/-! ## Canonical CLI PQXDH security proposition -/

/-- Holds when `i` is a PQXDH-mode input (`CliPqxdhInputs W`) excused by `exc` on which `run i`
has no outcome or aborts (`run i = none ∨ run i = some .aborted`). -/
def CliPqxdhExcusedAbort (exc : Inputs → Prop) (run : CliRun) (W : PEParams) (i : Inputs) : Prop :=
  CliPqxdhInputs W i ∧ exc i ∧ (run i = none ∨ run i = some .aborted)

/-- Adds `2 * CliPqxdhFlagProb … (CliPqxdhExcusedAbort exc run W)` to `rhs` when `exc? = some exc`,
or leaves `rhs` unchanged when `exc? = none`. -/
noncomputable abbrev withExcusedAbortTerm {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) : Option (Inputs → Prop) → ℝ≥0∞ → ℝ≥0∞
  | none, rhs => rhs
  | some exc, rhs =>
      rhs + 2 * CliPqxdhFlagProb S run X W ℓ qep decT encT A (CliPqxdhExcusedAbort exc run W)

/-- Canonical CLI PQXDH security statement at `realPEParams`, the concrete Curve25519 prime-order
x-only subgroup (`X25519Pt`, `x25519Dh`, `x25519EncPt`, `x25519EncT`, `x25519DecT`,
`x25519Delta = 1 / 2 ^ 250`), and round-3 CRYSTALS-Kyber-1024 key generation
`CryptoGames.MLKEM.kyber1024KemKeyGen` with concrete decapsulation failure parameter
`ε + 1 / 2 ^ 112` under `SignalPqxdh.KyberNoiseGap ε` (DEV-PQ21; key-generation wire lengths
`(1568, 3168)` proved unconditionally by `kyber1024_kem_delta_correct`, public-key collision bound
`_hKemColl` retained as a premise), parameterized by the run quantifier `ForRuns` over
`(run, exc?)`. Asserts cost- and query-bounded reductions and bounds `CliPqxdhAdvantage` against
`KeyInd1KeyRealAdvantage` and (given `KeyIndRoGap`) `pqxdhKeyIndAdvantageBoundActiveδ`.
Cost bounds (`CliAdapterCostBounded`, `CompositionCostedReductionFamilyBounded`) track both total
queries `qTot = b.q_total + qStart + qDR` and per-kind counts (`bhKindCounts b qStart qDR`)
separating online queries (`b.q_on`, `qStart`, `qDR`) from offline random-oracle queries
(`b.q_ro`), while the `KeyInd` bound depends only on `b_ki.q_on`. -/
def CliPqxdhSecurityFor
    (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (ForRuns : (CliRun → Option (Inputs → Prop) → Prop) → Prop) :
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
    ForRuns fun run exc? =>
      let X := realUnreachedPrims CryptoGames.MLKEM.kyber1024KemKeyGen
      let P := modelPrims X realPEParams
      ∀ (_hKemColl : ∀ targetPk,
            𝒟[do let (pk, _) ← SignalPqxdh.sampleKemKeyGen P; pure (pk == targetPk)] {true}
              ≤ 1 / (2 : ℝ≥0∞) ^ 255)
        (ε : ℝ≥0∞) (_hGap : SignalPqxdh.KyberNoiseGap ε)
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
                SignalPqxdh.Security.kemDecapsFailureTerm S (ε + 1 / 2 ^ 112) +
                2 * CliKemFailProb S run X realPEParams ℓ qep x25519DecT x25519EncT A) ∧
          (∀ ε_ro : ℝ≥0∞, SignalPqxdh.KeyIndRoGap S P advK ε_ro →
            CliPqxdhAdvantage S run X realPEParams ℓ qep x25519DecT x25519EncT A ≤
              withExcusedAbortTerm S run X realPEParams ℓ qep x25519DecT x25519EncT A exc?
                (2 * (let R := RK.eval
                      let Ab : SignalPqxdh.BoundedAdv (SignalPqxdh.KeyIndAdversary S) b_ki := ⟨advK, hK⟩
                      SignalPqxdh.Security.pqxdhKeyIndAdvantageBoundActiveδ S b_ki.q_on (ε + 1 / 2 ^ 112)
                        (SignalPqxdh.GapSigEufCma P P.isValidDhTriple (R.sig _ Ab))
                        (SignalPqxdh.KemShCr P (R.shcr _ Ab))
                        (SignalPqxdh.GapDhWithSign P P.isValidDhTriple P.pow8 (R.gdh _ Ab)) + ε_ro)
                  + prefixSum + SignalPqxdh.Security.kemDecapsFailureTerm S (ε + 1 / 2 ^ 112)
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

/-- Specializes `CliPqxdhSecurityFor` to the ELF-direct runner `cliRunElf elf addrs` at the closed
primitive bundle `realPEParams`, the concrete Curve25519 prime-order x-only subgroup (`X25519Pt`,
`x25519Dh`, `x25519Delta = 1 / 2 ^ 250`), and round-3 CRYSTALS-Kyber-1024 key generation
`kyber1024KemKeyGen` (`δ_kem = ε + 1 / 2 ^ 112` under `KyberNoiseGap ε`), with
`exc? := some (CliReachesSampleNttStuckElf elf addrs)` (for the `2 * CliPqxdhFlagProb` `SampleNTT`
seed-divergence term, DEV-CLI22) and no `.OutOfMemory` hypothesis. -/
abbrev CliPqxdhElfSecure (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  CliPqxdhSecurityFor S ℓ fun Bound =>
    Bound (cliRunElf elf addrs)
      (some (CliReachesSampleNttStuckElf elf addrs))

/-- `bytes` parses as `elf`, the 23 `.symtab` addresses resolve via `resolveCliElfAddrs`, and both
`CliPqxdhElfCorrect elf addrs` and `CliPqxdhElfSecure S ℓ elf addrs` hold. -/
def CliPqxdhBinaryCorrectAndSecure (bytes : List (BitVec 8)) : Prop :=
  ∃ elf addrs, ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliPqxdhElfCorrect elf addrs ∧
    ∀ (S : SignalPqxdh.Setup) (ℓ : ℕ),
      CliPqxdhElfSecure S ℓ elf addrs

end CryptoVerification.LibsignalCli
