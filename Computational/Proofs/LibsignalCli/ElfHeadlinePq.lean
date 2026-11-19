/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Specifications.LibsignalCli.StatementPqElfAnyKem
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
import Computational.Proofs.Kyber1024Delta.HeadlineProof
import Computational.Proofs.LibsignalCli.MainOfLemmas
import Computational.Proofs.SignalPqxdh.Delta.Statements
import Computational.Proofs.LibsignalCli.HeadlineSession
import Computational.Proofs.LibsignalCli.HeadlineModel
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge -- rooting-only, no decl used
import Computational.Proofs.LibsignalCli.MainHaltedGame
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK

public section

set_option autoImplicit false

/-!
# PQXDH + SPQR correctness and security of the concrete `signal-session` ELF

**Checked by Lean.**

Composes the relocatable binary correctness bundle, the 1 GiB no-OOM proof, the link-completeness
witnesses, and the ELF-direct bridge (`ElfDirectBridge.cliPqxdhBinaryCorrect_of_placed`) with
`main_of_lemmas` to prove `CliPqxdhBinaryCorrectAndSecure cliElfBytes`.
-/

namespace CryptoVerification.SignalSession

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  LibsignalCliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (MainOkPathBD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 MainOkValidMatchD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (MainOkUntypedD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (
  cliPqxdhElfCorrectPlaced_of_placedWith
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (MainInitSemF3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced (
  CliPqBinaryV2OomF3BytesPlaced
  cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms (
  H2KGhostArms h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1 (
  h2k_ghostArms_closed
)

/-! ## Relocatable binary correctness -/

theorem cliPqxdhBinaryCorrectPlacedAt_of_v2OomF3 {mpl mmpl : MultiPlacement}
    {bytes : List (BitVec 8)}
    (hcm : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → Placed.CliElfCodeMatchesPlaced mpl elf)
    (hv2 : LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl bytes :=
  let ⟨elf, hparse, h⟩ := hv2
  ⟨elf, hparse,
    LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.cliPqxdhElfCorrectPlaced_to_trusted
      (hcm elf hparse) (cliPqxdhElfCorrectPlaced_of_placedWith h.base)⟩

theorem cliPqxdhBinaryCorrectPlaced_of_v2OomF3 {bytes : List (BitVec 8)}
    (hmng : VerifiedLibraries.mallocngLib.LinkedIn bytes)
    (hcm : ∀ mpl : MultiPlacement, libsignalSessionLib.LinkedAt bytes mpl →
      ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf → Placed.CliElfCodeMatchesPlaced mpl elf)
    (hv2 : LibsignalCliPqBinaryV2OomF3Placed bytes) :
    CliPqxdhBinaryCorrectPlaced bytes := by
  intro mpl hLs
  obtain ⟨mmpl, hMm⟩ := hmng
  exact cliPqxdhBinaryCorrectPlacedAt_of_v2OomF3 (hcm mpl hLs) (hv2 mpl mmpl hLs hMm)

theorem libsignal_cli_pq_binary_correct_placed_of_v2
    (hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes) :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  cliPqxdhBinaryCorrectPlaced_of_v2OomF3
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_mallocng_linkedIn
    (fun _ hLs _ hparse =>
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_trustedCodeMatchesPlaced_of_parse
        hLs hparse)
    hv2

theorem libsignal_cli_pq_binary_correct_placed_of_main
    {elf : ElfImage} {exitStk : Nat} {stk : Nat}
    {CodeOk : MultiPlacement → MultiPlacement → Memory → Prop}
    (hparse : ElfImage.parse cliElfBytes = .ok elf)
    (hAssump : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk
        (mallocngAddrsOfPlacement mmpl).libc stk (CodeOk mpl mmpl) elf)
    (hmain : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hoverD3 : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkOverD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (huntyped : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkUntypedD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hpathB : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkPathBD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hvalidMatch : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkValidMatchD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hinitSem : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainInitSemF3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk) :
    CliPqxdhBinaryCorrectPlaced cliElfBytes :=
  libsignal_cli_pq_binary_correct_placed_of_v2
    (cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
      hparse hAssump hmain hoverD3 huntyped hpathB hvalidMatch hinitSem)

theorem libsignal_cli_pq_binary_correct_placed_proofK :
    H2KGhostArms →
      LibsignalBinary.Proofs.Placed.CliPlainPanPlaced.CliPqxdhBinaryCorrectPlainPanPlaced
        cliElfBytes :=
  fun hG mpl mmpl hLs hMm =>
    ⟨cliElfImage, cliElf_parse,
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK.cliElf_noOOMK
        hG mpl mmpl hLs hMm).1⟩

/-- Relocatable plain-memory binary correctness of `cliElfBytes`. -/
theorem libsignal_cli_pq_binary_correct_placed_proof :
    LibsignalBinary.Proofs.Placed.CliPlainPanPlaced.CliPqxdhBinaryCorrectPlainPanPlaced
      cliElfBytes :=
  libsignal_cli_pq_binary_correct_placed_proofK h2k_ghostArms_closed

/-- ELF-direct binary correctness of `cliElfBytes` (Lemma 4). -/
theorem libsignal_cli_pq_binary_correct_proof :
    CliPqxdhBinaryCorrect cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliPqxdhBinaryCorrect_of_plainPanPlaced
    libsignal_cli_pq_binary_correct_placed_proof

end CryptoVerification.SignalSession

namespace CryptoVerification.LibsignalCli

open scoped ENNReal
open Arm64.Process (ElfImage)
open CryptoGames.MLKEM (kyber1024KemKeyGen)
open CryptoVerification.E2E (model_secure_costed_proof session_secure_proof)
open CryptoVerification.SignalSession (
  CliElfAddrs CliPqxdhInputs CliReachesOOMElf Inputs
  cliElfBytes realPEParams resolveCliElfAddrs
  libsignal_cli_pq_binary_correct_proof
)
open _root_.SignalPqxdh.Security (headlineδ_proof)
open Computational.Proofs.Kyber1024Delta.HeadlineProof (kyber1024_kem_delta_correct_proof)
open Computational.Proofs.LibsignalCli.MainHaltedGame (cliHaltedBoundProp_holds)
open Computational.Proofs.LibsignalCli.MainOfLemmas (main_of_lemmas)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge (
  cliElf_parse_resolve_unique cliReachesOOMElf_iff
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK (cliElf_noOOM_of_parseK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (
  cliElf_linkedAt cliElf_mallocng_linkedIn
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1 (h2k_ghostArms_closed)

/-! ## ELF-direct main theorem -/

private theorem cliElf_noOOM_elf :
    ∀ (elf : ElfImage) (addrs : CliElfAddrs),
      ElfImage.parse cliElfBytes = .ok elf →
      resolveCliElfAddrs cliElfBytes elf = .ok addrs →
      ∀ (i : Inputs), CliPqxdhInputs realPEParams i →
        ¬ CliReachesOOMElf elf addrs i := by
  intro elf addrs hparse hres i hi hoom
  obtain ⟨rfl, rfl⟩ := cliElf_parse_resolve_unique hparse hres
  obtain ⟨mmpl, hMm⟩ := cliElf_mallocng_linkedIn
  have hNoOom := (cliElf_noOOM_of_parseK h2k_ghostArms_closed
    _ mmpl cliElf_linkedAt hMm _ hparse).2 i hi
  exact hNoOom ((cliReachesOOMElf_iff i).mp hoom)

/-- KEM-generic ELF-direct PQXDH + SPQR binary correctness and security of `cliElfBytes`. -/
theorem libsignal_cli_pq_secure_elf_binary_any_kem_proof :
    CliPqxdhBinaryCorrectAndSecureAnyKem cliElfBytes :=
  main_of_lemmas headlineδ_proof session_secure_proof model_secure_costed_proof
    libsignal_cli_pq_binary_correct_proof
    cliElf_noOOM_elf
    (fun {Pt} _ _ _ S ℓ => cliHaltedBoundProp_holds (Pt := Pt) S ℓ)

attribute [local irreducible] kyber1024KemKeyGen

/-- ELF-direct PQXDH + SPQR binary correctness and security of `cliElfBytes` at concrete
Round-3 CRYSTALS-Kyber-1024 (`kyber1024KemKeyGen`, `δ_kem = ε + 1 / 2 ^ 112` under
`KyberNoiseGap ε`). -/
theorem libsignal_cli_pq_secure_elf_binary_proof :
    CliPqxdhBinaryCorrectAndSecure cliElfBytes := by
  rcases libsignal_cli_pq_secure_elf_binary_any_kem_proof with ⟨elf, addrs, hparse, hres, hcorr, hsec⟩
  have ⟨hKemValid, hKemDelta⟩ := kyber1024_kem_delta_correct_proof
  refine ⟨elf, addrs, hparse, hres, hcorr, fun S ℓ => ?_⟩
  rcases hsec S ℓ with ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd, hRuns⟩
  exact ⟨L_cli, RK, D, reds, hRKb, hRKq, hDb, hBnd,
    fun hKemColl ε hGap => hRuns kyber1024KemKeyGen hKemValid hKemColl
      (ε + 1 / 2 ^ 112) (hKemDelta ε hGap)⟩

end CryptoVerification.LibsignalCli
