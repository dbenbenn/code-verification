/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomC2EntryGuardLr

/-!
# Concrete `cliElfBytes` Guarded Constructors (`ElfSlicesPqOomPlacedG`)

Hosts the two concrete `cliElfBytes` / `cliElfImage` entry-guarded constructors
(`cliElf_f3B2NeedLocksAssumptionsG` and `cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG`) in
`SpecLemmas/SignalSession/` (`CliElfLib`-only) so that `CliStrictPlaced2G`, `D3BinaryOomProofF3G`,
and `ProgressElfPlacedG` remain independent of `CliElf` in the default library.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesSampleNttStuckPlainPanPlaced cliRunPlainPanPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3
  (LibsignalCliPqBinaryV2OomF3PlainPanPlaced
   libsignalCliPqBinaryV2OomF3PlainPanPlacedAt_of_f3B2NeedLocksG)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G
   V2F3StuckDomain)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer
  (CliElfF3PlainB2NeedLocksAssumptionsG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
  (MainOkCliF3PqB2NeedLocksPlacedAtGWithF)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeOk cliElf_f3B2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomC2EntryGuardLr
  (cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

abbrev CliPqBinaryV2OomF3BytesPlainPanPlaced := LibsignalCliPqBinaryV2OomF3PlainPanPlaced

/-- Closed entry-guarded assumption bundle on plain `cliElfImage` for arbitrary `LinkedAt cliElfBytes`
placements `(mpl, mmpl)`, discharging `harnessG` internally via
`ElfSlicesPqOomC2EntryGuardLr.cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt`. -/
theorem cliElf_f3B2NeedLocksAssumptionsG {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl 80
      (mallocngAddrsOfPlacement mmpl).libc cliMainStk (F3CodeOk mpl mmpl) cliElfImage :=
  { toCliElfExtPlainB2NeedLocksAssumptions2 := cliElf_f3B2NeedLocksAssumptions hls hmng
    harnessG := cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt hls hmng }

/-- Plain-memory guarded constructor concluding `CliPqBinaryV2OomF3BytesPlainPanPlaced cliElfBytes`. -/
theorem cliPqBinaryV2OomF3BytesPlaced_cliElf_of_mainG
    {elf : ElfImage} {exitStk : Nat} {stk : Nat}
    {CodeOk : MultiPlacement → MultiPlacement → Memory → Prop}
    (hparse : ElfImage.parse cliElfBytes = .ok elf)
    (hAssump : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliElfF3PlainB2NeedLocksAssumptionsG mpl mmpl exitStk
        (mallocngAddrsOfPlacement mmpl).libc stk (CodeOk mpl mmpl) elf)
    (hmain : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hoverD3 : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkOverD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (huntyped : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkUntypedD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hpathB : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkPathBD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hvalidMatch : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkValidMatchD3F3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hinitSem : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainInitSemF3G mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hStuckDiv : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i →
          cliRunPlainPanPlacedSig mpl mmpl elf W i = none) :
    CliPqBinaryV2OomF3BytesPlainPanPlaced cliElfBytes :=
  fun mpl mmpl hLs hMm =>
    libsignalCliPqBinaryV2OomF3PlainPanPlacedAt_of_f3B2NeedLocksG hparse
      (hAssump mpl mmpl hLs hMm)
      (hmain mpl mmpl hLs hMm)
      (hoverD3 mpl mmpl hLs hMm)
      (huntyped mpl mmpl hLs hMm)
      (hpathB mpl mmpl hLs hMm)
      (hvalidMatch mpl mmpl hLs hMm)
      (hinitSem mpl mmpl hLs hMm)
      (hStuckDiv mpl mmpl hLs hMm)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
