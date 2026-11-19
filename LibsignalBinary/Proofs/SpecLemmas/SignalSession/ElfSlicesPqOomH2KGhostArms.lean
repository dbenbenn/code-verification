/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec

/-!
# `H2KGhostArms` Bundle and 6-Arm `MainOk*G` Corollaries (`ElfSlicesPqOomH2KGhostArms`)

**Checked by Lean.**

Packages the 6-arm ghost bundle `H2KGhostArms` across all valid `(mpl, mmpl)` placements of
`cliElfBytes` and projects the six guarded `MainOk*G` corollaries (`h2kg_hmain_cliElfG` ..
`h2kg_hinitSem_cliElfG`, which discharge `h2asm_h*_cliElfKG` via `hG`) plus
`h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms

open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomPlainF3
  (LibsignalCliPqBinaryV2OomF3PlainPanPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2GWithF
  (MainOkCliF3PqB2NeedLocksPlacedAtGWithF)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
  (H2KGhostArmsType cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_GhostMainArmsK
   h2asm_hinitSem_cliElfKG
   h2asm_hmain_cliElfKG
   h2asm_hoverD3_cliElfKG
   h2asm_hpathB_cliElfKG
   h2asm_huntyped_cliElfKG
   h2asm_hvalidMatch_cliElfKG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
  (h2ka_branch2HookReplaysK h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ghostArms)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-- 6-arm ghost witness bundle across all valid `(mpl, mmpl)` placements of `cliElfBytes`. -/
@[expose] def H2KGhostArms : Prop :=
  ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
    mallocngLib.LinkedAt cliElfBytes mmpl →
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainArmsK mpl mmpl

/-- Projects `H2KGhostArms` to the cycle-free `H2KGhostArmsType` carrier of
`ElfSampleNttStuckDiverge`. -/
theorem h2kg_ghostArmsType (hG : H2KGhostArms) : H2KGhostArmsType :=
  fun mpl mmpl hLs hMm =>
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    let ha := hG mpl mmpl hLs hMm
    ⟨ha.hmain, ha.hoverD3, ha.huntyped, ha.hpathB, ha.hvalidMatch, ha.hinitSem⟩

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.hmain_cliElf`. -/
theorem h2kg_hmain_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkCliF3PqB2NeedLocksPlacedAtGWithF sha256Compress mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hmain_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hmain

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.hoverD3_cliElf`. -/
theorem h2kg_hoverD3_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkOverD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hoverD3_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hoverD3

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.huntyped_cliElf`. -/
theorem h2kg_huntyped_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_huntyped_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).huntyped

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.hpathB_cliElf`. -/
theorem h2kg_hpathB_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkPathBD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hpathB_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hpathB

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.hvalidMatch_cliElf`. -/
theorem h2kg_hvalidMatch_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkValidMatchD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hvalidMatch_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hvalidMatch

/-- Guarded ghost-bundle twin of `ElfSlicesPqOomPlacedInst.hinitSem_cliElf`. -/
theorem h2kg_hinitSem_cliElfG
    (hG : H2KGhostArms)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  h2asm_hinitSem_cliElfKG mpl mmpl hLs hMm
    (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)
    (hG mpl mmpl hLs hMm).hinitSem

/-- Assembles `LibsignalCliPqBinaryV2OomF3PlainPanPlaced cliElfBytes` from `H2KGhostArms`. -/
theorem h2kg_cliPqBinaryV2OomF3BytesPlaced_cliElf
    (hG : H2KGhostArms) :
    LibsignalCliPqBinaryV2OomF3PlainPanPlaced cliElfBytes :=
  h2ka_cliPqBinaryV2OomF3BytesPlaced_cliElf_of_ghostArms hG
    (cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK (h2kg_ghostArmsType hG))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
