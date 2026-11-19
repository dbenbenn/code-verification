/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection
public meta import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public import Arm64.Trusted.Object.Labels
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib.BV
public import ProofLib.GenDecodes
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.LibcHooks
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.Multi
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.SyscallsMmap
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.Alloc
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
public import VerifiedLibraries.RustStd.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon

/-!
# Interned Symbol-Character Table for `cliElfImage`

Reflects `cliElfImage.symbols` into `List (List Char × BitVec 64)` once for reuse across
placed ELF symbol-resolution modules.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

open Arm64 ProofLib.ProgramReflection
open CryptoVerification.SignalSession (cliElfImage)

@[expose] noncomputable def cliElfSyms : List (String × BitVec 64) := cliElfImage.symbols

set_option maxRecDepth 4000000 in
-- noncomputable: compiling this 3,241-symbol reflected List Char table roughly triples this module's build time
@[expose] noncomputable def cliElfSymChars : List (List Char × BitVec 64) :=
  assoc_chars_of% cliElfSyms

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
theorem cliElf_symbols_eq :
    cliElfImage.symbols = toStringAssoc cliElfSymChars := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
