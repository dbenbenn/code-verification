/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5IfacePlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5SitesPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Mem
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.WPp
public import VerifiedLibraries.Mallocng.Spec

/-!
# Relocatable Address, Heap, and `commitFiles` Helpers for `main` Hop M5 (Block `617`)

Re-exports pure 128-bit pair, `vecBuf` borrow/unborrow, `dirAt_unpack`, and `commitFiles` lemmas
from `M5Mem.lean` alongside Block `617` symbol decodes (`MainCodeSym.lean`).
-/

public section

set_option autoImplicit false
