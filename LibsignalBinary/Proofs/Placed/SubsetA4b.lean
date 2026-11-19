/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.M4.DecryptPlaced
import LibsignalBinary.Proofs.SpqrV1.M4.EncryptPlaced
import LibsignalBinary.Proofs.SpqrV1.M4.RecordDecryptPlaced
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.IntoPbCodeSym
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.RecvPlacedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesPolyExactPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.SendPlacedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Relocatable `Subset A4b` Proof Barrel

Umbrella module rooting `SpqrV1/Drop/ChainEpochPlaced` (blocks `143, 269, 287`),
`SpqrV1/States/IntoPb` (block `334`), `SpqrV1/Top` (blocks `124, 323..329, 351, 352`), and
`SpqrV1/M4` under `[LibsignalPlacement]`.
-/

public section
