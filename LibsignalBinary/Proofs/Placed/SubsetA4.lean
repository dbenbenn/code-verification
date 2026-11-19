/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollaries
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.EntryPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropChain2Placed
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSessionStructure3Placed
import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedB
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlaced
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.FsTrace
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Relocatable `Subset A4` Proof Barrel

Umbrella module rooting `SpqrV1/Poly/NextChunk`, `SpqrV1/Auth`,
`SpqrV1/Prost/{MessageEncode,EncodeToVec}`, and `E2E/Pqxdh` under `[LibsignalPlacement]`.
-/

public section
