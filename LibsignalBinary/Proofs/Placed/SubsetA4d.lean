/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FinishGrowPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.Encode1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.EncodeBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Auth.ReprPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyDecoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.PolyEncoderPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.UnchunkedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.DecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.EncodeToVec.FinalPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.BasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.DecodesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.DefsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesBPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EpochEncodedLenPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.FetchPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.LayoutPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Relocatable `Subset A4d` Proof Barrel

Umbrella module rooting the 60 `Cli/SpqrV1` CGU-local callee `*Placed` modules (`Alloc`, `Auth`,
`Drop`, `Prost`, `ProtoRepr`, `Varint`; blocks `435..500`) into `LibsignalBinary.Cli`.
-/

public section
