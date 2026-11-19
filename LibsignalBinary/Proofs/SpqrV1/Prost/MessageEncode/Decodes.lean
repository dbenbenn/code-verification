/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym -- shake: keep -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection.SortedFresh
meta import GeneratedLean.LibsignalSessionPlacedObjShard13

/-!
# Block Placement Descriptors for `SpqrV1/Prost/MessageEncode` (`[local#2]`)

Generates per-block placement descriptors (`Blocks 313, 315–319`) for `ChainParams`,
`PolynomialDecoder`, `PolynomialEncoder`, and `EpochDirection` `encode` and `encoded_len`
monomorphizations.
-/

public section

namespace CryptoVerification

set_option maxRecDepth 2000000

gen_ls_blk 313
gen_ls_blk 315
gen_ls_blk 316
gen_ls_blk 317
gen_ls_blk 318
gen_ls_blk 319

end CryptoVerification
