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
public import ProofLib.ProgramReflection.SortedFresh
meta import GeneratedLean.LibsignalSessionPlacedObjShard1
meta import GeneratedLean.LibsignalSessionPlacedObjShard2
meta import GeneratedLean.LibsignalSessionPlacedObjShard4
meta import GeneratedLean.LibsignalSessionPlacedObjShard5

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.E2E.Pqxdh

open Arm64 CryptoVerification ProofLib.ProgramReflection

end CryptoVerification.E2E.Pqxdh

namespace CryptoVerification

gen_ls_blk 31
gen_ls_blk 34
gen_ls_blk 81
gen_ls_blk 110

end CryptoVerification
