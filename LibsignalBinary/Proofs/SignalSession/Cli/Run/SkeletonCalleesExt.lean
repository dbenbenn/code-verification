/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Ext
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt

open Arm64 ProofLib
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Alloc (MemcpyROOkExtX memcpyROOkExtX_of_hookSat_withStack)
open CryptoVerification.SignalSession.Cli (pathName dirGetName bundleReadName)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)


open CryptoVerification.SignalSession.Cli.RunProofs (cliConcatName cliConcat2Spec)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots pathNeed)

/-!
# Read-Only `memcpy` Callees from `RunHooksExt`

Derives `concat_ok_ext`, `path_ok_ext`, `dirGet_ok_ext`, and `bundleRead_ok_ext` from the
contract-backed `RunHooksExt` bundle.
-/

end LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SignalSession.Cli.RunSkeleton
end CryptoVerification.SignalSession.Cli.RunSkeleton
-- AUTO-BRIDGE END
