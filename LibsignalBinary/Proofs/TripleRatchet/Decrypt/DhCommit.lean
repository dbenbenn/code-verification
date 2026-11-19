/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMain
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Decrypt DH Step Commit Sub-Segment (`DhCommitSpec`)

Umbrella module re-exporting the DH commit submodules:
- `DhCommitChain`: `chainAt` byte-slice lemmas, `DhCommitState`, and `DhCommitSpec`
- `DhCommitPack`: packing/unpacking helpers, address lemmas, and `ReachesOrPanic` combinators
- `DhCommitWp`: basic-block `SepWP` lemmas `commit_step1_wp` .. `commit_step5_wp`
- `DhCommitEvict`: receiver-chain eviction loop (`dhCommit_evict_one`, `dhCommit_evict_loop`, `dhCommit_step4`)
- `DhCommitStep3`: receiver-chain push and box free (`dhCommit_step3a`, `dhCommit_step3`)
- `DhCommitStep12`: state commit, `PublicKey::serialize`, and `ChainKey::to_pb` (`dhCommit_step1_2`)
- `DhCommitStep5`: `sender_chain` commit and `ConsumeMsgKeyState` staging (`dhCommit_step5`)
- `DhCommitMain`: top-level `dhCommit_spec` and relocatable seams
-/

public section
