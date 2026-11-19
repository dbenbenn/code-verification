/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.RegChain

/-!
# CLI `try_decrypt_from_record` Clone Segment under `DistinctSid`

Defines weak-`pre` (`remote ≠ local ∨ DistinctSid`) record specification `recordDecryptSpecP`,
cutpoint `VStateP`, and proves `segClone_ok_ext_P` / `segClone_ok_P` over the public sub-segment
theorems in `CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Weak-`pre` (`DistinctSid`) Record Specs & Cutpoints -/

/-- `recPure` weakening `remote ≠ local` to `remote ≠ local ∨ DistinctSid`. -/
@[expose] def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recPureP
    (uuidParse : UuidParser) (x : RecordDecryptGhost) : Prop :=
  (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
    CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
  SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32

private theorem rcp_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_kernel

end CryptoVerification.Cli.LibsignalSpqrV1.M4
