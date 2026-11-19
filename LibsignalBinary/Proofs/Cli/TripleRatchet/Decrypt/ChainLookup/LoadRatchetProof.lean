/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` Segment S1 (`LoadRatchet`) Proof

Proves segment S1 (`LoadRatchetSpec`, `+0x1d8 → +0x2a4 / +0x384 → +0x3b0`), covering
`TripleRatchet::from_session_state` and its error-return and continuation branches.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainLookupFacts

end ChainLookupFacts

namespace ChainLookupFacts

end ChainLookupFacts

private abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
