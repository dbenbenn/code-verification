/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.SymWP
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

public section

set_option autoImplicit false

/-!
# Trap-Mode `segLoad` Prologue, Load Shim, and Poll (`+0x000..+0x160`)

Proves `segLoad_to_dispatch_trap` for the trap-at-RNG CLI program, stepping through prologue `E0`
(`+0x000..+0x08c`), `kit.loadShim`, pre-poll setup (`+0x090..+0x0a8`), `kit.loadPoll`, and
ready-path cleanup `E1` (`+0x0ac..+0x160`).
-/

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
