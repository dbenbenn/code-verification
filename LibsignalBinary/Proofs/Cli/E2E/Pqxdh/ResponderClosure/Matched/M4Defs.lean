/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# Matched-Session Stage P4 (`+0x34dc → exit`): Spatial Bundles and Statement

Defines the matched-session Stage P4 (`opkIdIsSome = 2#32`, skipping `mark_kyber_pre_key_used` and
`remove_pre_key`, over general `prevSessionsEmptyAt A coroPtr g`) stack budget, spatial entry/exit
predicates, three-way outcome `StageP4MatchedBranch`, and `StageP4MatchedExtStmt`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

/-! ## Stack budget -/

/-- Stack budget for matched-session Stage P4 (`save_identity`, `store_session`, and error
unwinds; `mark_kyber_pre_key_used` and `remove_pre_key` are skipped). -/
@[expose] def stageP4MatchedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (storeSessionCallStack kit)

theorem saveIdStack_le_matched {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    saveIdCallStack ikit ≤ stageP4MatchedCallStack kit ikit :=
  Nat.le_max_left _ _

theorem storeSessionStack_le_matched {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    storeSessionCallStack kit ≤ stageP4MatchedCallStack kit ikit :=
  Nat.le_max_right _ _

theorem stack_matched_to_saveId {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP4MatchedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4MatchedCallStack kit ikit))
        (stageP4MatchedCallStack kit ikit - saveIdCallStack ikit) ∗
        stackAt sp (saveIdCallStack ikit) :=
  stackAt_sub_eq sp (stageP4MatchedCallStack kit ikit) (saveIdCallStack ikit)
    (saveIdStack_le_matched kit ikit) hn

theorem stack_matched_to_storeSession {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP4MatchedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4MatchedCallStack kit ikit))
        (stageP4MatchedCallStack kit ikit - storeSessionCallStack kit) ∗
        stackAt sp (storeSessionCallStack kit) :=
  stackAt_sub_eq sp (stageP4MatchedCallStack kit ikit) (storeSessionCallStack kit)
    (storeSessionStack_le_matched kit ikit) hn

/-! ## Spatial entry/exit bundles and three-way outcome -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
