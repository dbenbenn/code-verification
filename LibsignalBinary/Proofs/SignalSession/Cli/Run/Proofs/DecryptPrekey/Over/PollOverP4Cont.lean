/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrusted -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Spatial
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P4 Continuation

Proves `slotOutTr_d2c_of_reject`, `slotOutTr_d2c_of_accept`, and `closure_pathC_p4_cont`, executing
`Over.StageP4Prev1VRegsStmt` (`+0x34dc → x30`) on overwrite Path C (`¬ SessMatchesPm`) and packaging
both `.ok pt` and `.markErr` into `dpPollSpecState.post`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `slotOutTr` D2(c) Helpers -/

theorem slotOutTr_d2c_of_reject {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    (g' : StoresGhost) {err : ApiError AddrVal Unit} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
    (hdec : decPkDefD2c X W Scope F peer me pm coins = some none) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.error err) tr0 trf := by
  refine ⟨fun h => hne_p (Except.error.inj h), fun h => hne_s (Except.error.inj h), ?_⟩
  rw [hS, hdec]

theorem slotOutTr_d2c_of_accept {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkDefD2c X W Scope)
    (hdec : decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.ok pt) tr0 trf := by
  refine ⟨nofun, nofun, ?_⟩
  rw [hS, hdec]
  exact ⟨rfl, hwr⟩

/-! ## 2. Stage P4 Continuation on Path C (`closure_pathC_p4_cont_ext`, `closure_pathC_p4_cont`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
