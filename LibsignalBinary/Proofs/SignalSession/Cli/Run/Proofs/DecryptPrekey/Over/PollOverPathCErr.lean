/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInst -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P2 Statement and Stage P3 Error Exit

Opens the six CLI store kits under `DecPkOkD2c` and `FilesOkPeer`, defines and instantiates the
Path C CPS Stage P2 contract `StageP2OverQpanCliStmt` (`+0x0868 → +0x1778`, plus `Ext` variants),
and folds Stage P3 `Err` / `verNe` rejection exits back into `dpPollSpecState.post`.
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

/-! ## 1. D2(c) Opened-Stores Kit Entailment -/

theorem storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext {A : RustAlloc} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    (b : BitVec 64) (σ : DpKitStk) (storesPtr : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hfPeer : Slots.FilesOkPeer Scope F peer.val)
    (hdecOk : DecPkOkD2c W Scope F peer.val me pm)
    (pid sid kid : BitVec 32) (kbk : PublicKey) :
    storesAt A storesPtr StoresGhost.opened ⊢
      cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ
        storesPtr StoresGhost.opened := by
  have hd0 := hdecOk.toDecPkOk₀_emptyScope
  exact storesAt_entails_cliPollStoresKitsAt (A := A) b σ
    storesPtr StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hfPeer)
    (cliIdOwnInv_opened hd0)
    (cliIdInv_opened_peer hfPeer)
    (cliPkInv_opened hd0 pid)
    (cliSpkInv_opened hd0 sid)
    (cliKpkInvFull_opened hd0 kid sid kbk)

theorem storesAt_opened_entails_cliPollStoresKitsAt_d2c {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    (b : BitVec 64) (σ : DpKitStk) (storesPtr : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hfPeer : Slots.FilesOkPeer Scope F peer.val)
    (hdecOk : DecPkOkD2c W Scope F peer.val me pm)
    (pid sid kid : BitVec 32) (kbk : PublicKey) :
    storesAt E2E.HooksE.A0 storesPtr StoresGhost.opened ⊢
      cliPollStoresKitsAt E2E.HooksE.A0 b F Slots.scopeKit peer pid sid kid kbk σ
        storesPtr StoresGhost.opened :=
  storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext (A := E2E.HooksE.A0) b σ storesPtr
    hsub hfPeer hdecOk pid sid kid kbk

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
