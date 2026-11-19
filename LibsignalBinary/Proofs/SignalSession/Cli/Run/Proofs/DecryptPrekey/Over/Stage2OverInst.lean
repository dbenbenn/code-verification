/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeCoins -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathACore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Open
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenDeserId

/-!
# CLI Poll Stage P2 Over-Path (`Path C`) Instantiation

Defines `StageP2PathCOverModelRej`, `StageP2PathCOverErr`, and `StageP2PathCOverQpanCliStmt` (plus
`Ext` generalizations) and proves `stageP2PathCOver_qpan_cli_ok` by instantiating
`Over.stageP2_over_v1_kits` at the CLI Poll store kits when `¬ DecPkS0.SessMatchesPm sess y.g.msg`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Stage P2 Over-Path (`Path C`) Error & CPS Statement -/

private theorem p2Over_cliPollSpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKit A b F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKit A b F sid σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollKpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKit A b F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKit A b F kid sid kbk σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollPk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKit A b F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKit A b F pid σ).getEvs id ans = [] := rfl

private theorem p2Over_cliPollPk_opkOkEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKit A b F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

private theorem p2Over_cliPollPk_opkOkUpdate (A : RustAlloc) (b : BitVec 64) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKit A b F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

private theorem p2Over_cliPollSelf_kpEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKit A b F peer σ).kpEvs ans = [] := rfl

private theorem p2Over_cliPollSelf_regIdEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKit A b F peer σ).regIdEvs ans = [] := rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
