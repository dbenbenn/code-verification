/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Open
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenDeserId

/-!
# CLI Poll Stage P2 V1 Instantiation

Instantiates `StageP2PathAQpanCliStmt` (`stageP2PathA_qpan_cli_ok`) and `StageP2PathAQpanExtAtB`
(`stageP2PathA_qpan_ext_of_kits`, `stageP2PathA_qpan_ext_of_hkdf_init`) on Path A (`opt = none`,
`DecPkOk₀`).
-/

public section

set_option autoImplicit false

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
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
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
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

private theorem cliPollSpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKit A b F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKit A b F sid σ).getEvs id ans = [] := rfl

private theorem cliPollKpk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKit A b F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKit A b F kid sid kbk σ).getEvs id ans = [] := rfl

private theorem cliPollPk_getEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKit A b F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKit A b F pid σ).getEvs id ans = [] := rfl

private theorem cliPollPk_opkOkEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKit A b F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

private theorem cliPollPk_opkOkUpdate (A : RustAlloc) (b : BitVec 64) (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKit A b F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

private theorem cliPollSelf_kpEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKit A b F peer σ).kpEvs ans = [] := rfl

private theorem cliPollSelf_regIdEvs {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKit A b F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKit A b F peer σ).regIdEvs ans = [] := rfl

private def pathAIkBSk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
  | .error _ => List.replicate 32 0

private def pathAIkBPk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
  | .error _ => List.replicate 32 0

private theorem pathAIkBSk_length (F : FsFiles) : (pathAIkBSk F).length = 32 := by
  dsimp only [pathAIkBSk]
  split
  · exact vecU8_length _
  · simp

private theorem pathAIkBPk_length (F : FsFiles) : (pathAIkBPk F).length = 32 := by
  dsimp only [pathAIkBPk]
  split
  · exact vecU8_length _
  · simp

private theorem pathAIkBSk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBSk F = E2E.vecU8 kp.privateKey.bytes := by
  dsimp only [pathAIkBSk]; rw [h]

private theorem pathAIkBPk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBPk F = E2E.vecU8 kp.identityKey.publicKey.bytes := by
  dsimp only [pathAIkBPk]; rw [h]

private theorem cliPollSelf_kpRel_sk_eq {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.privateKey.bytes.toList = bytesToBv8 (pathAIkBSk F) := by
  have hkpEq := cliPollSelf_kpRel_ok hrel
  dsimp only [pathAIkBSk]
  rw [hkpEq, bytesToBv8_vecU8]

private theorem cliPollSelf_kpRel_pk_eq {A : RustAlloc} {b : BitVec 64} {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKit A b F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (pathAIkBPk F) := by
  have hkpEq := cliPollSelf_kpRel_ok hrel
  dsimp only [pathAIkBPk]
  rw [hkpEq, bytesToBv8_vecU8]

private theorem stageP2V1CallStack4K_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack4K
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  dsimp only [stageP2V1CallStack4K]
  refine Nat.max_le.mpr
    ⟨(Nat.max_le.mp (stageP2CallStack4K_le_subStack b F0 peer spkId kpkId opkIdWord kbk B)).1, ?_⟩
  dsimp only [Initiator.pqxdhEntryStackExt, dpClosSubStack]
  omega

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
