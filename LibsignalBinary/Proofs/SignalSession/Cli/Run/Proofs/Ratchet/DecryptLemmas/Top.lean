/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.EntryExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.ModelDet
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stack
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Fs

/-!
# Stack Bound and Ghost Adapter for `decrypt_signal`

Proves `wsStackV_le_cliDecryptSignalNeed` and defines `toDecryptGhost` for
`signal_session_ratchet::decrypt_signal`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Stack budget bound showing `wsStackV` for `decSessKit` and `decIdKit` fits within `decNeedAux B`. -/
theorem wsStackV_le_cliDecryptSignalNeed (img : Unit) (F0 : FsFiles) (peer : AddrGhost)
    (B : RunBudgets) :
    wsStackV (decSessKit img F0 peer B) (decIdKit img F0 peer B) ≤ decNeedAux B := by
  have hk1 : (decSessKit img F0 peer B).loadShimStack = SessKit.loadShimNeed := rfl
  have hk2 : (decSessKit img F0 peer B).loadPollStack = SessKit.loadPollNeed B.readFile := rfl
  have hk3 : (decSessKit img F0 peer B).storeShimStack = SessKit.storeShimNeed := rfl
  have hk4 : (decSessKit img F0 peer B).storePollStack = SessKit.storePollNeedX := rfl
  have hi1 : (decIdKit img F0 peer B).trustShimStack = IdKit.trustShimNeed := rfl
  have hi2 : (decIdKit img F0 peer B).trustPollStack = IdKit.trustPollNeed B.readFile := rfl
  have hi3 : (decIdKit img F0 peer B).saveShimStack = IdKit.saveShimNeed := rfl
  have hi4 : (decIdKit img F0 peer B).savePollStack = IdKit.savePollNeed B.readFile := rfl
  have h1 : CryptoVerification.LibsignalTripleRatchet.doReserveStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.doReserveStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h2 : CryptoVerification.LibsignalTripleRatchet.finishGrowStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.finishGrowStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h3 : CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h4 : Proofs.libsignal.Hooks2.serializeStackX ≤ 262144 := by
    norm_num [Proofs.libsignal.Hooks2.serializeStackX,
      CryptoVerification.LibsignalTripleRatchet.doReserveStackX,
      CryptoVerification.LibsignalTripleRatchet.finishGrowStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h5 : E2E.Record.recDeserializeStack ≤ 262144 := by
    norm_num [E2E.Record.recDeserializeStack,
      CryptoVerification.LibsignalTripleRatchet.smallRootStack,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h6 : extHookStack ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have hpath : RunSkeleton.pathNeed ≤ 66000 := by
    dsimp only [RunSkeleton.pathNeed]
    have hm : max doReserveStackX extHookStack ≤ 65536 := Nat.max_le.mpr ⟨h1, h6⟩
    omega
  have hdget : RunBudgets.dirGetNeed ⟨B.readFile⟩ ≤ 66200 + B.readFile := by
    dsimp only [RunBudgets.dirGetNeed]
    have hm1 : max RunSkeleton.pathNeed B.readFile ≤ 66000 + B.readFile :=
      Nat.max_le.mpr ⟨Nat.le_trans hpath (Nat.le_add_right _ _), Nat.le_add_left _ _⟩
    have hm2 : max (max RunSkeleton.pathNeed B.readFile) extHookStack ≤ 66000 + B.readFile :=
      Nat.max_le.mpr ⟨hm1, Nat.le_trans h6 (by omega)⟩
    omega
  have hdec : SessKit.decNeed ≤ 67000 := by
    dsimp only [SessKit.decNeed]; omega
  have haddr : SessKit.addrTextNeed ≤ 68000 := by
    dsimp only [SessKit.addrTextNeed]
    have hm : max (max doReserveStackX extHookStack) SessKit.decNeed ≤ 67000 :=
      Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by omega, by omega⟩, hdec⟩
    omega
  have hgrowS : SessKit.growOneDirNeed ≤ 66000 := by
    dsimp only [SessKit.growOneDirNeed]; omega
  have hdput : SessKit.dirPutNeed ≤ 67000 := by
    dsimp only [SessKit.dirPutNeed]
    have hm : max SessKit.growOneDirNeed extHookStack ≤ 66000 :=
      Nat.max_le.mpr ⟨hgrowS, by omega⟩
    omega
  have hgrowI : IdKit.growOneDirNeed ≤ 66000 := by
    dsimp only [IdKit.growOneDirNeed]; omega
  have hdputS : IdKit.dirPutStrNeed ≤ 67000 := by
    dsimp only [IdKit.dirPutStrNeed]
    have hm : max IdKit.growOneDirNeed extHookStack ≤ 66000 :=
      Nat.max_le.mpr ⟨hgrowI, by omega⟩
    omega
  have hls : SessKit.loadShimNeed ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.loadShimNeed]; omega
  have hlp : SessKit.loadPollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.loadPollNeed]
    have hm1 : max SessKit.addrTextNeed (RunBudgets.dirGetNeed ⟨B.readFile⟩) ≤ 68000 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have hm2 : max E2E.Record.recDeserializeStack extHookStack ≤ 262144 :=
      Nat.max_le.mpr ⟨h5, by omega⟩
    have hm3 : max (max SessKit.addrTextNeed (RunBudgets.dirGetNeed ⟨B.readFile⟩))
        (max E2E.Record.recDeserializeStack extHookStack) ≤ 262144 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  have hss : SessKit.storeShimNeed ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.storeShimNeed]; omega
  have hsp : SessKit.storePollNeedX ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.storePollNeedX]
    have hm1 : max SessKit.addrTextNeed Proofs.libsignal.Hooks2.serializeStackX ≤ 262144 :=
      Nat.max_le.mpr ⟨by omega, h4⟩
    have hm2 : max SessKit.dirPutNeed extHookStack ≤ 67000 :=
      Nat.max_le.mpr ⟨hdput, by omega⟩
    have hm3 : max (max SessKit.addrTextNeed Proofs.libsignal.Hooks2.serializeStackX)
        (max SessKit.dirPutNeed extHookStack) ≤ 262144 :=
      Nat.max_le.mpr ⟨hm1, by omega⟩
    omega
  have hts : IdKit.trustShimNeed ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.trustShimNeed]; omega
  have htp : IdKit.trustPollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.trustPollNeed]
    have hm1 : max (RunBudgets.dirGetNeed ⟨B.readFile⟩) 0x60 ≤ 66200 + B.readFile :=
      Nat.max_le.mpr ⟨hdget, by omega⟩
    have hm2 : max 64 extHookStack ≤ 65536 :=
      Nat.max_le.mpr ⟨by omega, h6⟩
    have hm3 : max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) 0x60) (max 64 extHookStack) ≤
        66200 + B.readFile :=
      Nat.max_le.mpr ⟨hm1, by omega⟩
    omega
  have his : IdKit.saveShimNeed ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.saveShimNeed]; omega
  have hip : IdKit.savePollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.savePollNeed]
    have hm1 : max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed ≤ 67000 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have hm2 : max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed) (max 0x60 64) ≤
        67000 + B.readFile :=
      Nat.max_le.mpr ⟨hm1, by omega⟩
    have hm3 : max publicKeySerializeStackX extHookStack ≤ 65536 :=
      Nat.max_le.mpr ⟨h3, h6⟩
    have hm4 : max (max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed) (max 0x60 64))
        (max publicKeySerializeStackX extHookStack) ≤ 67000 + B.readFile :=
      Nat.max_le.mpr ⟨hm2, by omega⟩
    omega
  have hwsc : wsCalleeStack ≤ 1000000 + B.readFile := by
    have he : wsCalleeStack ≤ 524288 := by
      norm_num [wsCalleeStack, wsStack, wsFrame, entryStack]
    omega
  unfold wsStackV wsCalleeStackV decNeedAux
  rw [hk1, hk2, hk3, hk4, hi1, hi2, hi3, hi4]
  have hmax : max wsCalleeStack
      (max (max (max SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile))
                (max SessKit.storeShimNeed SessKit.storePollNeedX))
           (max (max IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile))
                (max IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)))) ≤ 1000000 + B.readFile :=
    Nat.max_le.mpr ⟨hwsc, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hls, hlp⟩,
      Nat.max_le.mpr ⟨hss, hsp⟩⟩, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hts, htp⟩,
      Nat.max_le.mpr ⟨his, hip⟩⟩⟩⟩
  have hwf : wsFrame = 0xee0 := rfl
  rw [hwf]
  omega

@[expose] def toDecryptGhost (x : DecSigGhost) : DecryptGhost where
  msgG := x.msgG
  msgA := x.msgA
  msg := x.msg
  rem := x.peer
  remA := x.peerA
  loc := x.me
  locA := x.meA
  ret := x.ret
  cur := x.coinsP
  rest := x.coins

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
