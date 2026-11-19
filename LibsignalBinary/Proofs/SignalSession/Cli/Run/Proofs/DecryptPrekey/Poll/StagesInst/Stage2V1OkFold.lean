/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Poll Stage P2 V1 `+0x1778` Success-Exit Spatial Fold

Proves `p2OkPost_fold_pathA` (and `p2OkPost_fold_pathA_ext`), converting `p2OkPostAt` and
`pathAInnerFrame` at `+0x1778` into the Stage P3 precondition of `hok`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-- Fold `coroPtr + 0x298` packed 64-bit `Option<PreKeyId>` word into `coroOpkIdAtP4`. -/
theorem p2_coro_opk_slot_fold (fut : BitVec 64) (opkId? : Option (BitVec 32)) (opkWord : BitVec 32)
    (hopk : ∀ id : BitVec 32, opkId? = some id → opkWord = id) :
    ((fut + 0x298#64) ↦₆₄ ((opkOptTag32 opkId?).zeroExtend 64 ||| (opkWord.zeroExtend 64 <<< 32))) ⊢
      coroOpkIdAtP4 fut opkId? := by
  rw [ProofLib.pointsTo64_split32_at fut 0x298#64]
  simp only [BitVec.reduceAdd]
  cases opkId? with
  | none =>
    have hlo : (((0#32).zeroExtend 64 ||| (opkWord.zeroExtend 64 <<< 32)).truncate 32) = 0#32 := by
      bv_bits
    have hhi : (((0#32).zeroExtend 64 ||| (opkWord.zeroExtend 64 <<< 32)).extractLsb' 32 32) = opkWord := by
      bv_bits
    dsimp only [opkOptTag32, coroOpkIdAtP4]
    rw [hlo, hhi]
    exact Entails.sepExists_right opkWord (Entails.refl _)
  | some id =>
    rw [hopk id rfl]
    have hlo : (((1#32).zeroExtend 64 ||| (id.zeroExtend 64 <<< 32)).truncate 32) = 1#32 := by
      bv_bits
    have hhi : (((1#32).zeroExtend 64 ||| (id.zeroExtend 64 <<< 32)).extractLsb' 32 32) = id := by
      bv_bits
    dsimp only [opkOptTag32, coroOpkIdAtP4]
    rw [hlo, hhi]
    exact Entails.refl _

private theorem kpkId_shift_or_eq_append (kpkId : BitVec 32) :
    (kpkId.zeroExtend 64 <<< 32) ||| 1#64 = kpkId ++ 1#32 := by
  bv_bits

/-- Fold Stage P2 `+0x1778` coroutine frame into `stageP3CoroFrameAt` for arbitrary `opkSlot` and `coro2a0Slot`. -/
theorem p2_coro_ok_fold (fut msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64)
    (opkSlot coro2a0Slot : SepProp) :
    processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
    decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
    coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
    opkSlot ∗ coro2a0Slot ∗
    memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
    ((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (fut + 0x398#64) 96 ∗
    ((fut + 0x4f1#64) ↦₈ 0#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x391#64) 7 ∗
    memRegion (fut + 0x488#64) 8 ∗ memRegion (fut + 0x4b0#64) 65 ∗
    memRegion (fut + 0x4f3#64) 5 ∗
    p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6 ⊢
      stageP3CoroFrameAt fut msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr opkSlot coro2a0Slot := by
  unfold stageP3CoroFrameAt coroPostP2UnusedAt
  rw [coroCopyAt_eq_head3_tail11]
  have h4b0 : memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8) ⊢
      memRegion (fut + 0x4b0#64) 66 := by
    rw [memRegion_split (fut + 0x4b0#64) 65 1 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (ProofLib.pointsTo8_entails_memRegion _ _)
  have h250 : cells (fut + 0x250#64) 6 = memRegion (fut + 0x250#64) 48 :=
    (ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide)).symm
  have h398 : memRegion (fut + 0x398#64) 96 =
      memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x3a8#64) 80 := by
    rw [memRegion_split (fut + 0x398#64) 16 80 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4f8 : p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6 =
      memRegion (fut + 0x4f8#64) 736 :=
    (coro_scratch_736_split fut).symm
  rw [h250, h398]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
      memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x488#64) 8) ∗
    (((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
      processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt) ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    (memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8)) ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    ((p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6) ∗
      decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
      coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      memRegion (fut + 0x250#64) 48 ∗ memRegion (fut + 0x280#64) 24 ∗
      opkSlot ∗ coro2a0Slot ∗
      memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
      memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x2c1#64) 7 ∗
      memRegion (fut + 0x391#64) 7 ∗ memRegion (fut + 0x4f3#64) 5)
    by sep_frame) ?_
  rw [h4f8]
  refine Entails.trans (sepConj_mono (active10_3a8_488_fold _ _ _ _ _ _ _ _ _ _)
    (sepConj_mono (innerInit_200_fold _ _ _ _ _ _ _ _ _ _ _ _)
      (sepConj_mono (postTrust_64_32_fold _ _ _ _ _ _ _ _ _ _ _ _)
        (sepConj_mono h4b0
          (sepConj_mono (ProofLib.pointsTo8_entails_memRegion _ _)
            (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _))))))) ?_
  rw [coro_2c8_16_184_eq fut]
  sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
