/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import ProofLib.RegChain
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Budget-Threaded Segment S3 (`DhStep`) Composition & Seam Theorems

Composes `DhStepBudgetCore` with `DhCommitMainBudget` to prove total-correctness (`dhStep_placed_ok`,
`dhStep_x_placed_ok`) and seam-level (`s3_placed_ok`, `s3_placed_okT`, `s3_x_placed_ok`, and block
`130` / `433` specializations) Segment S3 contracts (`+0x500 → +0x3e4 / +0x30c`) over
`RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open Arm64 ProofLib
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto KeyPair Mut PrivateKey PublicKey RatchetState ReceiverChain RootKey
  SenderChain SessionState TripleRatchet rootCreateChain
)
open CryptoVerification (
  LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
)
open CryptoVerification.RustHeap (vecAt vecU8At)
open CryptoVerification.LibsignalSessionRepr (
  chainAt chainKeyBytes length_keyToBytes32 msgTypeByte optSenderChainBytes ratchetAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws protocolAddressAt sessionStateAt signalMessageAt tapeAfter utf8
  uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  CreateChainGhost SpqrModel TrGhost TryDecryptGhost calculateAgreement createChainResultAt
  createChainStack createChainStackX logOff rootStack trAt
)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack dropChainStackX)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPC_434 blkPl_131 blkPl_434
  speBodyAt tryDecryptCommonHeap tryDecryptMidMetaPlaced
  tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  clampScalar_keyPair_generate decryptDraws_of_cc1_err decryptDraws_of_cc1_ok
  decryptDraws_of_senderChain_none dhRatchetStep_none dhRatchetStep_some_err1
  dhRatchetStep_some_err2 dhRatchetStep_some_ok fold_1d8_after_cc2_err fold_390_3b0_to_memRegion
  fold_after_cc2_ok fold_sp_20_after_cc2_err optSenderChainBytes_some_split
  pointsTo64_zero_32 pointsTo_32_as_four_64 rk_ne_zero signalMessageAt_senderRatchetKey
  signalMessageRestAt split_140_for_cc1 stackAt_subStack_createChain
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd (spqrNoPanic)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  chainKeyToPbSpec chainKeyToPbSpecX derivePublicKeyBytesBudgetSpec
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
  publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (growOneSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpec dropChainSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  CreateChainEnv createChainEvents createChainSpec createChainSpecWithStack createChainSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced
  S3SeamPlaced S3SeamXPlaced tryDecryptOnPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (
  S3SeamTightPlaced S3SeamTightXPlaced tryDecryptOnPanicTight
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (
  DhCommitBlockVmWp dhCommitBlockVmWp_159 dhCommitBlockVmWp_549 s3CommitDefaultEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudget (
  DhCommitStatePlaced S3CommitSeamPlaced S3CommitSeamXPlaced
  dhCommit_placed_ok dhCommit_x_placed_ok
  s3_commit_159_placed_ok s3_commit_549_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp (
  DhStepBlockVmWp dhStepBlockVmWp_159 dhStepBlockVmWp_549
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetSteps (
  lsStaticDropSym rngFillAtBudgetSpec zeroizeSecretBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetAux (dhStep_cc1_err_branch_vm_placed dhStep_cc1_ok_branch_vm_placed dhStep_cc2_err_branch_vm_placed dhStep_cc2_ok_branch_vm_placed dhStep_missing_sender_chain_vm_placed)

open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (DhStepAfterRecvChainStatePlaced createChainEnv_eq_dhStepPairEvents dhStepPairEvents dhStep_recv_create_chain_withStack_placed fitsEnv_cc1_of_s3EnvOf onPanicTightBudget_of_spqrNoPanic s3DefaultEnv s3EnvOf stackAt_subStack_createChainX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 3. Total-Correctness `dhStep` Composition & Seam Theorems (`S3Seam*Placed`) -/

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudget
