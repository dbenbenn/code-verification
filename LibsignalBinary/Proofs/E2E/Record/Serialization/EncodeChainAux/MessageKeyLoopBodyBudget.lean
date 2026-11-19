/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBody -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudgetAux
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField

/-!
# Budget-threaded per-element `MessageKey` loop body (`+0x2a8..+0x29c`)

Budget-threaded `[LibsignalPlacement]` proofs for the per-element `MessageKey` loop body of
`encode::<Chain, Vec<u8>>` (block `12`).
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded
  lsMemcpySym lsρ blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (MessageKeyGhost messageKeyAt)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf sepWPp_extract_vecU8Buf_le
  cap_beq_len_false bv_len_add_one vecU8Buf_eq_open_one vecU8Buf_snoc_eq cap_eq_ofNat_len
  encodeVarint_length_bounds
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
)
open CryptoVerification.E2E.Record (uint32Field lenField encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  encChainSubStack vecU8At_eq_cells_buf
  bv_len_add_slice spare_ult_iff ule_of_ult_false ule_false_of_ult_true bv_len_beq_zero_false
  vecReadRest vecU8Buf_eq_open_bytes sepWPp_congr_pre
  MkLoopRegs lenField4_encMessageKey_eq lenField4_encMessageKey_len_parts
  mkUnusedAt messageKeyAt_eq_cells sepWPp_extract_messageKey_seed_ne_nil
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveEvents doReserveSpec framelessMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (msgKeyLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm step_encChain_encodeVarint_placed step_encChain_reserve1_placed
  step_encChain_reserveSlice_placed step_encChain_memcpy_placed
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyFieldBudgetAux (
  encRawSegEnv_doReserve encRawSegEnv_of_encodeVarintEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  ofNat_countLeadingZeros_64
  ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  truncate32_zext64_lsr6
  hwVarintLen_eq_encodeVarint_length
  hwVarintLen_bvShift_eq_encodeVarint_length
  hwVarintLen_w32_eq_encodeVarint_length
  hwVarintLen_w32_natShift_eq_encodeVarint_length

export MessageKeyLoopBodyBudgetAux (
  step_encChain_msgKeyLen_placed
  step_encChain_mk_tag_len_placed
  step_encChain_mk_counter_placed
)

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudget
