/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Stage P2 Pure and Internal Callee Instantiation

Constructs `StageP2PureCallees` and `StageP2PureCallees4K` over `tripleRatchetExterns C ctl abs`
from the verified internal callees and SPQR V1 `initialize_bob_session` proofs, with `TrapsOnly`
extern-table refinement lifts.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding
  bv_sub_add_lit' stackAt_split_top sepWPp_pure_mid
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PromoteMatchingSessionExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

end PromoteMatchingSessionExt

section KeyPairExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv16_setWidth_8
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv8_setWidth_8
  zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  clamp_lo_byte_norm clamp_lo_byte_norm'
  clamp_hi_byte_norm clamp_hi_byte_norm' clamp_hi_byte_norm'' clamp_hi_bfm_norm
  bv64_mask_low32_orr_zext32 bv64_mask_high32_orr_lsl32 bv64_mask_low16_orr_zext16

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_0 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 0 8 =
      u.extractLsb' 0 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_8 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 8 8 =
      u.extractLsb' 8 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_16 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 16 8 =
      u.extractLsb' 16 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_24 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 24 8 =
      u.extractLsb' 24 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_clamp_lo_byte_norm_64 (b0 : BitVec 8) :
    ((b0.zeroExtend 64) &&& 1065151889656#64).setWidth 8 = b0 &&& 0xf8#8 := by
  bv_slice

private theorem p2_cells_sub32_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem p2_stackAt_promote_state_split (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 4000 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 := by
  dsimp only [stackAt, allocHookStack]
  rw [show (4096 : Nat) = 4000 + (64 + 32) by decide,
    memRegion_split (sp - 4096#64) 4000 (64 + 32) (by decide),
    show sp - 4096#64 + 4000#64 = sp - 96#64 by bv_omega,
    memRegion_split (sp - 96#64) 64 32 (by decide),
    show sp - 96#64 + 64#64 = sp - 32#64 by bv_omega,
    ProofLib.memRegion_cells (sp - 96#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]

private theorem p2_stackAt_kemKeyPairFromPubPriv (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := ResponderStore.stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

end KeyPairExt

section InitBobErr4KExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
private theorem p2_initBob_stack_ext_split (sp : BitVec 64) :
    stackAt sp (768 + Initiator.pqxdhEntryStackExt) =
      memRegion (sp - 33536#64) (32768 - pqxdhEntryStack) ∗ stackAt sp (768 + pqxdhEntryStack) := by
  have h := p2_stackAt_split_of_le sp (768 + Initiator.pqxdhEntryStackExt) (768 + pqxdhEntryStack)
    (by decide) (by decide)
  have h1 : BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt) = 33536#64 := rfl
  have h2 : (768 + Initiator.pqxdhEntryStackExt) - (768 + pqxdhEntryStack) =
      32768 - pqxdhEntryStack := by
    dsimp only [Initiator.pqxdhEntryStackExt]; omega
  rw [h1, h2] at h
  exact h

private theorem p2_initBob_sub768_ext_split (sp : BitVec 64) :
    stackAt (sp - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp - 33536#64) (32768 - pqxdhEntryStack) ∗
        stackAt (sp - 768#64) pqxdhEntryStack := by
  have h := p2_stackAt_split_of_le (sp - 768#64) Initiator.pqxdhEntryStackExt pqxdhEntryStack
    (by decide) (by decide)
  have h1 : (sp - 768#64) - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt = sp - 33536#64 := by
    dsimp only [Initiator.pqxdhEntryStackExt]; bv_omega
  have h2 : Initiator.pqxdhEntryStackExt - pqxdhEntryStack = 32768 - pqxdhEntryStack := rfl
  rw [h1, h2] at h
  exact h

private theorem p2_initBobErrOwnedAt_merge (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    Kits.initBobErrOwnedAt A outPtr := by
  change Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    Kits.initBobErrOwnedAt A outPtr
  have hrearr :
      Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
            memRegion (outPtr + 56#64) 288))))))) =
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  unfold Kits.initBobErrOwnedAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem p2_initBobErrOwnedAt_to_initBobErrAt (A : RustAlloc) (outPtr : BitVec 64) :
    Kits.initBobErrOwnedAt A outPtr ∗ anyHeap ⊢ initBobErrAt outPtr ∗ anyHeap := by
  unfold Kits.initBobErrOwnedAt
  conv =>
    lhs
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  rw [sepConj_left_comm]
  refine Entails.pure_left fun herr => ?_
  have h1 :
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        (((outPtr + 8#64) ↦₆₄ errTag) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗
          (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
            (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
              (Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
                (memRegion (outPtr + 56#64) 288 ∗ anyHeap)))))))) =
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        ((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 288) ∗
      (anyHeap ∗ Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4) := by ac_rfl
  rw [h1]
  exact sepConj_mono (initBobErrAt_merge outPtr errTag w2 w3 w4 w5 w6 herr) (entails_anyHeap _)

end InitBobErr4KExt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

