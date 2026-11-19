/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Head (`Chain3MkHeadStmt`)

Verifies step 4a (`+0x0a8 → +0x244`) of the tag-4 (`message_keys`) path: outer key `0x22` decode,
default `MessageKey` initialization in the 104 scratch bytes at `sp0 - 0xe8`, body-length varint `L`
decode, and inner limit `x25 = |rest|`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter DecodeVarintSlowGhost)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg Arm64.calleeSavedVRegs_writeVReg128_ite Arm64.isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Small facts -/

set_option maxHeartbeats 400000 in
theorem c3hd_sp_sub_240_aligned {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 :=
  sp_sub_240_aligned_receiverChains h

set_option maxHeartbeats 400000 in
theorem c3hd_spAligned {s : State} {sp0 : BitVec 64} (hsp : s.sp = sp0 - 0xf0#64)
    (halign : sp0 &&& 15#64 = 0#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  exact c3hd_sp_sub_240_aligned halign

set_option maxHeartbeats 400000 in
theorem c3hd_pointsTo_hdr_combine (ptr : BitVec 64) (b : BitVec 8) :
    (ptr ↦ₛ [0x22#8]) ∗ ((ptr + 1#64) ↦ₛ [b]) = (ptr ↦ₛ [0x22#8, b]) := by
  have h : ([0x22#8, b] : List (BitVec 8)) = [0x22#8] ++ [b] := rfl
  rw [h, pointsToBytes_append]; rfl

set_option maxHeartbeats 400000 in
theorem c3hd_ptr_add_one_add_one (ptr : BitVec 64) :
    ptr + 1#64 + 1#64 = ptr + 2#64 := by
  simp only [BitVec.add_assoc]; rfl

/-! ## 2. Callee step (`decode_varint [local#3]`) -/

set_option maxHeartbeats 400000 in
/-- The 104 scratch bytes `[sp0 - 232, sp0 - 128)` as 80 bytes, two words, a 32-bit word and 4 bytes. -/
theorem memRegion104_c3hd_split (sp0 : BitVec 64) :
    memRegion (sp0 - 232#64) 104 =
      memRegion (sp0 - 232#64) 80 ∗ (∃∗ c10 : BitVec 64, (sp0 - 152#64) ↦₆₄ c10) ∗
      (∃∗ c11 : BitVec 64, (sp0 - 144#64) ↦₆₄ c11) ∗ (∃∗ wc : BitVec 32, (sp0 - 136#64) ↦₃₂ wc) ∗
      memRegion (sp0 - 132#64) 4 := by
  have s80 := memRegion_split (sp0 - 232#64) 80 24 (by decide)
  have e80 : (sp0 - 232#64) + BitVec.ofNat 64 80 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e80] at s80
  have h24 := memRegion24_split_ck_seedChain (sp0 - 232#64)
  have eb0 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb1 : (sp0 - 232#64) + 0x58#64 = sp0 - 144#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb2 : (sp0 - 232#64) + 0x60#64 = sp0 - 136#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb3 : (sp0 - 232#64) + 0x64#64 = sp0 - 132#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [eb0, eb1, eb2, eb3] at h24; rw [s80, h24]

private theorem c3hd_emptyVec_entails_vecU8 (A : RustAlloc) (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A addr [] := by
  rw [emptyVec_eq_vecU8At_seedChain]
  change vecU8At A addr 0#64 1#64 [] ⊢ vecU8 A addr []
  unfold vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (Entails.refl _))

set_option maxHeartbeats 400000 in
/-- The default `MessageKey` the stores `+0x134..+0x150` write: three empty `Vec<u8>`s (`cap 0`,
`ptr 1`, `len 0`) and the seed `Vec<u8>` at `sp0 - 160` kept as `vecU8At … 0 1 []` for
`bytes::merge`. -/
theorem c3hd_default_of_cells {A : RustAlloc} (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
      ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
      ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64) ⊢
    vecU8 A (sp0 - 232#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
      vecU8At A (sp0 - 160#64) 0#64 1#64 [] := by
  have v0 := c3hd_emptyVec_entails_vecU8 A (sp0 - 232#64)
  have v1 := c3hd_emptyVec_entails_vecU8 A (sp0 - 208#64)
  have v2 := c3hd_emptyVec_entails_vecU8 A (sp0 - 184#64)
  have v3 : ((sp0 - 160#64) ↦₆₄ 0#64) ∗ (((sp0 - 160#64) + 8#64) ↦₆₄ 1#64) ∗
      (((sp0 - 160#64) + 16#64) ↦₆₄ 0#64) = vecU8At A (sp0 - 160#64) 0#64 1#64 [] :=
    emptyVec_eq_vecU8At_seedChain (sp0 - 160#64)
  have e0a : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 232#64) + 16#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 208#64) + 8#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 208#64) + 16#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 184#64) + 8#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 184#64) + 16#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 160#64) + 8#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 160#64) + 16#64 = sp0 - 144#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
        ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
        ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
        ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64) =
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 1#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 1#64) ∗ ((sp0 - 144#64) ↦₆₄ 0#64)))) := by
    ac_rfl
  rw [hgrp, v3]; exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 (Entails.refl _)))

/-! ## 4. Straight-line segments -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
