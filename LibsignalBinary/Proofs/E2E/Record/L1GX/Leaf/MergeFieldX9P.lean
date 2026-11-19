/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.L1GX.Frame
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Helpers
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.PendingId
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.PendingSpkNone
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF9PAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.CodeLayout

/-!
# `SessionStructure::merge_field` on tag 9 (`pending_pre_key`)

Re-exports `mergeFieldX9P_ok` for `<SessionStructure as prost::Message>::merge_field` (`0x581c`)
on PQXDH `pending_pre_key` fields (`GenFieldX.pendingId` and `GenFieldX.pendingSpk`).
-/

public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX9P

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux
open CryptoVerification.E2E.Record.Serialization (allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

private theorem final_post_entails_spk_some_x9p (ss cap' ptr' : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            prostSSRest_x9p A0 ss v ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗
            (ptr + 1#64) ↦₈ 8#8 ∗
            (sp0 - 80#64) ↦₆₄ r29 ∗
            (sp0 - 72#64) ↦₆₄ r30 ∗
            (sp0 - 64#64) ↦₆₄ r25 ∗
            (sp0 - 56#64) ↦₆₄ w118 ∗
            (sp0 - 48#64) ↦₆₄ r24 ∗
            (sp0 - 40#64) ↦₆₄ r23 ∗
            (sp0 - 32#64) ↦₆₄ r22 ∗
            (sp0 - 24#64) ↦₆₄ r21 ∗
            (sp0 - 16#64) ↦₆₄ r20 ∗
            (sp0 - 8#64) ↦₆₄ r19 ∗
            memRegion (sp0 - 240#64) 160)))) ⊢
    prostSSGXAt A0 ss (SSGX.apply ⟨v, ExtraG.empty⟩ (.pendingSpk (some i) k spk)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSRest_x9p A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗
      (sp0 - 72#64) ↦₆₄ r30 ∗
      (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗
      (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗
      (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14))
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono (prostSSGXAt_post_fold_spk_some_x9p A0 ss cap' ptr' v i k spk)
    (sepConj_mono_right (sepConj_mono_right
      (stackAt_mergeField_fold_mf14 sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19)))

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX9P
