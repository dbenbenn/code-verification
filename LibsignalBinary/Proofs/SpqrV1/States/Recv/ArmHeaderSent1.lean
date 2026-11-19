/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.headerSent` Arm, Part 1

Shared `RecvMemcpyOps` writeback helpers and the `msg.epoch > st.uc.epoch`,
`msg.epoch < st.uc.epoch`, and `msg.epoch = st.uc.epoch ∧ msg.payload ≠ .ct1 _` branches of
`.headerSent` (`0x55760`, `+780`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_4144_hs (sp : BitVec 64) : (sp - 4240#64) + 4144#64 = sp - 96#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem bv376_toNat_hs : (376#64 : BitVec 64).toNat = 376 := rfl

theorem Relocatable.of_pointsToBytes {n : Nat} (bs : List (BitVec 8)) (hlen : bs.length = n) :
    Relocatable n (fun a => a ↦ₛ bs) := by
  intro a; dsimp only
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  conv_lhs => rw [← sepConj_emp (a ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp]
  exact Entails.refl _

theorem epoch_cmp_ct1r_bne_1_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_bne_1_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = true := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem stackAt_statesRecvStackX_split_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19632 ∗ stackAt sp dropStackPoly64 :=
  stackAt_split_bottom sp dropStackPoly64 19632 (by decide)

theorem words63At_376_self_entails_memRegion_928 (selfA tag : BitVec 64) (w : Words63)
    (tailBytes : List (BitVec 8)) (hlen : tailBytes.length = 376) :
    (selfA ↦₆₄ tag) ∗ words63At (selfA + 8#64) w ∗
      ((selfA + 512#64) ↦ₛ tailBytes) ∗ memRegion (selfA + 888#64) 40 ⊢
      memRegion selfA chunkedStatesSize := by
  have h376 : ((selfA + 512#64) ↦ₛ tailBytes) ⊢ memRegion (selfA + 512#64) 376 := by
    rw [← hlen]
    exact ProofLib.pointsToBytes_entails_memRegion (selfA + 512#64) tailBytes
  have h880 : words63At (selfA + 8#64) w ∗ ((selfA + 512#64) ↦ₛ tailBytes) ⊢
      memRegion (selfA + 8#64) 880 :=
    Entails.trans (sepConj_mono_right h376)
      (words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega))
  refine Entails.trans (Entails.of_eq (show _ =
    (selfA ↦₆₄ tag) ∗ (words63At (selfA + 8#64) w ∗ ((selfA + 512#64) ↦ₛ tailBytes)) ∗
    memRegion (selfA + 888#64) 40 by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
    (self_880_40_entails_memRegion_928 selfA tag)

/-! ## 1. `.headerSent` (`0x55760`, `+780`): `msg.epoch > st.uc.epoch` -/

end CryptoVerification.SpqrV1.States.Recv
