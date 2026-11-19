/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpoch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `fnOff` Facts & Relative Address Bridges for `spqr::recv` Callees -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Split `memRegion (sp0 - 4992#64) 0x1320` (`4896`B) for `+312 .. +408`:
    - `32`B (`4` words at `sp0 - 4992#64 .. sp0 - 4960#64`),
    - `320`B (`memRegion (sp0 - 4960#64) 320` for `memcpy` destination),
    - `1584`B (`memRegion (sp0 - 4640#64) 1584`),
    - `352`B (`memRegion (sp0 - 3056#64) 352` for `decode_state` sret at `sp + 0x790`),
    - `608`B (`memRegion (sp0 - 2704#64) 608`),
    - `24`B (`3` words at `sp0 - 2096#64 .. sp0 - 2072#64` = `sp + 0xb50 .. sp + 0xb68`),
    - `1976`B (`memRegion (sp0 - 2072#64) 1976`). -/
theorem ownFrame_split_for_decode (sp0 : BitVec 64) :
    memRegion (sp0 - 4992#64) 0x1320 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
      ∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64,
        ((sp0 - 4992#64) ↦₆₄ d0) ∗ ((sp0 - 4984#64) ↦₆₄ d1) ∗
        ((sp0 - 4976#64) ↦₆₄ d2) ∗ ((sp0 - 4968#64) ↦₆₄ d3) ∗
        memRegion (sp0 - 4960#64) 320 ∗
        memRegion (sp0 - 4640#64) 1584 ∗
        memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
        memRegion (sp0 - 2072#64) 1976 := by
  have h1 : memRegion (sp0 - 4992#64) 0x1320 =
      memRegion (sp0 - 4992#64) 8 ∗ memRegion (sp0 - 4984#64) 8 ∗
      memRegion (sp0 - 4976#64) 8 ∗ memRegion (sp0 - 4968#64) 8 ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 352 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (0x1320 : Nat) = 8 + (8 + (8 + (8 + (320 + (1584 + (352 + (608 + (8 + (8 + (8 + 1976)))))))))) by decide,
        memRegion_split (sp0 - 4992#64) 8 _ (by decide), bv_sub_add_lit sp0 4992 8,
        memRegion_split (sp0 - 4984#64) 8 _ (by decide), bv_sub_add_lit sp0 4984 8,
        memRegion_split (sp0 - 4976#64) 8 _ (by decide), bv_sub_add_lit sp0 4976 8,
        memRegion_split (sp0 - 4968#64) 8 _ (by decide), bv_sub_add_lit sp0 4968 8,
        memRegion_split (sp0 - 4960#64) 320 _ (by decide), bv_sub_add_lit sp0 4960 320,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 352 _ (by decide), bv_sub_add_lit sp0 3056 352,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1,
      ProofLib.memRegion_eight (sp0 - 4992#64),
      ProofLib.memRegion_eight (sp0 - 4984#64),
      ProofLib.memRegion_eight (sp0 - 4976#64),
      ProofLib.memRegion_eight (sp0 - 4968#64),
      ProofLib.memRegion_eight (sp0 - 2096#64),
      ProofLib.memRegion_eight (sp0 - 2088#64),
      ProofLib.memRegion_eight (sp0 - 2080#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d2
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right d2 (Entails.sepExists_right d3
      (Entails.sepExists_right b0 (Entails.sepExists_right b1
        (Entails.sepExists_right b2 ?_))))))
  exact Entails.of_eq (by ac_rfl)

theorem ownFrame_join_4544_after_decode (sp0 w0 w1 w2 w3 b0 b1 b2 : BitVec 64)
    (bs320 : List (BitVec 8)) (hbs320 : bs320.length = 320) :
    memRegion (sp0 - 4640#64) 1584 ∗
      ((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3) ∗
      ((sp0 - 3024#64) ↦ₛ bs320) ∗
      memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
      memRegion (sp0 - 2072#64) 1976 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have h1 : memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 8 ∗ memRegion (sp0 - 3048#64) 8 ∗
      memRegion (sp0 - 3040#64) 8 ∗ memRegion (sp0 - 3032#64) 8 ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (4544 : Nat) = 1584 + (8 + (8 + (8 + (8 + (320 + (608 + (8 + (8 + (8 + 1976))))))))) by decide,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 8 _ (by decide), bv_sub_add_lit sp0 3056 8,
        memRegion_split (sp0 - 3048#64) 8 _ (by decide), bv_sub_add_lit sp0 3048 8,
        memRegion_split (sp0 - 3040#64) 8 _ (by decide), bv_sub_add_lit sp0 3040 8,
        memRegion_split (sp0 - 3032#64) 8 _ (by decide), bv_sub_add_lit sp0 3032 8,
        memRegion_split (sp0 - 3024#64) 320 _ (by decide), bv_sub_add_lit sp0 3024 320,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1, ← hbs320]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsToBytes_entails_memRegion _ _)
              (sepConj_mono_right
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))))))))

theorem ownFrame_join_4896_err_decode (sp0 d0 d1 d2 d3 w0 w1 w2 w3 b0 b1 b2 : BitVec 64) :
    ((sp0 - 4992#64) ↦₆₄ d0) ∗ ((sp0 - 4984#64) ↦₆₄ d1) ∗
      ((sp0 - 4976#64) ↦₆₄ d2) ∗ ((sp0 - 4968#64) ↦₆₄ d3) ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      ((sp0 - 3056#64) ↦₆₄ w0) ∗ ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗ ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ b0) ∗ ((sp0 - 2088#64) ↦₆₄ b1) ∗ ((sp0 - 2080#64) ↦₆₄ b2) ∗
      memRegion (sp0 - 2072#64) 1976 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  have h1 : memRegion (sp0 - 4992#64) 0x1320 =
      memRegion (sp0 - 4992#64) 8 ∗ memRegion (sp0 - 4984#64) 8 ∗
      memRegion (sp0 - 4976#64) 8 ∗ memRegion (sp0 - 4968#64) 8 ∗
      memRegion (sp0 - 4960#64) 320 ∗
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) 8 ∗ memRegion (sp0 - 3048#64) 8 ∗
      memRegion (sp0 - 3040#64) 8 ∗ memRegion (sp0 - 3032#64) 8 ∗
      memRegion (sp0 - 3024#64) 320 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) 8 ∗ memRegion (sp0 - 2088#64) 8 ∗ memRegion (sp0 - 2080#64) 8 ∗
      memRegion (sp0 - 2072#64) 1976 := by
    rw [show (0x1320 : Nat) = 8 + (8 + (8 + (8 + (320 + (1584 + (8 + (8 + (8 + (8 + (320 + (608 + (8 + (8 + (8 + 1976)))))))))))))) by decide,
        memRegion_split (sp0 - 4992#64) 8 _ (by decide), bv_sub_add_lit sp0 4992 8,
        memRegion_split (sp0 - 4984#64) 8 _ (by decide), bv_sub_add_lit sp0 4984 8,
        memRegion_split (sp0 - 4976#64) 8 _ (by decide), bv_sub_add_lit sp0 4976 8,
        memRegion_split (sp0 - 4968#64) 8 _ (by decide), bv_sub_add_lit sp0 4968 8,
        memRegion_split (sp0 - 4960#64) 320 _ (by decide), bv_sub_add_lit sp0 4960 320,
        memRegion_split (sp0 - 4640#64) 1584 _ (by decide), bv_sub_add_lit sp0 4640 1584,
        memRegion_split (sp0 - 3056#64) 8 _ (by decide), bv_sub_add_lit sp0 3056 8,
        memRegion_split (sp0 - 3048#64) 8 _ (by decide), bv_sub_add_lit sp0 3048 8,
        memRegion_split (sp0 - 3040#64) 8 _ (by decide), bv_sub_add_lit sp0 3040 8,
        memRegion_split (sp0 - 3032#64) 8 _ (by decide), bv_sub_add_lit sp0 3032 8,
        memRegion_split (sp0 - 3024#64) 320 _ (by decide), bv_sub_add_lit sp0 3024 320,
        memRegion_split (sp0 - 2704#64) 608 _ (by decide), bv_sub_add_lit sp0 2704 608,
        memRegion_split (sp0 - 2096#64) 8 _ (by decide), bv_sub_add_lit sp0 2096 8,
        memRegion_split (sp0 - 2088#64) 8 _ (by decide), bv_sub_add_lit sp0 2088 8,
        memRegion_split (sp0 - 2080#64) 8 1976 (by decide), bv_sub_add_lit sp0 2080 8]
  rw [h1]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono_right
                          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                              (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))))))))))))

end CryptoVerification.SpqrV1.Top.Recv

