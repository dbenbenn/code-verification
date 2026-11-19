/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Drops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoop
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Varint

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

theorem vecU8_unpack_at (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs = (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs) := rfl

theorem vecU8At_unpack_any (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, sepConj_assoc]
  ac_rfl

theorem vecU8At_of_live_parts (A : RustAlloc) (v v8 v16 cap ptr : BitVec 64)
    (bs : List (BitVec 8))
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16)
    (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ⊢
      vecU8At A v cap ptr bs := by
  subst hv8; subst hv16
  rw [vecU8At_unpack_any A v cap ptr bs]
  exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

theorem vecU8At_unpack_pos_lr (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hc : cap ≠ 0#64) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  ac_rfl

theorem assemble_baseKeysName (filePtr wDot : BitVec 64) (id : BitVec 32)
    (hwDot : unpack64 wDot = utf8 ".base-ke") :
    ((filePtr ↦ₛ keyName id) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length) ↦₆₄ wDot) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length + 8#64) ↦₁₆ 0x7379#16)) =
    SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName id) := by
  rw [pointsTo64_eq_pointsToBytes, hwDot, pointsTo16_ys_eq_bytes]
  have h1 : (filePtr ↦ₛ keyName id) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length) ↦ₛ utf8 ".base-ke") =
      (filePtr ↦ₛ (keyName id ++ utf8 ".base-ke")) :=
    (pointsToBytes_append filePtr (keyName id) (utf8 ".base-ke")).symm
  rw [← sepConj_assoc, h1]
  have had : filePtr + BitVec.ofNat 64 (keyName id).length + 8#64 =
      filePtr + BitVec.ofNat 64 (keyName id ++ utf8 ".base-ke").length := by
    rw [List.length_append, utf8_dot_base_ke_length, BitVec.ofNat_add]; bv_omega
  rw [had, ← pointsToBytes_append, baseKeysName_eq_append]
  rfl

theorem subStack_merge_adj (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (R : SepProp) :
    memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
      (kpkSubMax decStk getStk putStk - k) ∗
      (stackAt (sp0 - 0xf0#64) k ∗ R) =
    stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

theorem subStack_merge_rev_adj (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (R : SepProp) :
    stackAt (sp0 - 0xf0#64) k ∗
      (memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - k) ∗ R) =
    stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

theorem subStack_merge_pool_mid (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (X Pool R : SepProp) :
    (X ∗ stackAt (sp0 - 0xf0#64) k ∗ Pool) ∗
      (memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - k) ∗ R) =
    X ∗ Pool ∗ stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

/-! ## Post-`last_resort.get` Continuation (`+372 ..`, `kpk_after_lr_get_174`) -/

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
