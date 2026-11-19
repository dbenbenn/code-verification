/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Chain Resolution & `send_key` Dispatch

Basic-block steppers for chain resolution (`<Chain>::from_pb` and
`spqr::chain_from_version_negotiation`), optional `<Chain>::add_epoch`, and `<Chain>::send_key`
dispatch (`0x314d8..0x317fc`) in `spqr::send::<HookRng>`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem chainErrorAt_entails_words (a : BitVec 64) (err : Error) :
    chainErrorAt a err ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 56 := by
  unfold chainErrorAt
  apply Entails.sepExists_elim; intro q0
  apply Entails.sepExists_elim; intro w3
  apply Entails.pure_left; intro _
  have hq0 : ((a + 8#64) ↦₁₂₈ q0) ⊢
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
    rw [ProofLib.pointsTo128_split64]
    have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
    rw [h16]
    exact sepConj_mono (Entails.sepExists_right _ (Entails.refl _)) (Entails.sepExists_right _ (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hq0)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1
    (Entails.sepExists_right w2
      (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_24_words3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]

theorem words3_to_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _))

theorem words4_and_56_to_memRegion_88 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 32#64) 56 ⊢ memRegion a 88 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 80) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 72) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 64) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 56) (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))

@[expose] def vecU8HeapRest (A : RustAlloc) (pin : VecPin) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
    if pin.cap = 0 then emp
    else A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ bs) ∗
      memRegion (pin.ptr + BitVec.ofNat 64 bs.length) (pin.cap.toNat - bs.length)

theorem vecU8HeapRest_expose_cap_ne (A : RustAlloc) (pin : VecPin) (bs : List (BitVec 8)) :
    vecU8HeapRest A pin bs ⊢
      ⌜pin.cap ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ vecU8HeapRest A pin bs := by
  unfold vecU8HeapRest
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hne : pin.cap ≠ LibsignalTripleRatchetRepr.noneCap := by
    intro h; rw [h] at hlt; revert hlt; decide
  exact Entails.pure_right hne (Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _))

theorem versionNegotiationPBAt_eq_rest (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v =
      vecU8HeapRest A pin v.authKey ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
      ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
      ((a + 0x24#64) ↦₃₂ v.direction) ∗
      ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
      memRegion (a + 0x2c#64) 4 := by
  unfold ChainFromVersionNegotiation.versionNegotiationPBAt vecU8At vecHeader vecU8HeapRest
  ac_rfl

theorem versionNegotiationPBAt_expose_cap (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v ⊢
      ⌜pin.cap ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
      vecU8HeapRest A pin v.authKey ∗
      ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
      ((a + 0x24#64) ↦₃₂ v.direction) ∗
      ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
      memRegion (a + 0x2c#64) 4 := by
  rw [versionNegotiationPBAt_eq_rest A pin a v]
  refine Entails.trans (sepConj_mono_left (vecU8HeapRest_expose_cap_ne A pin v.authKey)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem versionNegotiationPBAt_unexpose_cap (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
      vecU8HeapRest A pin v.authKey ∗
      ChainFromVersionNegotiation.optChainParamsPBAt (a + 0x18#64) v.chainParams ∗
      ((a + 0x24#64) ↦₃₂ v.direction) ∗
      ((a + 0x28#64) ↦₃₂ v.minVersion) ∗
      memRegion (a + 0x2c#64) 4 ⊢
      ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v := by
  rw [versionNegotiationPBAt_eq_rest A pin a v]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
