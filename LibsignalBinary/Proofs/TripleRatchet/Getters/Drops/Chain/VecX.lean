/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.X
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# `AllocContractsX` Verification of `drop_glue<Vec<Chain>>`

Proves the `extHookStack` contract `dropVecChainSpecX` for
`core::ptr::drop_glue::<alloc::vec::Vec<...::Chain>>` under `AllocContractsX`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

private structure VecHdrSnap where
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64

private def VecHdrLayout : ProofLib.Sep.StructLayout VecHdrSnap where
  totalSz := 24
  fields := [.u64 0 (·.cap), .u64 8 (·.ptr), .u64 16 (·.len)]

private theorem vecHdr_reclaim_24 (v cap ptr : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ⊢ memRegion v 24 := by
  rw [memRegion_eight (v + 16#64), sepExists_sepConj_right, sepExists_sepConj_right]
  exact Entails.sepExists_elim fun len => Entails.trans (by
    simp (config := { decide := true }) only [VecHdrLayout, ProofLib.Sep.StructLayout.own,
      ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
      ProofLib.Sep.StructField.u64, ProofLib.Sep.StructField.field64,
      ProofLib.Sep.fieldAddr, ↓reduceIte]
    bi_entail) (VecHdrLayout.struct_to_memRegion v ⟨cap, ptr, len⟩)

@[reducible]
private def vecPinDeallocX (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗ A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

@[reducible]
private def ckDeallocX (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

private theorem vecU8At_entails_pin_deallocX (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDeallocX
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases h0 : pin.cap = 0
  · simp only [h0, ↓reduceIte]; exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < pin.cap.toNat :=
      Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
    exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)

private theorem vecGhostAt_entails_pin_deallocX (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_deallocX A a ⟨g.cap, g.ptr⟩ g.bytes

private theorem optChainKeyAt_entails_deallocX (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        ckDeallocX A cap ptr := by
  unfold ckDeallocX
  cases ck with
  | none =>
    unfold optChainKeyAt
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    refine Entails.trans (by sep_interval :
      (a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 24 ⊢
        (a ↦₆₄ optChainKeyNone) ∗ (∃∗ ptr : BitVec 64, (a + 8#64) ↦₆₄ ptr) ∗
        memRegion (a + 16#64) 16) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right optChainKeyNone (Entails.sepExists_right ptr ?_)
    simp only [hslt, ↓reduceIte, sepConj_emp]
    bi_entail
  | some c =>
    unfold optChainKeyAt
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : pin.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        have hpos : 0 < pin.cap.toNat :=
          Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
        exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    have h16 : (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
        ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢ memRegion (a + 16#64) 16 := by
      sep_interval
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16)))
    bi_entail

private theorem messageKeyAt_entails_deallocX (A : RustAlloc) (cur : BitVec 64)
    (pin : MessageKeyGhost) (mk : MessageKeyGenerator) :
    messageKeyAt A (pin, mk) cur ⊢
      mkHeadersAt cur pin ∗
      vecPinDeallocX A pin.cipher ∗ vecPinDeallocX A pin.mac ∗
      vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed := by
  unfold messageKeyAt mkHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecU8At_entails_pin_deallocX A cur pin.cipher []
  have h2 := vecU8At_entails_pin_deallocX A (cur + 24#64) pin.mac []
  have h3 := vecU8At_entails_pin_deallocX A (cur + 48#64) pin.iv []
  have h4 := vecU8At_entails_pin_deallocX A (cur + 72#64) pin.seed mk.seed
  have h5 : ((cur + 96#64) ↦₃₂ mk.counter) ∗ memRegion (cur + 100#64) 4 ⊢
      memRegion (cur + 96#64) 8 := by sep_interval
  have ha1 : (cur + 24#64) + 8#64 = cur + 32#64 := by bv_omega
  have ha2 : (cur + 24#64) + 16#64 = cur + 40#64 := by bv_omega
  have hb1 : (cur + 48#64) + 8#64 = cur + 56#64 := by bv_omega
  have hb2 : (cur + 48#64) + 16#64 = cur + 64#64 := by bv_omega
  have hc1 : (cur + 72#64) + 8#64 = cur + 80#64 := by bv_omega
  have hc2 : (cur + 72#64) + 16#64 = cur + 88#64 := by bv_omega
  rw [ha1, ha2] at h2; rw [hb1, hb2] at h3; rw [hc1, hc2] at h4
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 h5)))) ?_
  bi_entail

private theorem protoChainAt_entails_deallocX (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    protoChainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold protoChainAt chainOuterHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecGhostAt_entails_pin_deallocX A g.srk a
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_deallocX A g.ck c.chainKey (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2; rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  bi_entail

private theorem chainAt_entails_deallocX (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    chainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) :=
  Entails.trans (chainAt_entails_protoChainAt A (g, c) a) (protoChainAt_entails_deallocX A a g c)

private theorem stack_restore_48_vecChainX (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropVecChainStackX := by
  simp only [stackAt, dropVecChainStackX, dropVecMessageKeyStackX, extHookStack,
    Nat.reducePow, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  sep_interval

private theorem cap0_weaken_48_vecChainX (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  refine Entails.trans ?_
    (sepConj_mono (vecHdr_reclaim_24 v cap ptr)
      (sepConj_mono_right (stack_restore_48_vecChainX sp fp lr x22 x21 x20 x19)))
  bi_entail

private theorem tail_dealloc_vecChain_pre_weakenX (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion v 24 ∗ memRegion (sp - 16480#64) 96) := by
  have h1 := vecHdr_reclaim_24 v cap ptr
  have h2 : stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      stackAt sp extHookStack ∗ memRegion (sp - 16480#64) 96 := by
    simp only [stackAt, dropVecMessageKeyStackX, extHookStack,
      Nat.reducePow, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    sep_interval
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_right (P := Pool ∗ Live) (sepConj_mono h1 h2)) (by bi_entail))
  bi_entail

private theorem vecChain_tail_dealloc_postX (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ memRegion v 24 ∗ memRegion (sp - 16480#64) 96 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  have hs : stackAt sp extHookStack ∗ memRegion (sp - 16480#64) 96 ⊢ stackAt sp dropVecChainStackX := by
    simp only [stackAt, dropVecChainStackX, dropVecMessageKeyStackX, extHookStack,
      Nat.reducePow, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    sep_interval
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hs))
  bi_entail

end CryptoVerification.LibsignalTripleRatchet.Getters
