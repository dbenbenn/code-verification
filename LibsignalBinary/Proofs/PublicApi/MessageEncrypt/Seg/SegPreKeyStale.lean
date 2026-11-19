/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness -- proof-setup: allow-public-import
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `segPreKey` Stale Pre-Key Error Path (`segPreKey_stale_ok`)

When `expiry.lt x.now = true` at `+0x6fc`, clones `x.rem.name`, stages
`SessionNotFound(x.rem, "message_encrypt")`, and exits via `tailDropRecord_ok` at `+0x46c`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `SystemTime.lt` Branch Normalization (`+0x6fc..+0x71c`) -/

@[simp, arm64_norm, wp_norm]
theorem systemTime_lt_w9_eq (a b : SystemTime) :
    (if (a.tvSec == b.tvSec) = true then
       if b.tvNsec.ule a.tvNsec = true then 0#64 else 1#64
     else if b.tvSec.sle a.tvSec = true then 0#64 else 1#64) =
    if a.lt b then 1#64 else 0#64 := by
  rw [← systemTime_lt_cond_eq a b]
  by_cases hsec : a.tvSec = b.tvSec
  · simp only [hsec, beq_self_eq_true, ↓reduceIte]
    by_cases hns : a.tvNsec.ult b.tvNsec = true
    · have hule : b.tvNsec.ule a.tvNsec = false := by
        simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hns ⊢
        omega
      simp [hns, hule]
    · have hns' : a.tvNsec.ult b.tvNsec = false := Bool.eq_false_iff.mpr hns
      have hule : b.tvNsec.ule a.tvNsec = true := by
        simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hns' ⊢
        omega
      simp [hns', hule]
  · have hbeq : (a.tvSec == b.tvSec) = false := beq_false_of_ne hsec
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    by_cases hslt : a.tvSec.slt b.tvSec = true
    · have hsle : b.tvSec.sle a.tvSec = false := by
        simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at hslt ⊢
        omega
      simp [hslt, hsle]
    · have hslt' : a.tvSec.slt b.tvSec = false := Bool.eq_false_iff.mpr hslt
      have hsle : b.tvSec.sle a.tvSec = true := by
        simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at hslt' ⊢
        omega
      simp [hslt', hsle]

/-! ## Separation-Logic Helpers for the Stale Branch -/

theorem takenRecord_sessionRecordAt_pack_exact (A : RustAlloc) (sp : BitVec 64)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ⊢
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) := by
  unfold sessionRecordAt takenRecord
  dsimp only
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128]
  exact Entails.refl _

theorem cmSlotAt_none_pack (A : RustAlloc) (sp : BitVec 64) (k : IdentityKey) :
    (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      ((sp + 0x468#64) ↦₈ 0#8)) ⊢
    cmSlotAt A sp none := by
  unfold cmSlotAt
  have h1 := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
  rw [k.publicKey.bytes.toList_length] at h1
  have h2 : ((sp + 0x468#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x468#64) 1 :=
    pointsTo8_entails_memRegion _ _
  rw [mr_cut_add sp 0x350 0x20 0xf9 (by decide),
      mr_cut_add sp 0x370 0xf8 1 (by decide)]
  exact sepConj_mono h1 (sepConj_mono_right h2)

theorem preKeyScratch_stale_weaken (sp kyLen : BitVec 64) (spk kyIdVal pkVal : BitVec 32)
    (kyber : Option PendingKyberPreKey) :
    preKeyScratch sp kyLen spk kyIdVal pkVal kyber ⊢
      memRegion sp 0x48 ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) := by
  unfold preKeyScratch
  rw [memRegion_split sp 0x18 0x30 (by decide),
      mr_cut_add sp 0x18 8 0x28 (by decide),
      mr_cut_add sp 0x20 4 0x24 (by decide),
      mr_cut_add sp 0x24 4 0x20 (by decide),
      mr_cut_add sp 0x28 8 0x18 (by decide),
      mr_cut_add sp 0x30 4 0x14 (by decide),
      mr_cut_add sp 0x34 4 0x10 (by decide),
      mr_cut_add sp 0x38 8 8 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))))

theorem curScratch_stale_pack (sp : BitVec 64) :
    (memRegion sp 0x48 ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ⊢
    curScratch sp := by
  unfold curScratch
  rw [memRegion_split sp 0x48 8 (by decide), sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem pollWithBaseKey_stale_weaken (sp : BitVec 64) (items : PendingPreKey) :
    pollWithBaseKey sp items ⊢ memRegion (sp + 0x46a#64) 0x716 := by
  unfold pollWithBaseKey
  have h2 := pointsToBytes_entails_memRegion (sp + 0xab4#64) items.baseKey.bytes.toList
  rw [items.baseKey.bytes.toList_length] at h2
  rw [mr_cut_add sp 0x46a 0x64a 0xcc (by decide),
      mr_cut_add sp 0xab4 32 0xac (by decide)]
  exact sepConj_mono_right (sepConj_mono_left h2)

theorem memRegion_16_unpack_598 (sp : BitVec 64) :
    memRegion (sp + 0x598#64) 16 ⊢
      ∃∗ w5a0 : BitVec 64, ∃∗ w598 : BitVec 64,
        ((sp + 0x598#64) ↦₆₄ w598) ∗ ((sp + 0x5a0#64) ↦₆₄ w5a0) := by
  rw [mr_cut_add sp 0x598 8 8 (by decide),
      ProofLib.memRegion_eight (sp + 0x598#64),
      ProofLib.memRegion_eight (sp + 0x5a0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion_24_unpack_9d0 (sp : BitVec 64) :
    memRegion (sp + 0x9d0#64) 24 ⊢
      ∃∗ w9e0 : BitVec 64, ∃∗ w9d8 : BitVec 64, ∃∗ w9d0 : BitVec 64,
        ((sp + 0x9d0#64) ↦₆₄ w9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ w9d8) ∗ ((sp + 0x9e0#64) ↦₆₄ w9e0) := by
  rw [mr_cut_add sp 0x9d0 8 16 (by decide),
      mr_cut_add sp 0x9d8 8 8 (by decide),
      ProofLib.memRegion_eight (sp + 0x9d0#64),
      ProofLib.memRegion_eight (sp + 0x9d8#64),
      ProofLib.memRegion_eight (sp + 0x9e0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem poll_stale_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 16 ∗
      memRegion (sp + 0x5a8#64) 0x428 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      memRegion (sp + 0x9e8#64) 0x198 := by
  rw [mr_cut_add sp 0x46a 0x116 0x600 (by decide),
      mr_cut_add sp 0x580 24 0x5e8 (by decide),
      mr_cut_add sp 0x598 16 0x5d8 (by decide),
      mr_cut_add sp 0x5a8 0x428 0x1b0 (by decide),
      mr_cut_add sp 0x9d0 24 0x198 (by decide)]

theorem vecU8_580_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x580#64) bs ⊢
      ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
        ((sp + 0x580#64) ↦₆₄ cap) ∗
        ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Body
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
    Entails.sepExists_right ptr (Entails.sepExists_right cap ?_)
  have ha1 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have ha2 : sp + 0x580#64 + 16#64 = sp + 0x590#64 := by bv_omega
  rw [ha1, ha2]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem pollWith_9d0_pack (sp cap ptr len w598 w5a0 w3 w4 w5 : BitVec 64) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      ((sp + 0x580#64) ↦₆₄ cap) ∗
      ((sp + 0x588#64) ↦₆₄ ptr) ∗
      ((sp + 0x590#64) ↦₆₄ len) ∗
      ((sp + 0x598#64) ↦₆₄ w598) ∗
      ((sp + 0x5a0#64) ↦₆₄ w5a0) ∗
      memRegion (sp + 0x5a8#64) 0x428 ∗
      ((sp + 0x9d0#64) ↦₆₄ w3) ∗
      ((sp + 0x9d8#64) ↦₆₄ w4) ∗
      ((sp + 0x9e0#64) ↦₆₄ w5) ∗
      memRegion (sp + 0x9e8#64) 0x198) ⊢
    pollWith sp 0x9d0 [w3, w4, w5] := by
  unfold pollWith
  dsimp only [words64At]
  rw [show (0x9d0 - 0x46a : Nat) = 0x566 from rfl,
      mr_cut_add sp 0x46a 0x116 0x450 (by decide),
      mr_cut_add sp 0x580 8 0x448 (by decide),
      mr_cut_add sp 0x588 8 0x440 (by decide),
      mr_cut_add sp 0x590 8 0x438 (by decide),
      mr_cut_add sp 0x598 8 0x430 (by decide),
      mr_cut_add sp 0x5a0 8 0x428 (by decide)]
  have hw0 : sp + BitVec.ofNat 64 0x9d0 = sp + 0x9d0#64 := rfl
  have hw1 : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
  have hw2 : sp + 0x9d8#64 + 8#64 = sp + 0x9e0#64 := by bv_omega
  have hw3 : sp + BitVec.ofNat 64 (0x9d0 + 8 * [w3, w4, w5].length) = sp + 0x9e8#64 := rfl
  have hlen3 : 0xb80 - (0x9d0 + 8 * [w3, w4, w5].length) = 0x198 := rfl
  rw [hw0, hw1, hw2, hw3, hlen3, sepConj_emp]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
