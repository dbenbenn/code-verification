/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTail -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segPreKey` Non-Stale Kyber Setup and Top-Level Composition (`segPreKey_ok_body`)

Steps the non-stale pending-pre-key branch from `+0x6fc` through `localRegistrationId` loading and
`kyberMapSpec` invocation to `PreKeyEncryptState` at `+0x8b4`, and composes all `segPreKey`
sub-segments into `SegPreKeySpec`.
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

/-! ## `sessionStateReprAt` Borrow Helpers -/

theorem pointsToBytes_leBytes4_eq_pointsTo32 (a : BitVec 64) (v : BitVec 32) :
    (a ↦ₛ leBytes 4 v.toNat) = (a ↦₃₂ v) := by
  rw [CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply.leBytes_4_eq_unpack32,
      ← pointsTo32_eq_pointsToBytes]

theorem regIds_eq_append {regIds : List (BitVec 8)} {remId locId : BitVec 32}
    (hlen : regIds.length = 8)
    (hrem : regIds.take 4 = leBytes 4 remId.toNat)
    (hloc : (regIds.drop 4).take 4 = leBytes 4 locId.toNat) :
    regIds = leBytes 4 remId.toNat ++ leBytes 4 locId.toNat := by
  have hdrop : (regIds.drop 4).take 4 = regIds.drop 4 :=
    List.take_of_length_le (by simp [hlen])
  rw [hdrop] at hloc
  rw [← hrem, ← hloc, List.take_append_drop]

theorem pointsToBytes_regIds_eq (a : BitVec 64) {regIds : List (BitVec 8)} {remId locId : BitVec 32}
    (hlen : regIds.length = 8)
    (hrem : regIds.take 4 = leBytes 4 remId.toNat)
    (hloc : (regIds.drop 4).take 4 = leBytes 4 locId.toNat) :
    (a ↦ₛ regIds) = ((a ↦₃₂ remId) ∗ ((a + 4#64) ↦₃₂ locId)) := by
  rw [regIds_eq_append hlen hrem hloc,
      pointsToBytes_append a (leBytes 4 remId.toNat) (leBytes 4 locId.toNat),
      pointsToBytes_leBytes4_eq_pointsTo32, pointsToBytes_leBytes4_eq_pointsTo32]
  rfl

@[expose] def sessionRegIdFrame (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
    G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat ∧
    PublicKey.deserialize G.localIk.bytes = .ok taken.localIdentity.publicKey ∧
    (match taken.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = taken.receiverChains.length ∧
    G.pending.isSome = taken.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (taken.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 taken.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip taken.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr taken.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender taken.senderChain ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    ((ss + 0x148#64) ↦₃₂ taken.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ taken.previousCounter) ∗
    ((ss + 0x150#64) ↦₃₂ sess.remoteRegistrationId)

theorem sessionAt_regId_unpack (A : RustAlloc) (sp : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    sessionStateReprAt A (sp + 0x128#64) G ({ sess with state := taken }) ⊢
      ⌜KyberRel G.kyber sess.pendingKyberPreKey⌝ ∗
      sessionRegIdFrame A (sp + 0x128#64) G sess taken ∗
      optTailVecAt A 32 (sp + 0x250#64) G.kyber ∗
      ((sp + 0x27c#64) ↦₃₂ sess.localRegistrationId) := by
  unfold sessionStateReprAt sessionStateAt sessionRegIdFrame
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hp1, hky, hal, hrem, hloc⟩
  apply Entails.pure_left
  rintro ⟨hlik, hrik, hch, hpend, hlen, hlik33, hrik33⟩
  rw [pointsToBytes_regIds_eq (sp + 0x128#64 + 0x150#64) hlen hrem hloc]
  have h250 : sp + 0x128#64 + 0x128#64 = sp + 0x250#64 := by bv_omega
  have h27c : sp + 0x128#64 + 0x150#64 + 4#64 = sp + 0x27c#64 := by bv_omega
  rw [h250, h27c]
  apply Entails.pure_right hky
  apply Entails.pure_right ⟨hp1, hky, hal, hrem, hloc, hlik, hrik, hch, hpend, hlen, hlik33, hrik33⟩
  exact Entails.of_eq (by ac_rfl)

theorem sessionAt_regId_pack (A : RustAlloc) (sp : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (sessionRegIdFrame A (sp + 0x128#64) G sess taken ∗
      optTailVecAt A 32 (sp + 0x250#64) G.kyber ∗
      ((sp + 0x27c#64) ↦₃₂ sess.localRegistrationId)) ⊢
    sessionStateReprAt A (sp + 0x128#64) G ({ sess with state := taken }) := by
  unfold sessionStateReprAt sessionStateAt sessionRegIdFrame
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨hp1, hky, hal, hrem, hloc, hlik, hrik, hch, hpend, hlen, hlik33, hrik33⟩
  rw [pointsToBytes_regIds_eq (sp + 0x128#64 + 0x150#64) hlen hrem hloc]
  have h250 : sp + 0x128#64 + 0x128#64 = sp + 0x250#64 := by bv_omega
  have h27c : sp + 0x128#64 + 0x150#64 + 4#64 = sp + 0x27c#64 := by bv_omega
  rw [h250, h27c]
  apply Entails.pure_right ⟨hp1, hky, hal, hrem, hloc⟩
  apply Entails.pure_right ⟨hlik, hrik, hch, hpend, hlen, hlik33, hrik33⟩
  exact Entails.of_eq (by ac_rfl)

@[expose] def vecU8BorrowRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr cap.toNat 1 ∗
     memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Buf_borrow (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜ptr ≠ 0#64⌝ ∗ (ptr ↦ₛ bs) ∗ vecU8BorrowRest A cap ptr bs := by
  unfold vecU8Buf vecU8BorrowRest
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hptr64 : ptr ≠ 0#64 := hptr
  apply Entails.pure_right hptr64
  by_cases hcap : cap = 0
  · have h0 : cap.toNat = 0 := by rw [hcap]; rfl
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [hcap, ↓reduceIte, hbs0, pointsToBytes_nil, emp_sepConj]
    exact Entails.pure_right ⟨by rw [← hcap, ← hbs0]; exact hle, by rw [← hcap]; exact hlt, hptr⟩
      (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    rw [sepConj_pure_left_comm]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)

theorem vecU8Buf_unborrow (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((ptr ↦ₛ bs) ∗ vecU8BorrowRest A cap ptr bs) ⊢
      vecU8Buf A cap ptr bs := by
  unfold vecU8Buf vecU8BorrowRest
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  apply Entails.pure_right ⟨hle, hlt, hptr⟩
  by_cases hcap : cap = 0
  · have h0 : cap.toNat = 0 := by rw [hcap]; rfl
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp only [hcap, ↓reduceIte, hbs0, pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

@[expose] def optTailVecBorrowRest (A : RustAlloc) (a : BitVec 64) (g : TailVecGhost) : SepProp :=
  ⌜g.tail.length = 8⌝ ∗
  vecHeader a g.vec.cap g.vec.ptr (BitVec.ofNat 64 g.vec.bytes.length) ∗
  vecU8BorrowRest A g.vec.cap g.vec.ptr g.vec.bytes ∗
  ((a + 24#64) ↦ₛ g.tail)

theorem optTailVecAt_borrow (A : RustAlloc) (a : BitVec 64) (g : TailVecGhost) :
    optTailVecAt A 32 a (some g) ⊢
      ⌜g.vec.ptr ≠ 0#64⌝ ∗
      (g.vec.ptr ↦ₛ g.vec.bytes) ∗
      optTailVecBorrowRest A a g := by
  dsimp only [optTailVecAt, vecGhostAt, optTailVecBorrowRest]
  rw [vecU8At_eq_header_sep_buf]
  simp only [Nat.reduceSub, sepConj_assoc]
  apply Entails.pure_left
  intro htail
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (vecU8Buf_borrow A g.vec.cap g.vec.ptr g.vec.bytes) (Entails.refl _))) ?_
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  intro hptr
  apply Entails.pure_right hptr
  rw [sepConj_pure_left_comm]
  apply Entails.pure_right htail
  exact Entails.of_eq (by ac_rfl)

theorem optTailVecAt_unborrow (A : RustAlloc) (a : BitVec 64) (g : TailVecGhost) :
    ((g.vec.ptr ↦ₛ g.vec.bytes) ∗ optTailVecBorrowRest A a g) ⊢
      optTailVecAt A 32 a (some g) := by
  dsimp only [optTailVecAt, vecGhostAt, optTailVecBorrowRest]
  rw [vecU8At_eq_header_sep_buf]
  simp only [Nat.reduceSub, sepConj_assoc]
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  intro htail
  apply Entails.pure_right htail
  have h1 :
      ((g.vec.ptr ↦ₛ g.vec.bytes) ∗
        vecHeader a g.vec.cap g.vec.ptr (BitVec.ofNat 64 g.vec.bytes.length) ∗
        vecU8BorrowRest A g.vec.cap g.vec.ptr g.vec.bytes ∗
        ((a + 24#64) ↦ₛ g.tail)) =
      (vecHeader a g.vec.cap g.vec.ptr (BitVec.ofNat 64 g.vec.bytes.length) ∗
        ((g.vec.ptr ↦ₛ g.vec.bytes) ∗ vecU8BorrowRest A g.vec.cap g.vec.ptr g.vec.bytes) ∗
        ((a + 24#64) ↦ₛ g.tail)) := by ac_rfl
  rw [h1]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (vecU8Buf_unborrow A g.vec.cap g.vec.ptr g.vec.bytes) (Entails.refl _))

/-! ## Scratch and Stack Helpers (`+0x6fc..+0x8b4`) -/

theorem encSubStack_split_kyber {sp ssp : BitVec 64} (hsp : ssp = sp) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack)
        (encSubStack - (allocHookStack + 0x40)) ∗
      stackAt ssp (allocHookStack + 0x40) := by
  subst ssp
  show memRegion (sp - BitVec.ofNat 64 encSubStack) encSubStack = _
  rw [mr_cut' sp encSubStack (allocHookStack + 0x40) (encSubStack - (allocHookStack + 0x40))
    (allocHookStack + 0x40) encSubStack rfl rfl (by decide) (by decide) (by decide)]

theorem preKeyScratch_regId_unpack (sp kyLen : BitVec 64) (spk kyIdVal pkVal : BitVec 32)
    (kyber : Option PendingKyberPreKey) :
    preKeyScratch sp kyLen spk kyIdVal pkVal kyber ⊢
      ∃∗ w14 : BitVec 32,
        memRegion sp 0x14 ∗
        ((sp + 0x14#64) ↦₃₂ w14) ∗
        ((sp + 0x18#64) ↦₆₄ kyLen) ∗
        memRegion (sp + 0x20#64) 4 ∗
        ((sp + 0x24#64) ↦₃₂ spk) ∗
        ((sp + 0x28#64) ↦₆₄ (kyIdVal ++ (if (kyber.map (·.preKeyId)).isSome then 1#32 else 0#32))) ∗
        memRegion (sp + 0x30#64) 4 ∗
        ((sp + 0x34#64) ↦₃₂ pkVal) ∗
        ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
        ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
        ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) := by
  unfold preKeyScratch
  rw [memRegion_split sp 0x14 4 (by decide),
      ProofLib.memRegion_four (sp + 0x14#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

theorem preKeyEncryptScratch_pack (sp kyLen w28 : BitVec 64) (regId spk pkVal : BitVec 32) :
    (memRegion sp 0x14 ∗
      ((sp + 0x14#64) ↦₃₂ regId) ∗
      ((sp + 0x18#64) ↦₆₄ kyLen) ∗
      memRegion (sp + 0x20#64) 4 ∗
      ((sp + 0x24#64) ↦₃₂ spk) ∗
      ((sp + 0x28#64) ↦₆₄ w28) ∗
      memRegion (sp + 0x30#64) 4 ∗
      ((sp + 0x34#64) ↦₃₂ pkVal) ∗
      ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ⊢
    preKeyEncryptScratch sp regId spk pkVal := by
  unfold preKeyEncryptScratch preKeyEncryptScratch'
  rw [mr_cut_add sp 0x18 8 4 (by decide),
      mr_cut_add sp 0x28 8 4 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))

theorem pollWithBaseKey_regId_unpack (sp : BitVec 64) (items : PendingPreKey) :
    pollWithBaseKey sp items ⊢
      ∃∗ w590 : BitVec 64, ∃∗ w588 : BitVec 64, ∃∗ w580 : BitVec 32,
        memRegion (sp + 0x46a#64) 0x116 ∗
        ((sp + 0x580#64) ↦₃₂ w580) ∗
        memRegion (sp + 0x584#64) 4 ∗
        ((sp + 0x588#64) ↦₆₄ w588) ∗
        ((sp + 0x590#64) ↦₆₄ w590) ∗
        memRegion (sp + 0x598#64) 0x308 ∗
        memRegion (sp + 0x8a0#64) 24 ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗
        ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0xac := by
  unfold pollWithBaseKey
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 4 0x530 (by decide),
      mr_cut_add sp 0x584 4 0x52c (by decide),
      mr_cut_add sp 0x588 8 0x524 (by decide),
      mr_cut_add sp 0x590 8 0x51c (by decide),
      mr_cut_add sp 0x598 0x308 0x214 (by decide),
      mr_cut_add sp 0x8a0 24 0x1fc (by decide),
      ProofLib.memRegion_four (sp + 0x580#64),
      ProofLib.memRegion_eight (sp + 0x588#64),
      ProofLib.memRegion_eight (sp + 0x590#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

theorem kyberArgAt_none_pack (sp : BitVec 64) (w580 : BitVec 32) (w590 : BitVec 64) :
    (((sp + 0x580#64) ↦₃₂ w580) ∗
      memRegion (sp + 0x584#64) 4 ∗
      ((sp + 0x588#64) ↦₆₄ 0#64) ∗
      ((sp + 0x590#64) ↦₆₄ w590)) ⊢
    kyberArgAt ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩ := by
  dsimp only [kyberArgAt]
  have h8 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have h10 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [h8, h10, mr_cut_add sp 0x580 4 4 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _)))

theorem kyberArgAt_none_to_memRegion (sp : BitVec 64) :
    kyberArgAt ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩ ⊢
      memRegion (sp + 0x580#64) 24 := by
  dsimp only [kyberArgAt]
  have h8 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have h10 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [h8, h10, mr_cut_add sp 0x580 8 16 (by decide), mr_cut_add sp 0x588 8 8 (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem kyberArgAt_some_pack (sp ptr : BitVec 64) (ky : PendingKyberPreKey)
    (hptr : ptr ≠ 0#64) (hlen : ky.ciphertext.length < 2 ^ 32) :
    (((sp + 0x580#64) ↦₃₂ ky.preKeyId) ∗
      memRegion (sp + 0x584#64) 4 ∗
      ((sp + 0x588#64) ↦₆₄ ptr) ∗
      ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 ky.ciphertext.length) ∗
      (ptr ↦ₛ ky.ciphertext)) ⊢
    kyberArgAt ⟨sp + 0x8a0#64, sp + 0x580#64, ptr,
      some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩ := by
  dsimp only [kyberArgAt]
  have h4 : sp + 0x580#64 + 4#64 = sp + 0x584#64 := by bv_omega
  have h8 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have h10 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [h4, h8, h10]
  exact Entails.pure_right ⟨hptr, hlen⟩ (Entails.refl _)

theorem kyberArgAt_some_unpack (sp ptr : BitVec 64) (ky : PendingKyberPreKey) :
    kyberArgAt ⟨sp + 0x8a0#64, sp + 0x580#64, ptr,
      some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩ ⊢
      memRegion (sp + 0x580#64) 24 ∗ (ptr ↦ₛ ky.ciphertext) := by
  dsimp only [kyberArgAt]
  apply Entails.pure_left
  intro _
  have h4 : sp + 0x580#64 + 4#64 = sp + 0x584#64 := by bv_omega
  have h8 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have h10 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [h4, h8, h10,
      mr_cut_add sp 0x580 4 20 (by decide),
      mr_cut_add sp 0x584 4 16 (by decide),
      mr_cut_add sp 0x588 8 8 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))

theorem pollPreKeyEncrypt_pack (A : RustAlloc) (sp bp : BitVec 64) (items : PendingPreKey)
    (kyber : Option PendingKyberPreKey) (kp : Option KyberPayload)
    (hkp : kp = kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x308 ∗
      optKyberAt A (sp + 0x8a0#64) bp kp ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac) ⊢
    pollPreKeyEncrypt A sp bp items kyber := by
  subst hkp
  unfold pollPreKeyEncrypt pollE6c'
  rw [mr_cut_add sp 0x46a 0x116 0x320 (by decide),
      mr_cut_add sp 0x580 24 0x308 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

/-! ## Non-Stale Check and `kyberMap` Call (`+0x6fc..+0x8b4`) -/

@[simp, arm64_norm, wp_norm]
theorem append32_getLsbD_zero (hi lo : BitVec 32) :
    (hi ++ lo).getLsbD 0 = lo.getLsbD 0 := by
  have hlt : 0 < 32 := by omega
  simp only [BitVec.getLsbD_append, hlt, ↓reduceIte]

@[simp, arm64_norm, wp_norm]
theorem append32_setWidth32 (hi lo : BitVec 32) :
    (hi ++ lo).setWidth 32 = lo := by
  ext i hi_lt
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    hi_lt, decide_true, Bool.true_and, ↓reduceIte]

@[simp, arm64_norm, wp_norm]
theorem append32_ushiftRight32_setWidth32 (hi lo : BitVec 32) :
    ((hi ++ lo) >>> 32).setWidth 32 = hi := by
  ext i hi_lt
  have hnot : ¬ (32 + i < 32) := by omega
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi_lt, hnot, decide_true, Bool.true_and, ↓reduceIte,
    Nat.add_sub_cancel_left]

@[simp, arm64_norm, wp_norm]
theorem append32_ushiftRight32_and_setWidth32 (hi lo : BitVec 32) :
    (((hi ++ lo) >>> 32) &&& 4294967295#64).setWidth 32 = hi := by
  ext i hi_lt
  have hnot : ¬ (32 + i < 32) := by omega
  have hmask_all : ∀ j < 32, (4294967295#64).getLsbD j = true := by decide
  have hmask := hmask_all i hi_lt
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hi_lt, hnot, hmask,
    decide_true, Bool.true_and, Bool.and_true, ↓reduceIte, Nat.add_sub_cancel_left]

theorem kyberPost_unpack (A : RustAlloc) (out arg ctPtr : BitVec 64) (kp : Option KyberPayload) :
    (kyberArgAt ⟨out, arg, ctPtr, kp⟩ ∗ (∃∗ bp : BitVec 64, optKyberAt A out bp kp)) ⊢
      ∃∗ bp : BitVec 64, kyberArgAt ⟨out, arg, ctPtr, kp⟩ ∗ optKyberAt A out bp kp := by
  rw [sepExists_sepConj_right]
  exact Entails.refl _

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
