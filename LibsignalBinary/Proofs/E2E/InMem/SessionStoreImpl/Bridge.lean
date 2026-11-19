/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Skeleton -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Skeleton
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HashbrownBin` Bridge for `InMemSessionStore`

Connects the raw `HashbrownBin` single-entry `load_session` and `store_session` poll
specifications (`loadSessionSingleSpec`, `storeSessionSingleHitSpec`) to the
`SessionRecord`-level contracts (`HashbrownBinSessionBridge`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.InMem.SessionStoreImpl

open Arm64 ProofLib
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel (hashAddrBv)
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.Record.DeserializeGeneral (DeserializeScope)
open CryptoVerification.E2E.Record.Serialization (CanonSession CanonCur CanonRecord)

set_option maxRecDepth 200000

/-! ## Bucket Entry and `SessionRecord` Representation Bridges -/

private def singleBucketRestAt (stride : Nat) (ctrl : BitVec 64) (k : Nat) : SepProp :=
  arrayAt
    (fun i a => if i = k then emp else memRegion a stride) stride
    (ctrl - BitVec.ofNat 64 (4 * stride)) [3, 2, 1, 0]

private theorem sub1600_add400 (ctrl : BitVec 64) :
    ctrl - 1600#64 + 400#64 = ctrl - 1200#64 := by bv_omega

private theorem sub1200_add400 (ctrl : BitVec 64) :
    ctrl - 1200#64 + 400#64 = ctrl - 800#64 := by bv_omega

private theorem sub800_add400 (ctrl : BitVec 64) :
    ctrl - 800#64 + 400#64 = ctrl - 400#64 := by bv_omega

private theorem arrayAt_single_split_400 (ctrl : BitVec 64) (k : Nat) (hk : k < 4)
    (entryAt : BitVec 64 → SepProp) :
    arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 400) 400
      (ctrl - BitVec.ofNat 64 (4 * 400)) (List.range 4).reverse =
    entryAt (bucketAddr ctrl 400 k) ∗ singleBucketRestAt 400 ctrl k := by
  change arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 400) 400
      (ctrl - 1600#64) [3, 2, 1, 0] =
    entryAt (bucketAddr ctrl 400 k) ∗ singleBucketRestAt 400 ctrl k
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [singleBucketRestAt, bucketAddr, arrayAt, List.mem_singleton,
      Nat.reduceAdd, Nat.reduceMul,
      sub1600_add400, sub1200_add400, sub800_add400, ite_true]
    ac_rfl

private def table4SingleHeaderAt (A : RustAlloc) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (ctrl : BitVec 64) : SepProp :=
  let cbs := singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))
  let full : List Nat := [k]
  ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
    4 * 400 ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
    (full.length = 4 → (2#64 : BitVec 64) = 0#64) ∧
    CtrlMirrorInv 3#64 cbs ∧ FullBucketsInv 3#64 cbs full⌝ ∗
  (mp ↦₆₄ ctrl) ∗
  ((mp + asm64% tableMaskOff) ↦₆₄ 3#64) ∗
  ((mp + asm64% tableGrowthLeftOff) ↦₆₄ 2#64) ∗
  ((mp + asm64% tableItemsOff) ↦₆₄ BitVec.ofNat 64 full.length) ∗
  ((mp + asm64% tableHasherOff) ↦₆₄ k0) ∗
  ((mp + asm64% tableHasherOff + 8#64) ↦₆₄ k1) ∗
  A.live (ctrl - BitVec.ofNat 64 (4 * 400)) (tableAllocSize 4 400) (asm% hashbrownTableAlign) ∗
  (ctrl ↦ₛ cbs) ∗
  singleBucketRestAt 400 ctrl k

private theorem table4SingleAt_eq_header (A : RustAlloc) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) :
    table4SingleAt A HashbrownBin.sessionBucketStride mp k0 k1 k peerName peerDev entryAt =
      ∃∗ ctrl : BitVec 64,
        entryAt (bucketAddr ctrl 400 k) ∗
        (⌜k < 4⌝ ∗ table4SingleHeaderAt A mp k0 k1 k peerName peerDev ctrl) := by
  unfold table4SingleAt table4At table4SingleHeaderAt
  dsimp only [HashbrownBin.sessionBucketStride, AsmConstants.sessionBucketStride]
  rw [sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun ctrl => ?_)
  rw [arrayAt_single_split_400 ctrl k hk entryAt]
  ac_rfl

theorem sessionBucketEntryAt_pack {A : RustAlloc} {g : AddrGhost}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {r : SessionRecord (List (BitVec 8))}
    (hr : r = ⟨some ss⟩) (hScope : RecordInScope r) (a : BitVec 64) :
    sessionBucketEntryAt A g G ss a ⊢ sessionRecordBucketEntryAt A g r a := by
  unfold sessionBucketEntryAt sessionRecordBucketEntryAt
  refine Entails.pure_left fun hCanon => ?_
  refine Entails.sepExists_right G (Entails.sepExists_right ss ?_)
  refine Entails.pure_right ⟨hr, hScope, hCanon⟩ ?_
  have heq := record_sessionRecordAt_eq A (a + 0x20#64) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩
  dsimp only [toRecordGhost, HashbrownBin.sessionBucketValueOff, AsmConstants.sessionBucketValueOff] at heq ⊢
  rw [heq]
  exact Entails.refl _

theorem sessionRecordBucketEntryAt_unpack (A : RustAlloc) (g : AddrGhost)
    (r : SessionRecord (List (BitVec 8))) (a : BitVec 64) :
    sessionRecordBucketEntryAt A g r a ⊢
      ∃∗ G : SessionGhost, ∃∗ ss : Session (List (BitVec 8)),
        ⌜r = ⟨some ss⟩ ∧ RecordInScope r⌝ ∗ sessionBucketEntryAt A g G ss a := by
  unfold sessionRecordBucketEntryAt sessionBucketEntryAt
  refine Entails.sepExists_elim fun G => Entails.sepExists_elim fun ss => ?_
  refine Entails.pure_left fun ⟨hr, hScope, hCanon⟩ => ?_
  refine Entails.sepExists_right G (Entails.sepExists_right ss ?_)
  refine Entails.pure_right ⟨hr, hScope⟩ (Entails.pure_right hCanon ?_)
  have heq := record_sessionRecordAt_eq A (a + 0x20#64) ⟨0#64, 8#64, some G⟩ ⟨some ss⟩
  dsimp only [toRecordGhost, HashbrownBin.sessionBucketValueOff, AsmConstants.sessionBucketValueOff] at heq ⊢
  rw [← heq]
  exact Entails.refl _

theorem table4SingleAt_sessionBucketEntryAt_pack
    {A : RustAlloc} {mp k0 k1 : BitVec 64} {k : Nat} (hk : k < 4)
    {peerName : List (BitVec 8)} {peerDev : BitVec 8}
    {g : AddrGhost} {G : SessionGhost} {ss : Session (List (BitVec 8))}
    {r : SessionRecord (List (BitVec 8))}
    (hr : r = ⟨some ss⟩) (hScope : RecordInScope r) :
    table4SingleAt A HashbrownBin.sessionBucketStride mp k0 k1 k peerName peerDev
        (sessionBucketEntryAt A g G ss) ⊢
      table4SingleAt A HashbrownBin.sessionBucketStride mp k0 k1 k peerName peerDev
        (sessionRecordBucketEntryAt A g r) := by
  rw [table4SingleAt_eq_header A mp k0 k1 k hk peerName peerDev (sessionBucketEntryAt A g G ss),
      table4SingleAt_eq_header A mp k0 k1 k hk peerName peerDev (sessionRecordBucketEntryAt A g r)]
  exact Entails.sepExists_elim fun ctrl =>
    Entails.sepExists_right ctrl
      (sepConj_mono_left (sessionBucketEntryAt_pack hr hScope _))

theorem table4SingleAt_sessionRecordBucketEntryAt_unpack
    (A : RustAlloc) (mp k0 k1 : BitVec 64) (k : Nat) (hk : k < 4)
    (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (g : AddrGhost) (r : SessionRecord (List (BitVec 8))) :
    table4SingleAt A HashbrownBin.sessionBucketStride mp k0 k1 k peerName peerDev
        (sessionRecordBucketEntryAt A g r) ⊢
      ∃∗ G : SessionGhost, ∃∗ ss : Session (List (BitVec 8)),
        ⌜r = ⟨some ss⟩ ∧ RecordInScope r⌝ ∗
        table4SingleAt A HashbrownBin.sessionBucketStride mp k0 k1 k peerName peerDev
          (sessionBucketEntryAt A g G ss) := by
  rw [table4SingleAt_eq_header A mp k0 k1 k hk peerName peerDev (sessionRecordBucketEntryAt A g r)]
  refine Entails.sepExists_elim fun ctrl => ?_
  refine Entails.trans (sepConj_mono_left (sessionRecordBucketEntryAt_unpack A g r _)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun G => Entails.sepExists_elim fun ss => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun h => ?_
  refine Entails.sepExists_right G (Entails.sepExists_right ss ?_)
  refine Entails.pure_right h ?_
  rw [table4SingleAt_eq_header A mp k0 k1 k hk peerName peerDev (sessionBucketEntryAt A g G ss)]
  exact Entails.sepExists_right ctrl (Entails.refl _)

theorem pollOptSessionRecordResultAt_pack
    {A : RustAlloc} {sret : BitVec 64} {cond : Prop} [Decidable cond]
    {ss : Session (List (BitVec 8))} {r : SessionRecord (List (BitVec 8))}
    (hr : r = ⟨some ss⟩) (hScope : RecordInScope r) :
    pollOptSessionRecordResultAt A sret (if cond then some ss else none) ⊢
      pollOptSessionRecordAt A sret (if cond then some r else none) := by
  by_cases hc : cond
  · simp only [hc, ↓reduceIte, pollOptSessionRecordResultAt, pollOptSessionRecordAt]
    refine Entails.sepExists_elim fun G' => ?_
    refine Entails.pure_left fun hCanon => ?_
    refine Entails.sepExists_right G' (Entails.sepExists_right ss ?_)
    refine Entails.pure_right ⟨hr, hScope, hCanon⟩ ?_
    have heq := record_sessionRecordAt_eq A sret ⟨0#64, 8#64, some G'⟩ ⟨some ss⟩
    dsimp only [toRecordGhost] at heq
    rw [heq]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte, pollOptSessionRecordResultAt, pollOptSessionRecordAt]
    exact Entails.refl _

private theorem sessionRecordAt_entails_canonRecord_some (A : RustAlloc) (recPtr : BitVec 64)
    (rg : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hSome : r.currentSession.isSome) :
    sessionRecordAt A recPtr rg r ⊢
      ⌜CanonRecord (toRecordGhost rg) r⌝ ∗ sessionRecordAt A recPtr rg r := by
  have h_chain : ∀ (gc : ChainGhost × ReceiverChain) (a : BitVec 64),
      chainAt A gc a ⊢ ⌜CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗ chainAt A gc a := by
    intro gc a
    unfold chainAt
    apply Entails.pure_left
    rintro ⟨hd, hmax, hklen, hlen, hpriv⟩
    exact Entails.pure_right ⟨eq_serialize_of_deserialize hd hlen, hpriv⟩
      (Entails.pure_right ⟨hd, hmax, hklen, hlen, hpriv⟩ (Entails.refl _))
  have h_arr : ∀ (xs : List (ChainGhost × ReceiverChain)) (base : BitVec 64),
      arrayAt (chainAt A) 104 base xs ⊢
        ⌜∀ gc ∈ xs, CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
          arrayAt (chainAt A) 104 base xs := by
    intro xs
    induction xs with
    | nil =>
      intro base
      dsimp only [arrayAt]
      exact Entails.pure_right (by intro _ h; cases h) (Entails.refl _)
    | cons gc xs ih =>
      intro base
      dsimp only [arrayAt]
      refine Entails.trans (sepConj_mono (h_chain gc base) (ih (base + BitVec.ofNat 64 104))) ?_
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hgc
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; intro hxs
      refine Entails.pure_right (fun x hx => ?_) (Entails.refl _)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hgc
      · exact hxs x hx
  have h_vec : ∀ (v cap ptr : BitVec 64) (xs : List (ChainGhost × ReceiverChain)),
      vecAt A 104 8 (chainAt A) v cap ptr xs ⊢
        ⌜∀ gc ∈ xs, CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
          vecAt A 104 8 (chainAt A) v cap ptr xs := by
    intro v cap ptr xs
    unfold vecAt vecBuf
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hbuf
    by_cases hcap : cap = 0
    · subst hcap
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbuf.1)
      subst hnil
      exact Entails.pure_right (by intro _ h; cases h) (Entails.pure_right hbuf (Entails.refl _))
    · simp only [hcap, ↓reduceIte]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (h_arr xs ptr)))) ?_
      have hpull :
          (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
            A.live ptr (cap.toNat * 104) 8 ∗
            (⌜∀ gc ∈ xs, CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
              arrayAt (chainAt A) 104 ptr xs) ∗
            memRegion (ptr + BitVec.ofNat 64 (xs.length * 104)) ((cap.toNat - xs.length) * 104)) =
          (⌜∀ gc ∈ xs, CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
            (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
              A.live ptr (cap.toNat * 104) 8 ∗
              arrayAt (chainAt A) 104 ptr xs ∗
              memRegion (ptr + BitVec.ofNat 64 (xs.length * 104)) ((cap.toNat - xs.length) * 104))) := by
        ac_rfl
      rw [hpull]
      apply Entails.pure_left; intro hall
      exact Entails.pure_right hall (Entails.pure_right hbuf (Entails.refl _))
  have h_sender : ∀ (a : BitVec 64) (og : Option SenderChainGhost) (os : Option SenderChain),
      optSenderChainAt A a og os ⊢
        ⌜CryptoVerification.E2E.Record.Serialization.CanonSender og os⌝ ∗
          optSenderChainAt A a og os := by
    intro a og os
    rcases og with _ | g <;> rcases os with _ | sc
    · exact Entails.pure_right trivial (Entails.refl _)
    · dsimp only [optSenderChainAt]; exact Entails.pure_left_only False.elim
    · dsimp only [optSenderChainAt]; exact Entails.pure_left_only False.elim
    · unfold optSenderChainAt
      apply Entails.pure_left
      rintro ⟨hd, hpriv, hclamp, hlen⟩
      exact Entails.pure_right ⟨eq_serialize_of_deserialize hd hlen, hpriv⟩
        (Entails.pure_right ⟨hd, hpriv, hclamp, hlen⟩ (Entails.refl _))
  obtain ⟨s, hr⟩ := Option.isSome_iff_exists.mp hSome
  unfold sessionRecordAt
  rw [hr]
  cases hcur : rg.cur with
  | none =>
    dsimp only
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | some G =>
    dsimp only
    unfold CanonRecord CanonCur toRecordGhost
    dsimp only
    rw [hcur, hr]
    have h_sess : sessionStateReprAt A (recPtr + 0x18#64) G s ⊢
        ⌜CanonSession G s⌝ ∗ sessionStateReprAt A (recPtr + 0x18#64) G s := by
      unfold sessionStateReprAt
      apply Entails.pure_left
      rintro ⟨hPendRel, hkyb, halice, hremReg, hlocReg⟩
      have h_state : sessionStateAt A (recPtr + 0x18#64) G s.state ⊢
          ⌜CanonSession G s⌝ ∗ sessionStateAt A (recPtr + 0x18#64) G s.state := by
        unfold sessionStateAt
        apply Entails.pure_left
        rintro ⟨hLocal, hRemote, hChainsLen, hpend_some, hreg_len, hLocalLen, hRemoteLen⟩
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono
              (h_vec ((recPtr + 0x18#64) + 0x48#64) G.chainsCap G.chainsPtr
                (G.chains.zip s.state.receiverChains))
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left
                  (h_sender ((recPtr + 0x18#64) + 0x90#64) G.sender s.state.senderChain)))))))) ?_
        have hpull :
            (vecGhostAt A G.localIk (recPtr + 0x18#64) ∗
              vecGhostAt A G.remoteIk ((recPtr + 0x18#64) + 0x18#64) ∗
              vecU8At A ((recPtr + 0x18#64) + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) ∗
              (⌜∀ gc ∈ G.chains.zip s.state.receiverChains,
                  CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
                vecAt A 104 8 (chainAt A) ((recPtr + 0x18#64) + 0x48#64) G.chainsCap G.chainsPtr
                  (G.chains.zip s.state.receiverChains)) ∗
              vecGhostAt A G.alice ((recPtr + 0x18#64) + 0x60#64) ∗
              vecU8At A ((recPtr + 0x18#64) + 0x78#64) G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
              (⌜CryptoVerification.E2E.Record.Serialization.CanonSender G.sender s.state.senderChain⌝ ∗
                optSenderChainAt A ((recPtr + 0x18#64) + 0x90#64) G.sender s.state.senderChain) ∗
              optTailVecAt A 48 ((recPtr + 0x18#64) + 0xf8#64) G.pending ∗
              optTailVecAt A 32 ((recPtr + 0x18#64) + 0x128#64) G.kyber ∗
              (((recPtr + 0x18#64) + 0x148#64) ↦₃₂ s.state.sessionVersion) ∗
              (((recPtr + 0x18#64) + 0x14c#64) ↦₃₂ s.state.previousCounter) ∗
              (((recPtr + 0x18#64) + 0x150#64) ↦ₛ G.regIds)) =
            (⌜∀ gc ∈ G.chains.zip s.state.receiverChains,
                CryptoVerification.E2E.Record.Serialization.CanonChain gc⌝ ∗
              ⌜CryptoVerification.E2E.Record.Serialization.CanonSender G.sender s.state.senderChain⌝ ∗
              (vecGhostAt A G.localIk (recPtr + 0x18#64) ∗
                vecGhostAt A G.remoteIk ((recPtr + 0x18#64) + 0x18#64) ∗
                vecU8At A ((recPtr + 0x18#64) + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 s.state.rootKey) ∗
                vecAt A 104 8 (chainAt A) ((recPtr + 0x18#64) + 0x48#64) G.chainsCap G.chainsPtr
                  (G.chains.zip s.state.receiverChains) ∗
                vecGhostAt A G.alice ((recPtr + 0x18#64) + 0x60#64) ∗
                vecU8At A ((recPtr + 0x18#64) + 0x78#64) G.pq.cap G.pq.ptr s.state.pqRatchetState ∗
                optSenderChainAt A ((recPtr + 0x18#64) + 0x90#64) G.sender s.state.senderChain ∗
                optTailVecAt A 48 ((recPtr + 0x18#64) + 0xf8#64) G.pending ∗
                optTailVecAt A 32 ((recPtr + 0x18#64) + 0x128#64) G.kyber ∗
                (((recPtr + 0x18#64) + 0x148#64) ↦₃₂ s.state.sessionVersion) ∗
                (((recPtr + 0x18#64) + 0x14c#64) ↦₃₂ s.state.previousCounter) ∗
                (((recPtr + 0x18#64) + 0x150#64) ↦ₛ G.regIds))) := by
          ac_rfl
        rw [hpull]
        apply Entails.pure_left; intro hChainsCanon
        apply Entails.pure_left; intro hSenderCanon
        have hRemEq : G.remoteIk.bytes = (s.state.remoteIdentity.map IdentityKey.serialize).getD [] := by
          cases hrem : s.state.remoteIdentity with
          | none => rw [hrem] at hRemote; simp [hRemote]
          | some ik => rw [hrem] at hRemote hRemoteLen; simp [IdentityKey.serialize, eq_serialize_of_deserialize hRemote (hRemoteLen rfl)]
        have hPendCanon : CryptoVerification.E2E.Record.Serialization.CanonPending G.pending s.pendingPreKey := by
          cases hgp : G.pending <;> cases hsp : s.pendingPreKey <;>
            simp only [hgp, hsp, PendingRel, CryptoVerification.E2E.Record.Serialization.CanonPending] at hPendRel ⊢
          exact eq_serialize_of_deserialize hPendRel.1 hPendRel.2.2.2.2
        have hCanon : CanonSession G s :=
          ⟨eq_serialize_of_deserialize hLocal hLocalLen, hRemEq, hSenderCanon, hChainsLen, hChainsCanon, hPendCanon⟩
        exact Entails.pure_right hCanon
          (Entails.pure_right ⟨hLocal, hRemote, hChainsLen, hpend_some, hreg_len, hLocalLen, hRemoteLen⟩ (Entails.refl _))
      refine Entails.trans h_state ?_
      apply Entails.pure_left; intro hCanon
      exact Entails.pure_right hCanon
        (Entails.pure_right ⟨hPendRel, hkyb, halice, hremReg, hlocReg⟩ (Entails.refl _))
    refine Entails.trans (sepConj_mono_right h_sess) ?_
    rw [sepConj_pure_left_comm]
    exact Entails.refl _

private theorem sessionRecordAt_entails_canonRecord (A : RustAlloc) (recPtr : BitVec 64)
    (rg : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hOk : InMemRecOk r) :
    sessionRecordAt A recPtr rg r ⊢
      ⌜CanonRecord (toRecordGhost rg) r⌝ ∗ sessionRecordAt A recPtr rg r :=
  sessionRecordAt_entails_canonRecord_some A recPtr rg r hOk.2.2

private theorem sessionRecordAt_none_some_false (A : RustAlloc) (recPtr : BitVec 64)
    (prevCap prevPtr : BitVec 64) (s : Session (List (BitVec 8))) (Q : SepProp) :
    sessionRecordAt A recPtr ⟨prevCap, prevPtr, none⟩ ⟨some s⟩ ⊢ Q := by
  unfold sessionRecordAt
  dsimp only
  rw [sepConj_comm]
  exact Entails.pure_left False.elim

theorem sessionRecordAt_unpack_of_some (A : RustAlloc) (recPtr : BitVec 64)
    (rg : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hSome : r.currentSession.isSome) :
    sessionRecordAt A recPtr rg r ⊢
      ∃∗ newRecG : SessionGhost, ∃∗ newSs : Session (List (BitVec 8)),
        ⌜r = ⟨some newSs⟩ ∧ rg = ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ∧
          CanonSession newRecG newSs⌝ ∗
        CryptoVerification.E2E.Record.sessionRecordAt A recPtr
          ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ⟨some newSs⟩ := by
  refine Entails.trans (sessionRecordAt_entails_canonRecord_some A recPtr rg r hSome) ?_
  refine Entails.pure_left fun hCanon => ?_
  obtain ⟨newSs, hr⟩ := Option.isSome_iff_exists.mp hSome
  cases r with
  | mk cur =>
    dsimp only at hr
    subst hr
    cases rg with
    | mk prevCap prevPtr gcur =>
      cases gcur with
      | none =>
        exact sessionRecordAt_none_some_false A recPtr prevCap prevPtr newSs _
      | some newRecG =>
        unfold CanonRecord CanonCur toRecordGhost at hCanon
        dsimp only at hCanon
        refine Entails.sepExists_right newRecG
          (Entails.sepExists_right newSs
            (Entails.pure_right ⟨rfl, rfl, hCanon⟩ ?_))
        have heq := record_sessionRecordAt_eq A recPtr ⟨prevCap, prevPtr, some newRecG⟩ ⟨some newSs⟩
        dsimp only [toRecordGhost] at heq
        rw [heq]
        exact Entails.refl _

/-- Unpack `sessionRecordAt` under `InMemRecOk` into a canonical `SessionGhost` and
`Record.sessionRecordAt`. -/
theorem sessionRecordAt_unpack_of_inMemRecOk (A : RustAlloc) (recPtr : BitVec 64)
    (rg : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (hOk : InMemRecOk r) :
    sessionRecordAt A recPtr rg r ⊢
      ∃∗ newRecG : SessionGhost, ∃∗ newSs : Session (List (BitVec 8)),
        ⌜r = ⟨some newSs⟩ ∧ rg = ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ∧
          CanonSession newRecG newSs⌝ ∗
        CryptoVerification.E2E.Record.sessionRecordAt A recPtr
          ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ⟨some newSs⟩ :=
  sessionRecordAt_unpack_of_some A recPtr rg r hOk.2.2

theorem sessionRecordAt_pack (A : RustAlloc) (recPtr : BitVec 64)
    {rg : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {newRecG : SessionGhost} {newSs : Session (List (BitVec 8))}
    (hr : r = ⟨some newSs⟩)
    (hrg : rg = ⟨rg.prevCap, rg.prevPtr, some newRecG⟩) :
    CryptoVerification.E2E.Record.sessionRecordAt A recPtr
        ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ⟨some newSs⟩ ⊢
      sessionRecordAt A recPtr rg r := by
  have heq := record_sessionRecordAt_eq A recPtr ⟨rg.prevCap, rg.prevPtr, some newRecG⟩ ⟨some newSs⟩
  dsimp only [toRecordGhost] at heq
  rw [heq, ← hrg, ← hr]
  exact Entails.refl _

/-! ## Poll Closure Bridge Theorems -/

end CryptoVerification.E2E.InMem.SessionStoreImpl

