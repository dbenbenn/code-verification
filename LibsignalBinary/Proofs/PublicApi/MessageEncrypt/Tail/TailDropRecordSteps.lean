/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.RegChain
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sepWP_call_dropSs {prog : Program} {entry target_pc : BitVec 64} (ret_pc : BitVec 64)
    {A : RustAlloc} (hdrop : subroutine_ok prog entry (FromRecordCallees.dropSessionStructureLocal2Spec A))
    {ss sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hsp : s.sp = sp)
    (hP : P = (sessionStateAt A ss G st ∗ A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F)
    (hx0 : s.readReg64 .x0 = ss)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP prog target_pc sf
        ((memRegion ss 344 ∗ A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  subst hsp
  exact SepWP.call_framed_mut hdrop ⟨ss, G, st⟩ rfl (fun _ => rfl) hP hx0
    hpc hrun hsp_al hlr hnext

theorem stackAt_encSubStack_dropSs (sp : BitVec 64) :
    stackAt sp encSubStack =
      stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack)
          (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) := by
  have hd : FromRecordCallees.dropSessionStructureLocal2Stack = 4192 := rfl
  unfold stackAt
  rw [memRegion_split' (b := sp - BitVec.ofNat 64 encSubStack)
        (b' := sp - BitVec.ofNat 64 FromRecordCallees.dropSessionStructureLocal2Stack)
        (N := encSubStack)
        (n := encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack)
        (k := FromRecordCallees.dropSessionStructureLocal2Stack)
        (by decide)
        (by dsimp [encSubStack, withStoresEncStack, entryStack, encFrameSize, hd]; bv_omega)
        (by decide),
      sepConj_comm]

theorem scratch_has_50 {scratch : BitVec 64 → SepProp}
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (sp : BitVec 64) :
    ∃ S50 : SepProp,
      scratch sp = S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∧
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ⊢ memRegion sp 0x58) := by
  rcases hscr with rfl | rfl
  · refine ⟨memRegion sp 0x50, rfl, ?_⟩
    rw [memRegion_split' (b := sp) (b' := sp + 0x50#64) (N := 0x58) (n := 0x50) (k := 8)
          (by decide) (by bv_omega) (by decide)]
    exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)
  · refine ⟨memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗ memRegion (sp + 0x48#64) 8,
      by unfold cmScratch; ac_rfl, ?_⟩
    have h1 := pointsTo64_entails_memRegion (sp + 0x38#64) (sp + 0x288#64)
    have h2 := pointsTo64_entails_memRegion (sp + 0x40#64) (sp + 0x350#64)
    have h3 := pointsTo64_entails_memRegion (sp + 0x50#64) (sp + 0x128#64)
    have hjoin :
        memRegion sp 0x58 =
          (memRegion sp 0x38 ∗ (memRegion (sp + 0x38#64) 8 ∗
            (memRegion (sp + 0x40#64) 8 ∗ memRegion (sp + 0x48#64) 8))) ∗
          memRegion (sp + 0x50#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x38#64) (N := 0x58) (n := 0x38) (k := 0x20)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x38#64) (b' := sp + 0x40#64) (N := 0x20) (n := 8) (k := 0x18)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x40#64) (b' := sp + 0x48#64) (N := 0x18) (n := 8) (k := 0x10)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x48#64) (b' := sp + 0x50#64) (N := 0x10) (n := 8) (k := 8)
            (by decide) (by bv_omega) (by decide)]
      ac_rfl
    rw [hjoin]
    exact sepConj_mono
      (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) h3

theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

@[expose] def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]
  ac_rfl

@[expose] def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostTailAt A G.localIk ss ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      ((ss ↦₆₄ G.localIk.cap) ∗ sessionStateAfterLocalIk A ss G st) := by
  unfold sessionStateAt sessionStateAfterLocalIk
  rw [vecGhostAt_unfold_cap]
  ac_rfl

/-! ## Stepper lemmas from `+0x54c` (`1356`) and `+0x488` (`1160`) -/

theorem cur_none_weaken (sp : BitVec 64) :
    ((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336 ⊢
      memRegion (sp + 0x128#64) 0x158 := by
  rw [memRegion_split' (b := sp + 0x128#64) (b' := sp + 0x130#64) (N := 0x158) (n := 8) (k := 336)
        (by decide) (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem flag_memRegion_weaken (sp : BitVec 64) (b469 : BitVec 8) :
    memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ⊢
      memRegion (sp + 0x280#64) 0x1ea := by
  rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
        (by decide) (by bv_omega) (by decide)]
  exact sepConj_mono_right (pointsTo8_entails_memRegion _ _)

theorem otr_none_slots_eq (A : RustAlloc) (sp : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ otrSlotAt A sp none ∗ cmSlotAt A sp none =
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8) := by
  dsimp only [otrSlotAt, cmSlotAt]
  have hm :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 200 ∗ memRegion (sp + 0x350#64) 0x119) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x350#64) (N := 0x1e1) (n := 200) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hm]
  ac_rfl

theorem otrAt_weaken_vecU8At (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    otrAt A o pqCap pqPtr ot ⊢
      vecU8At A o pqCap pqPtr ot.pqrState ∗ memRegion (o + 0x18#64) 176 := by
  unfold otrAt
  refine sepConj_mono_right ?_
  have h1 := ProofLib.pointsToBytes_entails_memRegion (o + 0x18#64) ot.senderRatchetKey.publicKey.bytes.toList
  have h2 := ProofLib.pointsToBytes_entails_memRegion (o + 0x38#64) ot.senderRatchetKey.privateKey.bytes.toList
  have h3 := ProofLib.pointsToBytes_entails_memRegion (o + 0x58#64) ot.localIdentityKey.publicKey.bytes.toList
  have h4 := ProofLib.pointsToBytes_entails_memRegion (o + 0x78#64) ot.remoteIdentityKey.publicKey.bytes.toList
  rw [List.Vector.toList_length] at h1 h2 h3 h4
  have h5 := ProofLib.pointsToBytes_entails_memRegion (o + 0x98#64) (chainKeyBytes ot.senderChainKey)
  have hck_len : (chainKeyBytes ot.senderChainKey).length = 36 := by
    unfold chainKeyBytes leBytes CryptoGames.HMAC.keyToBytes32
    simp
  rw [hck_len] at h5
  have h6 := pointsTo32_entails_memRegion (o + 0xbc#64) ot.previousCounter
  have h7 := pointsTo8_entails_memRegion (o + 0xc0#64) ot.sessionVersion
  have hjoin :
      memRegion (o + 0x18#64) 176 =
        memRegion (o + 0x18#64) 32 ∗ (memRegion (o + 0x38#64) 32 ∗
          (memRegion (o + 0x58#64) 32 ∗ (memRegion (o + 0x78#64) 32 ∗
            (memRegion (o + 0x98#64) 36 ∗ (memRegion (o + 0xbc#64) 4 ∗
              (memRegion (o + 0xc0#64) 1 ∗ memRegion (o + 0xc1#64) 7)))))) := by
    rw [memRegion_split' (b := o + 0x18#64) (b' := o + 0x38#64) (N := 176) (n := 32) (k := 144)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x38#64) (b' := o + 0x58#64) (N := 144) (n := 32) (k := 112)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x58#64) (b' := o + 0x78#64) (N := 112) (n := 32) (k := 80)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x78#64) (b' := o + 0x98#64) (N := 80) (n := 32) (k := 48)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x98#64) (b' := o + 0xbc#64) (N := 48) (n := 36) (k := 12)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0xbc#64) (b' := o + 0xc0#64) (N := 12) (n := 4) (k := 8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0xc0#64) (b' := o + 0xc1#64) (N := 8) (n := 1) (k := 7)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4
    (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono_left h7))))))

theorem vecU8At_zero_weaken (A : RustAlloc) (v pqPtr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v 0#64 pqPtr bs ⊢
      (v ↦₆₄ 0#64) ∗ memRegion (v + 8#64) 16 := by
  unfold vecU8At vecHeader
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm]
  refine Entails.pure_left fun _ => ?_
  have h1 := pointsTo64_entails_memRegion (v + 8#64) pqPtr
  have h2 := pointsTo64_entails_memRegion (v + 16#64) (BitVec.ofNat 64 bs.length)
  have hm : memRegion (v + 8#64) 16 = memRegion (v + 8#64) 8 ∗ memRegion (v + 16#64) 8 := by
    rw [memRegion_split' (b := v + 8#64) (b' := v + 16#64) (N := 16) (n := 8) (k := 8)
          (by decide) (by bv_omega) (by decide)]
  rw [hm]
  exact sepConj_mono_right (sepConj_mono h1 h2)

theorem otr_zero_post_weaken (sp : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
      memRegion (sp + 0x350#64) 0x119 ⊢
    memRegion (sp + 0x280#64) 0x1e9 := by
  have h0 := pointsTo64_entails_memRegion (sp + 0x288#64) 0#64
  have hjoin :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 8 ∗
            (memRegion (sp + 0x290#64) 16 ∗
              (memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x290#64) (N := 0x1e1) (n := 8) (k := 0x1d9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x2a0#64) (N := 0x1d9) (n := 16) (k := 0x1c9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x2a0#64) (b' := sp + 0x350#64) (N := 0x1c9) (n := 176) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono_right (sepConj_mono_left h0)

theorem vecU8At_nz_weaken (A : RustAlloc) (v pqCap pqPtr : BitVec 64) (bs : List (BitVec 8))
    (hpq : pqCap ≠ 0#64) :
    vecU8At A v pqCap pqPtr bs ⊢
      (v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ memRegion (v + 16#64) 8 ∗
        A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat := by
  unfold vecU8At vecHeader
  have hpq' : pqCap ≠ 0 := hpq
  simp only [hpq', ↓reduceIte]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hle, _, _⟩ => ?_
  have hlen := pointsTo64_entails_memRegion (v + 16#64) (BitVec.ofNat 64 bs.length)
  have hbs := ProofLib.pointsToBytes_entails_memRegion pqPtr bs
  have hjoin :
      memRegion pqPtr bs.length ∗
        memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length) =
      memRegion pqPtr pqCap.toNat := by
    rw [← memRegion_split pqPtr bs.length (pqCap.toNat - bs.length) (by omega),
        Nat.add_sub_of_le hle]
  have hassoc :
      ((v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        (A.live pqPtr pqCap.toNat 1 ∗ (pqPtr ↦ₛ bs) ∗
          memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length)) =
      (v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live pqPtr pqCap.toNat 1 ∗
        ((pqPtr ↦ₛ bs) ∗
          memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length)) := by
    ac_rfl
  rw [hassoc, ← hjoin]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hlen (sepConj_mono_right (sepConj_mono_left hbs))))

theorem otr_nz_post_weaken (sp pqCap pqPtr : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
      ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
      memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119 ⊢
    memRegion (sp + 0x280#64) 0x1e9 := by
  have h0 := pointsTo64_entails_memRegion (sp + 0x288#64) pqCap
  have h1 := pointsTo64_entails_memRegion (sp + 0x290#64) pqPtr
  have hjoin :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 8 ∗
            (memRegion (sp + 0x290#64) 8 ∗
              (memRegion (sp + 0x298#64) 8 ∗
                (memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119)))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x290#64) (N := 0x1e1) (n := 8) (k := 0x1d9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x298#64) (N := 0x1d9) (n := 8) (k := 0x1d1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x298#64) (b' := sp + 0x2a0#64) (N := 0x1d1) (n := 8) (k := 0x1c9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x2a0#64) (b' := sp + 0x350#64) (N := 0x1c9) (n := 176) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono_right (sepConj_mono h0 (sepConj_mono_left h1))

/-! ## `SegExit` bridge theorems for `+0x55c`, `+0x54c`, `+0x488`, and `+0x46c` -/

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
