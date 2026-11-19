/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.ChainKeyCodeSym -- proof-setup: allow-public-import
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.Sep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.CodeLayout

public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "findReceiverChainKey_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    State.writeVReg128_setPC, State.writeVReg128_setPState, State.writeVReg128_setMem,
    arm64_norm, *]
  done))

/-! ## 1. Rodata & Address Helpers -/

open ProofLib.ProgramReflection

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range, List.range.loop, List.map]
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = (w >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = (w >>> 16).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = (w >>> 24).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
  unfold BitVec.extractLsb'
  rfl

private theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

/-! ## 2. `ratchetAt`, `chainAt`, and `optChainKeyAt` Exposure and Reassembly -/

@[expose] def vecBufRest_shared_lb {α : Type} (A : RustAlloc) (stride align : Nat)
    (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr (cap.toNat * stride) align ∗
     memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))

private theorem vecBuf_expose_arrayAt {α : Type} (A : RustAlloc) {stride : Nat}
    (align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    vecBuf A stride align elem cap ptr xs ⊢
      ⌜xs.length * stride < 2 ^ 63⌝ ∗
      arrayAt elem stride ptr xs ∗
      vecBufRest_shared_lb A stride align cap ptr xs := by
  unfold vecBuf vecBufRest_shared_lb
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hxs_lt : xs.length * stride < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right stride hlen) hlt
  have hp : xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil; simp only [↓reduceIte, arrayAt_nil]; bi_entail
  · simp only [hcap, ↓reduceIte]; bi_entail

private theorem vecBuf_reassemble_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    arrayAt elem stride ptr xs ∗ vecBufRest_shared_lb A stride align cap ptr xs ⊢
      vecBuf A stride align elem cap ptr xs := by
  unfold vecBuf vecBufRest_shared_lb
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
  have hp : xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 := ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil; simp only [↓reduceIte, arrayAt_nil]; bi_entail
  · simp only [hcap, ↓reduceIte]; bi_entail

@[expose] def ratchetTailRest (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) : SepProp :=
  ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
    st.maxForwardJumps < 2 ^ 64⌝ ∗
  (self ↦₆₄ G.chainsCap) ∗
  vecBufRest_shared_lb A 104 8 G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

theorem ratchetAt_expose_findIndex (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A self G st ⊢
      ⌜G.chains.length = st.receiverChains.length ∧
        (G.chains.zip st.receiverChains).length * 104 < 2 ^ 63⌝ ∗
      ((self + 8#64) ↦₆₄ G.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
      arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
      ratchetTailRest A self G st := by
  set cs := G.chains.zip st.receiverChains
  unfold ratchetAt vecAt vecHeader ratchetTailRest
  apply Entails.pure_left; rintro ⟨hchains_len, hpad, hmax⟩
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right
      (vecBuf_expose_arrayAt A 8 (chainAt A) G.chainsCap G.chainsPtr cs))) ?_
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcs_lt
  have hp1 : G.chains.length = st.receiverChains.length ∧ cs.length * 104 < 2 ^ 63 := ⟨hchains_len, hcs_lt⟩
  have hp2 : G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
      st.maxForwardJumps < 2 ^ 64 := ⟨hchains_len, hpad, hmax⟩
  bi_entail

theorem ratchetAt_reassemble_findIndex (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ((self + 8#64) ↦₆₄ G.chainsPtr) ∗
    ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
    arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
    ratchetTailRest A self G st ⊢
      ratchetAt A self G st := by
  set cs := G.chains.zip st.receiverChains
  unfold ratchetAt vecAt vecHeader ratchetTailRest
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
      (vecBuf_reassemble_arrayAt A 104 8 (chainAt A) G.chainsCap G.chainsPtr cs))))
  bi_entail

@[expose] def chainRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
    vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

theorem chainAt_eq_optChainKeyAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a = optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ chainRest A gc a := by
  unfold chainAt chainRest; sep_ac_rfl

@[expose] def optChainKeySomeRest (A : RustAlloc) (pin : VecPin) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
  A.live pin.ptr pin.cap.toNat 1 ∗
  memRegion (pin.ptr + 32#64) (pin.cap.toNat - 32) ∗
  memRegion (a + 28#64) 4

theorem optChainKeyAt_some_expose (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) a ⊢
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ pin.cap) ∗
      ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ 32#64) ∗
      ((a + 24#64) ↦₃₂ ck.index) ∗
      (pin.ptr ↦ₛ keyToBytes32 ck.key) ∗
      optChainKeySomeRest A pin a := by
  dsimp only [optChainKeyAt, vecU8At, vecHeader, optChainKeySomeRest]
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [hlen]
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨h32, hlt, hptr⟩
  have hcap : pin.cap ≠ 0 := by intro h0; rw [h0] at h32; simp at h32
  have hp : 32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0 := ⟨h32, hlt, hptr⟩
  simp only [hcap, ↓reduceIte]; bi_entail

theorem optChainKeyAt_some_reassemble (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    (a ↦₆₄ pin.cap) ∗
    ((a + 8#64) ↦₆₄ pin.ptr) ∗
    ((a + 16#64) ↦₆₄ 32#64) ∗
    ((a + 24#64) ↦₃₂ ck.index) ∗
    (pin.ptr ↦ₛ keyToBytes32 ck.key) ∗
    optChainKeySomeRest A pin a ⊢
      optChainKeyAt A pin (some ck) a := by
  dsimp only [optChainKeyAt, vecU8At, vecHeader, optChainKeySomeRest]
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [hlen]
  conv => lhs; simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨h32, hlt, hptr⟩
  have hcap : pin.cap ≠ 0 := by intro h0; rw [h0] at h32; simp at h32
  have hp : 32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0 := ⟨h32, hlt, hptr⟩
  simp only [hcap, ↓reduceIte]; bi_entail

@[expose] def optChainKeyNoneRest_shared_lb (a : BitVec 64) : SepProp :=
  memRegion (a + 80#64) 24

theorem chainAt_none_expose (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) (hnone : gc.2.chainKey = none) :
    chainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      optChainKeyNoneRest_shared_lb a ∗
      chainRest A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hnone]
  dsimp only [optChainKeyAt, optChainKeyNone, optChainKeyNoneRest_shared_lb]
  rw [show a + 72#64 + 8#64 = a + 80#64 by bv_omega]; sep_ac_rfl

theorem chainAt_some_expose (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) (hsome : gc.2.chainKey = some ck) :
    chainAt A gc a ⊢
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      optChainKeySomeRest A gc.1.ck (a + 72#64) ∗
      chainRest A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hsome]
  refine Entails.trans (sepConj_mono_left (optChainKeyAt_some_expose A gc.1.ck ck (a + 72#64))) ?_
  bi_entail

theorem chainAt_some_reassemble (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) (hsome : gc.2.chainKey = some ck) :
    ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
    ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
    ((a + 88#64) ↦₆₄ 32#64) ∗
    ((a + 96#64) ↦₃₂ ck.index) ∗
    (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
    optChainKeySomeRest A gc.1.ck (a + 72#64) ∗
    chainRest A gc a ⊢
      chainAt A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hsome]
  refine Entails.trans ?_ (sepConj_mono_left (optChainKeyAt_some_reassemble A gc.1.ck ck (a + 72#64)))
  bi_entail

/-! ## 3. Stack, Result Buffer, and Unaligned Copy Helpers -/

private theorem stackAt_findReceiverChainKeyStack (sp : BitVec 64) :
    stackAt sp findReceiverChainKeyStack =
      memRegion (sp - 2048#64) 944 ∗
      stackAt (sp - 80#64) 1024 ∗
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v29 : BitVec 64, (sp - 48#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 40#64) ↦₆₄ v30) ∗
      (∃∗ v21 : BitVec 64, (sp - 32#64) ↦₆₄ v21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  dsimp only [findReceiverChainKeyStack]; sep_interval_eq

private theorem stackAt_findReceiverChainKeyStack_repack (sp : BitVec 64) (v29 v30 v21 v20 v19 : BitVec 64) :
    memRegion (sp - 2048#64) 944 ∗
    stackAt (sp - 80#64) 1024 ∗
    memRegion (sp - 80#64) 32 ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 8 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp findReceiverChainKeyStack := by
  dsimp only [findReceiverChainKeyStack]; sep_interval

theorem sp_scratch32_unpack (sp : BitVec 64) :
    memRegion (sp - 80#64) 32 =
      (∃∗ s0 : BitVec 16, (sp - 80#64) ↦₁₆ s0) ∗
      (∃∗ s2 : BitVec 8, (sp - 78#64) ↦₈ s2) ∗
      (∃∗ s3 : BitVec 64, (sp - 77#64) ↦₆₄ s3) ∗
      memRegion (sp - 69#64) 5 ∗
      (∃∗ s16 : BitVec 64, (sp - 64#64) ↦₆₄ s16) ∗
      (∃∗ s24 : BitVec 8, (sp - 56#64) ↦₈ s24) ∗
      memRegion (sp - 55#64) 7 := by
  sep_interval_eq

theorem sp_scratch32_repack (sp : BitVec 64) (w0 : BitVec 64) (w8 : BitVec 16)
    (w10 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8) :
    ((sp - 80#64) ↦₆₄ w0) ∗
    ((sp - 72#64) ↦₁₆ w8) ∗
    ((sp - 70#64) ↦₈ w10) ∗
    memRegion (sp - 69#64) 5 ∗
    ((sp - 64#64) ↦₆₄ s16) ∗
    ((sp - 56#64) ↦₈ s24) ∗
    memRegion (sp - 55#64) 7 ⊢
      memRegion (sp - 80#64) 32 := by
  sep_interval

theorem mr_add_split (r : BitVec 64) (off n k off' nk : Nat)
    (hnk : n + k = nk) (hoff : off + n = off') (h : nk ≤ 2 ^ 64) :
    memRegion (r + BitVec.ofNat 64 off) nk =
      memRegion (r + BitVec.ofNat 64 off) n ∗ memRegion (r + BitVec.ofNat 64 off') k := by
  subst hnk hoff
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memRegion40_unpack_none (r : BitVec 64) :
    memRegion r 40 = (∃∗ t0 : BitVec 32, r ↦₃₂ t0) ∗ memRegion (r + 4#64) 36 := by
  sep_interval_eq

theorem memRegion40_unpack_err (r : BitVec 64) :
    memRegion r 40 =
      (∃∗ t0 : BitVec 32, r ↦₃₂ t0) ∗
      memRegion (r + 4#64) 4 ∗
      (∃∗ p0 : BitVec 64, (r + 8#64) ↦₆₄ p0) ∗
      (∃∗ l0 : BitVec 64, (r + 16#64) ↦₆₄ l0) ∗
      memRegion (r + 24#64) 16 := by
  sep_interval_eq

theorem memRegion40_unpack_some (r : BitVec 64) :
    memRegion r 40 =
      (∃∗ r0 : BitVec 32, r ↦₃₂ r0) ∗
      (∃∗ r4 : BitVec 32, (r + 4#64) ↦₃₂ r4) ∗
      (∃∗ r8 : BitVec 64, (r + 8#64) ↦₆₄ r8) ∗
      (∃∗ r16 : BitVec 16, (r + 16#64) ↦₁₆ r16) ∗
      (∃∗ r18 : BitVec 8, (r + 18#64) ↦₈ r18) ∗
      (∃∗ r19 : BitVec 32, (r + 19#64) ↦₃₂ r19) ∗
      (∃∗ r23 : BitVec 8, (r + 23#64) ↦₈ r23) ∗
      (∃∗ r24 : BitVec 16, (r + 24#64) ↦₁₆ r24) ∗
      (∃∗ r26 : BitVec 8, (r + 26#64) ↦₈ r26) ∗
      (∃∗ r27 : BitVec 64, (r + 27#64) ↦₆₄ r27) ∗
      (∃∗ r35 : BitVec 8, (r + 35#64) ↦₈ r35) ∗
      (∃∗ r36 : BitVec 32, (r + 36#64) ↦₃₂ r36) := by
  sep_interval_eq

private theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsToBytes_combine (a : BitVec 64) (xs ys : List (BitVec 8))
    {a' : BitVec 64} (ha : a + BitVec.ofNat 64 xs.length = a') :
    (a ↦ₛ xs) ∗ (a' ↦ₛ ys) = (a ↦ₛ (xs ++ ys)) := by
  subst ha
  exact (pointsToBytes_append a xs ys).symm

private theorem sp_11_repack_aux (a : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    (a ↦₁₆ v4) ∗ ((a + 2#64) ↦₈ v6) ∗ ((a + 3#64) ↦₆₄ v7) =
      (a ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((a + 8#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((a + 10#64) ↦₈ (v7.extractLsb' 56 8)) := by
  rw [pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack16 v4) [v6] (by rfl),
      pointsToBytes_combine a (unpack16 v4 ++ [v6]) (unpack64 v7) (by rfl)]
  rw [← sepConj_assoc,
      pointsToBytes_combine a (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4))
        (unpack16 (v7.extractLsb' 40 16)) (by rfl),
      pointsToBytes_combine a
        (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4) ++ unpack16 (v7.extractLsb' 40 16))
        [v7.extractLsb' 56 8] (by rfl)]
  congr 1
  simp only [unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem sp_11_repack (sp : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    ((sp - 80#64) ↦₁₆ v4) ∗ ((sp - 78#64) ↦₈ v6) ∗ ((sp - 77#64) ↦₆₄ v7) =
      ((sp - 80#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((sp - 72#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((sp - 70#64) ↦₈ (v7.extractLsb' 56 8)) := by
  have h78 : (sp - 80#64) + 2#64 = sp - 78#64 := by bv_omega
  have h77 : (sp - 80#64) + 3#64 = sp - 77#64 := by bv_omega
  have h72 : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
  have h70 : (sp - 80#64) + 10#64 = sp - 70#64 := by bv_omega
  rw [← h78, ← h77, ← h72, ← h70]
  exact sp_11_repack_aux (sp - 80#64) v4 v6 v7

theorem sp_11_repack_rest (sp : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 : BitVec 64) (R : SepProp) :
    ((sp - 80#64) ↦₁₆ v4) ∗ ((sp - 78#64) ↦₈ v6) ∗ ((sp - 77#64) ↦₆₄ v7) ∗ R =
      ((sp - 80#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((sp - 72#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((sp - 70#64) ↦₈ (v7.extractLsb' 56 8)) ∗ R := by
  have h := congrArg (· ∗ R) (sp_11_repack sp v4 v6 v7)
  simpa only [sepConj_assoc] using h

private theorem ret_11_repack (a : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    ((a + 8#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
    ((a + 16#64) ↦₁₆ (((v7 >>> 40).truncate 32).truncate 16)) ∗
    ((a + 18#64) ↦₈ ((BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8)) =
      ((a + 8#64) ↦₁₆ v4) ∗ ((a + 10#64) ↦₈ v6) ∗ ((a + 11#64) ↦₆₄ v7) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1,
      pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 8#64) (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4))
        (unpack16 (((v7 >>> 40).truncate 32).truncate 16)) (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 8#64)
        (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4) ++
          unpack16 (((v7 >>> 40).truncate 32).truncate 16))
        [(BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8] (by rw [BitVec.add_assoc]; rfl)]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 8#64) (unpack16 v4) [v6] (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 8#64) (unpack16 v4 ++ [v6]) (unpack64 v7) (by rw [BitVec.add_assoc]; rfl)]
  congr 1
  simp only [unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

private theorem ret_8_repack (a : BitVec 64) (v15 : BitVec 64) :
    ((a + 19#64) ↦₃₂ (v15.truncate 32)) ∗
    ((a + 23#64) ↦₈ ((v15 >>> 32).truncate 8)) ∗
    ((a + 24#64) ↦₁₆ (((v15 >>> 40).truncate 32).truncate 16)) ∗
    ((a + 26#64) ↦₈ ((BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8)) =
      ((a + 19#64) ↦₆₄ v15) := by
  rw [pointsTo32_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1,
      pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 19#64) (unpack32 (v15.truncate 32))
        [((v15 >>> 32).truncate 8)] (by rw [BitVec.add_assoc]; rfl),
      ← sepConj_assoc,
      pointsToBytes_combine (a + 19#64)
        (unpack32 (v15.truncate 32) ++ [((v15 >>> 32).truncate 8)])
        (unpack16 (((v15 >>> 40).truncate 32).truncate 16)) (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 19#64)
        (unpack32 (v15.truncate 32) ++ [((v15 >>> 32).truncate 8)] ++
          unpack16 (((v15 >>> 40).truncate 32).truncate 16))
        [(BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8] (by rw [BitVec.add_assoc]; rfl)]
  congr 1
  simp only [unpack32, unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

@[expose] def findReceiverChainKeyKeyChunks (a : BitVec 64) (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v4) ∗ ((a + 6#64) ↦₈ v6) ∗
  ((a + 7#64) ↦₆₄ v7) ∗ ((a + 15#64) ↦₆₄ v15) ∗
  ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

namespace FindReceiverChainKeyFacts

theorem unpack32_16_8_eq (w0 : BitVec 64) :
    unpack32 (w0.extractLsb' 0 32) ++ unpack16 (w0.extractLsb' 32 16) ++ [w0.extractLsb' 48 8] =
      [w0.extractLsb' 0 8, w0.extractLsb' 8 8, w0.extractLsb' 16 8, w0.extractLsb' 24 8,
       w0.extractLsb' 32 8, w0.extractLsb' 40 8, w0.extractLsb' 48 8] := by
  simp only [unpack32, unpack16, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem unpack64_shift8 (lo hi : BitVec 64) :
    unpack64 (hi.extractLsb' 0 56 ++ lo.extractLsb' 56 8) =
      [lo.extractLsb' 56 8, hi.extractLsb' 0 8, hi.extractLsb' 8 8, hi.extractLsb' 16 8,
       hi.extractLsb' 24 8, hi.extractLsb' 32 8, hi.extractLsb' 40 8, hi.extractLsb' 48 8] := by
  simp only [unpack64, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem findReceiverChainKeyResultAt_some_perm (p0 p4 p8 p16 p18 p19 p23 p24 p26 p27 p35 p36 p8' p10' p11' p19' : SepProp)
    (h11 : p8 ∗ p16 ∗ p18 = p8' ∗ p10' ∗ p11')
    (h8 : p19 ∗ p23 ∗ p24 ∗ p26 = p19') :
    p0 ∗ p4 ∗ p8 ∗ p16 ∗ p18 ∗ p19 ∗ p23 ∗ p24 ∗ p26 ∗ p27 ∗ p35 ∗ p36 =
      p0 ∗ ((p4 ∗ p8' ∗ p10' ∗ p11' ∗ p19' ∗ p27 ∗ p35) ∗ p36) := by
  have h1 : p8 ∗ (p16 ∗ (p18 ∗ (p19 ∗ (p23 ∗ (p24 ∗ (p26 ∗ (p27 ∗ (p35 ∗ p36)))))))) =
      p8' ∗ (p10' ∗ (p11' ∗ (p19' ∗ (p27 ∗ (p35 ∗ p36))))) := by
    have := congrArg₂ (· ∗ ·) h11 (congrArg (· ∗ (p27 ∗ (p35 ∗ p36))) h8)
    simpa only [sepConj_assoc] using this
  simpa only [sepConj_assoc] using congrArg (fun X => p0 ∗ (p4 ∗ X)) h1

end FindReceiverChainKeyFacts

theorem cells4_eq_findReceiverChainKeyKeyChunks (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) =
      findReceiverChainKeyKeyChunks a
        (w0.extractLsb' 0 32)
        (w0.extractLsb' 32 16)
        (w0.extractLsb' 48 8)
        (w1.extractLsb' 0 56 ++ w0.extractLsb' 56 8)
        (w2.extractLsb' 0 56 ++ w1.extractLsb' 56 8)
        (w3.extractLsb' 0 56 ++ w2.extractLsb' 56 8)
        (w3.extractLsb' 56 8) := by
  unfold findReceiverChainKeyKeyChunks
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo16_eq_pointsToBytes,
      pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack64 w0) (unpack64 w1) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a (unpack64 w0 ++ unpack64 w1) (unpack64 w2) (by rfl),
      pointsToBytes_combine a (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2) (unpack64 w3) (by rfl)]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack32 (w0.extractLsb' 0 32)) (unpack16 (w0.extractLsb' 32 16)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ [w0.extractLsb' 48 8] (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w1.extractLsb' 0 56 ++ w0.extractLsb' 56 8)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w2.extractLsb' 0 56 ++ w1.extractLsb' 56 8)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w3.extractLsb' 0 56 ++ w2.extractLsb' 56 8)) (by rfl),
      pointsToBytes_combine a _ [w3.extractLsb' 56 8] (by rfl)]
  rw [FindReceiverChainKeyFacts.unpack32_16_8_eq w0, FindReceiverChainKeyFacts.unpack64_shift8 w0 w1, FindReceiverChainKeyFacts.unpack64_shift8 w1 w2, FindReceiverChainKeyFacts.unpack64_shift8 w2 w3]
  rfl

theorem exists_findReceiverChainKeyKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
      (v7 v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = findReceiverChainKeyKeyChunks a v0 v4 v6 v7 v15 v23 v31 := by
  obtain ⟨w0, w1, w2, w3, _, hw⟩ := exists_unpack64_of_length_32 h
  exact ⟨_, _, _, _, _, _, _, fun a => (hw a).trans (cells4_eq_findReceiverChainKeyKeyChunks a w0 w1 w2 w3)⟩

theorem findReceiverChainKeyResultAt_some_repack (r : BitVec 64) (ck : ChainKey)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8)
    (hkey : ∀ a : BitVec 64, (a ↦ₛ keyToBytes32 ck.key) = findReceiverChainKeyKeyChunks a v0 v4 v6 v7 v15 v23 v31) :
    (r ↦₃₂ 1#32) ∗
    ((r + 4#64) ↦₃₂ v0) ∗
    ((r + 8#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
    ((r + 16#64) ↦₁₆ (((v7 >>> 40).truncate 32).truncate 16)) ∗
    ((r + 18#64) ↦₈ ((BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8)) ∗
    ((r + 19#64) ↦₃₂ (v15.truncate 32)) ∗
    ((r + 23#64) ↦₈ ((v15 >>> 32).truncate 8)) ∗
    ((r + 24#64) ↦₁₆ (((v15 >>> 40).truncate 32).truncate 16)) ∗
    ((r + 26#64) ↦₈ ((BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8)) ∗
    ((r + 27#64) ↦₆₄ v23) ∗
    ((r + 35#64) ↦₈ v31) ∗
    ((r + 36#64) ↦₃₂ ck.index) =
      findReceiverChainKeyResultAt r (.ok (some ck)) := by
  dsimp only [findReceiverChainKeyResultAt]
  rw [pointsToBytes_chainKeyBytes_eq (r + 4#64) ck,
      show r + 4#64 + 32#64 = r + 36#64 by bv_omega,
      hkey (r + 4#64)]
  unfold findReceiverChainKeyKeyChunks
  rw [show r + 4#64 + 4#64 = r + 8#64 by bv_omega,
      show r + 4#64 + 6#64 = r + 10#64 by bv_omega,
      show r + 4#64 + 7#64 = r + 11#64 by bv_omega,
      show r + 4#64 + 15#64 = r + 19#64 by bv_omega,
      show r + 4#64 + 23#64 = r + 27#64 by bv_omega,
      show r + 4#64 + 31#64 = r + 35#64 by bv_omega]
  exact FindReceiverChainKeyFacts.findReceiverChainKeyResultAt_some_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ret_11_repack r v4 v6 v7) (ret_8_repack r v15)

theorem findReceiverChainKeyResultAt_err_repack (r p : BitVec 64) :
    (r ↦₃₂ 2#32) ∗
    memRegion (r + 4#64) 4 ∗
    ((r + 8#64) ↦₆₄ p) ∗
    ((r + 16#64) ↦₆₄ 26#64) ∗
    memRegion (r + 24#64) 16 ∗
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ⊢
      findReceiverChainKeyResultAt r (.error (.invalidSessionStructure .missingReceiverChainKey)) := by
  dsimp only [findReceiverChainKeyResultAt, strRefAt]
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length = 26#64 := by rfl_kernel
  rw [hlen, show r + 8#64 + 8#64 = r + 16#64 by bv_omega]; bi_entail

/-! ## 4. Pure Model & Subroutine Helpers -/

theorem zip_map_snd {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (xs.zip ys).map (·.2) = ys
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [List.zip_cons_cons, zip_map_snd xs ys h]

theorem zip_length_eq {α β : Type} {xs : List α} {ys : List β}
    (h : xs.length = ys.length) :
    (xs.zip ys).length = ys.length := by
  simp [List.length_zip, h]

theorem findIdx_q_go_lt_shared_lb {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k idx : Nat), List.findIdx?.go p xs k = some idx → idx < k + xs.length
  | [], _, _, h => by simp [List.findIdx?.go] at h
  | _ :: xs, k, idx, h => by
    simp only [List.findIdx?.go] at h
    split at h
    · injection h with h; subst h; simp only [List.length_cons]; omega
    · have ih := findIdx_q_go_lt_shared_lb p xs (k + 1) idx h
      simp only [List.length_cons]; omega

theorem findReceiverChainIndex_lt {st : RatchetState} {their : PublicKey} {idx : Nat}
    (h : st.findReceiverChainIndex their = some idx) :
    idx < st.receiverChains.length := by
  unfold RatchetState.findReceiverChainIndex List.findIdx? at h
  have := findIdx_q_go_lt_shared_lb (fun c => c.senderRatchetKey == their) st.receiverChains 0 idx h
  omega

theorem receiverChains_getElem?_eq_zip_snd {G : RatchetGhost} {st : RatchetState}
    (hlen : G.chains.length = st.receiverChains.length)
    {idx : Nat} (hidx : idx < (G.chains.zip st.receiverChains).length) :
    st.receiverChains[idx]? = some ((G.chains.zip st.receiverChains)[idx]).2 := by
  have hidx' : idx < st.receiverChains.length := by rwa [zip_length_eq hlen] at hidx
  rw [List.getElem?_eq_getElem hidx']
  simp [List.getElem_zip]

theorem findReceiverChainKey_of_none {st : RatchetState} {their : PublicKey}
    (h : st.findReceiverChainIndex their = none) :
    st.findReceiverChainKey their = .ok none := by
  simp [RatchetState.findReceiverChainKey, h]

theorem findReceiverChainKey_of_some_none {G : RatchetGhost} {st : RatchetState}
    {their : PublicKey} {idx : Nat}
    (hlen : G.chains.length = st.receiverChains.length)
    (hfind : st.findReceiverChainIndex their = some idx)
    (hidx : idx < (G.chains.zip st.receiverChains).length)
    (hck : ((G.chains.zip st.receiverChains)[idx]).2.chainKey = none) :
    st.findReceiverChainKey their =
      .error (.invalidSessionStructure .missingReceiverChainKey) := by
  unfold RatchetState.findReceiverChainKey
  rw [hfind]; dsimp only; rw [receiverChains_getElem?_eq_zip_snd hlen hidx]; dsimp only; rw [hck]

theorem findReceiverChainKey_of_some_some {G : RatchetGhost} {st : RatchetState}
    {their : PublicKey} {idx : Nat} {ck : ChainKey}
    (hlen : G.chains.length = st.receiverChains.length)
    (hfind : st.findReceiverChainIndex their = some idx)
    (hidx : idx < (G.chains.zip st.receiverChains).length)
    (hck : ((G.chains.zip st.receiverChains)[idx]).2.chainKey = some ck) :
    st.findReceiverChainKey their = .ok (some ck) := by
  unfold RatchetState.findReceiverChainKey
  rw [hfind]; dsimp only; rw [receiverChains_getElem?_eq_zip_snd hlen hidx]; dsimp only; rw [hck]

@[local arm64_norm]
theorem mul_104_eq (i : Nat) :
    BitVec.ofNat 64 i * 104#64 = BitVec.ofNat 64 (i * 104) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, BitVec.toNat_ofNat]

@[local arm64_norm]
theorem setWidth_32_16_of_64 (v : BitVec 16) :
    ((BitVec.setWidth 64 v).setWidth 32).setWidth 16 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_32_8_of_64 (v : BitVec 8) :
    ((BitVec.setWidth 64 v).setWidth 32).setWidth 8 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_16_of_64 (v : BitVec 16) :
    (BitVec.setWidth 64 v).setWidth 16 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_8_of_64 (v : BitVec 8) :
    (BitVec.setWidth 64 v).setWidth 8 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_32_of_64 (v : BitVec 32) :
    (BitVec.setWidth 64 v).setWidth 32 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_16_of_32 (v : BitVec 16) :
    (BitVec.setWidth 32 v).setWidth 16 = v := by bv_bits

@[local arm64_norm]
private theorem setWidth_8_of_32 (v : BitVec 8) :
    (BitVec.setWidth 32 v).setWidth 8 = v := by bv_bits

theorem len_ule_idx_false {i n : Nat} (hi : i < n) (hn : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
  exact decide_eq_false (by omega)

private theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left; intro hp; rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem SepWPp.conseq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem SepWPp_eq_pre_shared_lb {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h
private abbrev SepWPp.eq_pre := @SepWPp_eq_pre_shared_lb

namespace FindReceiverChainKeyFacts

theorem ratchet_reassemble_chain {P8 P16 Ch Chain Rest Tail Rat : SepProp}
    (hch : Ch ⊢ Chain)
    (hrat : P8 ∗ P16 ∗ (Chain ∗ Rest) ∗ Tail ⊢ Rat) :
    P8 ∗ P16 ∗ Ch ∗ Rest ∗ Tail ⊢ Rat := by
  refine Entails.trans ?_ hrat
  rw [sepConj_assoc Chain Rest Tail]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hch))

theorem stack_reassemble_scr {M944 S1024 Scr M32 Rest Stk : SepProp}
    (hscr : Scr ⊢ M32)
    (hstk : M944 ∗ S1024 ∗ M32 ∗ Rest ⊢ Stk) :
    M944 ∗ S1024 ∗ Scr ∗ Rest ⊢ Stk :=
  Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))) hstk

end FindReceiverChainKeyFacts

/-! ## 5. Main Proof -/

attribute [local irreducible] Program.fnOff

@[expose] def findReceiverChainKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec FindReceiverChainKeyGhost where
  pre := fun x s =>
    ⌜LibsignalRoLoaded lsmpl s.mem ∧
      s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
    ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp findReceiverChainKeyStack
  post := fun x s0 sf =>
    ⌜LibsignalRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace⌝ ∗
    ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
    findReceiverChainKeyResultAt x.ret (x.st.findReceiverChainKey x.their) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findReceiverChainKeyStack

private theorem sepWPp_seq_lscl_ro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem ∧ LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen
    (fun (m _ : Memory) (hf : LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m) hkf =>
      ⟨hf.1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hf.2 hkf⟩)
    ⟨hcl, hro⟩
    h

private theorem sepWPp_intro_rodata_missingReceiverChainKey_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.297") ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.297") ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact lsro_intro_chk hro (by decide +kernel) hm
  exact h R hm' hL

private theorem findIndex_placed_ok_at_state [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok prog addr (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (FindReceiverChainIndex.findPlacedSpec A).post } := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded, FindReceiverChainIndex.findPlacedSpec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hx0, hx1, hx2, hlt⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hlt, hsp⟩, hspatial⟩

set_option maxHeartbeats 1600000 in
theorem find_receiver_chain_key_placed_ok_of_find_index [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hfind : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A))) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [findReceiverChainKeyPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hro0, hx0, hx1, hx8⟩, hmem⟩
  refine ⟨ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findReceiverChainKeyStack, R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  apply SepWPp.conseq_pre (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hcs_lt⟩ => ?_
  set cs := x.G.chains.zip x.st.receiverChains
  have hcs_toNat : (BitVec.ofNat 64 cs.length).toNat = cs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [stackAt_findReceiverChainKeyStack s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v29 => ?_
  apply sepWPp_seq_lscl_ro (mid := lsmpl.base 26) hcl0 hro0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro ⟨hcl1, hro1⟩
  have hfind1 := findIndex_placed_ok_at_state hfind hcl1
  apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 44#64) hcl1 hro1
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro ⟨hcl2, hro2⟩
  have hmap_cs : cs.map (·.2) = x.st.receiverChains :=
    zip_map_snd x.G.chains x.st.receiverChains hchains_len
  have hidx_post : match x.st.findReceiverChainIndex x.their with
      | some i => sf.readReg64 (Reg.gpr 0#5) = 1#64 ∧ (sf.readReg64 (Reg.gpr 1#5)).toNat = i
      | none => sf.readReg64 (Reg.gpr 0#5) = 0#64 := by
    have h := hpost; rw [hmap_cs] at h; exact h
  cases hfind_res : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hfind_res] at hidx_post; dsimp only at hidx_post
    rw [memRegion40_unpack_none x.ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun t0 => ?_
    apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro ⟨_, hro3⟩
    refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    rw [findReceiverChainKey_of_none hfind_res]; dsimp only [findReceiverChainKeyResultAt]
    refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
    have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
    refine Entails.trans ?_
      (sepConj_mono hrat (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    dsimp only [cs, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; bi_entail
  | some i =>
    rw [hfind_res] at hidx_post; rcases hidx_post with ⟨hx0_1, hx1_1⟩
    have hi_rc : i < x.st.receiverChains.length := findReceiverChainIndex_lt hfind_res
    have hi : i < cs.length := by rwa [zip_length_eq hchains_len]
    have hx1_eq : sf.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hule : (BitVec.ofNat 64 cs.length).ule (BitVec.ofNat 64 i) = false :=
      len_ule_idx_false hi hcs_lt
    rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi]
    set elemAddr := x.G.chainsPtr + BitVec.ofNat 64 (i * 104)
    cases hck : cs[i].2.chainKey with
    | none =>
      rw [chainAt_none_expose A cs[i] elemAddr hck, memRegion40_unpack_err x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun p0 =>
        SepWPp.exists_elim fun t0 => ?_
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨_, hro3⟩
      apply sepWPp_intro_rodata_missingReceiverChainKey_placed hro3
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_none hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have herr := findReceiverChainKeyResultAt_err_repack x.ret (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.297")
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi,
          chainAt_none_expose A cs[i] elemAddr hck] at hrat
      refine Entails.trans ?_
        (sepConj_mono hrat (sepConj_mono_right (sepConj_mono herr (sepConj_mono_right hstk))))
      dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; bi_entail
    | some ck =>
      apply SepWPp.conseq_pre
        (sepConj_mono_left (sepConj_mono_left (chainAt_some_expose A cs[i] ck elemAddr hck)))
      apply SepWPp.eq_pre (by simp only [sepConj_assoc]; rfl)
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hcap_lt
      have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
      obtain ⟨v0, v4, v6, v7, v15, v23, v31, hkey⟩ :=
        exists_findReceiverChainKeyKeyChunks_of_length_32 hlen_key
      rw [hkey cs[i].1.ck.ptr]; unfold findReceiverChainKeyKeyChunks
      rw [sp_scratch32_unpack s0.sp, memRegion40_unpack_some x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun r36 => SepWPp.exists_elim fun r35 =>
        SepWPp.exists_elim fun r27 => SepWPp.exists_elim fun r26 =>
        SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r23 =>
        SepWPp.exists_elim fun r19 => SepWPp.exists_elim fun r18 =>
        SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r8 =>
        SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r0 =>
        SepWPp.exists_elim fun s24 => SepWPp.exists_elim fun s16 =>
        SepWPp.exists_elim fun s3 => SepWPp.exists_elim fun s2 =>
        SepWPp.exists_elim fun s0_scr => ?_
      apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 156#64) hcl2 hro2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨hcl3, hro3⟩
      apply SepWPp.eq_pre (by simp only [sepConj_assoc, sp_11_repack_rest s0.sp v4 v6 v7]; rfl)
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl3 hro3
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨_, hro4⟩
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_some hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro4, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have hres := findReceiverChainKeyResultAt_some_repack x.ret ck v0 v4 v6 v7 v15 v23 v31 hkey
      have hscr := sp_scratch32_repack s0.sp
        (v7.extractLsb' 0 40 ++ v6 ++ v4) (v7.extractLsb' 40 16) (v7.extractLsb' 56 8) v23 v31
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      have hch := chainAt_some_reassemble A cs[i] ck elemAddr hck
      rw [hkey cs[i].1.ck.ptr] at hch; unfold findReceiverChainKeyKeyChunks at hch
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi] at hrat
      have hrat' := FindReceiverChainKeyFacts.ratchet_reassemble_chain hch hrat
      have hstk' := FindReceiverChainKeyFacts.stack_reassemble_scr hscr hstk
      rw [← hres]
      refine Entails.trans ?_
        (sepConj_mono hrat' (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk'))))
      dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; bi_entail

theorem find_receiver_chain_key_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) :=
  find_receiver_chain_key_placed_ok_of_find_index
    (ls_subroutine_ok_of_block (find_receiver_chain_index_placed_ok A h_bb))

end CryptoVerification.LibsignalTripleRatchet
