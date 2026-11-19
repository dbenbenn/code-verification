/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `MessageEncrypt` `save_identity` Segment (`segSave_ok`)

Verifies `SaveStateV → ApplyStateV` (`+0xbd4..+0xc14`, `+0xd50..+0xd9c`): invokes the async
`save_identity` shim, poll, future drop, and box deallocation, transitioning to `ApplyStateV` on
`Ok c` or exiting via `tailStoreHookErr_ok` (`+0xe28`) on `Err`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
theorem cs_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x24 = s0.readReg64 .x24 := h.2.2.2.2.2.1
theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## Basic-Block Stepping Lemmas (`+0xbd4..+0xd9c`) -/

@[expose] def savePollRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 6 ∗
  memRegion (sp + 0x480#64) 0x100 ∗
  memRegion (sp + 0x5b0#64) 0x3e0 ∗
  memRegion (sp + 0x9a8#64) 0x1d8

theorem savePoll_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x990#64) 24 ∗
      savePollRest sp := by
  unfold savePollRest
  rw [show (0x716 : Nat) = 6 + 0x710 by decide,
      memRegion_split (sp + 0x46a#64) 6 0x710 (by decide),
      show (0x710 : Nat) = 16 + 0x700 by decide,
      memRegion_split _ 16 0x700 (by decide),
      show (0x700 : Nat) = 0x100 + 0x600 by decide,
      memRegion_split _ 0x100 0x600 (by decide),
      show (0x600 : Nat) = 48 + 0x5d0 by decide,
      memRegion_split _ 48 0x5d0 (by decide),
      show (0x5d0 : Nat) = 0x3e0 + 0x1f0 by decide,
      memRegion_split _ 0x3e0 0x1f0 (by decide),
      show (0x1f0 : Nat) = 24 + 0x1d8 by decide,
      memRegion_split _ 24 0x1d8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem savePoll_merge_990 (sp w3 w4 w5 : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x990#64) ↦₆₄ w3) ∗ ((sp + 0x998#64) ↦₆₄ w4) ∗ ((sp + 0x9a0#64) ↦₆₄ w5)) ∗
      savePollRest sp ⊢
    pollWith sp 0x990 [w3, w4, w5] := by
  unfold pollWith savePollRest
  dsimp only [words64At, List.length]
  change _ ⊢ memRegion (sp + 0x46a#64) 0x526 ∗
    (((sp + 0x990#64) ↦₆₄ w3) ∗ ((sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
      ((sp + 0x990#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ emp) ∗
    memRegion (sp + 0x9a8#64) 0x1d8
  rw [show (0x526 : Nat) = 6 + (16 + (0x100 + (48 + 0x3e0))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 0x100 _ (by decide),
      memRegion_split _ 48 0x3e0 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq

@[expose] def savePassive (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗
  cmScratchRest sp ∗
  encSpillsRest ss_vt id_vt sp x ∗
  savePollRest sp ∗
  memRegion x.ret 248 ∗
  encCommonRest A ctl x draws s0

abbrev savePollOutHead (base out : BitVec 64) (ans : Except Unit IdentityChange) : SepProp :=
  match ans with
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 4
  | .error () =>
    (out ↦₆₄ 0x800000000000001A#64) ∗
      ((out + 8#64) ↦₆₄ base)

/-- Normalizes `savePollOutAt` after `ikit.savePoll` into six 64-bit words at `sp + 0x580`. -/
theorem savePollOut_words (b out : BitVec 64) (ans : Except Unit IdentityChange) :
    savePollOutAt b out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        match ans with
        | .ok c => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
            w1.setWidth 32 = (if c == .replacedExisting then 1#32 else 0#32) ∧ H = emp
        | .error () =>
          w0 = 0x800000000000001A#64 ∧ w1 = b ∧
          w2 = 10#64 ∧ w3 = 1#64 ∧ w4 = b + 16#64 ∧
          H = (b ↦ᵣ storeHookStr)⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | c
  · dsimp only [savePollOutAt, errTailAt]
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 ?_
    refine Entails.sepExists_right b ?_
    refine Entails.sepExists_right 10#64 ?_
    refine Entails.sepExists_right 1#64 ?_
    refine Entails.sepExists_right (b + 16#64) ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right (b ↦ᵣ storeHookStr) ?_
    refine Entails.pure_right ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [savePollOutAt]
    rw [show (36 : Nat) = 4 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split (out + 0xc#64) 4 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 8 (by decide),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64 + 8#64 + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => ?_
    have h32 := pointsTo32_memRegion4_exists_word64 (out + 8#64)
      (if c == .replacedExisting then 1#32 else 0#32)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
    have hreord :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          (memRegion (out + 0xc#64) 4 ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
            ((out + 0x28#64) ↦₆₄ w5)) =
        (((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          memRegion (out + 0xc#64) 4) ∗
        ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
          ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
          ((out + 0x28#64) ↦₆₄ w5)) := by ac_rfl
    rw [hreord]
    refine Entails.trans (sepConj_mono_left h32) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w1 => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hw1 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64 ?_
    refine Entails.sepExists_right w1 ?_
    refine Entails.sepExists_right w2 ?_
    refine Entails.sepExists_right w3 ?_
    refine Entails.sepExists_right w4 ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right emp ?_
    refine Entails.pure_right ⟨Or.inl rfl, rfl, hw1, rfl⟩ ?_
    rw [sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-! ## Shim, Poll, and Deallocation Path (`+0xbd4..+0xd94`) -/

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
