/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tag-7 Leaf (`mergeFieldGenReceiverChains_ok`) for `SessionStructure::merge_field`

Proves `mergeFieldGenReceiverChains_ok` for `receiver_chains` (tag `7`), decoding a `Chain` message
on the stack via `message::merge<Chain>` and pushing it into `Vec<Chain>` at `ss + 0x48` (calling
`RawVec<Chain>::grow_one` when `len = cap`).
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

/-! ## Field and `prostChainGAt` Helpers -/

theorem eq_recv_of_tag_eq_7 {fld : GenField} (h : fld.tag = 7) :
    ∃ c : ChainG, fld = .recv c := by
  cases fld <;> simp [GenField.tag] at h
  exact ⟨_, rfl⟩

theorem vecOf104_msgKey_nil_0_8 (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ⊢
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold vecOf vecAt vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm (vecHeader v 0#64 8#64 0#64)]
  exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)

theorem prostChainGAt_default_of_cells (A : RustAlloc) (sp0 : BitVec 64) :
    (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
      ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
      ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
      ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
      memRegion (sp0 - 152#64) 24 ⊢
    prostChainGAt A (sp0 - 232#64) ChainG.empty := by
  unfold prostChainGAt ChainG.empty
  dsimp only
  have e1 : (sp0 - 232#64) + 8#64 = sp0 - 224#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 232#64) + 16#64 = sp0 - 216#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 232#64) + 0x18#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 208#64) + 8#64 = sp0 - 200#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 208#64) + 16#64 = sp0 - 192#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e6 : (sp0 - 232#64) + 0x30#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e7 : (sp0 - 184#64) + 8#64 = sp0 - 176#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e8 : (sp0 - 184#64) + 16#64 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e9 : (sp0 - 232#64) + 0x48#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e10 : (sp0 - 232#64) + 0x50#64 = sp0 - 152#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e3, e6, e9, e10]
  have h1 := vecU8_nil_0_1_receiverChains A (sp0 - 232#64)
  rw [e1, e2] at h1
  have h2 := vecU8_nil_0_1_receiverChains A (sp0 - 208#64)
  rw [e4, e5] at h2
  have h3 := vecOf104_msgKey_nil_0_8 A (sp0 - 184#64)
  rw [e7, e8] at h3
  have hgrp :
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗
        ((sp0 - 216#64) ↦₆₄ 0#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64) ∗
        ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗
        ((sp0 - 168#64) ↦₆₄ 0#64) ∗ ((sp0 - 160#64) ↦₆₄ noneCap)) ∗
        memRegion (sp0 - 152#64) 24 =
      (((sp0 - 232#64) ↦₆₄ 0#64) ∗ ((sp0 - 224#64) ↦₆₄ 1#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 1#64) ∗ ((sp0 - 192#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((sp0 - 176#64) ↦₆₄ 8#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64)) ∗
      (((sp0 - 160#64) ↦₆₄ noneCap) ∗ memRegion (sp0 - 152#64) 24) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _)))

theorem prostChainGAt_default_of_cells_lit (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) ∗
    ((sp0 - 224#64) ↦₆₄ 1#64) ∗
    ((sp0 - 216#64) ↦₆₄ 0#64) ∗
    ((sp0 - 208#64) ↦₆₄ 0#64) ∗
    ((sp0 - 200#64) ↦₆₄ 1#64) ∗
    ((sp0 - 192#64) ↦₆₄ 0#64) ∗
    ((sp0 - 184#64) ↦₆₄ 0#64) ∗
    ((sp0 - 176#64) ↦₆₄ 8#64) ∗
    ((sp0 - 168#64) ↦₆₄ 0#64) ∗
    ((sp0 - 160#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
    memRegion (sp0 - 152#64) 24 ⊢
    prostChainGAt A0 (sp0 - 232#64) ChainG.empty := by
  simpa only [noneCap, sepConj_assoc] using prostChainGAt_default_of_cells A0 sp0

theorem vecOf104_msgKey_move_bytes (A : RustAlloc) (keys : List MessageKeyGenerator) (a : BitVec 64) :
    vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a keys ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b keys⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a cap ptr keys]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 keys.length)) ?_
  refine Entails.sepExists_right (vecBuf A 104 8 (fun mk b => prostMsgKeyAt A mk b) cap ptr keys) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b cap ptr keys]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem prostChainGAt_eq_parts (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
      prostCkAt_receiverChains A (a + 0x48#64) c.ck := by
  unfold prostChainGAt prostCkAt_receiverChains
  have e50 : a + 0x48#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e60 : a + 0x48#64 + 0x18#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
  have e64 : a + 0x48#64 + 0x1c#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
  cases c.ck with
  | none =>
    dsimp only
    rw [e50]
  | some ik =>
    rcases ik with ⟨i, k⟩
    dsimp only
    rw [e60, e64]

theorem prostChainGAt_move_bytes (A : RustAlloc) (c : ChainG) (a : BitVec 64) :
    prostChainGAt A a c ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk)
    (P2 := fun b => vecU8 A b c.priv)
    (n1 := 24) (n2 := 24) (off := 0x18#64) rfl
    (fun b => vecU8_move_bytes_receiverChains A b c.srk)
    (fun b => vecU8_move_bytes_receiverChains A b c.priv)
  have h123 := move_bytes_pair_receiverChains
    (P1 := fun b => vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv)
    (P2 := fun b => vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b c.keys)
    (n1 := 48) (n2 := 24) (off := 0x30#64) rfl
    h12
    (vecOf104_msgKey_move_bytes A c.keys)
  have h1234 := move_bytes_pair_receiverChains
    (P1 := fun b => (vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
      vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys)
    (P2 := fun b => prostCkAt_receiverChains A b c.ck)
    (n1 := 72) (n2 := 32) (off := 0x48#64) rfl
    h123
    (prostCkAt_move_bytes_receiverChains A c.ck) a
  have heq : ∀ b : BitVec 64,
      prostChainGAt A b c =
        ((vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
          vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys) ∗
        prostCkAt_receiverChains A (b + 0x48#64) c.ck := by
    intro b
    rw [prostChainGAt_eq_parts A b c]
    ac_rfl
  simp only [show (72 : Nat) + 32 = 104 from rfl, ← heq] at h1234
  exact h1234

theorem prostChainGAt_move_chunks104 (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64,
          (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostChainGAt_move_bytes A c a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _)
  rw [← hchunks b]
  exact hmov b

theorem arrayAt_prostChainGAt_move_bytes (A : RustAlloc) (cs : List ChainG) (a : BitVec 64) :
    arrayAt (fun c b => prostChainGAt A b c) 104 a cs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cs.length * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  induction cs generalizing a with
  | nil =>
    dsimp only [arrayAt, List.length_nil, Nat.zero_mul]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, sepConj_emp]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  | cons c cs ih =>
    dsimp only [arrayAt]
    have hm := move_bytes_pair_receiverChains
      (P1 := fun b => prostChainGAt A b c)
      (P2 := fun b => arrayAt (fun c' b' => prostChainGAt A b' c') 104 b cs)
      (n1 := 104) (n2 := cs.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostChainGAt_move_bytes A c)
      ih a
    have hlen : 104 + cs.length * 104 = (c :: cs).length * 104 := by
      simp [List.length_cons, Nat.add_mul]; omega
    rw [hlen] at hm
    exact hm

/-! ## `prostSSGAt` `recv` Open/Close and `growOneSpec` Helpers -/

@[expose] def prostSSGRest (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSGAt_eq_recv_sep_rest (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGAt A ss v =
      vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
        prostSSGRest A ss v := by
  unfold prostSSGAt prostSSGRest
  ac_rfl

theorem prostSSGRest_apply_recv (A : RustAlloc) (ss : BitVec 64) (v : SSG) (c : ChainG) :
    prostSSGRest A ss (v.apply (.recv c)) = prostSSGRest A ss v := rfl

theorem vecAt_recv_open (ss : BitVec 64) (cs : List ChainG) :
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) (ss + 0x48#64) cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, e58, hlive, h0]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem ofNat_length_eq_cap_of_eq {cs : List ChainG} {cap : BitVec 64}
    (h : cs.length = cap.toNat) :
    BitVec.ofNat 64 cs.length = cap := by
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem beq_ofNat_len_cap_false {cs : List ChainG} {cap : BitVec 64}
    (hlt : cs.length < cap.toNat) :
    (BitVec.ofNat 64 cs.length == cap) = false := by
  have hne : BitVec.ofNat 64 cs.length ≠ cap := by
    intro h
    have h' := congrArg BitVec.toNat h
    have hcap := cap.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
    omega
  cases hb : (BitVec.ofNat 64 cs.length == cap)
  · rfl
  · exact False.elim (hne (eq_of_beq hb))

theorem vecBuf_recv_full_open (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A0 b' c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs
    simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (arrayAt_prostChainGAt_move_bytes A0 cs ptr) ?_
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro H
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hlive' : A0.live ptr bs.length 8 = emp := rfl
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [hlive', emp_sepConj]
    exact Entails.pure_right ⟨hbs_cap, hmov⟩ (Entails.refl _)

theorem vecBuf_recv_not_full_open (cap ptr : BitVec 64) (cs : List ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (arrayAt (fun c b => prostChainGAt A0 b c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by
    intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 =
      104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]

theorem vecAt_recv_push_fold (ss cap ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
        ((cap.toNat - (cs.length + 1)) * 104) ⊢
    vecOf A0 104 8 (fun c' a => prostChainGAt A0 a c') (ss + 0x48#64) (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e50 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := by
    rw [BitVec.ofNat_add]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e50, e58, hlive, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]
  simp only [hne0, ↓reduceIte, emp_sepConj]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
            prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
          ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
          prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) := by
    ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

theorem prostSSGAt_fold_apply_recv (ss cap ptr : BitVec 64) (v : SSG) (c : ChainG)
    (hlt : v.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
      ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
        ((cap.toNat - (v.recv.length + 1)) * 104) ∗
      prostSSGRest A0 ss v) ⊢
    prostSSGAt A0 ss (v.apply (.recv c)) := by
  rw [prostSSGAt_eq_recv_sep_rest A0 ss (v.apply (.recv c)),
      prostSSGRest_apply_recv A0 ss v c]
  dsimp only [SSG.apply]
  have hgrp :
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
          ((cap.toNat - (v.recv.length + 1)) * 104) ∗
        prostSSGRest A0 ss v) =
      (((ss + 0x48#64) ↦₆₄ cap) ∗ ((ss + 0x50#64) ↦₆₄ ptr) ∗
        ((ss + 0x58#64) ↦₆₄ (BitVec.ofNat 64 v.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.recv.length + 1) * 104))
          ((cap.toNat - (v.recv.length + 1)) * 104)) ∗
      prostSSGRest A0 ss v := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_left (vecAt_recv_push_fold ss cap ptr v.recv c hlt hcap_lt hptr)

/-! ## Stepping Lemmas and `mergeFieldGenReceiverChains_ok` -/

attribute [local irreducible] prostSSGRest prostChainGAt prostSSGAt mfFramePad_receiverChains
  Prost.sliceCursorAt Prost.sliceCursorAfter mfSavedRegs_receiverChains

theorem recv_payload_append_eq {fld : GenField} {c : ChainG} (hfld : fld = .recv c)
    (tail : List (BitVec 8)) :
    c.payload ++ tail = fld.payload ++ tail := by
  subst hfld
  rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains

