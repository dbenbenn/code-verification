/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tag-1/2 Field Leaf (`chainSenderRatchetKeyG_ok`) for General `message::merge<Chain>`

Proves `chainSenderRatchetKeyG_ok` (`+0x120 → +0x120`, `k → k + 1`) for `sender_ratchet_key`
(tag `1`, `a`) and `sender_ratchet_key_private` (tag `2`, `a + 0x18`) via `bytes::merge`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Pure `ChainG`, `ChainField`, and `chainGAfter` Helpers -/

theorem chainGAfter_succ {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    chainGAfter c (k + 1) = (chainGAfter c k).apply (c.fields[k]'hk) := by
  simp only [chainGAfter, List.take_succ_eq_append_getElem hk, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem drop_flatMap_enc {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    (c.fields.drop k).flatMap ChainField.enc =
      (c.fields[k]'hk).enc ++ (c.fields.drop (k + 1)).flatMap ChainField.enc := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem mem_fields_srk_length_lt {c : ChainG} (hc : c.Ok) {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b.length < 128 := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  have hsrk : srk.length = 33 := hc.1
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> omega

theorem mem_fields_priv_length_lt {c : ChainG} (hc : c.Ok) {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b.length < 128 := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  have hpriv : priv = [] ∨ priv.length = 32 := hc.2.1
  rcases hpriv with rfl | h32
  · by_cases h1 : srk = [] <;> cases ck <;> simp [h1] at hmem
  · by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
      simp [h1, h2] at hmem <;> subst hmem <;> omega

theorem chainG_enc_eq_fields_local (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  unfold ChainG.enc ChainG.fields msgField
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;>
    (cases ck with
     | none =>
       simp [bytesField, h1, h2, ChainField.enc, Function.comp_def,
         List.append_assoc, List.flatMap_def]
     | some ik =>
       rcases ik with ⟨i, k⟩
       simp [bytesField, h1, h2, ChainField.enc, Function.comp_def,
         List.append_assoc, List.flatMap_def])

theorem lenField_eq_pbBytes (tag : Nat) (htag : tag = 1 ∨ tag = 2)
    (b : List (BitVec 8)) (hb : b.length < 128) :
    lenField tag b = pbBytes tag b := by
  unfold lenField pbBytes pbKey encodeKey WireType.toNat
  rw [encodeVarint_lt128_seedChain b.length hb]
  rcases htag with rfl | rfl <;> rfl

/-! ## Cursor and `prostChainGAt` Helpers -/

@[expose] def preBytes (c : ChainG) (k : Nat) : List (BitVec 8) :=
  encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc

@[expose] def curPtr (ptr : BitVec 64) (c : ChainG) (k : Nat) : BitVec 64 :=
  ptr + BitVec.ofNat 64 (preBytes c k).length

theorem payload_append_eq_preBytes (c : ChainG) (tail : List (BitVec 8)) (k : Nat) :
    c.payload ++ tail =
      preBytes c k ++ (((c.fields.drop k).flatMap ChainField.enc) ++ tail) := by
  have henc : c.enc =
      (c.fields.take k).flatMap ChainField.enc ++ (c.fields.drop k).flatMap ChainField.enc := by
    rw [← List.flatMap_append, List.take_append_drop]
    exact chainG_enc_eq_fields_local c
  unfold ChainG.payload preBytes
  rw [henc]
  simp only [List.append_assoc]

theorem sliceCursorAfter_eq_preBytes (slot ptr : BitVec 64) (c : ChainG)
    (tail : List (BitVec 8)) (k : Nat) :
    sliceCursorAfter slot ptr (c.payload ++ tail)
      (((c.fields.drop k).flatMap ChainField.enc) ++ tail) =
      (ptr ↦ₛ preBytes c k) ∗
        sliceCursorAt slot (curPtr ptr c k)
          (((c.fields.drop k).flatMap ChainField.enc) ++ tail) := by
  conv_lhs => rw [payload_append_eq_preBytes c tail k]
  exact sliceCursorAfter_append_eq_seedChain slot ptr (preBytes c k) _

theorem preBytes_succ {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    preBytes c (k + 1) = preBytes c k ++ (c.fields[k]'hk).enc := by
  simp only [preBytes, List.take_succ_eq_append_getElem hk, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem curPtr_succ (ptr : BitVec 64) {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    curPtr ptr c (k + 1) = curPtr ptr c k + BitVec.ofNat 64 (c.fields[k]'hk).enc.length := by
  unfold curPtr
  rw [preBytes_succ hk, List.length_append, BitVec.ofNat_add]
  bv_omega

theorem pointsToBytes_preBytes_succ (ptr : BitVec 64) {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) :
    (ptr ↦ₛ preBytes c k) ∗ (curPtr ptr c k ↦ₛ (c.fields[k]'hk).enc) =
      (ptr ↦ₛ preBytes c (k + 1)) := by
  rw [preBytes_succ hk, pointsToBytes_append, ← curPtr]

@[expose] def prostChainGRestAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

theorem prostChainGAt_eq_split (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗ prostChainGRestAt A a c := by
  unfold prostChainGAt prostChainGRestAt
  ac_rfl

theorem prostChainGAt_apply_srk (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    prostChainGAt A a (c.apply (.srk b)) =
      vecU8 A a b ∗ vecU8 A (a + 0x18#64) c.priv ∗ prostChainGRestAt A a c := by
  rw [prostChainGAt_eq_split]
  rfl

theorem prostChainGAt_apply_priv (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (b : List (BitVec 8)) :
    prostChainGAt A a (c.apply (.priv b)) =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) b ∗ prostChainGRestAt A a c := by
  rw [prostChainGAt_eq_split]
  rfl

/-! ## Register Preservation and Stack Alignment Helpers -/

@[expose] def LoopRegsPreserved (s s' : State) : Prop :=
  s'.readReg64 .x19 = s.readReg64 .x19 ∧
  s'.readReg64 .x20 = s.readReg64 .x20 ∧
  s'.readReg64 .x21 = s.readReg64 .x21 ∧
  s'.readReg64 .x22 = s.readReg64 .x22 ∧
  s'.readReg64 .x24 = s.readReg64 .x24 ∧
  s'.readReg64 .x25 = s.readReg64 .x25 ∧
  s'.readReg64 .x26 = s.readReg64 .x26 ∧
  s'.readReg64 .x29 = s.readReg64 .x29 ∧
  calleeSavedVRegs s' = calleeSavedVRegs s

theorem LoopRegsPreserved.trans {s0 s1 s2 : State}
    (h01 : LoopRegsPreserved s0 s1) (h12 : LoopRegsPreserved s1 s2) :
    LoopRegsPreserved s0 s2 := by
  reg_chain

theorem LoopRegsPreserved.of_calleeSaved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) : LoopRegsPreserved s1 s2 := by
  reg_chain

theorem sp0_aligned_of_sub_256 {sp0 : BitVec 64} (h : (sp0 - 256#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

@[expose] def dummySeedGhost : ChainMergeGhost := ⟨0, ⟨[], [], none⟩, 0, 0, 0, [], []⟩

/-! ## Tag-1 and Tag-2 Stepping Lemmas -/

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
