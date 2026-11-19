/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Ratchet-Key Field Decoding for `message::merge<Chain>`

Steps one iteration (`+0x0a8 → +0x0a8`) of `Chain3LoopAtW` inside
`prost::encoding::message::merge<Chain>` across protobuf tags 1 (`sender_ratchet_key`) and 2
(`sender_ratchet_key_private`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt sliceCursorAfter BytesMergeGhost BytesMergeCapOk DecodeVarintSlowGhost
   bytesMergeCapOk_of_len_lt32)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setPC_pre_seedChain
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm]
  CryptoVerification.E2E.Record.DeserializeSeed.ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Register preservation and stack alignment -/

/-- Register preservation across one `Chain3LoopAtW` iteration (`+0x0a8 → +0x0a8`), covering
`x19..x24`, `x26..x29`, and `calleeSavedVRegs` (`x25` is excluded from the loop invariant). -/
@[expose] def Chain3LoopRegsPreserved (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧
  s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧
  s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧
  s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧
  s1.readReg64 .x28 = s0.readReg64 .x28 ∧
  s1.readReg64 .x29 = s0.readReg64 .x29 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.refl (s : State) : Chain3LoopRegsPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.trans {s0 s1 s2 : State}
    (h01 : Chain3LoopRegsPreserved s0 s1) (h12 : Chain3LoopRegsPreserved s1 s2) :
    Chain3LoopRegsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem Chain3LoopRegsPreserved.of_calleeSaved {s0 s1 : State}
    (h : CalleeSavedPreserved s0 s1) : Chain3LoopRegsPreserved s0 s1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 400000 in
theorem sp_sub_240_aligned_c3 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
theorem sp0_aligned_of_sub_240_c3 {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
theorem decodeVarint_0a_cons (rest : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: rest) = some (0x0a#64, rest) := rfl

set_option maxHeartbeats 400000 in
theorem decodeVarint_12_cons (rest : List (BitVec 8)) :
    decodeVarint (0x12#8 :: rest) = some (0x12#64, rest) := rfl

/-! ## Callee step helpers -/

private def tailFields (c : ChainG) : List ChainField :=
  (match c.ck with
   | some (i, key) => [ChainField.ck i key]
   | none => []) ++ c.keys.map ChainField.key

set_option maxHeartbeats 400000 in
private theorem fields_eq_tailFields (c : ChainG) :
    c.fields =
      (if c.srk = [] then [] else [ChainField.srk c.srk]) ++
        ((if c.priv = [] then [] else [ChainField.priv c.priv]) ++ tailFields c) := by
  unfold ChainG.fields tailFields
  cases c.ck <;> simp [List.append_assoc]

set_option maxHeartbeats 400000 in
private theorem getElem?_tailFields_ne_srk (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields c)[j]? ≠ some (ChainField.srk b) := by
  unfold tailFields
  cases c.ck with
  | none =>
    simp only [List.nil_append, List.getElem?_map]
    cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨i, key⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

set_option maxHeartbeats 400000 in
private theorem getElem?_tailFields_ne_priv (c : ChainG) (j : Nat) (b : List (BitVec 8)) :
    (tailFields c)[j]? ≠ some (ChainField.priv b) := by
  unfold tailFields
  cases c.ck with
  | none =>
    simp only [List.nil_append, List.getElem?_map]
    cases c.keys[j]? <;> simp
  | some ik =>
    rcases ik with ⟨i, key⟩
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.singleton_append, List.getElem?_cons_succ, List.getElem?_map]
      cases c.keys[j']? <;> simp

set_option maxHeartbeats 400000 in
private theorem mem_fields_srk_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h1

set_option maxHeartbeats 400000 in
private theorem mem_fields_priv_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem
  rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h2

set_option maxHeartbeats 400000 in
private theorem chainGAfter_srk_eq_nil_of_getElem_srk {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .srk b) : (chainGAfter c k).srk = [] := by
  have hfl? : c.fields[k]? = some (.srk b) := by
    rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_srk c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · rfl
    · simp at hfl?
    · simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_srk c k' b)

set_option maxHeartbeats 400000 in
private theorem chainGAfter_priv_eq_nil_of_getElem_priv {c : ChainG} {k : Nat}
    (hk : k < c.fields.length) {b : List (BitVec 8)}
    (hfl : c.fields[k]'hk = .priv b) : (chainGAfter c k).priv = [] := by
  have hfl? : c.fields[k]? = some (.priv b) := by
    rw [List.getElem?_eq_getElem hk, hfl]
  rw [fields_eq_tailFields c] at hfl?
  by_cases hs : c.srk = [] <;> by_cases hp : c.priv = []
  · simp only [hs, hp, ↓reduceIte, List.nil_append] at hfl?
    exact absurd hfl? (getElem?_tailFields_ne_priv c k b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)
  · simp only [hs, hp, ↓reduceIte, List.nil_append, List.singleton_append] at hfl?
    cases k with
    | zero => simp at hfl?
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)
  · simp only [hs, hp, ↓reduceIte, List.singleton_append] at hfl?
    rcases k with _ | _ | k'
    · simp at hfl?
    · unfold chainGAfter
      rw [fields_eq_tailFields c]
      simp [hs, hp, ChainG.empty, ChainG.apply]
    · simp only [List.getElem?_cons_succ] at hfl?
      exact absurd hfl? (getElem?_tailFields_ne_priv c k' b)

set_option maxHeartbeats 400000 in
theorem chain3GAt_apply_srk (A : RustAlloc) (a : BitVec 64) (c : ChainG) (b : List (BitVec 8)) :
    chain3GAt A a (c.apply (.srk b)) =
      chain3VecAt A a b ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ chainGRest A a c := rfl

set_option maxHeartbeats 400000 in
theorem chain3GAt_apply_priv (A : RustAlloc) (a : BitVec 64) (c : ChainG) (b : List (BitVec 8)) :
    chain3GAt A a (c.apply (.priv b)) =
      chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) b ∗ chainGRest A a c := rfl

/-! ## Main theorems -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
