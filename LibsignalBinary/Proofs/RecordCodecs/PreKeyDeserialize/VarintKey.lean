/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Tag Varint Decode

Verifies the inline fast-path and `decode_varint` slow-path key decode steps in
`PreKeyRecord::deserialize`.
-/

public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Loop memory bundles & error-cleanup bridge entailments -/

@[expose] def pkLoopMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (m : PreKeyRecordStructure) : SepProp :=
  sliceCursorAt (sp' + 40#64) ptr bs ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    memRegion (sp' + 112#64) 48 ∗
    preKeyStructLoopOf A (sp' + 56#64) bs.length m ∗
    memRegion sp' 40 ∗
    memRegion x19 56 ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)
@[expose] def pkAfterVarintMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (n : ℕ) (m : PreKeyRecordStructure) : SepProp :=
  sliceCursorAfter (sp' + 40#64) ptr bs rest ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    memRegion (sp' + 112#64) 48 ∗
    preKeyStructLoopOf A (sp' + 56#64) n m ∗
    memRegion sp' 40 ∗
    memRegion x19 56 ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)
theorem pkPointsTo112_memRegion40_entails_memRegion48 (sp' v : BitVec 64) :
    ((sp' + 112#64) ↦₆₄ v) ∗ memRegion (sp' + 120#64) 40 ⊢ memRegion (sp' + 112#64) 48 := by
  rw [pkMemRegion48_split8 sp']
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 112#64) v)
theorem pkPointsTo120_memRegion32_entails_memRegion40 (sp' v : BitVec 64) :
    ((sp' + 120#64) ↦₆₄ v) ∗ memRegion (sp' + 128#64) 32 ⊢ memRegion (sp' + 120#64) 40 := by
  rw [ProofLib.memRegion_split (sp' + 120#64) 8 32 (by decide)]
  have ha : sp' + 120#64 + 8#64 = sp' + 128#64 := by bv_omega
  rw [ha]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 120#64) v)
theorem pkErrMem_of_structOf (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (n : ℕ) (mErr : PreKeyRecordStructure) (bs : List (BitVec 8)) :
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion (sp' + 112#64) 48 ∗
      decodeErrorAtStackLen A err n ∗
      preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗
      memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      decodeErrorAt A err ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  have hdec := decodeErrorWith_entails_at A err n
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hdec))))) ?_
  apply entails_of_eq
  ac_rfl
theorem pkErrMem_of_loopOf (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (n k : ℕ) (mErr : PreKeyRecordStructure) (bs : List (BitVec 8)) :
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion (sp' + 112#64) 48 ∗
      decodeErrorAtStackLen A err n ∗
      preKeyStructLoopOf A (sp' + 56#64) k mErr ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗
      memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      decodeErrorAt A err ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) k mErr)))))))
    (pkErrMem_of_structOf A sp' x19 ptr err n mErr bs)
/-! ## `DecodeError::from` & `DecodeError::push` tails (`+0x1c4..+0x1cc`, `+0x2cc..+0x2d4`) -/
theorem pkDecodeKey_err_entails (A : RustAlloc) (sp' x19 ptr w0 v : BitVec 64)
    (bs rest : List (BitVec 8)) (len : ℕ) (m : PreKeyRecordStructure) :
    sliceCursorAfter (sp' + 40#64) ptr bs rest ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      ((sp' + 112#64) ↦₆₄ w0) ∗
      ((sp' + 120#64) ↦₆₄ v) ∗
      memRegion (sp' + 128#64) 32 ∗
      preKeyStructLoopOf A (sp' + 56#64) len m ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      ((sp' + 112#64) ↦₆₄ w0) ∗ memRegion (sp' + 120#64) 40 ∗
      preKeyStructOf A (sp' + 56#64) m ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  refine Entails.trans
    (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 40#64) ptr bs rest)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  rw [← sepConj_assoc]
  exact sepConj_mono (pkPointsTo120_memRegion32_entails_memRegion40 sp' v)
    (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) len m))
section Placed
open CryptoVerification.RecordCodecs.Placed
theorem pkAdvanceCursor_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (pkEpiloguePostPlaced A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAfter (sp' + 40#64) ptr bs rest ∗ R)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 40#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => pkEpiloguePostPlaced_append_prefix A s0 sp' x19 ptr bs k hkl out sf Pf hqm)
end Placed
end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
