/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Base
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDrop
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `SessionRecord::serialize` (`Prev1`) Body Specs, Step Statements, and Helpers

Defines the memory-level output encoding `encodeRecordPrev1Mem`, internal body specification
`serializePrev1BodySpecX`, field-2 write step (`+444 .. +692`), epilogue tail step (`+692 .. ret`),
and stack/heap framing lemmas for `SessionRecord::serialize` on a record with one previous session.
-/

public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

/-! ## Memory-Level Result Encoding -/

/-- Wire bytes written by `SessionRecord::serialize` for current session `sess` (ghost `G`) and
`previous_sessions = [enc]`: field 1 (`encSessionMem G sess`) followed by field 2 (`enc`). -/
@[expose] def encodeRecordPrev1Mem (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List (BitVec 8) :=
  CryptoVerification.E2E.Record.lenField 1 (encSessionMem G sess) ++
    CryptoVerification.E2E.Record.lenField 2 enc

theorem encodeRecordPrev1Mem_eq_of_canon {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (enc : List (BitVec 8)) (h : CanonSession G sess) :
    encodeRecordPrev1Mem G sess enc = encodeRecordPrev1 sess enc := by
  unfold encodeRecordPrev1Mem encodeRecordPrev1
  have h1 := encRecordMem_eq_of_canon ⟨0#64, 0#64, some G⟩ ⟨some sess⟩ h
  simp only [encRecordMem, encCurMem] at h1
  rw [h1]

/-! ## Body and Bridge Contracts -/

structure SerializePrev1BodyGhost where
  self : BitVec 64
  out : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)

/-- Specification of `SessionRecord::serialize` on a record with a current session and
`previous_sessions = [enc]`, at `serializeStackX` and a 32-byte `out` slot. -/
@[expose] def serializePrev1BodySpecX (A : RustAlloc) : Spec SerializePrev1BodyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32⌝ ∗
      prevVecAt A x.self x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      memRegion x.out 32 ∗ A.pool ∗ stackAt s.sp serializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      prevVecAt A x.self x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A (x.self + 24#64) x.G x.sess ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecordPrev1Mem x.G x.sess x.enc) ∗
      A.pool ∗ stackAt s0.sp serializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Registers preserved across the field-2 write block: `x19` (`out`), `x23` (clone word 0),
`x24` (`sp`), `x28`, `fp`, and callee-saved vector registers. -/
@[expose] def SerField2Saved (s sm : State) : Prop :=
  sm.readReg64 .x19 = s.readReg64 .x19 ∧
  sm.readReg64 .x23 = s.readReg64 .x23 ∧
  sm.readReg64 .x24 = s.readReg64 .x24 ∧
  sm.readReg64 .x28 = s.readReg64 .x28 ∧
  sm.readReg64 .fp = s.readReg64 .fp ∧
  calleeSavedVRegs sm = calleeSavedVRegs s

@[expose] def vecVecClone1SubSpecX (A : RustAlloc) : Spec VecVecClone1Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 1#64⌝ ∗
      arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
      stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ arrayAt (prevElem A) 24 x.src [x.enc] ∗
      (∃∗ q' : BitVec 64, prevVecAt A x.dst 1#64 q' [x.enc]) ∗ A.pool ∗
      stackAt s0.sp serializeSubStackX
  onPanic := allocPanic

@[expose] def deallocSubSpecX (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.live p size align ∗ memRegion p size ∗ A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp serializeSubStackX

theorem layoutOk_cap_u8_ser {cap : BitVec 64} (h0 : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  refine ⟨?_, ⟨0, rfl⟩, by omega⟩
  rcases Nat.eq_zero_or_pos cap.toNat with h | h
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
  · exact h

theorem layoutOk_24_8_ser : LayoutOk 24 8 := ⟨by decide, ⟨3, rfl⟩, by decide⟩

/-! ## Heap Shapes and Length Helpers -/

theorem memRegion_zero_ser (a : BitVec 64) : memRegion a 0 = emp := by
  have hb := IsBlock.pointsToBytes a []
  rw [pointsToBytes_nil] at hb
  exact IsBlock.eq (IsBlock.memRegion a 0) hb
    fun _ => ⟨fun _ => ⟨by simp, by simp⟩, fun _ => trivial⟩

/-- Splits a one-element `previous_sessions` buffer into its allocation token, 1-element
`arrayAt`, and spare capacity, exposing `cap ≠ 0`. -/
theorem vecBuf_prev_one_split_ser (A : RustAlloc) (cap q : BitVec 64) (enc : List (BitVec 8)) :
    vecBuf A 24 8 (prevElem A) cap q [enc] =
      ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  by_cases hc : cap = 0#64
  · subst hc
    apply ProofLib.sepProp_eq_of_entails
    · unfold RustHeap.vecBuf
      exact Entails.pure_left fun h => absurd h.1 (by simp)
    · exact Entails.pure_left fun h => absurd rfl h.1
  · rw [vecBuf_prev_one_eq A cap q enc hc]
    have hle : 1 ≤ cap.toNat := by
      have : cap.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    have hp : (1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64) =
        (cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64) :=
      propext ⟨fun h => ⟨hc, h.2⟩, fun h => ⟨hle, h.2⟩⟩
    rw [hp]
    simp only [arrayAt, sepConj_emp]

theorem prevVecAt_one_cells_ser (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r cap q [enc] =
      (r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
        ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_eq, hdrP_eq, vecBuf_prev_one_split_ser]
  simp only [List.length_singleton, sepConj_assoc]

theorem prevVecAt_cap1_cells (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r 1#64 q [enc] =
      (r ↦₆₄ 1#64) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗ ⌜q ≠ 0#64⌝ ∗
        A.live q 24 8 ∗ vecU8 A q enc := by
  rw [prevVecAt_one_eq A r 1#64 q enc (by decide), hdrP_eq]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  simp only [h1, Nat.one_mul, Nat.sub_self, Nat.zero_mul, memRegion_zero_ser, sepConj_emp,
    sepConj_assoc]
  apply ProofLib.sepProp_eq_of_entails
  · refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    exact Entails.pure_left fun ⟨_, _, hq⟩ => Entails.pure_right hq (Entails.refl _)
  · refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
    exact Entails.pure_left fun hq => Entails.pure_right ⟨le_refl 1, by decide, hq⟩ (Entails.refl _)

theorem vecU8At_cells (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs := by
  unfold vecU8At RustHeap.vecU8Buf vecHeader
  ac_rfl

/-- Exposes the allocation token and `cap`-byte block of `vecU8Buf` when `cap ≠ 0`, for the
inner `__rust_dealloc(ptr, cap, 1)` drop step. -/
theorem vecU8Buf_drop_view (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8Buf A cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
        (if cap = 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold RustHeap.vecU8Buf
  refine Entails.pure_left fun ⟨hlen, hlt, _⟩ => Entails.pure_right hlt ?_
  by_cases hc : cap = 0#64
  · have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hc, h0, ↓reduceIte]
    exact Entails.refl _
  · have hc' : ¬ (cap = 0) := hc
    simp only [hc, hc', ↓reduceIte]
    exact sepConj_mono_right (pointsToBytes_memRegion_entails ptr bs cap.toNat hlen (by omega))

theorem prevVec1_cap1_merge (q c p l : BitVec 64) :
    ((q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ ((q + 16#64) ↦₆₄ l)) ⊢ memRegion q 24 := by
  have h := prevVec1_outer_merge q c p 1 (le_refl 1) (by decide)
  simp only [Nat.sub_self, Nat.zero_mul, memRegion_zero_ser, sepConj_emp, Nat.one_mul] at h
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (pointsTo64_entails_memRegion _ _))) h

theorem repack_stack_hdr_cellsX (sp h0 h1 h2 w0 w1 w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStackX ∗
      ((sp - 800#64) ↦₆₄ h0) ∗ ((sp - 792#64) ↦₆₄ h1) ∗ ((sp - 784#64) ↦₆₄ h2) ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₆₄ w0) ∗
      ((sp - 424#64) ↦₆₄ w1) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
  have hp : ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1) =
      ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) := pointsTo64_pair_sub sp 432 w0 w1
  have hv : (((sp - 800#64) ↦₆₄ h0) ∗ ((sp - 792#64) ↦₆₄ h1) ∗ ((sp - 784#64) ↦₆₄ h2)) =
      vecHeader (sp - 800#64) h0 h1 h2 := by
    unfold vecHeader
    have e1 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
    have e2 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
    rw [e1, e2]
  have hpull :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        ((sp - 800#64) ↦₆₄ h0) ∗ ((sp - 792#64) ↦₆₄ h1) ∗ ((sp - 784#64) ↦₆₄ h2) ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₆₄ w0) ∗
        ((sp - 424#64) ↦₆₄ w1) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        (((sp - 800#64) ↦₆₄ h0) ∗ ((sp - 792#64) ↦₆₄ h1) ∗ ((sp - 784#64) ↦₆₄ h2)) ∗
        memRegion (sp - 776#64) 344 ∗
        (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w1)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull, hv, hp]
  rw [stackAt_serialize_baseX sp, memRegion_split (sp - 800#64) 24 344 (by decide)]
  have e1 : sp - 800#64 + BitVec.ofNat 64 24 = sp - 776#64 := bv_sub_add_lit sp 800 24
  rw [e1]
  have hpull2 :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        vecHeader (sp - 800#64) h0 h1 h2 ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        (vecHeader (sp - 800#64) h0 h1 h2 ∗ memRegion (sp - 776#64) 344) ∗
        (((sp - 432#64) ↦₁₂₈ (w1 ++ w0)) ∗ ((sp - 416#64) ↦₆₄ w2) ∗
          memRegion (sp - 408#64) 312) ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull2]
  exact sepConj_mono_right
    (sepConj_mono (sepConj_mono_left (vecHeader_entails_memRegion _ _ _ _))
      (sepConj_mono_left (repack_336_from_q01_w2 sp (w1 ++ w0) w2)))

theorem lenField_two_eq (bs : List (BitVec 8)) :
    CryptoVerification.E2E.Record.lenField 2 bs =
      [0x12#8] ++
        CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := rfl

theorem lenField_two_length (bs : List (BitVec 8)) :
    (CryptoVerification.E2E.Record.lenField 2 bs).length =
      1 + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 bs.length)).length +
        bs.length := by
  simp only [lenField_two_eq, List.length_append, List.length_singleton]

/-! ## Tail Step (`+692 .. ret`) -/

/-- The 12 callee-saved stack cells stored by `serialize`'s prologue at `sp0 - 96 .. sp0 - 8`,
with saved link register `ret`. -/
@[expose] def serSavedCells (s0 : State) (ret : BitVec 64) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 88#64) ↦₆₄ ret) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
