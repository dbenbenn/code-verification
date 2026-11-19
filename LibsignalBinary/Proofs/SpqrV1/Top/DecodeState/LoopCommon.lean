/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Shared Loop Frame & Call Wrappers for `spqr::decode_state` (`0x5349c`)

Defines shared active-loop stack frame
helpers (`decodeStateLoopCommon` and error-frame folding), panic-aware call wrappers
(`decode_varint`, `skip_field`, `bytes::merge`, `ChainParams::merge`), and pure
`Proto.mergeMessage` bridge lemmas.
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Stack Frame Helpers -/

theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Q_err) :
    SepWPp prog ret s P Q Q_err := by
  intro R hm hL
  exact hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

/-- The `240`-byte upper frame `memRegion (sp - 336#64) 240` splits into:
    - `(sp - 336#64) ↦₆₄ bRef` (`[x29 - 0xf0]`),
    - `memRegion (sp - 328#64) 224` (`[x29 - 0xe8 .. x29 - 0x08)`),
    - `memRegion (sp - 104#64) 8` (`[x29 - 0x08 .. x29)`). -/
theorem upper_240_fold (sp bRef : BitVec 64) :
    ((sp - 336#64) ↦₆₄ bRef) ∗ memRegion (sp - 328#64) 224 ∗ memRegion (sp - 104#64) 8 ⊢
      memRegion (sp - 336#64) 240 := by
  have hb : ((sp - 336#64) ↦₆₄ bRef) ⊢ memRegion (sp - 336#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp - 336#64) bRef
  rw [ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 232)
      (b' := sp - 328#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 224) (k := 8)
      (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left hb

/-- The `352`-byte lower frame `memRegion (sp - 1392#64) 352` is formed from
    `memRegion (sp - 1392#64) 336` and `memRegion (sp - 1056#64) 16` (`[sp + 0x150 .. sp + 0x160)`). -/
theorem lower_352_fold (sp : BitVec 64) :
    memRegion (sp - 1392#64) 336 ∗ memRegion (sp - 1056#64) 16 ⊢
      memRegion (sp - 1392#64) 352 := by
  rw [ProofLib.memRegion_split' (b := sp - 1392#64) (n := 336) (k := 16)
      (b' := sp - 1056#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Fold `sliceCursorAt (sp - 1056#64) ptr bs` into `memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs)`. -/
theorem sliceCursorAt_to_memRegion (sp ptr : BitVec 64) (bs : List (BitVec 8)) :
    sliceCursorAt (sp - 1056#64) ptr bs ⊢
      memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAt
  have h16 : ((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ⊢
      memRegion (sp - 1056#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 1056#64) (n := 8) (k := 8)
        (b' := sp - 1056#64 + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ ptr)
      (ProofLib.pointsTo64_entails_memRegion _ _)
  have hassoc :
      ((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) =
      (((sp - 1056#64) ↦₆₄ ptr) ∗ ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗ (ptr ↦ₛ bs) := by
    ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h16

/-- Remainder of `st.at A` when `(st.ptr ↦ₛ st.bytes)` is split out on the non-empty path (`st.bytes ≠ []`). -/
@[expose] def vecArgRestAt (A : RustAlloc) (st : VecArg) : SepProp :=
  (st.v ↦₆₄ st.cap) ∗ ((st.v + 8#64) ↦₆₄ st.ptr) ∗
    ((st.v + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
    ⌜st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63 ∧ st.ptr ≠ 0 ∧ st.cap ≠ 0⌝ ∗
    A.live st.ptr st.cap.toNat 1 ∗
    memRegion (st.ptr + BitVec.ofNat 64 st.bytes.length) (st.cap.toNat - st.bytes.length)

theorem vecArg_split_bytes (A : RustAlloc) (st : VecArg) (hne : st.bytes ≠ []) :
    st.at A ⊢ (st.ptr ↦ₛ st.bytes) ∗ vecArgRestAt A st := by
  simp only [VecArg.at, vecU8At, vecHeader, vecArgRestAt, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hlen_cap, hcap_lt, hptr⟩ => ?_
  have hcap : st.cap ≠ 0 := by
    intro hc
    have h0 : st.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < st.bytes.length := List.length_pos_of_ne_nil hne
    omega
  refine Entails.pure_right ⟨hlen_cap, hcap_lt, hptr, hcap⟩ ?_
  simp only [hcap, ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

theorem vecArg_join_bytes (A : RustAlloc) (st : VecArg) :
    (st.ptr ↦ₛ st.bytes) ∗ vecArgRestAt A st ⊢ st.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, vecArgRestAt, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hlen_cap, hcap_lt, hptr, hcap⟩ => ?_
  refine Entails.pure_right ⟨hlen_cap, hcap_lt, hptr⟩ ?_
  simp only [hcap, ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

/-- Shared stack & heap frame across the active loops of `spqr::decode_state`. -/
abbrev decodeStateLoopCommon (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (s0 : State) : SepProp :=
  v1StateJumpTablesAt b ∗
  vecArgRestAt A x.st ∗
  memRegion x.outPtr 352 ∗
  A.pool ∗
  stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
  memRegion (s0.sp - 1392#64) 336 ∗
  ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
  memRegion (s0.sp - 328#64) 224 ∗
  memRegion (s0.sp - 104#64) 8 ∗
  decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` into
    `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)`. -/
theorem sliceCursorAfter_to_memRegion (sp ptr : BitVec 64) (bs cur : List (BitVec 8)) :
    sliceCursorAfter (sp - 1056#64) ptr bs cur ⊢
      memRegion (sp - 1056#64) 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAfter
  have h16 := pointsTo64_pair_entails_memRegion16 (sp - 1056#64)
    (ptr + BitVec.ofNat 64 (bs.length - cur.length)) (BitVec.ofNat 64 cur.length)
  have hassoc :
      ((sp - 1056#64) ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - cur.length))) ∗
        ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗ (ptr ↦ₛ bs) =
      (((sp - 1056#64) ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - cur.length))) ∗
        ((sp - 1056#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length)) ∗ (ptr ↦ₛ bs) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h16

/-- Fold `memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗ protoPqRatchetStateAt ... ∗
    memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗ decodeStateLoopCommon`
    into `decodeStateErrFrame`. -/
theorem loopCommon_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      (x.st.ptr ↦ₛ x.st.bytes) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  dsimp only [decodeStateLoopCommon, decodeStateErrFrame]
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (v1StateJumpTablesAt b ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      v1StateJumpTablesAt b ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗ memRegion (s0.sp - 640#64) 304 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hst (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

/-- Fold `sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur` + `protoPqRatchetStateCapOkAt`
    + `decodeStateLoopCommon` directly into `decodeStateErrFrame`. -/
theorem loopCommon_cursor_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  rw [sepConj_assoc]
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-- Fold callee error cursor output (`memRegion slot 16 ∗ ((ptr + ...) ↦ₛ cur) ∗ (ptr ↦ₛ take)`)
    + `protoPqRatchetStateCapOkAt` + `decodeStateLoopCommon` into `decodeStateErrFrame`. -/
theorem loopCommon_calleeErr_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (x : DecodeStateGhost) {cur : List (BitVec 8)} (hcur_le : cur.length ≤ x.st.bytes.length)
    (hcur_suf : IsDropSuffix x.st.bytes cur) (remLen : Nat) (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remLen curSt
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remLen curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-- Fold callee error cursor output + `protoPqRatchetStateAt` + `decodeStateLoopCommon` into `decodeStateErrFrame`. -/
theorem loopCommon_calleeErr_proto_to_errFrame (H_inner : V1InnerHeapPred) (b : BitVec 64)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (curSt : PqRatchetState) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0 ⊢
      decodeStateErrFrame H_inner b A x curSt s0 := by
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
          ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h1)) ?_
  exact loopCommon_to_errFrame H_inner b A x curSt s0

/-! ## 2. Panic-Aware Call Wrappers (`decode_varint`, `skip_field`, `bytes::merge`, `ChainParams::merge`) -/

/-! ## 3. Pure `Proto.mergeMessage` Bridge Lemmas -/

theorem mergeMessage_toOption_of_ne_lengthDelimited {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {iwt : WireType} {m : M} {bs : List (BitVec 8)} {depth' : Nat}
    (hne : iwt ≠ .lengthDelimited) :
    (Proto.mergeMessage mergeField (codecWireTypeToProto iwt) m bs (depth' + 1)).toOption = none := by
  cases iwt <;> first | exact (hne rfl).elim | rfl

theorem mergeMessage_toOption_of_decodeVarint_none {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {m : M} {bs : List (BitVec 8)} {depth' : Nat}
    (hd : decodeVarint bs = none) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = none := by
  have hd' : (Proto.decodeVarint bs).toOption = none := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
  · simp [Proto.mergeMessage, Proto.checkWireType, hdv, Bind.bind, Except.bind, Except.toOption]
  · simp [hdv, Except.toOption] at hd'

theorem mergeMessage_toOption_of_lt {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    {m : M} {bs rest : List (BitVec 8)} {len64 : BitVec 64} {depth' : Nat}
    (hd : decodeVarint bs = some (len64, rest)) (hlt : rest.length < len64.toNat) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = none := by
  have hd' : (Proto.decodeVarint bs).toOption = some (len64, rest) := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨l', r'⟩
  · simp [hdv, Except.toOption] at hd'
  · simp only [hdv, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hd'
    rcases hd' with ⟨hl, hr⟩
    subst l' r'
    simp only [Proto.mergeMessage, Proto.checkWireType, ↓reduceIte, hdv, Bind.bind, Except.bind,
      takeExact_eq_take_drop]
    have hnot : ¬ len64.toNat ≤ rest.length := by omega
    simp [hnot, Except.toOption]

theorem mergeMessage_toOption_of_ge {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {bs rest : List (BitVec 8)} {len64 : BitVec 64} {depth' : Nat}
    (hd : decodeVarint bs = some (len64, rest)) (hge : ¬ rest.length < len64.toNat) :
    (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption =
      (mergeLoopBin mergeField (rest.length - (rest.length - len64.toNat)) m rest
        (rest.length - len64.toNat) depth').map (fun m' => (m', rest.drop len64.toNat)) := by
  have hd' : (Proto.decodeVarint bs).toOption = some (len64, rest) := by rw [proto_decodeVarint_toOption, hd]
  rcases hdv : Proto.decodeVarint bs with e | ⟨l', r'⟩
  · simp [hdv, Except.toOption] at hd'
  · simp only [hdv, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hd'
    rcases hd' with ⟨hl, hr⟩
    subst l' r'
    have hle : len64.toNat ≤ rest.length := by omega
    have hlen_take : (rest.take len64.toNat).length = rest.length - (rest.length - len64.toNat) := by
      simp [hle]; omega
    have happ := mergeLoopBin_append_eq hmf (rest.length - (rest.length - len64.toNat))
      (rest.take len64.toNat) (rest.drop len64.toNat) (rest.take len64.toNat).length m depth'
      (by omega) (Nat.le_refl _)
    rw [List.take_append_drop, List.length_drop, hlen_take] at happ
    have hchk : Proto.checkWireType .lengthDelimited .lengthDelimited = .ok () := rfl
    simp only [Proto.mergeMessage, hchk, hdv, Bind.bind, Except.bind,
      takeExact_eq_take_drop, hle, ↓reduceIte, Pure.pure, Except.pure, hlen_take, happ]
    rcases Proto.mergeFieldsLoop mergeField (rest.length - (rest.length - len64.toNat))
      m (rest.take len64.toNat) depth' with e | m' <;> rfl

end CryptoVerification.SpqrV1.Top.DecodeState
