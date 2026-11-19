/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof -- shake: keep

/-!
# `spqr::recv`: Message Preamble & Common Epilogue

48-byte `recvResultExactKeyAt` folding, stack-frame prologue/epilogue (`+1040..+1072`),
`Err(MsgDecode)` exit (`+276..+288`), and LEB128 varint decoding loops (`+0..+312`) for
`spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Top.DecodeState

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Result buffer (`ret`, 48 bytes) folding for `recvResultExactKeyAt` -/

/-- The 48-byte `recv` result buffer `ret`, cut at the four 8-byte words touched on the `Ok` and
    `Err` paths (`+0`, `+8`, `+16`, `+24`). -/
theorem ret_48_split (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16 := by
  have hs : ∀ (b : BitVec 64) (k : Nat), k ≤ 40 →
      memRegion b (8 + k) = memRegion b 8 ∗ memRegion (b + 8#64) k :=
    fun b k _ => memRegion_split' rfl rfl (by omega)
  rw [hs r 40 (by decide), hs _ 32 (by decide), hs _ 24 (by decide), hs _ 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

/-- `recvResultExactKeyAt A r (.ok ([], none))` folded from `0, 1, 0, -1`. -/
theorem recv_ok_empty_foldX (A : RustAlloc) (r : BitVec 64) :
    ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      ((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.ok ([], none)) := by
  have hv : ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗ ((r + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A r [] := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
    simp only [vecU8At, vecHeader, List.length_nil]
    split
    · rw [sepConj_emp, sepConj_comm _ ⌜_⌝]
      refine Entails.pure_right ?_ (Entails.refl _)
      exact ⟨Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl ‹_›
  simp only [recvResultExactKeyAt, optKeyBytesAt]
  refine Entails.trans (Entails.of_eq (Q := ((r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 1#64) ∗
      ((r + 16#64) ↦₆₄ 0#64)) ∗ (((r + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      memRegion (r + 32#64) 16)) (by simp only [sepConj_assoc])) ?_
  exact sepConj_mono hv (Entails.of_eq (by rw [BitVec.add_assoc]; rfl))

/-- `recvResultExactKeyAt A r (.error false)` for `Err(MsgDecode)` (`w8 = 2#64`). -/
theorem recv_err_msgDecode_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ 2#64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error false) := by
  simp only [recvResultExactKeyAt]
  have h8 : ((r + 8#64) ↦₆₄ 2#64) ⊢ ((r + 8#64) ↦₈ 2#8) ∗ memRegion (r + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes]
    change ((r + 8#64) ↦ₛ (2#8 :: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8])) ⊢ _
    rw [pointsToBytes_cons, show r + 8#64 + 1#64 = r + 9#64 by bv_arith]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [sepConj_assoc]
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro 2#8)
  exact Entails.pure_right (by decide) (Entails.refl _)

/-- Split the second 8-byte word `r + 8` of `ret` into its leading byte `r + 8` and 7 trailing
    bytes `r + 9 .. r + 16` (for `strb w8, [x19, #0x8]` error paths). -/
theorem ret8_expose_byte (r r1 : BitVec 64) :
    ((r + 8#64) ↦₆₄ r1) ⊢
      ∃∗ b : BitVec 8, ((r + 8#64) ↦₈ b) ∗ memRegion (r + 9#64) 7 := by
  refine Entails.trans (pointsTo64_entails_memRegion (r + 8#64) r1) ?_
  rw [memRegion_split (r + 8#64) 1 7 (by decide),
      show r + 8#64 + 1#64 = r + 9#64 by bv_arith,
      ProofLib.memRegion_one (r + 8#64), sepExists_sepConj_left]
  exact Entails.refl _

/-- Fold `Err(sd)` at `ret` when `r + 8` has been written via `strb` (`code : BitVec 8` with
    `code = 0#8 ↔ sd = true`). -/
theorem recv_err_byte_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) (code : BitVec 8) (sd : Bool)
    (hsd : code = 0#8 ↔ sd = true) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₈ code) ∗ memRegion (r + 9#64) 7 ∗
      ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error sd) := by
  simp only [recvResultExactKeyAt]
  have htail :
      memRegion (r + 9#64) 7 ∗ ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗
        memRegion (r + 32#64) 16 ⊢
      memRegion (r + 9#64) 39 := by
    rw [show (39 : Nat) = 7 + (8 + (8 + 16)) by decide,
        memRegion_split (r + 9#64) 7 32 (by decide),
        show r + 9#64 + 7#64 = r + 16#64 by bv_arith,
        memRegion_split (r + 16#64) 8 24 (by decide),
        show r + 16#64 + 8#64 = r + 24#64 by bv_arith,
        memRegion_split (r + 24#64) 8 16 (by decide),
        show r + 24#64 + 8#64 = r + 32#64 by bv_arith]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_right htail) ?_
  refine sepConj_mono_left ?_
  refine Entails.trans ?_ (Entails.sepExists_intro code)
  exact Entails.pure_right hsd (Entails.refl _)

/-! ## Exposing the `m.remaining` slice `(x24 ↦ₛ m.remaining)` inside `msg.at A` -/

/-- Validity invariant relating `(x24 = ptr_rem, x23 = rem.length)` after `msgPreamble` to
    `msg`: either `msg.bytes = []` and `rem = []`, or `msg.bytes = pre ++ rem` with `ptr_rem =
    msg.ptr + pre.length`. -/
@[expose] def MsgRemValid (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) : Prop :=
  (rem = [] ∧ msg.bytes = []) ∨
    ∃ pre : List (BitVec 8),
      msg.bytes = pre ++ rem ∧ ptr_rem = msg.ptr + BitVec.ofNat 64 pre.length

/-- Frame of `msg.at A` when `(ptr_rem ↦ₛ rem)` is exposed for `Message::deserialize`. -/
@[expose] def msgRemFrame (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) : SepProp :=
  ∃∗ pre : List (BitVec 8),
    ⌜(rem = [] ∧ pre = msg.bytes) ∨
      (msg.cap ≠ 0 ∧ msg.bytes = pre ++ rem ∧ ptr_rem = msg.ptr + BitVec.ofNat 64 pre.length)⌝ ∗
    ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
    vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
    if msg.cap = 0 then emp
    else A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre) ∗
      memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_rem (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8))
    (hvalid : MsgRemValid msg ptr_rem rem) :
    msg.at A ⊢ (ptr_rem ↦ₛ rem) ∗ msgRemFrame A msg ptr_rem rem := by
  simp only [VecArg.at, vecU8At, msgRemFrame]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => ?_
  by_cases hcap : msg.cap = 0
  · have hlen0 : msg.bytes.length = 0 := by
      have hc0 : msg.cap.toNat = 0 := by rw [hcap]; rfl
      omega
    have hnil : msg.bytes = [] := List.eq_nil_of_length_eq_zero hlen0
    have hrem0 : rem = [] := by
      rcases hvalid with ⟨hr, _⟩ | ⟨pre, hsplit, _⟩
      · exact hr
      · rw [hnil] at hsplit
        exact (List.append_eq_nil_iff.mp hsplit.symm).2
    subst hrem0
    rw [pointsToBytes_nil, emp_sepConj]
    refine Entails.sepExists_right msg.bytes ?_
    refine Entails.pure_right (Or.inl ⟨rfl, rfl⟩) (Entails.pure_right hp ?_)
    exact Entails.refl _
  · rcases hvalid with ⟨rfl, _⟩ | ⟨pre, hsplit, hptr⟩
    · rw [pointsToBytes_nil, emp_sepConj]
      refine Entails.sepExists_right msg.bytes ?_
      refine Entails.pure_right (Or.inl ⟨rfl, rfl⟩) (Entails.pure_right hp ?_)
      exact Entails.refl _
    · rw [sepExists_sepConj_right]
      refine Entails.sepExists_right pre ?_
      rw [ite_eq_right_iff.mpr (fun h => (hcap h).elim),
          ite_eq_right_iff.mpr (fun h => (hcap h).elim)]
      have hpts : (msg.ptr ↦ₛ msg.bytes) = (msg.ptr ↦ₛ pre) ∗ (ptr_rem ↦ₛ rem) := by
        rw [hsplit, pointsToBytes_append, ← hptr]
      rw [hpts]
      have hcomm :
          vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
            (A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre ∗ ptr_rem ↦ₛ rem) ∗
              memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)) =
          (ptr_rem ↦ₛ rem) ∗
            (vecHeader msg.v msg.cap msg.ptr (BitVec.ofNat 64 msg.bytes.length) ∗
              (A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ pre) ∗
                memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length))) := by
        ac_rfl
      rw [hcomm]
      refine sepConj_mono_right ?_
      refine Entails.pure_right (Or.inr ⟨hcap, hsplit, hptr⟩) (Entails.pure_right hp ?_)
      exact Entails.refl _

theorem msg_unexpose_rem (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64) (rem : List (BitVec 8)) :
    ((ptr_rem ↦ₛ rem) ∗ msgRemFrame A msg ptr_rem rem) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, msgRemFrame, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pre => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hcase => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => ?_
  conv_rhs => rw [sepConj_pure_left_comm]
  refine Entails.pure_right hp ?_
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hcap, hsplit, hptr⟩
  · rw [pointsToBytes_nil, emp_sepConj]
    exact Entails.refl _
  · rw [ite_eq_right_iff.mpr (fun h => (hcap h).elim),
        ite_eq_right_iff.mpr (fun h => (hcap h).elim)]
    have hpts : (msg.ptr ↦ₛ msg.bytes) = (msg.ptr ↦ₛ pre) ∗ (ptr_rem ↦ₛ rem) := by
      rw [hsplit, pointsToBytes_append, ← hptr]
    rw [hpts]
    exact Entails.of_eq (by ac_rfl)

/-! ## Prologue & Epilogue Stack Frame Lemmas (`fsp = s0.sp - 0x1380`) -/

theorem memRegion_16_split (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, a ↦₆₄ v0) ∗ (∃∗ v1 : BitVec 64, (a + 8#64) ↦₆₄ v1) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem prologue_frame_split (fsp : BitVec 64) :
    memRegion fsp 0x1320 ∗ memRegion (fsp + 0x1320#64) 96 ⊢
      memRegion fsp 0x320 ∗
      (∃∗ probe : BitVec 64, (fsp + 0x320#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0x328#64) 0xff8 ∗
      (∃∗ s29 : BitVec 64, (fsp + 0x1320#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (fsp + 0x1328#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (fsp + 0x1330#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (fsp + 0x1338#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (fsp + 0x1340#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (fsp + 0x1348#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (fsp + 0x1350#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (fsp + 0x1358#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (fsp + 0x1360#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (fsp + 0x1368#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (fsp + 0x1370#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (fsp + 0x1378#64) ↦₆₄ s19) := by
  have h1 : memRegion fsp 0x1320 =
      memRegion fsp 0x320 ∗ (∃∗ probe : BitVec 64, (fsp + 0x320#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0x328#64) 0xff8 := by
    rw [show (0x1320 : Nat) = 0x320 + (8 + 0xff8) by decide,
        memRegion_split fsp 0x320 (8 + 0xff8) (by decide),
        memRegion_split (fsp + 0x320#64) 8 0xff8 (by decide),
        show fsp + 0x320#64 + 8#64 = fsp + 0x328#64 by bv_arith,
        ProofLib.memRegion_eight (fsp + 0x320#64)]
  have h2 : memRegion (fsp + 0x1320#64) 96 =
      (∃∗ s29 : BitVec 64, (fsp + 0x1320#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (fsp + 0x1328#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (fsp + 0x1330#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (fsp + 0x1338#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (fsp + 0x1340#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (fsp + 0x1348#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (fsp + 0x1350#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (fsp + 0x1358#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (fsp + 0x1360#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (fsp + 0x1368#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (fsp + 0x1370#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (fsp + 0x1378#64) ↦₆₄ s19) := by
    rw [show (96 : Nat) = 16 + (16 + (16 + (16 + (16 + 16)))) by decide,
        memRegion_split (fsp + 0x1320#64) 16 80 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64) 16 64 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64) 16 48 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64 + 16#64) 16 32 (by decide),
        memRegion_split (fsp + 0x1320#64 + 16#64 + 16#64 + 16#64 + 16#64) 16 16 (by decide)]
    simp only [memRegion_16_split, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem prologue_frame_unsplit (fsp probe : BitVec 64) :
    memRegion fsp 0x320 ∗ ((fsp + 0x320#64) ↦₆₄ probe) ∗ memRegion (fsp + 0x328#64) 0xff8 ⊢
      memRegion fsp 0x1320 := by
  rw [show (0x1320 : Nat) = 0x320 + (8 + 0xff8) by decide,
      memRegion_split fsp 0x320 (8 + 0xff8) (by decide),
      memRegion_split (fsp + 0x320#64) 8 0xff8 (by decide),
      show fsp + 0x320#64 + 8#64 = fsp + 0x328#64 by bv_arith]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

/-! ## Common Epilogue (`+1040 .. +1072`, `0x54a3c .. 0x54a5c`) -/

theorem satisfies_pure_and_of_pure {mem : Memory} {p q : Prop} {X R : SepProp}
    (h : mem ⊨ (⌜p⌝ ∗ X) ∗ R) (hq : q) : mem ⊨ (⌜p ∧ q⌝ ∗ X) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  exact ⟨⟨h.1, hq⟩, h.2⟩

abbrev spqrRecvPanicPost (M : SpqrRecvModel)
    (st msg : VecArg) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (⌜(allocFailedIn s0 sf ∨ M.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem sp_sub_4992_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

theorem sp_sub_96_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

theorem spqrRecvSavedRegs_eq_decodeStateSavedAt (sp0 : BitVec 64) (s0 : State) :
    spqrRecvSavedRegs (sp0 - 4992#64) s0 =
      decodeStateSavedAt sp0 (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19) := by
  unfold spqrRecvSavedRegs decodeStateSavedAt
  rw [bv_sub_add_lit sp0 4992 4896,
      bv_sub_add_lit sp0 4992 4904,
      bv_sub_add_lit sp0 4992 4912,
      bv_sub_add_lit sp0 4992 4920,
      bv_sub_add_lit sp0 4992 4928,
      bv_sub_add_lit sp0 4992 4936,
      bv_sub_add_lit sp0 4992 4944,
      bv_sub_add_lit sp0 4992 4952,
      bv_sub_add_lit sp0 4992 4960,
      bv_sub_add_lit sp0 4992 4968,
      bv_sub_add_lit sp0 4992 4976,
      bv_sub_add_lit sp0 4992 4984]

open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgByteFrame msg_expose_byte msg_unexpose_byte
   varint_out_norm list_cons_of_length_pos
   nat_le_of_bv_ule nat_lt_of_not_bv_ule
   hb_ne_of_sxtb_tb hb_eq_of_not_sxtb_tb
   csel_rest1_min_10 rest1_nil_of_ule rest1_cons_of_not_ule
   index_bounds_ne varint_end_of_ge varint_cont_of_lt)

theorem decodeVarintLoop_err_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hend : i + 1 = 10 ∨ rest' = []) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') = none := by
  rw [LibsignalSpqrV1.decodeVarintLoop]
  simp only [hb, ↓reduceIte, MAX_VARINT_BYTES_LEN]
  rcases hend with h10 | rfl
  · simp [h10]
  · by_cases h10 : i + 1 = 10 <;> simp [h10, LibsignalSpqrV1.decodeVarintLoop]

theorem decodeVarintLoop_ok_of_lo {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 = 0#8) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') =
      some (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i)), rest') := by
  rw [LibsignalSpqrV1.decodeVarintLoop]
  simp [hb]

theorem decodeVarintLoop_step_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hi : i + 1 < 10) :
    LibsignalSpqrV1.decodeVarintLoop i out (b :: rest') =
      LibsignalSpqrV1.decodeVarintLoop (i + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))) rest' := by
  conv => lhs; rw [LibsignalSpqrV1.decodeVarintLoop]
  have hne : i + 1 ≠ MAX_VARINT_BYTES_LEN := by unfold MAX_VARINT_BYTES_LEN; omega
  simp [hb, hne]

theorem msgPreamble_nil :
    msgPreamble [] = .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } := rfl

theorem msgPreamble_singleton (v : BitVec 8) :
    msgPreamble [v] = .error .msgDecode := rfl

theorem msgPreamble_cons_cons (v b : BitVec 8) (rest : List (BitVec 8)) :
    msgPreamble (v :: b :: rest) =
      match LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b :: rest) with
      | none => .error .msgDecode
      | some (epoch, rest1) =>
        if epoch == 0#64 then .error .msgDecode
        else
          match LibsignalSpqrV1.decodeVarint rest1 with
          | .error e => .error e
          | .ok (index, rest2) =>
            if index.toNat < 2 ^ 32 then
              .ok { version := v, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
            else
              .error .msgDecode := by
  unfold msgPreamble msg_preamble LibsignalSpqrV1.decodeVarint
  simp only [decode_varint, Bind.bind, Except.bind]
  cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b :: rest) with
  | none => rfl
  | some p =>
    rcases p with ⟨epoch, rest1⟩
    dsimp only
    by_cases he : epoch = 0#64
    · subst he; rfl
    · have heb : (epoch == 0#64) = false := beq_false_of_ne he
      simp only [he, heb, Bool.false_eq_true, ↓reduceIte]
      cases LibsignalSpqrV1.decodeVarintLoop 0 0#64 rest1 with
      | none => rfl
      | some q =>
        rcases q with ⟨index, rest2⟩
        rfl

open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgHeaderTail msg_expose_hdr msg_unexpose_hdr
   msg_nil_of_len_zero msg_singleton_of_len_one msg_cons_cons_of_len_ge_two)

theorem zeroExtend_setWidth32_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (x.setWidth 32).zeroExtend 64 = x := by
  revert x h; bv_kernel

theorem rem_len_add_not {msg_len pre1_len j rem_len : Nat}
    (hlen : msg_len = 1 + pre1_len + j + 1 + rem_len)
    (hlt : msg_len < 2 ^ 63) :
    ~~~ (BitVec.ofNat 64 (pre1_len + j + 1)) + BitVec.ofNat 64 msg_len =
      BitVec.ofNat 64 rem_len := by
  have h1 : pre1_len + j + 1 < 2 ^ 63 := by omega
  have h2 : rem_len < 2 ^ 63 := by omega
  have hnot : ~~~ (BitVec.ofNat 64 (pre1_len + j + 1)) =
      -1#64 - BitVec.ofNat 64 (pre1_len + j + 1) := by bv_arith
  rw [hnot]
  bv_omega

end CryptoVerification.SpqrV1.Top.Recv

