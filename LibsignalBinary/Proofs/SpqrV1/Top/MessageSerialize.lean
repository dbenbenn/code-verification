/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::Message>::serialize`

Binary memory layout, separation-logic specification, and correctness proof for
`<spqr::v1::chunked::states::Message>::serialize` against `Message.serialize`.
-/

public section

namespace CryptoVerification.SpqrV1.Layout.L35MessageSerialize
end CryptoVerification.SpqrV1.Layout.L35MessageSerialize

namespace CryptoVerification.SpqrV1.Top.MessageSerialize

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint CryptoVerification.SpqrV1.Alloc
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L35MessageSerialize

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev messageSize : Nat := 48

/-- Memory representation of `MessagePayload P` at `a + 0x08#64` (`40` bytes). -/
@[expose] def messagePayloadAt (P : PolyApi) (a : BitVec 64) (p : MessagePayload P) : SepProp :=
  let toC := fun c : P.Chunk => ({ index := P.chunkIndex c, data := P.chunkData c } : Chunk)
  match p with
  | .none =>
      ((a + 0x08#64) ↦₈ 0#8) ∗ memRegion (a + 0x09#64) 39
  | .hdr c =>
      ((a + 0x08#64) ↦₈ 1#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ek c =>
      ((a + 0x08#64) ↦₈ 2#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ekCt1Ack c =>
      ((a + 0x08#64) ↦₈ 3#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ct1Ack b =>
      ((a + 0x08#64) ↦₈ 4#8) ∗ ((a + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗
        memRegion (a + 0x0a#64) 38
  | .ct1 c =>
      ((a + 0x08#64) ↦₈ 5#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ct2 c =>
      ((a + 0x08#64) ↦₈ 6#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4

/-- Memory representation of `spqr::v1::chunked::states::Message` (`48` bytes at `a`). -/
@[expose] def messageAt (P : PolyApi) (a : BitVec 64) (m : Message P) : SepProp :=
  (a ↦₆₄ m.epoch) ∗ messagePayloadAt P a m.payload

/-! ## 2. Symbol Name, Stack Budget, and Specification of `<Message>::serialize` -/

abbrev messageSerializeName : String :=
  "<spqr::v1::chunked::states::Message>::serialize"

/-- Stack budget for `<Message>::serialize`:
    * own frame `0x50 = 80` bytes (`+0x000: sub sp, sp, #0x50`);
    * calls `spqr::encode_varint` (`spqrEncodeVarintStackX = 0x50 + extHookStack = 16464`) and
    `do_reserve_and_handle [local#7]` (`doReserveStack = 4208 ≤ spqrEncodeVarintStackX`). -/
abbrev messageSerializeStackX : Nat := 0x50 + spqrEncodeVarintStackX

/-- Ghost state for `<Message>::serialize`: `(msgA, index, ret, msg)`. -/
structure MessageSerializeGhost (P : PolyApi) where
  msgA : BitVec 64
  index : BitVec 32
  ret : BitVec 64
  msg : Message P

/-- Specification of `<spqr::v1::chunked::states::Message>::serialize` against `Message.serialize`:
    * `x0 = x.msgA` (`&Message`), `w1 = x.index` (`u32`), `x8 = x.ret` (`*mut Vec<u8>`).
    * Preserves `messageAt P x.msgA x.msg` and writes `vecU8 A x.ret (x.msg.serialize x.index)`.
    * Panics only on OOM (`allocFailedIn`). -/
@[expose] def messageSerializeSpecX (P : PolyApi) (A : RustAlloc) : Spec (MessageSerializeGhost P) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret⌝ ∗
      messageAt P x.msgA x.msg ∗ memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp messageSerializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      messageAt P x.msgA x.msg ∗
      vecU8 A x.ret (x.msg.serialize x.index) ∗
      A.pool ∗ stackAt s0.sp messageSerializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem encodeVarintLoop_length_le (fuel : Nat) (a : BitVec 64) :
    (encodeVarintLoop fuel a).length ≤ fuel := by
  induction fuel generalizing a with
  | zero => simp [encodeVarintLoop]
  | succ fuel ih =>
    simp only [encodeVarintLoop]; split
    · simp
    · simp only [List.length_cons]; have := ih (a >>> 7); omega

theorem encode_varint_eq_append (a : BitVec 64) (into : Bytes) :
    CryptoVerification.LibsignalSpqrV1.encode_varint a into =
      into ++ encodeVarintLoop MAX_VARINT_BYTES_LEN a := rfl

theorem encode_varint_length_le (a : BitVec 64) (into : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint a into).length ≤ into.length + 10 := by
  rw [encode_varint_eq_append, List.length_append]
  have h := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN a
  have hm : MAX_VARINT_BYTES_LEN = 10 := rfl; omega

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem stackAt_messageSerialize_eq (sp : BitVec 64) :
    stackAt sp messageSerializeStackX =
      stackAt (sp - 80#64) spqrEncodeVarintStackX ∗
      (∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
       ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗ ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (spqrEncodeVarintStackX + 8 * 10) = _
  rw [ProofLib.stackAt_split_cells sp spqrEncodeVarintStackX 10 (by decide)]; congr 1; cells_unfold

theorem stackAt_spqrEncodeVarint_to_allocHook (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      memRegion (sp - 16464#64) 12368 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 allocHookStack = sp - BitVec.ofNat 64 spqrEncodeVarintStackX + 12368#64 := by
    change sp - 4096#64 = sp - 16464#64 + 12368#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 spqrEncodeVarintStackX)
    (n := 12368) (k := allocHookStack) (b' := sp - BitVec.ofNat 64 allocHookStack) rfl hbase (by decide)

theorem stackAt_spqrEncodeVarint_to_doReserve (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      memRegion (sp - 16464#64) 12256 ∗ stackAt sp doReserveStack := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 doReserveStack = sp - BitVec.ofNat 64 spqrEncodeVarintStackX + 12256#64 := by
    change sp - 4208#64 = sp - 16464#64 + 12256#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 spqrEncodeVarintStackX)
    (n := 12256) (k := doReserveStack) (b' := sp - BitVec.ofNat 64 doReserveStack) rfl hbase (by decide)

theorem memRegion_40_split_1_39 (ptr : BitVec 64) :
    memRegion ptr 40 = (∃∗ b0 : BitVec 8, (ptr ↦₈ b0)) ∗ memRegion (ptr + 1#64) 39 := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := 1) (k := 39)
      (b' := ptr + 1#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]

@[expose] def pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem unpack64_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  dsimp only [unpack64, pack64]
  have e0 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have e1 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  have e2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
  have e3 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel
  have e4 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_kernel
  have e5 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_kernel
  have e6 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_kernel
  have e7 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_kernel
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

theorem list_eq_unpack64_of_len8 :
    ∀ (bs : List (BitVec 8)), bs.length = 8 → ∃ w : BitVec 64, bs = unpack64 w
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    ⟨pack64 b0 b1 b2 b3 b4 b5 b6 b7, (unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7).symm⟩

theorem list_eq_unpack64_4_of_len32 (ds : List (BitVec 8)) (h : ds.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ds = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 := by
  let l1 := ds.drop 8; let l2 := l1.drop 8; let l3 := l2.drop 8
  have h3 : l2.take 8 ++ l3 = l2 := List.take_append_drop 8 l2
  have h2 : l1.take 8 ++ l2 = l1 := List.take_append_drop 8 l1
  have h1 : ds.take 8 ++ l1 = ds := List.take_append_drop 8 ds
  have hsplit : ds = ds.take 8 ++ l1.take 8 ++ l2.take 8 ++ l3 := by
    rw [List.append_assoc (ds.take 8 ++ l1.take 8), h3, List.append_assoc (ds.take 8), h2, h1]
  obtain ⟨w0, hw0⟩ := list_eq_unpack64_of_len8 (ds.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := list_eq_unpack64_of_len8 (l1.take 8) (by simp [l1, h])
  obtain ⟨w2, hw2⟩ := list_eq_unpack64_of_len8 (l2.take 8) (by simp [l2, l1, h])
  obtain ⟨w3, hw3⟩ := list_eq_unpack64_of_len8 l3 (by simp [l3, l2, l1, h])
  exact ⟨w0, w1, w2, w3, by rw [hsplit, hw0, hw1, hw2, hw3]⟩

theorem pointsToBytes_unpack64_4_eq (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (a ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3)) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  have hlen : ∀ w : BitVec 64, (unpack64 w).length = 8 := fun _ => rfl
  rw [List.append_assoc (unpack64 w0 ++ unpack64 w1) (unpack64 w2) (unpack64 w3),
    List.append_assoc (unpack64 w0) (unpack64 w1) (unpack64 w2 ++ unpack64 w3),
    pointsToBytes_append, hlen w0, pointsToBytes_append, hlen w1, pointsToBytes_append, hlen w2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

theorem memRegion_32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗ (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗ (∃∗ d0 : BitVec 64, a ↦₆₄ d0) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]
  ac_rfl

theorem vecU8At_eq_header_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Buf; simp only [BitVec.ofNat_eq_ofNat]; ac_rfl

theorem pointsTo64_pair (a lo hi : BitVec 64) :
    (a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi) = (a ↦₁₂₈ (hi ++ lo)) := by
  unfold pointsTo128; rw [extractLsb_lo_append64, extractLsb_hi_append64]

theorem vecU8At_init_40_one (A : RustAlloc) (v ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ 40#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64) ∗
      A.live ptr 40 1 ∗ (ptr ↦₈ 1#8) ∗ memRegion (ptr + 1#64) 39) =
    vecU8At A v 40#64 ptr [1#8] := by
  rw [vecU8At_eq_header_buf]; unfold vecU8Buf
  have h40_ne : (40#64 : BitVec 64) ≠ 0#64 := by decide
  have h40_toNat : (40#64 : BitVec 64).toNat = 40 := rfl
  have h1 : (ptr ↦ₛ [1#8]) = (ptr ↦₈ 1#8) := by rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, h40_ne, ↓reduceIte,
    h40_toNat, h1, Nat.reduceSub]
  have hpure : ((1 : Nat) ≤ 40 ∧ 40 < 2 ^ 63 ∧ ptr ≠ 0#64) = True := by simp [hptr]
  rw [hpure, pure_true, emp_sepConj]

/-- Callee-saved registers `x23..x28`, `calleeSavedVRegs`, + `StepInv` preserved across
    `<Message>::serialize`. -/
@[expose] def MsgSerializeCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧ StepInv s0 s

theorem MsgSerializeCalleeSaved.refl (s : State) : MsgSerializeCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s⟩

theorem MsgSerializeCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : MsgSerializeCalleeSaved s0 s1) (h2 : MsgSerializeCalleeSaved s1 s2) :
    MsgSerializeCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2⟩

theorem MsgSerializeCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : MsgSerializeCalleeSaved s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

@[expose] def vecRest32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))

theorem vecU8Buf_eq_open_32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length + 32 ≤ cap.toNat) :
    vecU8Buf A cap ptr bs =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ d0) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ d1) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ d2) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ d3) ∗
        vecRest32 A cap ptr bs) := by
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hle
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecRest32
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) 32 (cap.toNat - (bs.length + 32)) (by omega)
  rw [show 32 + (cap.toNat - (bs.length + 32)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add, memRegion_32_words4] at hsplit
  rw [hsplit]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext d0; congr 1; funext d1; congr 1; funext d2; congr 1; funext d3; ac_rfl

theorem vecU8Buf_append_32_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs ds : List (BitVec 8))
    (w0 w1 w2 w3 : BitVec 64)
    (hle : bs.length + 32 ≤ cap.toNat)
    (hds : ds = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3)
    (hlen32 : ds.length = 32) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) ∗
    vecRest32 A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ ds) := by
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hle
  unfold vecU8Buf vecRest32
  simp only [hne, ↓reduceIte]
  have h4 :
      ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) =
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ ds) := by
    rw [hds, pointsToBytes_unpack64_4_eq]
  have hreassoc :
      ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) ∗
      (⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))) =
      ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗
          (((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3))) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) := by
    ac_rfl
  rw [hreassoc, h4, ← pointsToBytes_append]
  simp only [List.length_append, hlen32]

attribute [local irreducible] Program.fnAddr

theorem rem40_ult_31_of_le {n : Nat} (hle : n + 32 ≤ 40) :
    (31#64).ult (40#64 - BitVec.ofNat 64 n) = true ∧
    (40#64 - BitVec.ofNat 64 n).ule 31#64 = false := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (40#64 - BitVec.ofNat 64 n).toNat = 40 - n := by
    rw [BitVec.toNat_sub_of_le]
    · simp [hn]
    · rw [BitVec.le_def, hn]; change n ≤ 40; omega
  rw [BitVec.ult_eq_decide, BitVec.ule_eq_decide, hsub]
  change decide (31 < 40 - n) = true ∧ decide (40 - n ≤ 31) = false
  exact ⟨decide_eq_true (by omega), decide_eq_false (by omega)⟩

theorem rem40_ult_31_of_gt {n : Nat} (hgt : ¬ (n + 32 ≤ 40)) (hle40 : n ≤ 40) :
    (31#64).ult (40#64 - BitVec.ofNat 64 n) = false ∧
    (40#64 - BitVec.ofNat 64 n).ule 31#64 = true := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (40#64 - BitVec.ofNat 64 n).toNat = 40 - n := by
    rw [BitVec.toNat_sub_of_le]
    · simp [hn]
    · rw [BitVec.le_def, hn]; change n ≤ 40; omega
  rw [BitVec.ult_eq_decide, BitVec.ule_eq_decide, hsub]
  change decide (31 < 40 - n) = false ∧ decide (40 - n ≤ 31) = true
  exact ⟨decide_eq_false (by omega), decide_eq_true (by omega)⟩

theorem vecU8At_sp72_eq (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 72#64) cap ptr bs =
      ((sp - 72#64) ↦₆₄ cap) ∗ ((sp - 64#64) ↦₆₄ ptr) ∗
      ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_buf]; simp only [arm64_norm]

/-! ## 4. Epilogue & Chunk Step Lemmas for `<Message>::serialize` -/

end CryptoVerification.SpqrV1.Top.MessageSerialize
