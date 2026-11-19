/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgByteFrame msg_expose_byte msg_unexpose_byte
   varint_out_norm list_cons_of_length_pos
   nat_le_of_bv_ule nat_lt_of_not_bv_ule
   hb_ne_of_sxtb_tb hb_eq_of_not_sxtb_tb
   csel_rest1_min_10 rest1_nil_of_ule rest1_cons_of_not_ule
   index_bounds_ne varint_end_of_ge varint_cont_of_lt
   msgHeaderTail msg_expose_hdr msg_unexpose_hdr
   msg_nil_of_len_zero msg_singleton_of_len_one msg_cons_cons_of_len_ge_two)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Empty-message preamble path (`+292 .. +308 -> +312`) -/

theorem sp_sub_4192_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

theorem stackAt_spqrRecvCallee_split (sp : BitVec 64) (k : Nat)
    (hk : k ≤ spqrRecvCalleeStackX) :
    stackAt sp spqrRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 spqrRecvCalleeStackX) (spqrRecvCalleeStackX - k) ∗
      stackAt sp k := by
  simp only [stackAt]
  have h1 : spqrRecvCalleeStackX - k + k = spqrRecvCalleeStackX := by omega
  have hbound : spqrRecvCalleeStackX - k + k ≤ 2 ^ 64 := by
    unfold spqrRecvCalleeStackX at hk ⊢; omega
  have hsplit := ProofLib.memRegion_split (sp - BitVec.ofNat 64 spqrRecvCalleeStackX)
    (spqrRecvCalleeStackX - k) k hbound
  rw [h1] at hsplit
  have haddr : (sp - BitVec.ofNat 64 spqrRecvCalleeStackX) +
      BitVec.ofNat 64 (spqrRecvCalleeStackX - k) = sp - BitVec.ofNat 64 k := by
    have h2 : spqrRecvCalleeStackX < 2 ^ 64 := by decide
    bv_omega
  rw [hsplit, haddr]

/-- Expose the 3 words `(a + 8, a + 16, a + 24)` of an error sret payload `((a + 8#64) ↦₈ tag) ∗
    memRegion (a + 9#64) n` (for `23 ≤ n`). -/
theorem err_payload_expose (a : BitVec 64) (tag : BitVec 8) (n : Nat)
    (hn : 23 ≤ n) (hn_bound : n ≤ 2 ^ 64) :
    ((a + 8#64) ↦₈ tag) ∗ memRegion (a + 9#64) n ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∀ r : BitVec 64, ((r + 8#64) ↦₆₄ w1) ⊢ ((r + 8#64) ↦₈ tag) ∗ memRegion (r + 9#64) 7⌝ ∗
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) (n - 23) := by
  have hsplit1 : n = 7 + (8 + (8 + (n - 23))) := by omega
  conv_lhs => rw [hsplit1]
  rw [memRegion_split (a + 9#64) 7 (8 + (8 + (n - 23))) (by omega),
      show a + 9#64 + 7#64 = a + 16#64 by bv_arith,
      memRegion_split (a + 16#64) 8 (8 + (n - 23)) (by omega),
      show a + 16#64 + 8#64 = a + 24#64 by bv_arith,
      memRegion_split (a + 24#64) 8 (n - 23) (by omega),
      show a + 24#64 + 8#64 = a + 32#64 by bv_arith,
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64),
      memRegion_eq_exists_bytes (a + 9#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro bs7
  have hpull :
      (((a + 8#64) ↦₈ tag) ∗ (⌜bs7.length = 7⌝ ∗ ((a + 9#64) ↦ₛ bs7)) ∗
       ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 32#64) (n - 23)) =
      ⌜bs7.length = 7⌝ ∗
        ((((a + 8#64) ↦₈ tag) ∗ ((a + 9#64) ↦ₛ bs7)) ∗
         ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ memRegion (a + 32#64) (n - 23)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hbs7
  have h8 : (tag :: bs7).length = 8 := by simp [hbs7]
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h8
  have hw1_eq : ∀ r : BitVec 64,
      ((r + 8#64) ↦₆₄ w1) = (((r + 8#64) ↦₈ tag) ∗ ((r + 9#64) ↦ₛ bs7)) := by
    intro r
    rw [pointsTo64_eq_pointsToBytes, ← hw1, pointsToBytes_cons,
        show (r + 8#64) + 1#64 = r + 9#64 by bv_arith]
  have hw1_ent : ∀ r : BitVec 64,
      ((r + 8#64) ↦₆₄ w1) ⊢ ((r + 8#64) ↦₈ tag) ∗ memRegion (r + 9#64) 7 := by
    intro r
    rw [hw1_eq r, ← hbs7]
    exact sepConj_mono_right (pointsToBytes_entails_memRegion (r + 9#64) bs7)
  rw [← hw1_eq a]
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  apply Entails.pure_right hw1_ent
  exact Entails.of_eq (by ac_rfl)

/-- Fold `recvResultExactKeyAt A r (.error sd)` from 4 words `(-1, w1, w2, w3)` when `w1`
    carries `tag` in its low byte. -/
theorem recv_err_words_foldX (A : RustAlloc) (r w1 w2 w3 : BitVec 64) (tag : BitVec 8) (sd : Bool)
    (hsd : tag = 0#8 ↔ sd = true)
    (hw1 : ∀ r' : BitVec 64, ((r' + 8#64) ↦₆₄ w1) ⊢ ((r' + 8#64) ↦₈ tag) ∗ memRegion (r' + 9#64) 7) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((r + 8#64) ↦₆₄ w1) ∗
      ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗ memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error sd) := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (hw1 r))) ?_
  rw [sepConj_assoc]
  exact recv_err_byte_foldX A r w2 w3 tag sd hsd

theorem head32_tail_entails_memRegion (a w0 w1 w2 w3 : BitVec 64) (k m : Nat)
    (hm : 32 + k = m) (hbound : m ≤ 2 ^ 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      memRegion (a + 32#64) k ⊢
    memRegion a m := by
  have hm' : m = 8 + (8 + (8 + (8 + k))) := by omega
  rw [hm',
      memRegion_split a 8 (8 + (8 + (8 + k))) (by omega),
      memRegion_split (a + 8#64) 8 (8 + (8 + k)) (by omega),
      show a + 8#64 + 8#64 = a + 16#64 by bv_arith,
      memRegion_split (a + 16#64) 8 (8 + k) (by omega),
      show a + 16#64 + 8#64 = a + 24#64 by bv_arith,
      memRegion_split (a + 24#64) 8 k (by omega),
      show a + 24#64 + 8#64 = a + 32#64 by bv_arith]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))

/-- Split `protoPqRatchetStateAt H_inner A a st` into its first 4 words `w0, w1, w2, w3` (`32`B)
    and a `320`-byte slice `bs320` at `a + 32#64` (for `+328 .. +404`). -/
theorem protoPqRatchetStateAt_entails_head32_tail320 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (st : PqRatchetState) :
    DecodeState.protoPqRatchetStateAt H_inner A a st ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ bs320 : List (BitVec 8),
        ⌜w0 ≠ DecodeState.none2Cap ∧ bs320.length = 320⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦ₛ bs320) ∗
        (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1
          (unpack64 w2 ++ unpack64 w3 ++ bs320) := by
  refine Entails.trans (protoPqRatchetStateAt_entails_head16_tail336 H_inner A a st) ?_
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro bs336
  apply Entails.pure_left; rintro ⟨hw0, hlen336⟩
  have h16 : (bs336.take 16).length = 16 := by simp [hlen336]
  have h320 : (bs336.drop 16).length = 320 := by simp [hlen336]
  obtain ⟨w2, w3, hw23, hp23⟩ := exists_unpack64_of_length_16 h16
  have hbs336 : bs336 = unpack64 w2 ++ unpack64 w3 ++ bs336.drop 16 := by
    conv_lhs => rw [← List.take_append_drop 16 bs336]
    rw [hw23, List.append_assoc]
  have hpts : ((a + 16#64) ↦ₛ bs336) =
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs336.drop 16) := by
    conv_lhs => rw [← List.take_append_drop 16 bs336]
    rw [pointsToBytes_append, h16, hp23 (a + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hrel :
      (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1 bs336 =
      (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1
        (unpack64 w2 ++ unpack64 w3 ++ bs336.drop 16) := by
    rw [← hbs336]
  rw [hpts, hrel]
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right (bs336.drop 16) ?_))))
  apply Entails.pure_right ⟨hw0, h320⟩
  exact Entails.of_eq (by ac_rfl)

/-- Reassemble `protoPqRatchetStateAt H_inner A a st` from its first 4 words `w0, w1, w2, w3`
    (`32`B) and the `320`-byte slice `bs320` at `a + 32#64` (`+412 .. +440`). -/
theorem head32_tail320_entails_protoPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a w0 w1 w2 w3 : BitVec 64) (bs320 : List (BitVec 8)) (st : PqRatchetState)
    (hlen320 : bs320.length = 320) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦ₛ bs320) ∗
      (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1
        (unpack64 w2 ++ unpack64 w3 ++ bs320) ⊢
    DecodeState.protoPqRatchetStateAt H_inner A a st := by
  have hlen336 : (unpack64 w2 ++ unpack64 w3 ++ bs320).length = 336 := by
    simp [hlen320]
  have hpts :
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs320) =
      ((a + 16#64) ↦ₛ (unpack64 w2 ++ unpack64 w3 ++ bs320)) := by
    rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
    simp only [unpack64_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      ← pointsTo64_eq_pointsToBytes, sepConj_assoc]
  have hgroup :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
       ((a + 32#64) ↦ₛ bs320) ∗
       (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1
         (unpack64 w2 ++ unpack64 w3 ++ bs320)) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs320)) ∗
        (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).1
          (unpack64 w2 ++ unpack64 w3 ++ bs320) := by
    ac_rfl
  rw [hgroup, hpts]
  exact head16_tail336_entails_protoPqRatchetStateAt H_inner A a w0 w1
    (unpack64 w2 ++ unpack64 w3 ++ bs320) st hlen336

/-- The 112-byte middle segment (`+16..+128`) of `PqRatchetState` given head words `w0, w1`:
    `optVersionNegotiationPBTailAt` (`32`B at `+16..+48`) followed by `optChainPBAt` (`80`B at
    `+48..+128`). -/
@[expose] def vnTailAndChainAt (A : RustAlloc) (w0 w1 : BitVec 64) (a16 : BitVec 64) (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBTailAt A w0 w1 a16 st.versionNegotiation ∗
    optChainPBAt A (a16 + 32#64) st.chain

@[expose] def relocVnTailAndChainAt (A : RustAlloc) (w0 w1 : BitVec 64) (st : PqRatchetState) :
    Σ' H, Relocatable (fun a16 => vnTailAndChainAt A w0 w1 a16 st) 112 H :=
  ⟨_, reloc_append 112 32#64
    (relocOptVersionNegotiationPBTailAt A w0 w1 st.versionNegotiation).2
    (relocOptChainPBAt A st.chain).2 rfl rfl⟩

/-- Split `protoPqRatchetStateAt H_inner A a st` into `w0, w1, w2, w3` (`32`B), `bs96` (`96`B),
    and `bs224` (`224`B) so `memcpy` (`320`B) copies `bs96 ++ bs224` and
    `optProtoPqRatchetInnerAt` can be reassembled immediately at `+408`. -/
theorem protoPqRatchetStateAt_entails_head32_bs96_bs224 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (st : PqRatchetState) :
    DecodeState.protoPqRatchetStateAt H_inner A a st ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ bs96 : List (BitVec 8), ∃∗ bs224 : List (BitVec 8),
        ⌜w0 ≠ DecodeState.none2Cap ∧ bs96.length = 96 ∧ bs224.length = 224 ∧
          (bs96 ++ bs224).length = 320⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦ₛ (bs96 ++ bs224)) ∗
        (relocVnTailAndChainAt A w0 w1 st).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
        (relocOptProtoPqRatchetInnerAt H_inner A st.inner).1 bs224 := by
  unfold DecodeState.protoPqRatchetStateAt
  refine Entails.trans (sepConj_mono_left (optVersionNegotiationPBAt_entails_head16_tail32 A a st.versionNegotiation)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  have hgroup1 :
      ((⌜w0 ≠ DecodeState.none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation) ∗
        optChainPBAt A (a + 48#64) st.chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner) =
      ⌜w0 ≠ DecodeState.none2Cap⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        vnTailAndChainAt A w0 w1 (a + 16#64) st ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner := by
    unfold vnTailAndChainAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  rw [hgroup1]
  apply Entails.pure_left; intro hw0
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono
        ((relocVnTailAndChainAt A w0 w1 st).2.to_bytes (a + 16#64))
        ((relocOptProtoPqRatchetInnerAt H_inner A st.inner).2.to_bytes (a + 128#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs224
  apply Entails.sepExists_elim; intro bs112
  have hpull :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       (⌜bs112.length = 112⌝ ∗ ((a + 16#64) ↦ₛ bs112) ∗ (relocVnTailAndChainAt A w0 w1 st).1 bs112) ∗
       (⌜bs224.length = 224⌝ ∗ ((a + 128#64) ↦ₛ bs224) ∗
        (relocOptProtoPqRatchetInnerAt H_inner A st.inner).1 bs224)) =
      ⌜bs112.length = 112⌝ ∗ ⌜bs224.length = 224⌝ ∗
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs112) ∗ ((a + 128#64) ↦ₛ bs224) ∗
         (relocVnTailAndChainAt A w0 w1 st).1 bs112 ∗
         (relocOptProtoPqRatchetInnerAt H_inner A st.inner).1 bs224) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hlen112
  apply Entails.pure_left; intro hlen224
  have h16 : (bs112.take 16).length = 16 := by simp [hlen112]
  have h96 : (bs112.drop 16).length = 96 := by simp [hlen112]
  obtain ⟨w2, w3, hw23, hp23⟩ := exists_unpack64_of_length_16 h16
  have hbs112 : bs112 = unpack64 w2 ++ unpack64 w3 ++ bs112.drop 16 := by
    conv_lhs => rw [← List.take_append_drop 16 bs112]
    rw [hw23, List.append_assoc]
  have hpts112 : ((a + 16#64) ↦ₛ bs112) =
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs112.drop 16) := by
    conv_lhs => rw [← List.take_append_drop 16 bs112]
    rw [pointsToBytes_append, h16, hp23 (a + 16#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hpts320 :
      ((a + 32#64) ↦ₛ (bs112.drop 16 ++ bs224)) =
      ((a + 32#64) ↦ₛ bs112.drop 16) ∗ ((a + 128#64) ↦ₛ bs224) := by
    rw [pointsToBytes_append, h96]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hrel112 :
      (relocVnTailAndChainAt A w0 w1 st).1 bs112 =
      (relocVnTailAndChainAt A w0 w1 st).1 (unpack64 w2 ++ unpack64 w3 ++ bs112.drop 16) := by
    rw [← hbs112]
  have hlen320 : (bs112.drop 16 ++ bs224).length = 320 := by
    rw [List.length_append, h96, hlen224]
  rw [hpts112, hrel112]
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right (bs112.drop 16) (Entails.sepExists_right bs224 ?_)))))
  apply Entails.pure_right ⟨hw0, h96, hlen224, hlen320⟩
  rw [hpts320]
  exact Entails.of_eq (by ac_rfl)

/-- Right after `memcpy` (`+404`), split `(a + 32#64) ↦ₛ (bs96 ++ bs224)` and reassemble
    `optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner`. -/
theorem bs320_entails_bs96_inner (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (bs96 bs224 : List (BitVec 8)) (st : PqRatchetState)
    (h96 : bs96.length = 96) (h224 : bs224.length = 224) :
    ((a + 32#64) ↦ₛ (bs96 ++ bs224)) ∗
      (relocOptProtoPqRatchetInnerAt H_inner A st.inner).1 bs224 ⊢
    ((a + 32#64) ↦ₛ bs96) ∗
      DecodeState.optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner := by
  have hpts : ((a + 32#64) ↦ₛ (bs96 ++ bs224)) =
      ((a + 32#64) ↦ₛ bs96) ∗ ((a + 128#64) ↦ₛ bs224) := by
    rw [pointsToBytes_append, h96]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hpts, sepConj_assoc]
  exact sepConj_mono_right ((relocOptProtoPqRatchetInnerAt H_inner A st.inner).2.of_bytes (a + 128#64) bs224 h224)

/-- Right after `+440`, reassemble `optVersionNegotiationPBTailAt` and `optChainPBAt` from `w2,
    w3, bs96`. -/
theorem head16_bs96_entails_vnTailAndChainAt (A : RustAlloc)
    (a w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8)) (st : PqRatchetState)
    (h96 : bs96.length = 96) :
    ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs96) ∗
      (relocVnTailAndChainAt A w0 w1 st).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ⊢
    optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation ∗
      optChainPBAt A (a + 48#64) st.chain := by
  have hlen112 : (unpack64 w2 ++ unpack64 w3 ++ bs96).length = 112 := by simp [h96]
  have hpts :
      ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs96) =
      ((a + 16#64) ↦ₛ (unpack64 w2 ++ unpack64 w3 ++ bs96)) := by
    rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
    simp only [unpack64_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      ← pointsTo64_eq_pointsToBytes, sepConj_assoc]
  have hgroup :
      (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs96) ∗
       (relocVnTailAndChainAt A w0 w1 st).1 (unpack64 w2 ++ unpack64 w3 ++ bs96)) =
      (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦ₛ bs96)) ∗
        (relocVnTailAndChainAt A w0 w1 st).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) := by
    ac_rfl
  rw [hgroup, hpts]
  have h := (relocVnTailAndChainAt A w0 w1 st).2.of_bytes (a + 16#64)
    (unpack64 w2 ++ unpack64 w3 ++ bs96) hlen112
  unfold vnTailAndChainAt at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- Expose the low byte `v.truncate 8` of a 32-bit cell `a ↦₃₂ v` (for `ldrb w9, [sp, #0x28]` at
    `+448`). -/
theorem pointsTo32_expose_byte0 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) = ((a ↦₈ v.truncate 8) ∗ ((a + 1#64) ↦ₛ (unpack32 v).tail)) := by
  have h0 : v.extractLsb' 0 8 = v.truncate 8 := by revert v; bv_kernel
  have hu : unpack32 v = v.truncate 8 :: (unpack32 v).tail := by
    rw [← h0]; rfl
  rw [pointsTo32_eq_pointsToBytes]
  conv_lhs => rw [hu]
  rw [pointsToBytes_cons]

theorem pointsTo32_unexpose_byte0 (a : BitVec 64) (v : BitVec 32) :
    ((a ↦₈ v.truncate 8) ∗ ((a + 1#64) ↦ₛ (unpack32 v).tail)) ⊢ (a ↦₃₂ v) := by
  rw [← pointsTo32_expose_byte0]
  exact Entails.refl _

/-- Expose the `minVersion` low byte at `a + 40#64` inside `versionNegotiationPBTailAt (a +
    16#64) vn`. -/
theorem versionNegotiationPBTailAt_expose_minVersion (a : BitVec 64) (vn : VersionNegotiationPB) :
    versionNegotiationPBTailAt (a + 16#64) vn ⊢
      ((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗
      (∃∗ P : SepProp,
        ⌜((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗ P ⊢ versionNegotiationPBTailAt (a + 16#64) vn⌝ ∗ P) := by
  let P_rest :=
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      optChainParamsPBAt (a + 24#64) vn.chainParams ∗
      ((a + 36#64) ↦₃₂ vn.direction) ∗
      (((a + 40#64) + 1#64) ↦ₛ (unpack32 vn.minVersion).tail) ∗
      memRegion (a + 44#64) 4
  have hre : ((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗ P_rest ⊢
      versionNegotiationPBTailAt (a + 16#64) vn := by
    unfold versionNegotiationPBTailAt P_rest
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pointsTo32_expose_byte0 (a + 40#64) vn.minVersion]
    exact Entails.of_eq (by ac_rfl)
  conv_lhs =>
    unfold versionNegotiationPBTailAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pointsTo32_expose_byte0 (a + 40#64) vn.minVersion]
  have hpull :
      (((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
       optChainParamsPBAt (a + 24#64) vn.chainParams ∗
       ((a + 36#64) ↦₃₂ vn.direction) ∗
       (((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗
        (((a + 40#64) + 1#64) ↦ₛ (unpack32 vn.minVersion).tail)) ∗
       memRegion (a + 44#64) 4) =
      ((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗ P_rest := by
    unfold P_rest; ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right P_rest ?_
  exact Entails.pure_right hre (Entails.refl _)

theorem versionNegotiationPBTailAt_unexpose_minVersion (a : BitVec 64) (vn : VersionNegotiationPB) :
    ((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗
      (∃∗ P : SepProp,
        ⌜((a + 40#64) ↦₈ vn.minVersion.truncate 8) ∗ P ⊢ versionNegotiationPBTailAt (a + 16#64) vn⌝ ∗ P) ⊢
    versionNegotiationPBTailAt (a + 16#64) vn := by
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [← sepConj_assoc, sepConj_comm ((a + 40#64) ↦₈ vn.minVersion.truncate 8) ⌜_⌝, sepConj_assoc]
  apply Entails.pure_left; intro hP
  exact hP

/-- Extract `w0.toNat < 2 ^ 63` from `vecU8Heap A w0 w1 bs` without consuming it. -/
theorem vecU8Heap_cap_lt (A : RustAlloc) (w0 w1 : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Heap A w0 w1 bs ⊢ ⌜w0.toNat < 2 ^ 63⌝ ∗ vecU8Heap A w0 w1 bs := by
  unfold vecU8Heap
  apply Entails.pure_left; rintro ⟨hlen, hlt, hne⟩
  apply Entails.pure_right hlt
  apply Entails.pure_right ⟨hlen, hlt, hne⟩
  exact Entails.refl _

/-- Convert `(a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ optVersionNegotiationPBTailAt A w0 w1 (a +
    16#64) (some vn)` into dealloc form while keeping the exact same `w0, w1`. -/
theorem vnTail_some_entails_dealloc (A : RustAlloc) (a w0 w1 : BitVec 64) (vn : VersionNegotiationPB) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) (some vn) ⊢
    ⌜w0.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32 ∗
      vecCapPtrDealloc A w0 w1 := by
  unfold optVersionNegotiationPBTailAt versionNegotiationPBTailAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := vecU8At_entails_capPtr_dealloc_lt A a w0 w1 vn.authKey
  have h2 := versionNegotiationPBTail_entails_memRegion_24 a vn
  have hjoin32 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 = memRegion (a + 16#64) 32 := by
    rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24)
          (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  have hgroup :
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
       (((a + 16#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        optChainParamsPBAt (a + 24#64) vn.chainParams ∗
        ((a + 36#64) ↦₃₂ vn.direction) ∗
        ((a + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion (a + 44#64) 4) ∗
       vecU8Heap A w0 w1 vn.authKey) =
      vecU8At A a w0 w1 vn.authKey ∗
        (optChainParamsPBAt (a + 0x18#64) vn.chainParams ∗
         ((a + 0x24#64) ↦₃₂ vn.direction) ∗
         ((a + 0x28#64) ↦₃₂ vn.minVersion) ∗
         memRegion (a + 0x2c#64) 4) := by
    rw [vecU8At_eq_header_heap]
    unfold vecHeader
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  refine Entails.pure_right hcap_lt ?_
  rw [← hjoin32]
  exact Entails.of_eq (by ac_rfl)

/-! ## Callee Relative Address Bridges and `PqRatchetState` Drop Tail (`+936 .. +1036`) -/

/-- Condition on the head word `w26` of `Drop.optProtoPqRatchetInnerAt A d opt` loaded into
    `x26` at `+412`. -/
@[expose] def InnerWordInv (opt : Option PqRatchetState.Inner) (w26 : BitVec 64) : Prop :=
  match opt with
  | none => w26 = none3Cap'
  | some (.v1 _) => ¬((w26 + 3#64 == 0#64) = true)

theorem optProtoPqRatchetInnerAt_expose_word (A : RustAlloc) (d : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    Drop.optProtoPqRatchetInnerAt A d opt ⊢
      ∃∗ w : BitVec 64,
        ⌜InnerWordInv opt w⌝ ∗
        (d ↦₆₄ w) ∗
        (∃∗ P : SepProp, ⌜(d ↦₆₄ w) ∗ P ⊢ Drop.optProtoPqRatchetInnerAt A d opt⌝ ∗ P) := by
  cases opt with
  | none =>
    dsimp only [Drop.optProtoPqRatchetInnerAt, InnerWordInv]
    refine Entails.sepExists_right none3Cap' ?_
    apply Entails.pure_right rfl
    refine sepConj_mono_right ?_
    refine Entails.sepExists_right (memRegion (d + 8#64) 216) ?_
    exact Entails.pure_right (Entails.refl _) (Entails.refl _)
  | some innerVal =>
    cases innerVal with
    | v1 v1 =>
      dsimp only [Drop.optProtoPqRatchetInnerAt, InnerWordInv]
      refine Entails.trans (optProtoInnerStateAt_expose_word A d v1.innerState) ?_
      apply Entails.sepExists_elim; intro w
      apply Entails.pure_left; intro hne3
      refine Entails.sepExists_right w ?_
      apply Entails.pure_right hne3
      exact Entails.refl _

theorem optProtoPqRatchetInnerAt_unexpose_word (A : RustAlloc) (d w : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    (d ↦₆₄ w) ∗ (∃∗ P : SepProp, ⌜(d ↦₆₄ w) ∗ P ⊢ Drop.optProtoPqRatchetInnerAt A d opt⌝ ∗ P) ⊢
      Drop.optProtoPqRatchetInnerAt A d opt := by
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [← sepConj_assoc, sepConj_comm (d ↦₆₄ w) ⌜_⌝, sepConj_assoc]
  apply Entails.pure_left; intro hP
  exact hP

theorem ownFrame_join_352_4544 (sp0 : BitVec 64) :
    memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 4544 ⊢
      memRegion (sp0 - 4992#64) 0x1320 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4992#64) (n := 352) (k := 4544)
      (b' := sp0 - 4640#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

end CryptoVerification.SpqrV1.Top.Recv

