/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 2 (`0x61254 .. 0x61488`)

**Checked by Lean.** Verifies `polyDecoderNew1152` initialization and `hdr` copy
(`recv_hdr_chunk_init_dec_wpp`, offsets `320 .. 564`) and assembles the combined entry prefix
`recv_hdr_chunk_part1_wpp` (offsets `0 .. 564`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem exists_unpack64_of_length_64_hdr {bs : List (BitVec 8)} (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) := by
  have h1 : (bs.take 32).length = 32 := by rw [List.length_take]; omega
  have h2 : (bs.drop 32).length = 32 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, _, ha1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w4, w5, w6, w7, _, ha2⟩ := exists_unpack64_of_length_32 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  conv_lhs => rw [← List.take_append_drop 32 bs, pointsToBytes_append, h1]
  rw [ha1 a, ha2 (a + 32#64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion_64_cells_hdr (a : BitVec 64) :
    memRegion a 64 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7)) := by
  rw [ProofLib.memRegion_cells a 8 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem ct2DeallocAt_of_cells64_drop (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (hge : 64 ≤ bs.length) (hle : bs.length ≤ cap.toNat)
    (hmax : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hcap : cap ≠ 0#64) :
    ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
      ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
      ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
      ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7)) ∗
      ((ptr + 64#64) ↦ₛ bs.drop 64) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 ⊢
    ct2DeallocAt A cap ptr := by
  have h64 :
      ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
        ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3) ∗
        ((ptr + 32#64) ↦₆₄ w4) ∗ ((ptr + 40#64) ↦₆₄ w5) ∗
        ((ptr + 48#64) ↦₆₄ w6) ∗ ((ptr + 56#64) ↦₆₄ w7)) ⊢
      memRegion ptr 64 := by
    rw [memRegion_64_cells_hdr ptr]
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
        (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.refl _))))))))
  have hdrop : ((ptr + 64#64) ↦ₛ bs.drop 64) ⊢ memRegion (ptr + 64#64) (bs.length - 64) := by
    have hlen : (bs.drop 64).length = bs.length - 64 := List.length_drop
    rw [← hlen]
    exact pointsToBytes_entails_memRegion (ptr + 64#64) (bs.drop 64)
  refine Entails.trans (sepConj_mono h64 (sepConj_mono_left hdrop)) ?_
  dsimp only [ct2DeallocAt]
  refine Entails.pure_right ⟨hcap, hmax, hptr⟩ ?_
  have hsplit1 : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) :=
    ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)
  have hsplit2 : memRegion ptr bs.length =
      memRegion ptr 64 ∗ memRegion (ptr + 64#64) (bs.length - 64) :=
    ProofLib.memRegion_split' (b := ptr) (n := 64) (k := bs.length - 64)
      (b' := ptr + 64#64) (by omega) rfl (by omega)
  rw [hsplit1, hsplit2]
  exact Entails.of_eq (by ac_rfl)

theorem byte_1_entails_exists (a : BitVec 64) :
    memRegion a 1 ⊢ (∃∗ b0 : BitVec 8, a ↦₈ b0) := by
  rw [memRegion_eq_exists_bytes a 1 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b0, _ | _⟩
  · simp at hlen
  · refine Entails.sepExists_right b0 ?_
    simp [pointsToBytes_cons, pointsToBytes_nil]
    exact Entails.refl _
  · simp at hlen

theorem three_words_entails_sortedSetPtOf_new (A : RustAlloc) (b : BitVec 64) :
    (b ↦₆₄ 0#64) ∗ ((b + 8#64) ↦₆₄ 2#64) ∗ ((b + 16#64) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A b SortedSetPt.new := by
  unfold sortedSetPtOf SortedSetPt.new vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl)), sepConj_emp]
  have hpure : ([] : List Pt).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * ptStride < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hpure (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem sortedSetPtOf_new_sp (A : RustAlloc) (sp off0 off1 off2 : BitVec 64)
    (h1 : (sp - off0) + 8#64 = sp - off1)
    (h2 : (sp - off0) + 16#64 = sp - off2) :
    ((sp - off0) ↦₆₄ 0#64) ∗ ((sp - off1) ↦₆₄ 2#64) ∗ ((sp - off2) ↦₆₄ 0#64) ⊢
      sortedSetPtOf A (sp - off0) SortedSetPt.new := by
  rw [← h1, ← h2]
  exact three_words_entails_sortedSetPtOf_new A (sp - off0)

@[expose] def polyDecoderNew1152RawAt (A : RustAlloc) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    sortedSetPtListOf A (a + 24#64) (List.replicate 15 SortedSetPt.new) ∗
    ((a + 384#64) ↦₆₄ 576#64) ∗
    ((a + 392#64) ↦₈ 0#8) ∗
    memRegion (a + 393#64) 7

theorem polyDecoderNew1152RawAt_entails_polyDecoderAt (A : RustAlloc) (a : BitVec 64) :
    polyDecoderNew1152RawAt A a ⊢ polyDecoderAt A a polyDecoderNew1152 := by
  unfold polyDecoderNew1152RawAt polyDecoderAt polyDecoderNew1152
  have hpure : (List.replicate 16 SortedSetPt.new).length = NUM_POLYS ∧ 576 < 2 ^ 64 :=
    ⟨rfl, by decide⟩
  refine Entails.pure_right hpure ?_
  dsimp only [polyDecoderPtsNeededOff, polyDecoderIsCompleteOff, polyDecoderPadOff,
    polyDecoderPadSize, boolByte, NUM_POLYS, CHUNK_SIZE, sortedSetPtListOf,
    Poly.vecHeaderBytes]
  rw [show (if false = true then (1#8 : BitVec 8) else 0#8) = 0#8 from rfl]
  have h16 : List.replicate 16 SortedSetPt.new = SortedSetPt.new :: List.replicate 15 SortedSetPt.new := rfl
  rw [h16]
  dsimp only [arrayAt]
  rw [← sepConj_assoc, ← sepConj_assoc]
  have hslot0 :
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 2#64)) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
        sortedSetPtOf A a SortedSetPt.new := by
    rw [sepConj_assoc]
    exact three_words_entails_sortedSetPtOf_new A a
  refine Entails.trans (sepConj_mono_left hslot0) ?_
  exact Entails.of_eq (by ac_rfl)

theorem polyDecoderNew1152Raw_of_slots (A : RustAlloc) (sp : BitVec 64) :
    ((sp - 1136#64) ↦₆₄ 0#64) ∗
      ((sp - 1128#64) ↦₆₄ 2#64) ∗
      ((sp - 1120#64) ↦₆₄ 0#64) ∗
      sortedSetPtOf A (sp - 1112#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1088#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1064#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1040#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 1016#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 992#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 968#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 944#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 920#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 896#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 872#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 848#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 824#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 800#64) SortedSetPt.new ∗
      sortedSetPtOf A (sp - 776#64) SortedSetPt.new ∗
      ((sp - 752#64) ↦₆₄ 576#64) ∗
      ((sp - 744#64) ↦₈ 0#8) ∗
      memRegion (sp - 743#64) 7 ⊢
    polyDecoderNew1152RawAt A (sp - 1136#64) := by
  unfold polyDecoderNew1152RawAt sortedSetPtListOf
  dsimp only [Poly.vecHeaderBytes]
  simp only [List.replicate, arrayAt, wp_norm, arm64_norm, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_128_sp_1136 (sp : BitVec 64) :
    memRegion (sp - 1136#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 1136#64) ↦₆₄ v0) ∗ ((sp - 1128#64) ↦₆₄ v1) ∗ ((sp - 1120#64) ↦₆₄ v2) ∗ ((sp - 1112#64) ↦₆₄ v3) ∗
        ((sp - 1104#64) ↦₆₄ v4) ∗ ((sp - 1096#64) ↦₆₄ v5) ∗ ((sp - 1088#64) ↦₆₄ v6) ∗ ((sp - 1080#64) ↦₆₄ v7) ∗
        ((sp - 1072#64) ↦₆₄ v8) ∗ ((sp - 1064#64) ↦₆₄ v9) ∗ ((sp - 1056#64) ↦₆₄ v10) ∗ ((sp - 1048#64) ↦₆₄ v11) ∗
        ((sp - 1040#64) ↦₆₄ v12) ∗ ((sp - 1032#64) ↦₆₄ v13) ∗ ((sp - 1024#64) ↦₆₄ v14) ∗ ((sp - 1016#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 1136#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_128_sp_1008 (sp : BitVec 64) :
    memRegion (sp - 1008#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 1008#64) ↦₆₄ v0) ∗ ((sp - 1000#64) ↦₆₄ v1) ∗ ((sp - 992#64) ↦₆₄ v2) ∗ ((sp - 984#64) ↦₆₄ v3) ∗
        ((sp - 976#64) ↦₆₄ v4) ∗ ((sp - 968#64) ↦₆₄ v5) ∗ ((sp - 960#64) ↦₆₄ v6) ∗ ((sp - 952#64) ↦₆₄ v7) ∗
        ((sp - 944#64) ↦₆₄ v8) ∗ ((sp - 936#64) ↦₆₄ v9) ∗ ((sp - 928#64) ↦₆₄ v10) ∗ ((sp - 920#64) ↦₆₄ v11) ∗
        ((sp - 912#64) ↦₆₄ v12) ∗ ((sp - 904#64) ↦₆₄ v13) ∗ ((sp - 896#64) ↦₆₄ v14) ∗ ((sp - 888#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 1008#64)]
  simp only [wp_norm, arm64_norm]

theorem memRegion_128_sp_880 (sp : BitVec 64) :
    memRegion (sp - 880#64) 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        ((sp - 880#64) ↦₆₄ v0) ∗ ((sp - 872#64) ↦₆₄ v1) ∗ ((sp - 864#64) ↦₆₄ v2) ∗ ((sp - 856#64) ↦₆₄ v3) ∗
        ((sp - 848#64) ↦₆₄ v4) ∗ ((sp - 840#64) ↦₆₄ v5) ∗ ((sp - 832#64) ↦₆₄ v6) ∗ ((sp - 824#64) ↦₆₄ v7) ∗
        ((sp - 816#64) ↦₆₄ v8) ∗ ((sp - 808#64) ↦₆₄ v9) ∗ ((sp - 800#64) ↦₆₄ v10) ∗ ((sp - 792#64) ↦₆₄ v11) ∗
        ((sp - 784#64) ↦₆₄ v12) ∗ ((sp - 776#64) ↦₆₄ v13) ∗ ((sp - 768#64) ↦₆₄ v14) ∗ ((sp - 760#64) ↦₆₄ v15)) := by
  rw [memRegion_128_cells (sp - 880#64)]
  simp only [wp_norm, arm64_norm]

theorem hdrSomeBranchFrameAt_expose (sp : BitVec 64) :
    hdrSomeBranchFrameAt (sp - 1648#64) ⊢
      memRegion (sp - 1136#64) 128 ∗
      memRegion (sp - 1008#64) 128 ∗
      memRegion (sp - 880#64) 128 ∗
      (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
      (∃∗ b744 : BitVec 8, (sp - 744#64) ↦₈ b744) ∗
      memRegion (sp - 743#64) 7 ∗
      memRegion (sp - 736#64) 80 ∗
      (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 168#64) 48 ∗
      memRegion (sp - 120#64) 8 ∗
      memRegion (sp - 112#64) 16 := by
  unfold hdrSomeBranchFrameAt
  have h1 : (sp - 1648#64) + 0x200#64 = sp - 1136#64 := by bv_omega
  have h2 : (sp - 1648#64) + 0x390#64 = sp - 736#64 := by bv_omega
  have h3 : (sp - 1648#64) + 0x5a8#64 = sp - 200#64 := by bv_omega
  have h4 : (sp - 1648#64) + 0x5b0#64 = sp - 192#64 := by bv_omega
  have h5 : (sp - 1648#64) + 0x5c8#64 = sp - 168#64 := by bv_omega
  have h6 : (sp - 1648#64) + 0x5f8#64 = sp - 120#64 := by bv_omega
  have h7 : (sp - 1648#64) + 0x600#64 = sp - 112#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7,
      ProofLib.memRegion_split' (b := sp - 1136#64) (n := 128) (k := 272)
        (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 128) (k := 144)
        (b' := sp - 880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 880#64) (n := 128) (k := 16)
        (b' := sp - 752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 752#64) (n := 8) (k := 8)
        (b' := sp - 744#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 744#64) (n := 1) (k := 7)
        (b' := sp - 743#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 752#64),
      ProofLib.memRegion_eight (sp - 200#64)]
  have hcomm :
      memRegion (sp - 1136#64) 128 ∗
        memRegion (sp - 1008#64) 128 ∗
        memRegion (sp - 880#64) 128 ∗
        (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
        memRegion (sp - 744#64) 1 ∗
        memRegion (sp - 743#64) 7 ∗
        memRegion (sp - 736#64) 80 ∗
        (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
        memRegion (sp - 192#64) 24 ∗
        memRegion (sp - 168#64) 48 ∗
        memRegion (sp - 120#64) 8 ∗
        memRegion (sp - 112#64) 16 =
      memRegion (sp - 744#64) 1 ∗
        (memRegion (sp - 1136#64) 128 ∗
          memRegion (sp - 1008#64) 128 ∗
          memRegion (sp - 880#64) 128 ∗
          (∃∗ v : BitVec 64, (sp - 752#64) ↦₆₄ v) ∗
          memRegion (sp - 743#64) 7 ∗
          memRegion (sp - 736#64) 80 ∗
          (∃∗ v : BitVec 64, (sp - 200#64) ↦₆₄ v) ∗
          memRegion (sp - 192#64) 24 ∗
          memRegion (sp - 168#64) 48 ∗
          memRegion (sp - 120#64) 8 ∗
          memRegion (sp - 112#64) 16) := by ac_rfl
  simp only [sepConj_assoc]
  rw [hcomm]
  refine Entails.trans (sepConj_mono_left (byte_1_entails_exists (sp - 744#64))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem cells12_sp_96_expand_hdr (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
       ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r6 : BitVec 64, ∃∗ r7 : BitVec 64,
       ∃∗ r8 : BitVec 64, ∃∗ r9 : BitVec 64, ∃∗ r10 : BitVec 64, ∃∗ r11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗ ((sp - 80#64) ↦₆₄ r2) ∗
        ((sp - 72#64) ↦₆₄ r3) ∗ ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
        ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗ ((sp - 32#64) ↦₆₄ r8) ∗
        ((sp - 24#64) ↦₆₄ r9) ∗ ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

