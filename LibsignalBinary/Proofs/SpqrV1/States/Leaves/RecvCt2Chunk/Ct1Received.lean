/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::send_ek::Ct1Received>::recv_ct2_chunk` (`0x58e18`)

Verifies `<Ct1Received>::recv_ct2_chunk` (`0x58e18`, 67 instructions) against
`ct1ReceivedRecvCt2ChunkSpec A F`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

theorem wordsAt_13' (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]

theorem cells_13_unfold' (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
  rw [ProofLib.memRegion_cells a 13 (by decide), ProofLib.cells_succ]
  simp only [wordsAt_13', cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl, show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl, show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]
  exact Entails.refl _

theorem stackAt_448_split (sp : BitVec 64) :
    stackAt sp ct1ReceivedRecvCt2ChunkStack =
      memRegion (sp - 16976#64) 12224 ∗ stackAt (sp - 448#64) addChunkStack ∗
      memRegion (sp - 448#64) 128 ∗ memRegion (sp - 320#64) 128 ∗ memRegion (sp - 192#64) 128 ∗
      memRegion (sp - 64#64) 8 ∗ memRegion (sp - 56#64) 1 ∗ memRegion (sp - 55#64) 7 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 16976#64) 16976 =
    memRegion (sp - 16976#64) 12224 ∗ memRegion (sp - 448#64 - 4304#64) 4304 ∗ _
  have hsub : sp - 448#64 - 4304#64 = sp - 4752#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12224) (k := 4752) (b' := sp - 4752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4752#64) (n := 4304) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 128) (k := 320) (b' := sp - 320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 320#64) (n := 128) (k := 192) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 55) (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 55#64) (n := 7) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

theorem stackAt_448_to_dropPoly16 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    memRegion (sp - 16976#64) 12224 ∗ stackAt (sp - 448#64) addChunkStack ∗ memRegion (sp - 448#64) 400 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    memRegion (sp - 16976#64) 12848 ∗ stackAt sp dropGluePoly16Stack := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6))) ?_
  change memRegion (sp - 16976#64) 12224 ∗
      (memRegion (sp - 448#64 - 4304#64) 4304 ∗ (memRegion (sp - 448#64) 400 ∗ memRegion (sp - 48#64) 48)) ⊢
    memRegion (sp - 16976#64) 12848 ∗ memRegion (sp - 4128#64) 4128
  have hsub : sp - 448#64 - 4304#64 = sp - 4752#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 4752#64) (n := 4304) (k := 448) (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12224) (k := 4752) (b' := sp - 4752#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12848) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_448_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 16976#64) 12848 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp ct1ReceivedRecvCt2ChunkStack := by
  change memRegion (sp - 16976#64) 12848 ∗ memRegion (sp - 4128#64) 4128 ⊢ memRegion (sp - 16976#64) 16976
  rw [← ProofLib.memRegion_split' (b := sp - 16976#64) (n := 12848) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem uc_104_copy_recompose {A : RustAlloc} {F : ShaCompress}
    (outA stA : BitVec 64) (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (g : FourVecWords) :
    wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) ⊢
    unchunkedEkSentCt1ReceivedAt A outA st ∗ memRegion (stA + 400#64) 104 := by
  have h1 : wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) ⊢
      unchunkedEkSentCt1ReceivedAt A outA st := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ outA
  have h2 : wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) ⊢
      memRegion (stA + 400#64) 104 :=
    wordsAt_entails_memRegion (ekSentCt1ReceivedWordsList g st.epoch) (stA + 400#64) 104 rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt outA (ekSentCt1ReceivedWordsList g st.epoch) ∗
      relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
        (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch))) ∗
    wordsAt (stA + 400#64) (ekSentCt1ReceivedWordsList g st.epoch) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem chunkedEkSentCt1ReceivedAt_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := uc, receiving_ct2 := dec }) :
    unchunkedEkSentCt1ReceivedAt A outA uc ∗ polyDecoderAt A (outA + 104#64) dec ⊢
    chunkedEkSentCt1ReceivedAt A outA outSt := by
  subst hout; exact Entails.refl _

end CryptoVerification.SpqrV1.States.Leaves
