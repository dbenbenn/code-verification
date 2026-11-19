/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Chunked Braid Send-Chunk Leaf Transitions 2 (`SendChunk2`)

**Checked by Lean.** Verifies `<Ct1Received>::send_ek_chunk` (`0x5e250`, `41` insns) and
`<Ct1Sampled>::send_ct1_chunk` (`0x5d7bc`, `41` insns).
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk (polyNextChunkStack)
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. 13-Word Unfolding Helpers for `unchunkedEkSentCt1ReceivedAt` (`104` bytes) -/

theorem wordsAt_13 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
      ((a + 96#64) ↦₆₄ w12) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]

theorem cells_13_unfold (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7,
      ∃∗ v8, ∃∗ v9, ∃∗ v10, ∃∗ v11, ∃∗ v12,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] := by
  rw [ProofLib.memRegion_cells a 13 (by decide), cells_succ]
  simp only [wordsAt_13, cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl,
    show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl,
    show (64#64 + 8#64 : BitVec 64) = 72#64 from rfl,
    show (72#64 + 8#64 : BitVec 64) = 80#64 from rfl,
    show (80#64 + 8#64 : BitVec 64) = 88#64 from rfl,
    show (88#64 + 8#64 : BitVec 64) = 96#64 from rfl]
  exact Entails.refl _

/-! ## 2. Proof 5: `<Ct1Received>::send_ek_chunk` (`0x5e250`, 41 insns) -/

theorem stackAt_944_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 944) =
      stackAt (sp - 944#64) polyNextChunkStack ∗
      memRegion (sp - 944#64) 8 ∗
      memRegion (sp - 936#64) 400 ∗
      memRegion (sp - 536#64) 400 ∗
      memRegion (sp - 136#64) 104 ∗
      memRegion (sp - 32#64) 32 := by
  change memRegion (sp - 19376#64) 19376 =
    memRegion (sp - 944#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 944#64 - 18432#64 = sp - 19376#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19376#64) (n := 18432) (k := 944)
        (b' := sp - 944#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 944#64) (n := 8) (k := 936)
        (b' := sp - 936#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 936#64) (n := 400) (k := 536)
        (b' := sp - 536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 536#64) (n := 400) (k := 136)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 104) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]

theorem stackAt_944_rejoin (sp w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 944#64) polyNextChunkStack ∗
      memRegion (sp - 944#64) 8 ∗
      memRegion (sp - 936#64) 400 ∗
      memRegion (sp - 536#64) 504 ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
    stackAt sp (polyNextChunkStack + 944) := by
  have h4 :
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
      memRegion (sp - 32#64) 32 := by
    have heq :
        (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
         ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) =
        wordsAt (sp - 32#64) [w0, w1, w2, w3] := by
      simp only [wordsAt_4, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3] (sp - 32#64) 32 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h4)))) ?_
  rw [stackAt_944_split sp,
      ProofLib.memRegion_split' (b := sp - 536#64) (n := 400) (k := 104)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt1ReceivedAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ek := outSt.sending_ek }) :
    polyEncoderAt A (sp - 536#64) outSt.sending_ek ∗
      unchunkedEkSentCt1ReceivedAt A (sp - 136#64) st.uc ⊢
    chunkedCt1ReceivedAt A (sp - 536#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hoff : (sp - 536#64) + 400#64 = sp - 136#64 := by bv_omega
  unfold chunkedCt1ReceivedAt
  rw [huc, hoff]
  exact Entails.refl _

theorem stackAt_1376_split (sp : BitVec 64) :
    stackAt sp (polyNextChunkStack + 1376) =
      stackAt (sp - 1376#64) polyNextChunkStack ∗
      memRegion (sp - 1376#64) 8 ∗
      memRegion (sp - 1368#64) 392 ∗
      memRegion (sp - 976#64) 400 ∗
      memRegion (sp - 576#64) 128 ∗
      memRegion (sp - 448#64) 400 ∗
      memRegion (sp - 48#64) 48 := by
  change memRegion (sp - 19808#64) 19808 =
    memRegion (sp - 1376#64 - 18432#64) 18432 ∗ _
  have hsub : sp - 1376#64 - 18432#64 = sp - 19808#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 19808#64) (n := 18432) (k := 1376)
        (b' := sp - 1376#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1376#64) (n := 8) (k := 1368)
        (b' := sp - 1368#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1368#64) (n := 392) (k := 976)
        (b' := sp - 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 400) (k := 576)
        (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 128) (k := 448)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 448#64) (n := 400) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide)]

theorem stackAt_1376_rejoin (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    stackAt (sp - 1376#64) polyNextChunkStack ∗
      memRegion (sp - 1376#64) 400 ∗
      memRegion (sp - 976#64) 928 ∗
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
    stackAt sp (polyNextChunkStack + 1376) := by
  have h6 :
      (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
       ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 48#64) 48 := by
    have heq :
        (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗ ((sp - 32#64) ↦₆₄ w2) ∗
         ((sp - 24#64) ↦₆₄ w3) ∗ ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) =
        wordsAt (sp - 48#64) [w0, w1, w2, w3, w4, w5] := by
      simp only [wordsAt_6, arm64_norm]
    rw [heq]
    exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp - 48#64) 48 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h6))) ?_
  rw [stackAt_1376_split sp,
      ProofLib.memRegion_split' (b := sp - 1376#64) (n := 8) (k := 392)
        (b' := sp - 1368#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 400) (k := 528)
        (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 128) (k := 400)
        (b' := sp - 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedCt1SampledAt_recompose_sp (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (st outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := st.uc, sending_ct1 := outSt.sending_ct1, receiving_ek := st.receiving_ek }) :
    polyEncoderAt A (sp - 976#64) outSt.sending_ct1 ∗
      unchunkedCt1SentAt A (sp - 576#64) st.uc ∗
      polyDecoderAt A (sp - 448#64) st.receiving_ek ⊢
    chunkedCt1SampledAt A (sp - 976#64) outSt := by
  have huc : st.uc = outSt.uc := by rw [hout]
  have hdec : st.receiving_ek = outSt.receiving_ek := by rw [hout]
  have hoff1 : (sp - 976#64) + 400#64 = sp - 576#64 := by bv_omega
  have hoff2 : (sp - 976#64) + 528#64 = sp - 448#64 := by bv_omega
  unfold chunkedCt1SampledAt
  rw [huc, hdec, hoff1, hoff2]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.Leaves
