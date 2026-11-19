/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

alias bv_add_lit_add_lit_ek := bv_add_lit_add_lit_recv
alias memRegion_16_entails_128_ek := memRegion_16_entails_128_recv
abbrev epilogueWords63 := writebackWords63

/-- 66 words (528 bytes): `Chunked.SendCt.EkReceivedCt1Sampled`. -/
structure Words66 where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10
  b5 : Words10
  q60 : BitVec 128
  w62 : BitVec 64
  q63 : BitVec 128
  w65 : BitVec 64

@[expose] def words66List (w : Words66) : List (BitVec 64) :=
  words10List w.b0 ++ words10List w.b1 ++ words10List w.b2 ++
  words10List w.b3 ++ words10List w.b4 ++ words10List w.b5 ++
  [w.q60.extractLsb' 0 64, w.q60.extractLsb' 64 64, w.w62,
   w.q63.extractLsb' 0 64, w.q63.extractLsb' 64 64, w.w65]

@[simp]
theorem length_words66List (w : Words66) : (words66List w).length = 66 := rfl

@[expose] def words66At (p : BitVec 64) (w : Words66) : SepProp :=
  words10At p w.b0 ∗ words10At (p + 80#64) w.b1 ∗ words10At (p + 160#64) w.b2 ∗
  words10At (p + 240#64) w.b3 ∗ words10At (p + 320#64) w.b4 ∗ words10At (p + 400#64) w.b5 ∗
  ((p + 480#64) ↦₁₂₈ w.q60) ∗ ((p + 496#64) ↦₆₄ w.w62) ∗
  ((p + 504#64) ↦₁₂₈ w.q63) ∗ ((p + 520#64) ↦₆₄ w.w65)

theorem words66At_eq_wordsAt (a : BitVec 64) (w : Words66) :
    words66At a w = wordsAt a (words66List w) := by
  unfold words66At words66List
  simp only [List.append_assoc, wordsAt_append, length_words10List,
    ← words10At_eq_wordsAt, pointsTo128_eq_pair64_recv, wordsAt, sepConj_emp,
    bv_add_lit_add_lit_recv, sepConj_assoc]

theorem words66At_entails_memRegion (a : BitVec 64) (w : Words66) :
    words66At a w ⊢ memRegion a 528 := by
  rw [words66At_eq_wordsAt]
  exact wordsAt_entails_memRegion (words66List w) a 528 rfl

theorem recompose66 {F_pred : BitVec 64 → SepProp} (dst : BitVec 64) (w : Words66) :
    words66At dst w ∗ relocatedHeap F_pred (wordsBytes (words66List w)) ⊢ F_pred dst := by
  rw [words66At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose F_pred (wordsBytes (words66List w)) dst

def mkWords66_50_16 (p : Words5x10) (g : FiveVecWords) (ep : BitVec 64) : Words66 :=
  { b0 := p.b0
    b1 := p.b1
    b2 := p.b2
    b3 := p.b3
    b4 := p.b4
    b5 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
           g.rest.rest.v1.w0, g.rest.rest.v1.w1, g.rest.rest.v1.w2, g.rest.rest.auth.v1.w0⟩
    q60 := g.rest.rest.auth.v1.w2 ++ g.rest.rest.auth.v1.w1
    w62 := g.rest.rest.auth.v2.w0
    q63 := g.rest.rest.auth.v2.w2 ++ g.rest.rest.auth.v2.w1
    w65 := ep }

theorem words66List_mkWords66_50_16 (p : Words5x10) (g : FiveVecWords) (ep : BitVec 64) :
    words5x10List p ++ fiveVecWordsList g ep = words66List (mkWords66_50_16 p g ep) := by
  simp only [words66List, mkWords66_50_16, words5x10List, words10List,
    fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
    authWordsList, vecWordsList, Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append,
    List.append_assoc, List.cons_append, List.nil_append]

theorem chunkedEkReceivedCt1SampledAt_extract66 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedEkReceivedCt1SampledAt A a st ⊢
      ∃∗ w : Words66,
        ⌜w.w65 = st.uc.epoch⌝ ∗
        words66At a w ∗
        relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) := by
  unfold chunkedEkReceivedCt1SampledAt
  refine Entails.trans (sepConj_mono
    (relocatable_400_extract_words5x10 (Relocatable.of_polyEncoderAt A st.sending_ct1) a)
    (unchunkedCt1SentEkReceivedAt_extract A (a + 400#64) st.uc)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  let w := mkWords66_50_16 p g st.uc.epoch
  refine Entails.sepExists_right w (Entails.pure_right rfl ?_)
  rw [words66At_eq_wordsAt, ← words66List_mkWords66_50_16]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

/-- 57 words (456 bytes): `Chunked.SendCt.Ct2Sampled`. -/
structure Words57 where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10
  w50 : BitVec 64
  w51 : BitVec 64
  w52 : BitVec 64
  w53 : BitVec 64
  w54 : BitVec 64
  w55 : BitVec 64
  w56 : BitVec 64

@[expose] def words57List (w : Words57) : List (BitVec 64) :=
  words10List w.b0 ++ words10List w.b1 ++ words10List w.b2 ++
  words10List w.b3 ++ words10List w.b4 ++
  [w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56]

@[simp]
theorem length_words57List (w : Words57) : (words57List w).length = 57 := rfl

@[expose] def words57At (p : BitVec 64) (w : Words57) : SepProp :=
  words10At p w.b0 ∗ words10At (p + 80#64) w.b1 ∗ words10At (p + 160#64) w.b2 ∗
  words10At (p + 240#64) w.b3 ∗ words10At (p + 320#64) w.b4 ∗
  ((p + 400#64) ↦₆₄ w.w50) ∗ ((p + 408#64) ↦₆₄ w.w51) ∗
  ((p + 416#64) ↦₆₄ w.w52) ∗ ((p + 424#64) ↦₆₄ w.w53) ∗
  ((p + 432#64) ↦₆₄ w.w54) ∗ ((p + 440#64) ↦₆₄ w.w55) ∗
  ((p + 448#64) ↦₆₄ w.w56)

theorem words57At_eq_wordsAt (a : BitVec 64) (w : Words57) :
    words57At a w = wordsAt a (words57List w) := by
  unfold words57At words57List
  simp only [List.append_assoc, wordsAt_append, length_words10List,
    ← words10At_eq_wordsAt, wordsAt, sepConj_emp,
    bv_add_lit_add_lit_recv, sepConj_assoc]

theorem words57At_entails_memRegion (a : BitVec 64) (w : Words57) :
    words57At a w ⊢ memRegion a 456 := by
  rw [words57At_eq_wordsAt]
  exact wordsAt_entails_memRegion (words57List w) a 456 rfl

theorem recompose57 {F_pred : BitVec 64 → SepProp} (dst : BitVec 64) (w : Words57) :
    words57At dst w ∗ relocatedHeap F_pred (wordsBytes (words57List w)) ⊢ F_pred dst := by
  rw [words57At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose F_pred (wordsBytes (words57List w)) dst

def mkWords57_50_7 (p : Words5x10) (g : AuthWords) (ep : BitVec 64) : Words57 :=
  { b0 := p.b0
    b1 := p.b1
    b2 := p.b2
    b3 := p.b3
    b4 := p.b4
    w50 := g.v1.w0
    w51 := g.v1.w1
    w52 := g.v1.w2
    w53 := g.v2.w0
    w54 := g.v2.w1
    w55 := g.v2.w2
    w56 := ep }

theorem words57List_mkWords57_50_7 (p : Words5x10) (g : AuthWords) (ep : BitVec 64) :
    words5x10List p ++ ct2SentWordsList g ep = words57List (mkWords57_50_7 p g ep) := by
  simp only [words57List, mkWords57_50_7, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList,
    List.append_assoc, List.cons_append, List.nil_append]

theorem chunkedCt2SampledAt_extract57 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedCt2SampledAt A a st ⊢
      ∃∗ w : Words57,
        words57At a w ∗
        relocatedHeap (fun dst => chunkedCt2SampledAt A dst st) (wordsBytes (words57List w)) := by
  unfold chunkedCt2SampledAt
  refine Entails.trans (sepConj_mono
    (relocatable_400_extract_words5x10 (Relocatable.of_polyEncoderAt A st.sending_ct2) a)
    (unchunkedCt2SentAt_extract A (a + 400#64) st.uc)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  let w := mkWords57_50_7 p g st.uc.epoch
  refine Entails.sepExists_right w ?_
  rw [words57At_eq_wordsAt, ← words57List_mkWords57_50_7]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

/-! ## 1. Pure Model Unfolding for `.ekReceivedCt1Sampled` -/

theorem states_recv_ekReceivedCt1Sampled_gt (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hgt : msg.epoch > s.uc.epoch) :
    States.recv K (.ekReceivedCt1Sampled s) msg =
      .error (.err (.epochOutOfRange msg.epoch)) := by
  simp only [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, hgt, ↓reduceIte]

theorem states_recv_ekReceivedCt1Sampled_lt (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hlt : msg.epoch < s.uc.epoch) :
    States.recv K (.ekReceivedCt1Sampled s) msg =
      .ok { key := none, state := .ekReceivedCt1Sampled s } := by
  have hnot_gt : ¬ (msg.epoch > s.uc.epoch) := by
    change ¬ (s.uc.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt)
  simp only [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, hnot_gt, hlt, ↓reduceIte]

theorem states_recv_ekReceivedCt1Sampled_eq_no_ack (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = s.uc.epoch)
    (hno : (match msg.payload with
      | .ct1Ack true => true
      | .ekCt1Ack _ => true
      | _ => false) = false) :
    States.recv K (.ekReceivedCt1Sampled s) msg =
      .ok { key := none, state := .ekReceivedCt1Sampled s } := by
  simp only [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, heq, BitVec.lt_irrefl,
    Bool.false_eq_true, ↓reduceIte]
  cases hp : msg.payload with
  | ct1Ack b =>
    rw [hp] at hno
    cases b <;> simp_all
  | _ => simp_all

theorem states_recv_ekReceivedCt1Sampled_eq_ack_ok (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (s' : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = s.uc.epoch)
    (hack : (match msg.payload with
      | .ct1Ack true => true
      | .ekCt1Ack _ => true
      | _ => false) = true)
    (hrecv : s.recv_ct1_ack K s.uc.epoch = .ok s') :
    States.recv K (.ekReceivedCt1Sampled s) msg =
      .ok { key := none, state := .ct2Sampled s' } := by
  simp only [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, heq, BitVec.lt_irrefl,
    hrecv, ↓reduceIte, StatesResult.ofPanic, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases hp : msg.payload with
  | ct1Ack b =>
    rw [hp] at hack
    cases b <;> simp_all
  | _ => simp_all

theorem states_recv_ekReceivedCt1Sampled_eq_ack_err (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (p : StatesPanic)
    (msg : Message spqrPolyApi) (heq : msg.epoch = s.uc.epoch)
    (hack : (match msg.payload with
      | .ct1Ack true => true
      | .ekCt1Ack _ => true
      | _ => false) = true)
    (hrecv : s.recv_ct1_ack K s.uc.epoch = .error p) :
    States.recv K (.ekReceivedCt1Sampled s) msg =
      .error (.panic p) := by
  simp only [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, heq, BitVec.lt_irrefl,
    hrecv, ↓reduceIte, StatesResult.ofPanic, ToStatesPanic.toStatesPanic,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases hp : msg.payload with
  | ct1Ack b =>
    rw [hp] at hack
    cases b <;> simp_all
  | _ => simp_all

/-! ## 2. Dispatch (`+36 -> +3392`) -/

@[expose] def ekUnusedRestAt (fsp : BitVec 64) : SepProp :=
  memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
  memRegion (fsp + 2736#64) 16 ∗ memRegion (fsp + 2768#64) 1088 ∗ memRegion (fsp + 3872#64) 272

theorem sendEkUnusedAt_split_ek (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qac0 : BitVec 128, ∃∗ qf10 : BitVec 128,
        ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ ekUnusedRestAt fsp := by
  unfold sendEkUnusedAt ekUnusedRestAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376) (b' := fsp + 2768#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2768#64) (n := 1088) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272) (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono (memRegion_16_entails_128_ek (fsp + 2752#64))
      (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_ek (fsp + 3856#64))))))))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro qac0
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right]; apply Entails.sepExists_elim; intro qf10
  exact Entails.sepExists_right qac0 (Entails.sepExists_right qf10 (Entails.of_eq (by ac_rfl)))

theorem ekUnusedRest_entails_sendEkUnusedAt (fsp : BitVec 64) (qac0 qf10 : BitVec 128) :
    ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ ekUnusedRestAt fsp ⊢ sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt ekUnusedRestAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376) (b' := fsp + 2768#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2768#64) (n := 1088) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272) (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ (memRegion (fsp + 568#64) 8 ∗ (memRegion (fsp + 952#64) 8 ∗
      (memRegion (fsp + 2736#64) 16 ∗ (((fsp + 2752#64) ↦₁₂₈ qac0) ∗
        (memRegion (fsp + 2768#64) 1088 ∗ (((fsp + 3856#64) ↦₁₂₈ qf10) ∗ memRegion (fsp + 3872#64) 272)))))) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 2752#64) qac0)
      (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 3856#64) qf10)))))))

@[expose] def ekLoadSpills (sp : SendEkSpills) (w : Words66) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w3 := w.b2.w9, w4 := w.b3.w2, w7 := w.b3.w8, w8 := w.b3.w4, w9 := w.b3.w3 }
    b1 := { sp.b1 with w0 := w.b5.w7, w1 := w.b5.w5, w3 := w.b3.w6, w4 := w.b5.w3, w5 := w.b3.w7, w6 := w.b0.w0, w7 := w.b5.w9 }
    b2 := { sp.b2 with w0 := w.b4.w7, w1 := w.b5.w1, w2 := w.b4.w9, w4 := w.b4.w5, w5 := w.b0.w1, w6 := w.b4.w8, w9 := w.b4.w2 }
    b3 := { sp.b3 with w0 := w.b5.w8, w1 := w.w62, w3 := w.b2.w1, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w2 := w.b1.w9, w4 := w.b2.w2, w5 := w.b0.w5, w7 := w.b1.w1, w8 := w.b2.w0 }
    b5 := { sp.b5 with w0 := w.b0.w9, w2 := w.b1.w4, w3 := w.b0.w8, w4 := w.b1.w7, w5 := w.b5.w0, w7 := w.b2.w4, w8 := w.b4.w6, w9 := w.b5.w4 }
    w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6 }

@[expose] def ekLoadSpillsA (sp : SendEkSpills) (w : Words66) : SendEkSpills :=
  { sp with
    b1 := { sp.b1 with w6 := w.b0.w0 }, b2 := { sp.b2 with w5 := w.b0.w1 }
    b3 := { sp.b3 with w3 := w.b2.w1, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w2 := w.b1.w9, w4 := w.b2.w2, w5 := w.b0.w5, w7 := w.b1.w1, w8 := w.b2.w0 }
    b5 := { sp.b5 with w0 := w.b0.w9, w2 := w.b1.w4, w3 := w.b0.w8, w4 := w.b1.w7, w7 := w.b2.w4 }
    w61 := w.b0.w2, w62 := w.b0.w6 }

@[expose] def ekCmpW8 (ps : PState) : BitVec 32 :=
  BitVec.truncate 32
    ((if ConditionHolds CondCode.CS ps = true then
        if ConditionHolds CondCode.LS ps = true then 0#64 else 1#64
      else 4294967295#64) &&& 1095216660735#64)

theorem ekCmpW8_of_eq {msg_ep ep : BitVec 64} (heq : msg_ep = ep) :
    ekCmpW8 (subsPState64 msg_ep ep) = 0#32 := by
  subst heq
  unfold ekCmpW8 ConditionHolds subsPState64 AddWithCarry64
  bv_kernel

theorem ekCmpW8_of_gt {msg_ep ep : BitVec 64} (hgt : ep < msg_ep) :
    ekCmpW8 (subsPState64 msg_ep ep) = 1#32 := by
  unfold ekCmpW8 ConditionHolds subsPState64 AddWithCarry64
  bv_kernel

theorem ekCmpW8_of_lt {msg_ep ep : BitVec 64} (hlt : msg_ep < ep) :
    ekCmpW8 (subsPState64 msg_ep ep) = 255#32 := by
  unfold ekCmpW8 ConditionHolds subsPState64 AddWithCarry64
  bv_kernel

@[expose] def ekSpills10136 (s : State) (sp : SendEkSpills) (q60 : BitVec 128) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w2 := s.readReg64 .x7 }
    b1 := { sp.b1 with w8 := s.readReg64 .x4, w9 := s.readReg64 .x20 }
    b2 := { sp.b2 with w3 := s.readReg64 .x13, w7 := 10#64 }
    b3 := { sp.b3 with w2 := s.readReg64 .x12, w4 := s.readReg64 .x18, w5 := s.readReg64 .x21, w6 := s.readReg64 .x17, w7 := s.readReg64 .x10 }
    b4 := { sp.b4 with w1 := s.readReg64 .x27, w3 := s.readReg64 .x26, w6 := s.readReg64 .x22, w9 := s.readReg64 .x30 }
    b5 := { sp.b5 with w1 := s.readReg64 .x5, w6 := s.readReg64 .x3 }
    q3c0 := q60 }

@[expose] def ekSpills10276 (s : State) (sp : SendEkSpills) : SendEkSpills :=
  { sp with
    b2 := { sp.b2 with w8 := noneCap }
    b5 := { sp.b5 with w4 := s.readReg64 .x9, w8 := s.readReg64 .x2, w9 := s.readReg64 .x20 }
    w60 := s.readReg64 .x13 }

theorem memRegion_528_entails_words66At (a : BitVec 64) :
    memRegion a 528 ⊢ ∃∗ w : Words66, words66At a w := by
  rw [ProofLib.memRegion_split' (b := a) (n := 504) (k := 24) (b' := a + 504#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 504#64) (n := 16) (k := 8) (b' := a + 520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 520#64)]
  refine Entails.trans (sepConj_mono (memRegion_504_entails_words63At a)
    (sepConj_mono_left (memRegion_16_entails_128_recv (a + 504#64)))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w63
  rw [← sepConj_assoc, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w65
  rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro q63
  unfold words63At
  simp only [sepConj_assoc]
  exact Entails.sepExists_right ⟨w63.b0, w63.b1, w63.b2, w63.b3, w63.b4, w63.b5, w63.q60, w63.w62, q63, w65⟩
    (Entails.refl _)

@[expose] def ekSpills9788 (sp : SendEkSpills) (w : Words57) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w2 := w.b3.w1, w3 := w.b2.w9 }
    b1 := { sp.b1 with w3 := w.b3.w6, w5 := w.b3.w7, w6 := w.b0.w0, w8 := w.b1.w5, w9 := w.b1.w6 }
    b2 := { sp.b2 with w1 := w.w51, w3 := w.b4.w3, w4 := w.b4.w5, w5 := w.b0.w1, w6 := w.b4.w8, w7 := 12#64, w9 := w.b4.w2 }
    b3 := { sp.b3 with w2 := w.b1.w8, w3 := w.b2.w1, w4 := w.b2.w7, w5 := w.b0.w7, w6 := w.b1.w3, w7 := w.b2.w5, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w1 := w.b1.w2, w2 := w.b1.w9, w3 := w.b1.w0, w4 := w.b2.w2, w5 := w.b0.w5, w6 := w.b0.w4, w7 := w.b1.w1, w8 := w.b2.w0, w9 := w.b2.w3 }
    b5 := { sp.b5 with w0 := w.b0.w9, w1 := w.b4.w4, w2 := w.b1.w4, w3 := w.b0.w8, w5 := w.w50, w6 := w.b0.w3, w7 := w.b2.w4 }
    w61 := w.b0.w2, w62 := w.b0.w6 }

@[expose] def ekTail376 (q63 : BitVec 128) (w65 : BitVec 64) (a : BitVec 64) : SepProp :=
  (a ↦₁₂₈ q63) ∗ ((a + 16#64) ↦₆₄ w65) ∗ memRegion (a + 24#64) 352

theorem relocatable_ekTail376 (q63 : BitVec 128) (w65 : BitVec 64) :
    Relocatable 376 (ekTail376 q63 w65) := by
  have h8a : Relocatable 8 (fun a => a ↦₆₄ q63.extractLsb' 0 64) :=
    Relocatable.pointsTo64 _
  have h8b : Relocatable 8 (fun a => a ↦₆₄ q63.extractLsb' 64 64) :=
    Relocatable.pointsTo64 _
  have h16' : Relocatable 16 (fun a => (a ↦₆₄ q63.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q63.extractLsb' 64 64)) :=
    Relocatable.sepConj (n := 8) (k := 8) (m := 16) (off := 8#64) rfl rfl h8a h8b
  have h16 : Relocatable 16 (fun a => a ↦₁₂₈ q63) :=
    Relocatable.congr rfl (fun a => (pointsTo128_eq_pair64_recv a q63).symm) h16'
  have h8c : Relocatable 8 (fun a => a ↦₆₄ w65) :=
    Relocatable.pointsTo64 _
  have h24 : Relocatable 24 (fun a => (a ↦₁₂₈ q63) ∗ ((a + 16#64) ↦₆₄ w65)) :=
    Relocatable.sepConj (n := 16) (k := 8) (m := 24) (off := 16#64) rfl rfl h16 h8c
  have h376 : Relocatable 376 (fun a => ((a ↦₁₂₈ q63) ∗ ((a + 16#64) ↦₆₄ w65)) ∗ memRegion (a + 24#64) 352) :=
    Relocatable.sepConj (n := 24) (k := 352) (m := 376) (off := 24#64) rfl rfl h24
      (Relocatable.of_memRegion 352)
  refine Relocatable.congr rfl (fun a => ?_) h376
  dsimp only [ekTail376]
  rw [sepConj_assoc]

theorem q60_reconstruct (q : BitVec 128) :
    BitVec.ofNat 128 (q.truncate 64).toNat |||
      (BitVec.ofNat 128 ((q >>> 64).truncate 64).toNat <<< 64) = q := by
  bv_bits

theorem words63At_ekTail376_eq_words66At (a : BitVec 64) (w : Words66) :
    words63At (a + 8#64)
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
        q60 := w.q60, w62 := w.w62 } ∗
    ekTail376 w.q63 w.w65 (a + 512#64) =
    words66At (a + 8#64) w ∗ memRegion (a + 536#64) 352 := by
  dsimp only [words63At, words66At, ekTail376]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]

theorem selfA_ekReceivedCt1Sampled_entails_memRegion (selfA : BitVec 64) (w : Words66) :
    (selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 528) (k := 392)
        (b' := selfA + 536#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion selfA 10#64)
    (sepConj_mono_left (words66At_entails_memRegion (selfA + 8#64) w))

theorem selfA_528_entails_memRegion (selfA : BitVec 64) :
    (selfA ↦₆₄ 10#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 528) (k := 392)
        (b' := selfA + 536#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 10#64)

theorem ek_frame_entails_memRegion_4144 (fsp : BitVec 64) (sp : SendEkSpills) (qAC0 qF10 : BitVec 128) :
    sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
      ((fsp + 2752#64) ↦₁₂₈ qAC0) ∗ ((fsp + 3856#64) ↦₁₂₈ qF10) ∗ ekUnusedRestAt fsp ⊢
      memRegion fsp 4144 := by
  refine Entails.trans ?_ (sendEkFrame_entails_memRegion_4144 fsp sp)
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  exact ekUnusedRest_entails_sendEkUnusedAt fsp qAC0 qF10

theorem optEpochSecretAt_none_of_parts (A : RustAlloc) (a : BitVec 64) (w0 : BitVec 64) (q1 : BitVec 128) :
    (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w0) ∗ ((a + 16#64) ↦₁₂₈ q1) ⊢
      optEpochSecretAt A a none := by
  rw [optEpochSecretAt_none,
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono
    (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w0)
    (pointsTo128_entails_memRegion_16 (a + 16#64) q1))

theorem ek_noop_out_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words66) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 10#64) ∗
      words63At (outA + 8#64)
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
          q60 := w.q60, w62 := w.w62 } ∗
      ekTail376 w.q63 w.w65 (outA + 512#64) ∗
      memRegion (outA + 888#64) 40 ∗
      ((outA + 928#64) ↦₆₄ noneCap) ∗
      ((outA + 936#64) ↦₆₄ w936) ∗
      ((outA + 944#64) ↦₁₂₈ q944) ∗
      relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekReceivedCt1Sampled st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  rw [ProofLib.memRegion_split' (b := outA + 536#64) (n := 352) (k := 40)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
  have h66 := words63At_ekTail376_eq_words66At outA w
  have hrec := recompose66 (F_pred := fun dst => chunkedEkReceivedCt1SampledAt A dst st) (outA + 8#64) w
  have hopt := optEpochSecretAt_none_of_parts A (outA + 928#64) w936 q944
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at hopt
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 10#64) ∗
    (words63At (outA + 8#64)
       { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
         q60 := w.q60, w62 := w.w62 } ∗
     ekTail376 w.q63 w.w65 (outA + 512#64)) ∗
    relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
    memRegion (outA + 888#64) 40 ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  rw [h66]
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 10#64) ∗
    (words66At (outA + 8#64) w ∗
     relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
    (memRegion (outA + 536#64) 352 ∗ memRegion (outA + 888#64) 40) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_right hopt))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem words63At_entails_words57At (a : BitVec 64) (w : Words57)
    (w57 w58 w59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) :
    words63At (a + 8#64)
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w57, w58, w59⟩
        q60 := q60, w62 := w62 } ⊢
      words57At (a + 8#64) w ∗ memRegion (a + 464#64) 48 := by
  have htail :
      ((a + 464#64) ↦₆₄ w57) ∗ ((a + 472#64) ↦₆₄ w58) ∗ ((a + 480#64) ↦₆₄ w59) ∗
      ((a + 488#64) ↦₁₂₈ q60) ∗ ((a + 504#64) ↦₆₄ w62) ⊢
      memRegion (a + 464#64) 48 := by
    rw [pointsTo128_eq_pair64_recv]
    have heq :
        ((a + 464#64) ↦₆₄ w57) ∗ ((a + 472#64) ↦₆₄ w58) ∗ ((a + 480#64) ↦₆₄ w59) ∗
        (((a + 488#64) ↦₆₄ q60.extractLsb' 0 64) ∗ (((a + 488#64) + 8#64) ↦₆₄ q60.extractLsb' 64 64)) ∗
        ((a + 504#64) ↦₆₄ w62) =
        wordsAt (a + 464#64) [w57, w58, w59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] := by
      simp only [wordsAt_6, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    rw [heq]
    exact wordsAt_entails_memRegion _ (a + 464#64) 48 rfl
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right htail)
  dsimp only [words63At, words57At, words10At]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]

theorem ek_ack_out_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words57) (w57 w58 w59 : BitVec 64) (q60 : BitVec 128) (w62 w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 12#64) ∗
      words63At (outA + 8#64)
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
          b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w57, w58, w59⟩
          q60 := q60, w62 := w62 } ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ∗
      ((outA + 928#64) ↦₆₄ noneCap) ∗
      ((outA + 936#64) ↦₆₄ w936) ∗
      ((outA + 944#64) ↦₁₂₈ q944) ∗
      relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled outSt }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  rw [ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
        (b' := outA + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
  have h57 := words63At_entails_words57At outA w w57 w58 w59 q60 w62
  have hrec := recompose57 (F_pred := fun dst => chunkedCt2SampledAt A dst outSt) (outA + 8#64) w
  have hopt := optEpochSecretAt_none_of_parts A (outA + 928#64) w936 q944
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at hopt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h57)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 12#64) ∗
    (words57At (outA + 8#64) w ∗
     relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w))) ∗
    (memRegion (outA + 464#64) 48 ∗ (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_right hopt))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_880_split_456_424 (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 880 =
      memRegion (fsp + 976#64) 456 ∗ memRegion (fsp + 1432#64) 424 :=
  ProofLib.memRegion_split' (b := fsp + 976#64) (n := 456) (k := 424)
    (b' := fsp + 1432#64) rfl (by bv_omega) (by decide)

theorem memRegion_880_split_528_352 (fsp : BitVec 64) :
    memRegion (fsp + 1856#64) 880 =
      memRegion (fsp + 1856#64) 528 ∗ memRegion (fsp + 2384#64) 352 :=
  ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 528) (k := 352)
    (b' := fsp + 2384#64) rfl (by bv_omega) (by decide)

theorem words57At_424_entails_memRegion_880 (fsp : BitVec 64) (w : Words57) :
    words57At (fsp + 976#64) w ∗ memRegion (fsp + 1432#64) 424 ⊢
      memRegion (fsp + 976#64) 880 := by
  rw [memRegion_880_split_456_424 fsp]
  exact sepConj_mono_left (words57At_entails_memRegion (fsp + 976#64) w)

theorem words66At_352_entails_memRegion_880 (fsp : BitVec 64) (w : Words66) :
    words66At (fsp + 1856#64) w ∗ memRegion (fsp + 2384#64) 352 ⊢
      memRegion (fsp + 1856#64) 880 := by
  rw [memRegion_880_split_528_352 fsp]
  exact sepConj_mono_left (words66At_entails_memRegion (fsp + 1856#64) w)

theorem selfA_recompose_ekReceivedCt1Sampled (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words66) :
    words66At (selfA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ⊢
      chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st :=
  recompose66 (F_pred := fun dst => chunkedEkReceivedCt1SampledAt A dst st) (selfA + 8#64) w

theorem selfA_recompose_528 (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words66) :
    (selfA ↦₆₄ 10#64) ∗
      (words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
      memRegion (selfA + 536#64) 392 ⊢
      (selfA ↦₆₄ 10#64) ∗
      chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st ∗
      memRegion (selfA + 536#64) 392 :=
  sepConj_mono_right (sepConj_mono_left (selfA_recompose_ekReceivedCt1Sampled A selfA st w))

theorem memRegion_576_376_split_ekTail (fsp : BitVec 64) :
    memRegion (fsp + 576#64) 376 ⊢
      ∃∗ q576 : BitVec 128, ∃∗ w592 : BitVec 64,
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦₆₄ w592) ∗ memRegion (fsp + 600#64) 352 := by
  rw [ProofLib.memRegion_split' (b := fsp + 576#64) (n := 16) (k := 360)
        (b' := fsp + 592#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 592#64) (n := 8) (k := 352)
        (b' := fsp + 600#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 592#64)]
  refine Entails.trans (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 576#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w592
  apply Entails.sepExists_elim; intro q576
  exact Entails.sepExists_right q576 (Entails.sepExists_right w592 (Entails.refl _))

end CryptoVerification.SpqrV1.States.Recv

