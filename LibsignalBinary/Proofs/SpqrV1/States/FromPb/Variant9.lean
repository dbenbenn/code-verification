/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9d
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`)

Assembles the Variant 9 (`InnerState.ct1Acknowledged`, jump-table target `+444`) stage continuations
from `+2864` and `+2768` into `states_from_pb_ct1Acknowledged_444` and `states_from_pb_ct1Acknowledged_ok_ext`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

theorem v9_sepWPp_call_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post (fun sf' P_f => P_f ⊢ Qpan sf'))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf) hnext

theorem v9_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp :=
  SepWPp.exists_elim h

theorem v9_sepWPp_pure_left {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  SepWPp.pure_left h

theorem v9_ct1Sent_from_pb_err_eq {F : ShaCompress}
    (u : V1State.Unchunked.Ct1Sent) {e : StatesError}
    (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h
  · split at h
    · cases h; rfl
    · nomatch h
  · cases h; rfl

theorem v9_optProtoPolyDecoderHeap_some_cap_lt (A : RustAlloc)
    (d : ProtoPolynomialDecoder) (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    v9_optProtoPolyDecoderHeap A (some d) w0 w8 w16 d24 d28 w32 ⊢
      ⌜w0.toNat < 2 ^ 63 ∧ d24 = d.ptsNeeded⌝ ∗
        v9_optProtoPolyDecoderHeap A (some d) w0 w8 w16 d24 d28 w32 := by
  dsimp only [v9_optProtoPolyDecoderHeap]
  apply Entails.pure_left; rintro ⟨hw16, hd24, hd28, hle, hcap, hp_ne, hw32⟩
  have hw0_lt : w0.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right ⟨hw0_lt, hd24⟩
    (Entails.pure_right ⟨hw16, hd24, hd28, hle, hcap, hp_ne, hw32⟩ (Entails.refl _))

theorem v9_optProtoUcHeap_some_cap_lt (A : RustAlloc)
    (u : V1State.Unchunked.Ct1Sent)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64) :
    v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ⊢
      ⌜u0.toNat < 2 ^ 63⌝ ∗
        v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 := by
  dsimp only [v9_optProtoUcHeap, v9_vecU8Heap, vecU8Payload]
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlen
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)))

theorem v9_fsp_1888_err_entails_2304 (fsp w0 w8 w16 w24 : BitVec 64) :
    memRegion fsp 1888 ∗
      (((fsp + 1888#64) ↦₆₄ w0) ∗ ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗
       ((fsp + 1912#64) ↦₆₄ w24) ∗ memRegion (fsp + 1920#64) 96) ∗
      memRegion (fsp + 2016#64) 288 ⊢
      memRegion fsp 2304 := by
  have h128 := v9_words4_region96_entails_128 (fsp + 1888#64) w0 w8 w16 w24
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h128
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step h128 <|
    Entails.refl _

theorem v9_memRegion_2304_split_2768 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 1392 ∗
      (∃∗ z1392 : BitVec 64, ((fsp + 1392#64) ↦₆₄ z1392)) ∗
      (∃∗ b1400 : BitVec 8, ((fsp + 1400#64) ↦₈ b1400)) ∗
      (∃∗ z1401 : BitVec 64, ((fsp + 1401#64) ↦₆₄ z1401)) ∗
      (∃∗ z1409 : BitVec 64, ((fsp + 1409#64) ↦₆₄ z1409)) ∗
      ((∃∗ z1417 : BitVec 64, ((fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 z1417)) ∗
       (∃∗ z1424 : BitVec 64, ((fsp + 1424#64) ↦₆₄ z1424))) ∗
      (∃∗ z1432 : BitVec 64, ((fsp + 1432#64) ↦₆₄ z1432)) ∗
      (∃∗ z1440 : BitVec 64, ((fsp + 1440#64) ↦₆₄ z1440)) ∗
      (∃∗ z1448 : BitVec 64, ((fsp + 1448#64) ↦₆₄ z1448)) ∗
      (∃∗ z1456 : BitVec 64, ((fsp + 1456#64) ↦₆₄ z1456)) ∗
      (∃∗ z1464 : BitVec 64, ((fsp + 1464#64) ↦₆₄ z1464)) ∗
      (∃∗ z1472 : BitVec 64, ((fsp + 1472#64) ↦₆₄ z1472)) ∗
      (∃∗ z1480 : BitVec 64, ((fsp + 1480#64) ↦₆₄ z1480)) ∗
      (∃∗ z1488 : BitVec 64, ((fsp + 1488#64) ↦₆₄ z1488)) ∗
      (∃∗ z1496 : BitVec 64, ((fsp + 1496#64) ↦₆₄ z1496)) ∗
      (∃∗ z1504 : BitVec 64, ((fsp + 1504#64) ↦₆₄ z1504)) ∗
      (∃∗ z1512 : BitVec 64, ((fsp + 1512#64) ↦₆₄ z1512)) ∗
      memRegion (fsp + 1520#64) 368 ∗
      memRegion (fsp + 1888#64) 128 ∗
      memRegion (fsp + 2016#64) 288 := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.of_eq (memRegion_one _)) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.trans (v9_memRegion_loBytes7_gap_at fsp 1417#64 1424#64 7)
      (sepConj_mono_right (mem64_entails _))) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_1392_1520_entails_1888 (fsp : BitVec 64) :
    memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 128 ∗ memRegion (fsp + 1520#64) 368 ⊢
      memRegion fsp 1888 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

/-! ## 1. From `+2864` (Return of `Ct1Sent::from_pb`) to `s0.x30` -/

end CryptoVerification.SpqrV1.States.FromPb
