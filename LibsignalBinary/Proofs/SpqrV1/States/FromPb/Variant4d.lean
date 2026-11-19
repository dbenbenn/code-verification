/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part D

Early `ptsNeeded ≠ 80` error path (`+248 -> +304 -> ret`), `uc = none` error path, and
post-`<EkSentCt1Received>::from_pb` continuations (`+2308 -> ret`).
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



/-! ## Pure & Stack Helpers (`v4d_*`) -/

theorem v4d_sepWP_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : Prop} {Q : SepProp} {post : State → SepProp → Prop}
    (h : P → SepWP prog target_pc s Q post) :
    SepWP prog target_pc s (⌜P⌝ ∗ Q) post :=
  ProofLib.SepWP.pure_elim h

theorem v4d_seq_clean_weaken {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P1 P1' P2 : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P1' (fun s' P' => (P' ⊢ P2) ∧ Q s'))
    (hpre : P1 ⊢ P1')
    (h2 : ∀ s2, s2.pc = mid_pc → s2.status = .Running → Q s2 →
      SepWP prog target_pc s2 P2 post) :
    SepWP prog target_pc s P1 post :=
  SepWP.weaken_pre hpre (EncoderFromPb.seq_clean h1 h2)

theorem v4d_fsp_aligned (sp0 : BitVec 64) (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 2400#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_kernel

theorem v4d_sp_sub_1136_eq (sp0 : BitVec 64) :
    sp0 - 1136#64 = (sp0 - 2400#64) + 1264#64 := by bv_omega

theorem v4d_memRegion_2304_split_2228 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      ∃∗ v224 : BitVec 64, ∃∗ v232 : BitVec 32,
      ∃∗ s0_u : BitVec 64, ∃∗ s8_u : BitVec 64, ∃∗ s16_u : BitVec 64,
      ∃∗ s24_u : BitVec 64, ∃∗ s32_u : BitVec 64, ∃∗ s40_u : BitVec 64,
      ∃∗ s48_u : BitVec 64, ∃∗ s56_u : BitVec 64, ∃∗ s64_u : BitVec 64,
      ∃∗ s72_u : BitVec 64, ∃∗ s80_u : BitVec 64, ∃∗ s88_u : BitVec 64,
      ∃∗ s96_u : BitVec 64,
        ((fsp + 224#64) ↦₆₄ v224) ∗
        ((fsp + 232#64) ↦₃₂ v232) ∗
        v4b_optProtoUcWordsAt (fsp + 1392#64)
          s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u ∗
        memRegion fsp 224 ∗
        memRegion (fsp + 236#64) 1156 ∗
        memRegion (fsp + 1496#64) 392 ∗
        memRegion (fsp + 1888#64) 104 ∗
        memRegion (fsp + 1992#64) 312 := by
  have hsplit : memRegion fsp 2304 ⊢
      memRegion fsp 224 ∗
      (∃∗ v224 : BitVec 64, (fsp + 224#64) ↦₆₄ v224) ∗
      (∃∗ v232 : BitVec 32, (fsp + 232#64) ↦₃₂ v232) ∗
      memRegion (fsp + 236#64) 1156 ∗
      memRegion (fsp + 1392#64) 104 ∗
      memRegion (fsp + 1496#64) 392 ∗
      memRegion (fsp + 1888#64) 104 ∗
      memRegion (fsp + 1992#64) 312 := by
    exact split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem32_entails _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans hsplit ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (v4b_memRegion_104_to_ucWordsAt (fsp + 1392#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro s0_u
  apply Entails.sepExists_elim; intro s8_u
  apply Entails.sepExists_elim; intro s16_u
  apply Entails.sepExists_elim; intro s24_u
  apply Entails.sepExists_elim; intro s32_u
  apply Entails.sepExists_elim; intro s40_u
  apply Entails.sepExists_elim; intro s48_u
  apply Entails.sepExists_elim; intro s56_u
  apply Entails.sepExists_elim; intro s64_u
  apply Entails.sepExists_elim; intro s72_u
  apply Entails.sepExists_elim; intro s80_u
  apply Entails.sepExists_elim; intro s88_u
  apply Entails.sepExists_elim; intro s96_u
  apply Entails.sepExists_elim; intro v232
  apply Entails.sepExists_elim; intro v224
  refine Entails.sepExists_right v224 (Entails.sepExists_right v232
    (Entails.sepExists_right s0_u (Entails.sepExists_right s8_u
      (Entails.sepExists_right s16_u (Entails.sepExists_right s24_u
        (Entails.sepExists_right s32_u (Entails.sepExists_right s40_u
          (Entails.sepExists_right s48_u (Entails.sepExists_right s56_u
            (Entails.sepExists_right s64_u (Entails.sepExists_right s72_u
              (Entails.sepExists_right s80_u (Entails.sepExists_right s88_u
                (Entails.sepExists_right s96_u ?_))))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem v4d_memRegion_1156_104_392_entails_1652 (fsp : BitVec 64) :
    memRegion (fsp + 236#64) 1156 ∗
      memRegion (fsp + 1392#64) 104 ∗
      memRegion (fsp + 1496#64) 392 ⊢
    memRegion (fsp + 236#64) 1652 := by
  exact collapse_top <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v4d_stack_2308_err_entails_2304 (fsp d32 : BitVec 64) (d28 : BitVec 32)
    (w1896 w1904 w1912 : BitVec 64) :
    memRegion fsp 224 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗
      ((fsp + 1896#64) ↦₆₄ w1896) ∗
      ((fsp + 1904#64) ↦₆₄ w1904) ∗
      ((fsp + 1912#64) ↦₆₄ w1912) ∗
      memRegion (fsp + 1920#64) 72 ∗
      memRegion (fsp + 1992#64) 312 ⊢
    memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v4d_stack_6860_entails_2304 (fsp : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 d32 : BitVec 64) (d28 : BitVec 32)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) :
    memRegion fsp 32 ∗
      memRegion (fsp + 64#64) 8 ∗
      memRegion (fsp + 88#64) 40 ∗
      memRegion (fsp + 152#64) 64 ∗
      v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
      ((fsp + 224#64) ↦₆₄ d32) ∗
      ((fsp + 232#64) ↦₃₂ d28) ∗
      memRegion (fsp + 236#64) 1652 ∗
      v4b_optProtoUcWordsAt (fsp + 1888#64) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 ∗
      memRegion (fsp + 1992#64) 312 ⊢
    memRegion fsp 2304 := by
  have h1888 := v4c_ucWords_312_entails_400_16 fsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h1888)))))))) ?_
  exact v4c_err_8500_stack_collapse fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 d32 d28

/-! ## Shared `+5264 -> +5348 -> ret` Error Cleanup -/

theorem v4d_sepWPp_exists_left {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog target_pc s (P x ∗ Q) post Qp) :
    SepWPp prog target_pc s ((∃∗ x, P x) ∗ Q) post Qp := by
  intro R' hm
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R' hmx

theorem v4d_sepWPp_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : Prop} {Q : SepProp} {post Qp : State → SepProp → Prop}
    (h : P → SepWPp prog target_pc s Q post Qp) :
    SepWPp prog target_pc s (⌜P⌝ ∗ Q) post Qp := by
  intro R' hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R' hm.2

theorem v4d_seq_clean_p_weaken {prog : Program} {mid_pc target_pc : BitVec 64} {s : State}
    {P1 P1' P2 : SepProp} {Q : State → Prop} {post Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P1' (fun s' P' => (P' ⊢ P2) ∧ Q s'))
    (hpre : P1 ⊢ P1')
    (h2 : ∀ s2, s2.pc = mid_pc → s2.status = .Running → Q s2 →
      SepWPp prog target_pc s2 P2 post Qp) :
    SepWPp prog target_pc s P1 post Qp :=
  SepWPp.weaken_pre hpre (v4_sepWPp_seq_clean h1 h2)

theorem v4d_pull_pures {P1 P2 : Prop} {A B C : SepProp} :
    (⌜P1⌝ ∗ A) ∗ (⌜P2⌝ ∗ B) ∗ C = ⌜P1⌝ ∗ ⌜P2⌝ ∗ (A ∗ B ∗ C) := by ac_rfl

theorem v4d_sepWPp_call {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    hnext

theorem v4d_vecU8Heap_cap_lt (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr len : BitVec 64) :
    v4b_vecU8Heap A bs cap ptr len ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ v4b_vecU8Heap A bs cap ptr len := by
  unfold v4b_vecU8Heap
  apply Entails.pure_left; rintro ⟨h1, hcap⟩
  exact Entails.pure_right hcap (Entails.pure_right ⟨h1, hcap⟩ (Entails.refl _))

theorem v4d_ekSentCt1ReceivedHeap_rk_lt (A : RustAlloc) {F : ShaCompress}
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ⊢
    ⌜rkCap.toNat < 2 ^ 63⌝ ∗
    v4b_ekSentCt1ReceivedHeap A
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc := by
  unfold v4b_ekSentCt1ReceivedHeap
  exact Entails.trans (sepConj_mono_left (v4d_vecU8Heap_cap_lt A uc.auth.rootKey rkCap rkPtr rkLen))
    (Entails.of_eq (sepConj_assoc _ _ _))

theorem v4d_optProtoPolyDecoderHeap_some_d0_lt (A : RustAlloc) (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64) :
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ⊢
    ⌜d0.toNat < 2 ^ 63⌝ ∗
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 := by
  unfold v4b_optProtoPolyDecoderHeap
  apply Entails.pure_left; rintro ⟨h1, h2, h3, hle, hcap, h6, h7⟩
  have hd0 : d0.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right hd0 (Entails.pure_right ⟨h1, h2, h3, hle, hcap, h6, h7⟩ (Entails.refl _))

theorem v4d_optProtoUcHeap_some_u0_lt (A : RustAlloc) (u : V1State.Unchunked.EkSentCt1Received)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ⊢
    ⌜u0.toNat < 2 ^ 63⌝ ∗
    v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 := by
  dsimp only [v4b_optProtoUcHeap]
  exact Entails.trans (sepConj_mono_left (v4d_vecU8Heap_cap_lt A u.dk u0 u8 u16))
    (Entails.of_eq (sepConj_assoc _ _ _))

theorem v4d_ekSent_from_pb_error_eq (F : ShaCompress)
    (u : V1State.Unchunked.EkSentCt1Received) (e : StatesError)
    (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h
  split at h
  · rcases hauth : u.auth with _ | a <;> simp [hauth] at h
    exact h.symm
  · simp at h; exact h.symm

theorem v4d_rot3 (A B C D : SepProp) : A ∗ B ∗ C ∗ D = C ∗ A ∗ B ∗ D := by ac_rfl

theorem v4d_rot4 (A1 A2 A3 B C : SepProp) :
    A1 ∗ A2 ∗ A3 ∗ B ∗ C = B ∗ A1 ∗ A2 ∗ A3 ∗ C := by ac_rfl

end CryptoVerification.SpqrV1.States.FromPb
