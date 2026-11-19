/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part A

Shared `+7084` `Err(err)` exit, inline `ProtoPolynomialDecoder` deallocation loop (`+5360..+5440 -> +7084`),
and `uc` error-cleanup paths (`+7024`, `+6904`, `+8588`, `+488`, `+2768`) for Variant 9.
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

theorem v9_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v9_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v9_sepWPp_call_ret {α : Type} {prog : Program}
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
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v9_fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

theorem v9_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v9_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

@[expose, reducible]
def v9_Saved5368Preserved (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x21 = ptsCap ∧
  s.readReg64 .x28 = x28_val ∧
  TraceCalleeSaved s s0

theorem v9_ptsCap_add_one_ne_zero {ptsCap : BitVec 64} (h : ptsCap.toNat * 24 < 2 ^ 63) :
    ¬((ptsCap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h1 : (ptsCap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

@[expose] def v9_Saved7084Preserved (s0 s : State) (fsp out : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x28 = 0#64 ∧
  TraceCalleeSaved s s0

theorem v9_stackAt_allocHook_to_drop32 (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  refine Entails.trans (v9_stackAt_allocHook_to_encoderFromPbStack fsp) ?_
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v9_stackAt_drop32_to_allocHook (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  refine Entails.trans ?_ (v9_stackAt_encoderFromPbStack_to_allocHook fsp)
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v9_stackAt_encoderFromPbStack_eq_decoderFromPb (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      stackAt fsp decoderFromPbStack ∗
        memRegion (fsp - 5152#64) (encoderFromPbStack - decoderFromPbStack) := by
  have h := ProofLib.stackAt_split_bottom fsp decoderFromPbStack (encoderFromPbStack - decoderFromPbStack) (by decide)
  rw [show decoderFromPbStack + (encoderFromPbStack - decoderFromPbStack) = encoderFromPbStack by decide,
      show BitVec.ofNat 64 encoderFromPbStack = 5152#64 by decide, sepConj_comm] at h
  exact h

theorem v9_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k)
    (b' := a + o1 + 8#64) rfl rfl hk,
    ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k)
    (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem v9_memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]; exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v9_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]; exact Entails.refl _

theorem v9_loBytes7_64_313_entails_bs328 (fsp u240 ep : BitVec 64) :
    ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 u240) ∗
      ((fsp + 247#64) ↦₆₄ ep) ∗
      memRegion (fsp + 255#64) 313 ⊢
    ∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val) := by
  refine Entails.trans ?_ (v9_memRegion_entails_bs 328 (fsp + 240#64) (by decide))
  exact collapse_top <|
    collapse_step (loBytes7_entails_memRegion_7 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v9_memRegion_1888_split_none (fsp : BitVec 64) :
    memRegion fsp 1888 ⊢
      memRegion fsp 72 ∗ (∃∗ w72 : BitVec 64, ((fsp + 72#64) ↦₆₄ w72)) ∗
      memRegion (fsp + 80#64) 16 ∗ (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗
      memRegion (fsp + 100#64) 28 ∗ (∃∗ w128 : BitVec 64, ((fsp + 128#64) ↦₆₄ w128)) ∗
      memRegion (fsp + 136#64) 8 ∗ (∃∗ w144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w144)) ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗ memRegion (fsp + 160#64) 80 ∗
      (∃∗ w240 : BitVec 64, ((fsp + 240#64) ↦₆₄ w240)) ∗
      ((∃∗ w248 : BitVec 64, ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248)) ∗
       memRegion (fsp + 255#64) 1633) := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| v9_memRegion_loBytes7_gap_at fsp 248#64 255#64 1632

theorem v9_memRegion_1888_split_some (fsp : BitVec 64) :
    memRegion fsp 1888 ⊢
      memRegion fsp 40 ∗ (∃∗ w40 : BitVec 64, ((fsp + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((fsp + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((fsp + 56#64) ↦₆₄ w56)) ∗
      memRegion (fsp + 64#64) 8 ∗ (∃∗ w72 : BitVec 64, ((fsp + 72#64) ↦₆₄ w72)) ∗
      (∃∗ w80 : BitVec 64, ((fsp + 80#64) ↦₆₄ w80)) ∗
      memRegion (fsp + 88#64) 8 ∗ (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗
      memRegion (fsp + 100#64) 28 ∗ (∃∗ w128 : BitVec 64, ((fsp + 128#64) ↦₆₄ w128)) ∗
      (∃∗ w136 : BitVec 64, ((fsp + 136#64) ↦₆₄ w136)) ∗
      (∃∗ w144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w144)) ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗
      memRegion (fsp + 160#64) 40 ∗ (∃∗ w200 : BitVec 64, ((fsp + 200#64) ↦₆₄ w200)) ∗
      memRegion (fsp + 208#64) 8 ∗ (∃∗ w216 : BitVec 64, ((fsp + 216#64) ↦₆₄ w216)) ∗
      memRegion (fsp + 224#64) 16 ∗ (∃∗ w240 : BitVec 64, ((fsp + 240#64) ↦₆₄ w240)) ∗
      ((∃∗ w248 : BitVec 64, ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248)) ∗
       memRegion (fsp + 255#64) 641) ∗
      memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem32_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (v9_memRegion_loBytes7_gap_at fsp 248#64 255#64 640) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_3044_collapse_err (fsp mkLen hdrLen u240 ep : BitVec 64) (d96 : BitVec 32) :
    (memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
      (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
       ((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 28) ∗
      (memRegion (fsp + 224#64) 16 ∗
       ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 u240) ∗ ((fsp + 247#64) ↦₆₄ ep) ∗
       memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
       memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1888#64) 400 ∗
       memRegion (fsp + 2288#64) 16) ⊢
    memRegion fsp 48 ∗ memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 224#64) 2080 := by
  refine sepConj_mono ?_ (sepConj_mono ?_ ?_)
  · exact collapse_top <| collapse_step0 (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _
  · exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <| Entails.refl _
  · exact collapse_top <|
      collapse_step (Entails.refl _) <| collapse_step (loBytes7_entails_memRegion_7 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_255_641_split_ok (fsp : BitVec 64) :
    memRegion (fsp + 255#64) 641 ⊢
      memRegion (fsp + 255#64) 313 ∗ memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
      (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
      (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
      (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
      (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
      (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
      (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
      (∃∗ w832 : BitVec 64, ((fsp + 832#64) ↦₆₄ w832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
      ((∃∗ w864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, ((fsp + 880#64) ↦₆₄ w880)) ∗
      ((∃∗ w888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)) ∗ memRegion (fsp + 895#64) 1) := by
  exact split_top <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (v9_memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (v9_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <| v9_memRegion_loBytes7_gap_at fsp 888#64 895#64 0

end CryptoVerification.SpqrV1.States.FromPb

