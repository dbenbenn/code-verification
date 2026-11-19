/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7j
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) Part K

Proves the encoder/decoder stage compositions (`+3720`, `+7348`, `+7404`) and discharges
`V7Ok7404Prop` from `v7_dec_ok_7404_to_ret`.
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero



/-! ## 1. Stack Frame Splitting Helpers -/

theorem v7_stackAt_encoderFromPbStack_to_ct1SentFromPbStack (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 816 ∗ stackAt fsp ct1SentFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_stackAt_ct1SentFromPbStack_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 816 ∗ stackAt fsp ct1SentFromPbStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v7_memRegion_2304_split_uc (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 240 ∗
      memRegion (fsp + 240#64) 128 ∗
      memRegion (fsp + 368#64) 1520 ∗
      memRegion (fsp + 1888#64) 128 ∗
      memRegion (fsp + 2016#64) 288 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    split_step (Entails.refl _) <|
    Entails.refl _

theorem v7_memRegion_2304_unsplit_uc (fsp : BitVec 64) :
    memRegion fsp 240 ∗
    memRegion (fsp + 240#64) 128 ∗
    memRegion (fsp + 368#64) 1520 ∗
    memRegion (fsp + 1888#64) 128 ∗
    memRegion (fsp + 2016#64) 288 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_memRegion_uc_rest_to_1888 (fsp : BitVec 64) :
    memRegion fsp 240 ∗
    memRegion (fsp + 240#64) 128 ∗
    memRegion (fsp + 368#64) 1520 ⊢
      memRegion fsp 1888 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

@[expose] def v7_stackGapsEncDec (fsp : BitVec 64) : SepProp :=
  memRegion fsp 16 ∗
  memRegion (fsp + 32#64) 168 ∗
  memRegion (fsp + 208#64) 688 ∗
  memRegion (fsp + 952#64) 312 ∗
  memRegion (fsp + 2288#64) 16

theorem v7_memRegion_1888_288_split_encDec (fsp : BitVec 64) :
    memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ⊢
      (∃∗ slot16 : BitVec 64, (fsp + 16#64) ↦₆₄ slot16) ∗
      (∃∗ slot24 : BitVec 64, (fsp + 24#64) ↦₆₄ slot24) ∗
      (∃∗ slot200 : BitVec 64, (fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 2016#64) 272 ∗
      v7_stackGapsEncDec fsp := by
  have h1888 : memRegion fsp 1888 ⊢
      memRegion fsp 16 ∗
      (∃∗ slot16 : BitVec 64, (fsp + 16#64) ↦₆₄ slot16) ∗
      (∃∗ slot24 : BitVec 64, (fsp + 24#64) ↦₆₄ slot24) ∗
      memRegion (fsp + 32#64) 168 ∗
      (∃∗ slot200 : BitVec 64, (fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 208#64) 688 ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 952#64) 312 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 := by
    exact split_top <|
      split_step0 (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (mem64_entails _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      split_step (Entails.refl _) <|
      Entails.refl _
  have h288 : memRegion (fsp + 2016#64) 288 ⊢
      memRegion (fsp + 2016#64) 272 ∗ memRegion (fsp + 2288#64) 16 := by
    exact split_top <|
      split_step (Entails.refl _) <|
      Entails.refl _
  refine Entails.trans (sepConj_mono h1888 h288) ?_
  unfold v7_stackGapsEncDec
  exact Entails.of_eq (by ac_rfl)

theorem v7_memRegion_1888_128_272_to_400 (fsp : BitVec 64) :
    memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 272 ⊢
      memRegion (fsp + 1888#64) 400 := by
  exact collapse_top <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_stackGapsEncDec_unsplit (fsp slot16 slot24 slot200 : BitVec 64) :
    ((fsp + 16#64) ↦₆₄ slot16) ∗
    ((fsp + 24#64) ↦₆₄ slot24) ∗
    ((fsp + 200#64) ↦₆₄ slot200) ∗
    memRegion (fsp + 896#64) 56 ∗
    memRegion (fsp + 1264#64) 128 ∗
    memRegion (fsp + 1392#64) 400 ∗
    memRegion (fsp + 1792#64) 56 ∗
    memRegion (fsp + 1848#64) 40 ∗
    memRegion (fsp + 1888#64) 400 ∗
    v7_stackGapsEncDec fsp ⊢
      memRegion fsp 2304 := by
  have hcol :
      memRegion fsp 16 ∗
      ((fsp + 16#64) ↦₆₄ slot16) ∗
      ((fsp + 24#64) ↦₆₄ slot24) ∗
      memRegion (fsp + 32#64) 168 ∗
      ((fsp + 200#64) ↦₆₄ slot200) ∗
      memRegion (fsp + 208#64) 688 ∗
      memRegion (fsp + 896#64) 56 ∗
      memRegion (fsp + 952#64) 312 ∗
      memRegion (fsp + 1264#64) 128 ∗
      memRegion (fsp + 1392#64) 400 ∗
      memRegion (fsp + 1792#64) 56 ∗
      memRegion (fsp + 1848#64) 40 ∗
      memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢
        memRegion fsp 2304 := by
    exact collapse_top <|
      collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <|
      Entails.refl _
  unfold v7_stackGapsEncDec
  refine Entails.trans (Entails.of_eq ?_) hcol
  ac_rfl

theorem v7_pbA_128_56_40_to_224 (pbA : BitVec 64) :
    memRegion pbA 128 ∗ memRegion (pbA + 128#64) 56 ∗ memRegion (pbA + 184#64) 40 ⊢
      memRegion pbA optProtoInnerStateSize := by
  change _ ⊢ memRegion pbA 224
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Entails.refl _) <|
    Entails.refl _

theorem v7_sepWPp_call_wpp {α : Type} {prog : Program}
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
    (fun sf hpcf hrunf hspf hcsf => hnext sf hpcf hrunf hspf hcsf)

/-- Every error returned by `Unchunked.SendCt.Ct1Sent.from_pb` is `.err .stateDecode`. -/
theorem v7_ct1Sent_from_pb_error_eq (F : ShaCompress) (u : V1State.Unchunked.Ct1Sent)
    {e : StatesError} (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h
  · rcases hauth : u.auth with _ | a <;> rw [hauth] at h <;> [injection h with h; nomatch h]
    exact h.symm
  · injection h with h; exact h.symm

end CryptoVerification.SpqrV1.States.FromPb
