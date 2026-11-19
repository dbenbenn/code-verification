/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part D

Pure model reductions, `<PolyDecoder>::from_pb` setup and post-call staging (`+2864 -> +3040`,
`+3044 -> +8588 | +8180`), and exit-tail compositions (`+5368`, `+5360`, `+6904`, `+8588`, `+3044 -> s0.x30`)
for `InnerState.ct1Acknowledged`.
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

theorem v9_ptsNeeded_toNat_bne_576_eq (w : BitVec 32) :
    (w.toNat != ENCAPSULATION_KEY_SIZE / 2) = !(w == 576#32) := by
  change (w.toNat != 576) = !(w == 576#32)
  by_cases h : w = 576#32
  · subst h; rfl
  · have hne : w.toNat ≠ 576 := by
      intro heq
      apply h
      apply BitVec.eq_of_toNat_eq
      exact heq
    have hb1 : (w.toNat != 576) = true := bne_iff_ne.mpr hne
    have hb2 : (w == 576#32) = false := beq_false_of_ne h
    rw [hb1, hb2]; rfl

theorem v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne {F : ShaCompress}
    (uc : Option V1State.Unchunked.Ct1Sent) (d : PolynomialDecoder)
    (hne : (d.ptsNeeded == 576#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := uc, receivingEk := some d }) } =
    .error (.err .msgDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, hne]
  rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_none_dec_none {F : ShaCompress} :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := none, receivingEk := none }) } =
    .error (.err .stateDecode) := rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_none_dec_some {F : ShaCompress}
    (d : PolynomialDecoder) (heq : (d.ptsNeeded == 576#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := none, receivingEk := some d }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, heq]
  rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_some_dec_none {F : ShaCompress}
    (u : V1State.Unchunked.Ct1Sent) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := none }) } =
    match Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
    | .ok _ => .error (.err .stateDecode)
    | .error e => .error e := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only [bind, Except.bind, Functor.map, Except.map]
  cases Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u <;> rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_some_dec_some {F : ShaCompress}
    (u : V1State.Unchunked.Ct1Sent) (d : PolynomialDecoder)
    (heq : (d.ptsNeeded == 576#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := some d }) } =
    match Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
    | .error e => .error e
    | .ok uc =>
      match decoderFromPbResult (pbToProtoPolyDecoder d) with
      | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := dec })
      | .error _ => .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, heq]
  dsimp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
  | error e => rfl
  | ok uc =>
    dsimp only
    rw [decoderFromPbStateDecode_some d]
    cases decoderFromPbResult (pbToProtoPolyDecoder d) <;> rfl

/-! ## 2. Stepping Lemmas for `+2864 -> +3040` and `+3044 -> +8588 | +8180` -/

section StepLemmas

attribute [local simp, local arm64_norm ↓, local wp_norm ↓] v9_x25_add_209 v9_x25_add_209_sext v9_pbA_add_145 v9_x21_add_57 v9_x21_add_57_sext v9_x24_add_9 v9_x24_add_9_sext v9_x21_add_15 v9_x21_add_15_sext v9_x21_add_39 v9_x21_add_39_sext v9_fsp_add_247_sext v9_bv_add_add_lit

end StepLemmas

/-! ## 3. Composition Helpers & Exit Tails (`+5368`, `+5360`, `+6904`, `+8588`, `+8180`) -/

theorem v9_sepWPp_entails_to_satisfies {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s sf)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s sf ∗ R)) := by
  intro R' hm hL; obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with hok | ⟨hst, Pf, hmf, hPf⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hPf) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem v9_sepWPp_call_ret_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf) (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v9_sepWPp_frame_right {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P Post J : SepProp} {Regs : State → Prop}
    (h : SepWPp prog ret s P
      (fun sf Pf => (Pf ⊢ Post) ∧ Regs sf)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s (P ∗ J)
      (fun sf Pf => (Pf ⊢ Post ∗ J) ∧ Regs sf)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  intro R' hm hL; rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, hout⟩ := h (J ∗ R') hm hL
  rcases hout with ⟨hpc, hrun, Pf, hmf, hPf, hregs⟩ | ⟨hst, Pf, hmf, hPf⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ J, hmf, sepConj_mono_left hPf, hregs⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf ∗ J, hmf,
      Entails.trans (sepConj_mono_left hPf) (v9_onPanic_frame_entails ⟨rfl, rfl⟩)⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem v9_pbA_entails_224
    (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000009#64) ∗
      v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (v9_optProtoUcWordsAt_entails_128 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) <|
    collapse_step (v9_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v9_pbA_128_entails_224
    (pbA w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (pbA + 8#64) 128 ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (v9_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 := by
  rw [show encoderFromPbStack = ct1SentFromPbStack + 816 from rfl,
      ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide),
      sepConj_comm]

end CryptoVerification.SpqrV1.States.FromPb
