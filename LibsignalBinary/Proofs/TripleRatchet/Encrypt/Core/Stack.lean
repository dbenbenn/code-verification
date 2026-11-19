/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp

/-!
# Stack Frame Layout & `SepWPp` Call Combinators for `OTR::encrypt`

Defines the stack frame decomposition and `LsCallInv`-preserving `SepWPp` call and
panic-framing combinators for relocatable `[LibsignalPlacement]` `OTR::encrypt` proofs.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``vecU8Buf, #[1, 2]), (``optKeyBuf, #[1, 2, 3]), (``vecU8Spare, #[1, 2])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

/-! ## Stack layout for `OTR::encrypt` -/

theorem stackAt_encrypt_prologue (sp : BitVec 64) :
    stackAt sp rootStack =
      stackAt (sp - 640#64) (rootStack - 640) ∗
      memRegion (sp - 640#64) 80 ∗
      (∃∗ w560 : BitVec 64, (sp - 560#64) ↦₆₄ w560) ∗
      memRegion (sp - 552#64) 88 ∗
      memRegion (sp - 464#64) 48 ∗
      memRegion (sp - 416#64) 8 ∗
      memRegion (sp - 408#64) 72 ∗
      memRegion (sp - 336#64) 48 ∗
      memRegion (sp - 288#64) 32 ∗
      memRegion (sp - 256#64) 112 ∗
      memRegion (sp - 144#64) 24 ∗
      memRegion (sp - 120#64) 24 ∗
      (∃∗ s96 : BitVec 64, (sp - 96#64) ↦₆₄ s96) ∗
      (∃∗ s88 : BitVec 64, (sp - 88#64) ↦₆₄ s88) ∗
      (∃∗ s80 : BitVec 64, (sp - 80#64) ↦₆₄ s80) ∗
      (∃∗ s72 : BitVec 64, (sp - 72#64) ↦₆₄ s72) ∗
      (∃∗ s64 : BitVec 64, (sp - 64#64) ↦₆₄ s64) ∗
      (∃∗ s56 : BitVec 64, (sp - 56#64) ↦₆₄ s56) ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s40 : BitVec 64, (sp - 40#64) ↦₆₄ s40) ∗
      (∃∗ s32 : BitVec 64, (sp - 32#64) ↦₆₄ s32) ∗
      (∃∗ s24 : BitVec 64, (sp - 24#64) ↦₆₄ s24) ∗
      (∃∗ s16 : BitVec 64, (sp - 16#64) ↦₆₄ s16) ∗
      (∃∗ s8 : BitVec 64, (sp - 8#64) ↦₆₄ s8) := by
  simp only [stackAt, rootStack, Nat.reducePow, Nat.reduceSub]
  sep_interval_eq

theorem stackAt_encrypt_epilogue (sp : BitVec 64)
    (w560 s96 s88 s80 s72 s64 s56 s48 s40 s32 s24 s16 s8 : BitVec 64) :
    (stackAt (sp - 640#64) (rootStack - 640) ∗
      memRegion (sp - 640#64) 80 ∗
      ((sp - 560#64) ↦₆₄ w560) ∗
      memRegion (sp - 552#64) 88 ∗
      memRegion (sp - 464#64) 48 ∗
      memRegion (sp - 416#64) 8 ∗
      memRegion (sp - 408#64) 72 ∗
      memRegion (sp - 336#64) 48 ∗
      memRegion (sp - 288#64) 32 ∗
      memRegion (sp - 256#64) 112 ∗
      memRegion (sp - 144#64) 24 ∗
      memRegion (sp - 120#64) 24 ∗
      ((sp - 96#64) ↦₆₄ s96) ∗
      ((sp - 88#64) ↦₆₄ s88) ∗
      ((sp - 80#64) ↦₆₄ s80) ∗
      ((sp - 72#64) ↦₆₄ s72) ∗
      ((sp - 64#64) ↦₆₄ s64) ∗
      ((sp - 56#64) ↦₆₄ s56) ∗
      ((sp - 48#64) ↦₆₄ s48) ∗
      ((sp - 40#64) ↦₆₄ s40) ∗
      ((sp - 32#64) ↦₆₄ s32) ∗
      ((sp - 24#64) ↦₆₄ s24) ∗
      ((sp - 16#64) ↦₆₄ s16) ∗
      ((sp - 8#64) ↦₆₄ s8)) ⊢
    stackAt sp rootStack := by
  simp only [stackAt, rootStack, Nat.reducePow, Nat.reduceSub]
  sep_interval

/-! ## `SepWPp` combinators and `onPanic` frame bridges -/

theorem SepWPp.exists_elim {α : Type _} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Φ a ∗ P) Q Qp) :
    SepWPp prog ret s ((∃∗ a, Φ a) ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  rw [← sepConj_assoc] at hm
  exact h a R hm hL

theorem add_one_beq_zero_false_of_lt_2_63 {w : BitVec 64} (h : w.toNat < 2 ^ 63) :
    (w + 1#64 == 0#64) = false ∧ (w + 1#64 = 0#64 ↔ False) := by
  refine ⟨?_, ⟨fun heq => by bv_omega, False.elim⟩⟩
  cases hbeq : (w + 1#64 == 0#64)
  · rfl
  · exfalso
    have heq : w + 1#64 = 0#64 := of_decide_eq_true hbeq
    bv_omega

theorem SepWPp.shift_frame_to_post {prog : Program} {ret : BitVec 64} {s0 s1 : State}
    {F Rest M1 M2 M3 M4 M5 M6 M7 M8 R : SepProp}
    {φ_post : State → Prop} {P_ex : BitVec 64 → BitVec 64 → SepProp}
    {φ_pan : State → Prop}
    (h : ∀ R' : SepProp,
      SepWPp prog ret s1 Rest
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R') →
            ∃ x_1 x_2, φ_post sf ∧
              sf.mem ⊨ P_ex x_1 x_2 ∗ M1 ∗ M2 ∗ M3 ∗ M4 ∗ M5 ∗ M6 ∗ M7 ∗ M8 ∗ R') ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R') → φ_pan sf ∧ (sf.mem ⊨ anyHeap ∗ R'))) :
    SepWPp prog ret s1 (F ∗ Rest)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          ∃ x_1 x_2, φ_post sf ∧
            sf.mem ⊨ F ∗ P_ex x_1 x_2 ∗ M1 ∗ M2 ∗ M3 ∗ M4 ∗ M5 ∗ M6 ∗ M7 ∗ M8 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → φ_pan sf ∧ (sf.mem ⊨ anyHeap ∗ R)) := by
  intro R0 hm hL
  have hm' : s1.mem ⊨ Rest ∗ (F ∗ R0) := Satisfies.mono (by bi_entail) hm
  obtain ⟨sf, hsteps, hout⟩ := h (F ∗ R) (F ∗ R0) hm' hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨hq, hspf, hcsf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, F ∗ P_f, Satisfies.mono (by bi_entail) hmf, ⟨fun hmfR => ?_, hspf, hcsf⟩⟩⟩
    obtain ⟨x_1, x_2, hφ, hpost⟩ := hq (Satisfies.mono (by bi_entail) hmfR)
    exact ⟨x_1, x_2, hφ, Satisfies.mono (by bi_entail) hpost⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, F ∗ P_f, Satisfies.mono (by bi_entail) hmf, fun hmfR => ?_⟩)⟩
    obtain ⟨hφ, hpan'⟩ := hqp (Satisfies.mono (by bi_entail) hmfR)
    have hpan'' : sf.mem ⊨ (anyHeap ∗ F) ∗ R := Satisfies.mono (by bi_entail) hpan'
    exact ⟨hφ, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpan''⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem allocFailedIn_congr_left {s0 s1 sf : State} (htr : s1.trace = s0.trace) :
    allocFailedIn s1 sf ↔ allocFailedIn s0 sf := by
  simp only [allocFailedIn, htr]

theorem onPanic_of_send {C : Crypto} {S : SpqrModel}
    {x : OtrEncryptGhost} {s0 s1 sf : State} {F R : SepProp}
    (htr : s1.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜(allocFailedIn s1 sf ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜((x.model C S uuidTryParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
      allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (fun ⟨hp, hpref⟩ => ?_) hm
  rw [htr] at hpref
  rcases hp with halloc | hsp
  · exact ⟨Or.inr (Or.inr ((allocFailedIn_congr_left htr).mp halloc)), hpref⟩
  · exact ⟨Or.inr (Or.inl hsp), hpref⟩

theorem onPanic_of_alloc {C : Crypto} {S : SpqrModel}
    {x : OtrEncryptGhost} {s0 s1 sf : State} {F R : SepProp}
    (htr : s1.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    (((x.model C S uuidTryParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
      allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R := by
  rw [← satisfies_pure_sepConj, ← sepConj_assoc]
  refine allowPanic_frame (fun ⟨halloc, hpref⟩ => ?_) hm
  rw [htr] at hpref
  exact ⟨Or.inr (Or.inr ((allocFailedIn_congr_left htr).mp halloc)), hpref⟩

theorem onPanic_of_nck {C : Crypto} {S : SpqrModel}
    {x : OtrEncryptGhost} {newPqrState : List (BitVec 8)} {pqrKey : HKDF.Salt}
    {pqrMsg : List (BitVec 8)} {s0 s1 sf : State} {F R : SepProp}
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (htr : s1.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜x.ot.senderChainKey.nextChainKey C.F = .error .panic ∧
      s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    (((x.model C S uuidTryParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
      allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R := by
  rw [← satisfies_pure_sepConj, ← sepConj_assoc]
  refine allowPanic_frame (fun ⟨hnck, hpref⟩ => ?_) hm
  rw [htr] at hpref
  exact ⟨Or.inl (model_of_send_some_panic x C S newPqrState pqrKey pqrMsg hsend hnck), hpref⟩

theorem ret120_split_err (r : BitVec 64) :
    memRegion r 120 =
      (∃∗ r0 : BitVec 64, r ↦₆₄ r0) ∗ (∃∗ r1 : BitVec 64, (r + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (r + 16#64) ↦₆₄ r2) ∗ (∃∗ r3 : BitVec 64, (r + 24#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (r + 32#64) ↦₆₄ r4) ∗ (∃∗ r5 : BitVec 64, (r + 40#64) ↦₆₄ r5) ∗
      (∃∗ r6 : BitVec 64, (r + 48#64) ↦₆₄ r6) ∗ memRegion (r + 56#64) 64 := by
  sep_interval_eq

theorem err_branch_stack_split (sp : BitVec 64) :
    (memRegion (sp - 552#64) 88 ∗ memRegion (sp - 464#64) 48 ∗
      memRegion (sp - 400#64) 64 ∗ memRegion (sp - 288#64) 32) =
      (memRegion (sp - 552#64) 8 ∗ memRegion (sp - 544#64) 24 ∗ memRegion (sp - 520#64) 56 ∗
        (∃∗ a0 : BitVec 64, (sp - 464#64) ↦₆₄ a0) ∗
        (∃∗ a1 : BitVec 64, (sp - 456#64) ↦₆₄ a1) ∗
        (∃∗ a2 : BitVec 64, (sp - 448#64) ↦₆₄ a2) ∗
        memRegion (sp - 440#64) 24 ∗
        (∃∗ c0 : BitVec 64, (sp - 400#64) ↦₆₄ c0) ∗
        (∃∗ c1 : BitVec 64, (sp - 392#64) ↦₆₄ c1) ∗
        (∃∗ c2 : BitVec 64, (sp - 384#64) ↦₆₄ c2) ∗
        memRegion (sp - 376#64) 40 ∗
        (∃∗ b0 : BitVec 64, (sp - 288#64) ↦₆₄ b0) ∗
        (∃∗ b1 : BitVec 64, (sp - 280#64) ↦₆₄ b1) ∗
        memRegion (sp - 272#64) 16) := by
  sep_interval_eq

theorem err_branch_stack_join (sp : BitVec 64)
    (f0 f1 f2 a0 a1 a2 c0 c1 c2 b0 b1 w408 : BitVec 64) :
    (memRegion (sp - 552#64) 8 ∗
      ((sp - 544#64) ↦₆₄ f0) ∗ ((sp - 536#64) ↦₆₄ f1) ∗ ((sp - 528#64) ↦₆₄ f2) ∗
      memRegion (sp - 520#64) 56 ∗
      ((sp - 464#64) ↦₆₄ a0) ∗ ((sp - 456#64) ↦₆₄ a1) ∗ ((sp - 448#64) ↦₆₄ a2) ∗
      memRegion (sp - 440#64) 24 ∗
      ((sp - 408#64) ↦₆₄ w408) ∗
      ((sp - 400#64) ↦₆₄ c0) ∗ ((sp - 392#64) ↦₆₄ c1) ∗ ((sp - 384#64) ↦₆₄ c2) ∗
      memRegion (sp - 376#64) 40 ∗
      ((sp - 288#64) ↦₆₄ b0) ∗ ((sp - 280#64) ↦₆₄ b1) ∗
      memRegion (sp - 272#64) 16) ⊢
    (memRegion (sp - 552#64) 88 ∗ memRegion (sp - 464#64) 48 ∗
      memRegion (sp - 408#64) 72 ∗ memRegion (sp - 288#64) 32) := by
  sep_interval

theorem sendResultAt_some_unpack (A : RustAlloc) (sp : BitVec 64)
    (newPqrState : List (BitVec 8)) (pqrKey : HKDF.Salt) (pqrMsg : List (BitVec 8)) :
    spqrSendResultAt A (sp - 408#64) (some (newPqrState, pqrKey, pqrMsg)) ⊢
      ∃∗ newPqrCap : BitVec 64, ∃∗ newPqrPtr : BitVec 64,
      ∃∗ pqrMsgCap : BitVec 64, ∃∗ pqrMsgPtr : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
        ⌜pqrMsg.length < 2 ^ 32 ∧ newPqrCap.toNat < 2 ^ 63⌝ ∗
          ((sp - 408#64) ↦₆₄ newPqrCap) ∗ ((sp - 400#64) ↦₆₄ newPqrPtr) ∗
          ((sp - 392#64) ↦₆₄ BitVec.ofNat 64 newPqrState.length) ∗
          ((sp - 384#64) ↦₆₄ pqrMsgCap) ∗ ((sp - 376#64) ↦₆₄ pqrMsgPtr) ∗
          ((sp - 368#64) ↦₆₄ BitVec.ofNat 64 pqrMsg.length) ∗
          ((sp - 360#64) ↦₆₄ k0) ∗ ((sp - 352#64) ↦₆₄ k1) ∗ ((sp - 344#64) ↦₆₄ k2) ∗
          vecU8Buf A newPqrCap newPqrPtr newPqrState ∗
          vecU8Buf A pqrMsgCap pqrMsgPtr pqrMsg ∗
          optKeyBuf A k0 k1 k2 pqrKey := by
  simp only [spqrSendResultAt]
  refine Entails.pure_left fun hmsg => ?_
  unfold vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pqrMsgCap => Entails.sepExists_elim fun pqrMsgPtr =>
    Entails.sepExists_elim fun newPqrCap => Entails.sepExists_elim fun newPqrPtr => ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (optKeyAt_unpack A (sp - 408#64 + 48#64) pqrKey))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun k0 => Entails.sepExists_elim fun k1 =>
    Entails.sepExists_elim fun k2 => ?_
  rw [vecU8At_eq_header_sep_buf A (sp - 408#64), vecU8At_eq_header_sep_buf A (sp - 408#64 + 24#64)]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (vecU8Buf_pqCap_lt A newPqrCap newPqrPtr newPqrState))) ?_
  unfold vecHeader
  bi_entail

theorem some_branch_pre_mk_split (sp : BitVec 64) :
    (memRegion (sp - 640#64) 80 ∗ memRegion (sp - 552#64) 88 ∗
      memRegion (sp - 464#64) 48 ∗ memRegion (sp - 144#64) 24) =
    ((∃∗ w640 : BitVec 64, (sp - 640#64) ↦₆₄ w640) ∗
      (∃∗ w632 : BitVec 64, (sp - 632#64) ↦₆₄ w632) ∗
      (∃∗ w624 : BitVec 64, (sp - 624#64) ↦₆₄ w624) ∗
      (∃∗ w616 : BitVec 64, (sp - 616#64) ↦₆₄ w616) ∗
      (∃∗ w608 : BitVec 64, (sp - 608#64) ↦₆₄ w608) ∗
      (∃∗ w600 : BitVec 64, (sp - 600#64) ↦₆₄ w600) ∗
      (∃∗ w592 : BitVec 64, (sp - 592#64) ↦₆₄ w592) ∗
      (∃∗ w584 : BitVec 64, (sp - 584#64) ↦₆₄ w584) ∗
      (∃∗ w576 : BitVec 64, (sp - 576#64) ↦₆₄ w576) ∗
      (∃∗ w568 : BitVec 64, (sp - 568#64) ↦₆₄ w568) ∗
      memRegion (sp - 552#64) 84 ∗ memRegion (sp - 468#64) 4 ∗
      memRegion (sp - 464#64) 24 ∗ memRegion (sp - 440#64) 24 ∗
      (∃∗ u144 : BitVec 64, (sp - 144#64) ↦₆₄ u144) ∗
      (∃∗ u136 : BitVec 64, (sp - 136#64) ↦₆₄ u136) ∗
      (∃∗ u128 : BitVec 64, (sp - 128#64) ↦₆₄ u128)) := by
  sep_interval_eq

theorem some_branch_pre_mk_fold (A : RustAlloc) (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 k0 k1 k2 : BitVec 64) (pqrKey : HKDF.Salt) :
    (((sp - 408#64) ↦₆₄ w0) ∗ ((sp - 400#64) ↦₆₄ w1) ∗ ((sp - 392#64) ↦₆₄ w2) ∗
      ((sp - 384#64) ↦₆₄ w3) ∗ ((sp - 376#64) ↦₆₄ w4) ∗ ((sp - 368#64) ↦₆₄ w5) ∗
      ((sp - 360#64) ↦₆₄ k0) ∗ ((sp - 352#64) ↦₆₄ k1) ∗ ((sp - 344#64) ↦₆₄ k2) ∗
      ((sp - 144#64) ↦₆₄ k0) ∗ ((sp - 136#64) ↦₆₄ k1) ∗ ((sp - 128#64) ↦₆₄ k2) ∗
      optKeyBuf A k0 k1 k2 pqrKey) ⊢
    (memRegion (sp - 408#64) 40 ∗ memRegion (sp - 368#64) 32 ∗
      spqrRecvKeyAt A (sp - 144#64) pqrKey) := by
  have h72 : (((sp - 408#64) ↦₆₄ w0) ∗ ((sp - 400#64) ↦₆₄ w1) ∗ ((sp - 392#64) ↦₆₄ w2) ∗
      ((sp - 384#64) ↦₆₄ w3) ∗ ((sp - 376#64) ↦₆₄ w4) ∗ ((sp - 368#64) ↦₆₄ w5) ∗
      ((sp - 360#64) ↦₆₄ k0) ∗ ((sp - 352#64) ↦₆₄ k1) ∗ ((sp - 344#64) ↦₆₄ k2)) ⊢
    (memRegion (sp - 408#64) 40 ∗ memRegion (sp - 368#64) 32) := by sep_interval
  have h144 :
      (((sp - 144#64) ↦₆₄ k0) ∗ ((sp - 136#64) ↦₆₄ k1) ∗ ((sp - 128#64) ↦₆₄ k2) ∗
        optKeyBuf A k0 k1 k2 pqrKey) ⊢ spqrRecvKeyAt A (sp - 144#64) pqrKey := by
    simpa (disch := decide) only [bv_sub_add_lit, Nat.reduceSub] using
      Entails.trans (optKeyAt_pack A (sp - 144#64) k0 k1 k2 pqrKey)
        (optKeyAt_entails_optKeyRecvAt A (sp - 144#64) pqrKey)
  simpa only [sepConj_assoc] using sepConj_mono h72 h144

theorem otrAt_exists_pack (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    (vecU8At A o pqCap pqPtr ot.pqrState ∗
      ((o + 0x18#64) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
      ((o + 0x38#64) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
      ((o + 0x58#64) ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) ∗
      ((o + 0x78#64) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((o + 0x98#64) ↦ₛ chainKeyBytes ot.senderChainKey) ∗
      ((o + 0xbc#64) ↦₃₂ ot.previousCounter) ∗ ((o + 0xc0#64) ↦₈ ot.sessionVersion) ∗
      memRegion (o + 0xc1#64) 7) ⊢
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64, otrAt A o pqCap' pqPtr' ot) :=
  Entails.sepExists_right pqCap (Entails.sepExists_right pqPtr (Entails.refl _))

theorem vecU8_544_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp - 544#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp - 544#64) ↦₆₄ cap) ∗ ((sp - 536#64) ↦₆₄ ptr) ∗
        ((sp - 528#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  unfold vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  rw [vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]
  bi_entail

theorem spAligned_sub_640 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 640#64) &&& 15#64) = 0#64 ∧ (((sp - 640#64) &&& 15#64 == 0#64) = true) :=
  ⟨eq_of_beq (spAligned_sub sp 640#64 h), spAligned_sub sp 640#64 h⟩

theorem vecU8_464_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp - 464#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((sp - 464#64) ↦₆₄ cap) ∗ ((sp - 456#64) ↦₆₄ ptr) ∗
        ((sp - 448#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8Spare A cap ptr bs.length := by
  unfold vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  exact Entails.trans (sepConj_mono_right (vecU8Buf_expose_slice A cap ptr bs)) (by bi_entail)

theorem pre_new_stack_split (sp : BitVec 64) :
    (memRegion (sp - 408#64) 40 ∗ memRegion (sp - 368#64) 32 ∗
      memRegion (sp - 336#64) 48 ∗ memRegion (sp - 288#64) 32) =
    (memRegion (sp - 408#64) 120 ∗
      (∃∗ d0 : BitVec 64, (sp - 288#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp - 280#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp - 272#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp - 264#64) ↦₆₄ d3)) := by
  sep_interval_eq

theorem srk_copy_pack (o sp : BitVec 64) (bs : List (BitVec 8))
    (srk0 srk1 srk2 srk3 : BitVec 64) (hsrk : bytes32WordsProp bs srk0 srk1 srk2 srk3) :
    (((o + 24#64) ↦₆₄ srk0) ∗ ((o + 32#64) ↦₆₄ srk1) ∗
      ((o + 40#64) ↦₆₄ srk2) ∗ ((o + 48#64) ↦₆₄ srk3) ∗
      ((sp - 288#64) ↦₆₄ srk0) ∗ ((sp - 280#64) ↦₆₄ srk1) ∗
      ((sp - 272#64) ↦₆₄ srk2) ∗ ((sp - 264#64) ↦₆₄ srk3)) ⊢
    (((o + 24#64) ↦ₛ bs) ∗ ((sp - 288#64) ↦ₛ bs)) := by
  have h1 : (((o + 24#64) ↦₆₄ srk0) ∗ ((o + 32#64) ↦₆₄ srk1) ∗
      ((o + 40#64) ↦₆₄ srk2) ∗ ((o + 48#64) ↦₆₄ srk3)) ⊢ ((o + 24#64) ↦ₛ bs) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      Entails.trans (Entails.pure_right hsrk (Entails.refl _))
        (bytes32_pack (o + 24#64) bs srk0 srk1 srk2 srk3)
  have h2 : (((sp - 288#64) ↦₆₄ srk0) ∗ ((sp - 280#64) ↦₆₄ srk1) ∗
      ((sp - 272#64) ↦₆₄ srk2) ∗ ((sp - 264#64) ↦₆₄ srk3)) ⊢ ((sp - 288#64) ↦ₛ bs) := by
    simpa (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc] using
      Entails.trans (Entails.pure_right hsrk (Entails.refl _))
        (bytes32_pack (sp - 288#64) bs srk0 srk1 srk2 srk3)
  exact Entails.trans (by bi_entail) (sepConj_mono h1 h2)

theorem SepWPp.exists_elim_top {α : Type _} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Φ a) Q Qp) :
    SepWPp prog ret s (∃∗ a, Φ a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  exact h a R hm hL

theorem SepWPp.false_elim {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {Q Qp : State → SepProp → Prop} :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜False⌝ ∗ P3) Q Qp := by
  intro R hm
  have hfalse : s.mem ⊨ ⌜False⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ R) := Satisfies.mono (by bi_entail) hm
  exact (not_satisfies_false_sepConj hfalse).elim

theorem pre_nck_stack_split (sp : BitVec 64) :
    (memRegion (sp - 440#64) 24 ∗ memRegion (sp - 256#64) 112) =
    ((∃∗ e0 : BitVec 64, (sp - 440#64) ↦₆₄ e0) ∗
      (∃∗ e1 : BitVec 64, (sp - 432#64) ↦₆₄ e1) ∗
      (∃∗ e2 : BitVec 64, (sp - 424#64) ↦₆₄ e2) ∗
      (∃∗ t0 : BitVec 64, (sp - 256#64) ↦₆₄ t0) ∗
      (∃∗ t1 : BitVec 64, (sp - 248#64) ↦₆₄ t1) ∗
      (∃∗ t2 : BitVec 64, (sp - 240#64) ↦₆₄ t2) ∗
      (∃∗ t3 : BitVec 64, (sp - 232#64) ↦₆₄ t3) ∗
      (∃∗ t4 : BitVec 64, (sp - 224#64) ↦₆₄ t4) ∗
      (∃∗ t5 : BitVec 64, (sp - 216#64) ↦₆₄ t5) ∗
      (∃∗ t6 : BitVec 64, (sp - 208#64) ↦₆₄ t6) ∗
      (∃∗ t7 : BitVec 64, (sp - 200#64) ↦₆₄ t7) ∗
      (∃∗ t8 : BitVec 64, (sp - 192#64) ↦₆₄ t8) ∗
      (∃∗ t9 : BitVec 64, (sp - 184#64) ↦₆₄ t9) ∗
      (∃∗ t10 : BitVec 64, (sp - 176#64) ↦₆₄ t10) ∗
      (∃∗ t11 : BitVec 64, (sp - 168#64) ↦₆₄ t11) ∗
      (∃∗ t12 : BitVec 64, (sp - 160#64) ↦₆₄ t12) ∗
      (∃∗ t13 : BitVec 64, (sp - 152#64) ↦₆₄ t13)) := by
  sep_interval_eq

theorem pre_nck_fold (sp : BitVec 64)
    (a0 a1 a2 a3 a4 a5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) :
    (((sp - 464#64) ↦₆₄ a0) ∗ ((sp - 456#64) ↦₆₄ a1) ∗ ((sp - 448#64) ↦₆₄ a2) ∗
      ((sp - 440#64) ↦₆₄ a3) ∗ ((sp - 432#64) ↦₆₄ a4) ∗ ((sp - 424#64) ↦₆₄ a5) ∗
      ((sp - 408#64) ↦₆₄ w0) ∗ ((sp - 400#64) ↦₆₄ w1) ∗ ((sp - 392#64) ↦₆₄ w2) ∗
      ((sp - 384#64) ↦₆₄ w3) ∗ ((sp - 376#64) ↦₆₄ w4) ∗ ((sp - 368#64) ↦₆₄ w5) ∗
      ((sp - 360#64) ↦₆₄ w6) ∗ ((sp - 352#64) ↦₆₄ w7) ∗ ((sp - 344#64) ↦₆₄ w8) ∗
      ((sp - 336#64) ↦₆₄ w9) ∗ ((sp - 328#64) ↦₆₄ w10) ∗ ((sp - 320#64) ↦₆₄ w11) ∗
      ((sp - 312#64) ↦₆₄ w12) ∗ ((sp - 304#64) ↦₆₄ w13) ∗ ((sp - 296#64) ↦₆₄ w14)) ⊢
    (memRegion (sp - 464#64) 48 ∗ memRegion (sp - 408#64) 36 ∗
      memRegion (sp - 372#64) 36 ∗ memRegion (sp - 336#64) 48) := by
  sep_interval

theorem vecU8At_unpack_dealloc (A : RustAlloc) (o cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A o cap ptr bs ⊢
      (o ↦₆₄ cap) ∗ ((o + 8#64) ↦₆₄ ptr) ∗ ((o + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (vecU8Buf_expose_slice A cap ptr bs) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (vecU8Spare_dealloc A cap ptr bs) ?_
  exact Entails.pure_left fun _ => Entails.refl _

theorem pre_dealloc1_stack_fold (sp : BitVec 64)
    (w640 w632 w624 w616 w608 w600 : BitVec 64) (mk : MessageKeys)
    (srk : List (BitVec 8)) (hsrk : srk.length = 32) :
    (((sp - 640#64) ↦₆₄ w640) ∗ ((sp - 632#64) ↦₆₄ w632) ∗
      ((sp - 624#64) ↦₆₄ w624) ∗ ((sp - 616#64) ↦₆₄ w616) ∗
      ((sp - 608#64) ↦₆₄ w608) ∗ ((sp - 600#64) ↦₆₄ w600) ∗
      ((sp - 552#64) ↦ₛ keyToBytes32 mk.cipherKey) ∗
      ((sp - 520#64) ↦ₛ keyToBytes32 mk.macKey) ∗
      ((sp - 488#64) ↦ₛ blockToBytesLE mk.iv) ∗
      ((sp - 472#64) ↦₃₂ mk.counter) ∗
      memRegion (sp - 468#64) 4 ∗
      memRegion (sp - 464#64) 48 ∗
      memRegion (sp - 416#64) 8 ∗
      memRegion (sp - 372#64) 36 ∗
      memRegion (sp - 336#64) 48 ∗
      ((sp - 288#64) ↦ₛ srk) ∗
      memRegion (sp - 144#64) 24 ∗
      memRegion (sp - 120#64) 24) ⊢
    (memRegion (sp - 640#64) 48 ∗
      memRegion (sp - 552#64) 144 ∗
      memRegion (sp - 372#64) 116 ∗
      memRegion (sp - 144#64) 48) := by
  have := length_keyToBytes32 mk.cipherKey
  have := length_keyToBytes32 mk.macKey
  have := blockToBytesLE_length mk.iv
  sep_interval

theorem post_dealloc1_copy_fold (o sp : BitVec 64) (ck' : ChainKey)
    (ck0 ck1 ck2 ck3 : BitVec 64) (hck : bytes32WordsProp (keyToBytes32 ck'.key) ck0 ck1 ck2 ck3) :
    (((o + 152#64) ↦₆₄ ck0) ∗ ((o + 160#64) ↦₆₄ ck1) ∗
      ((o + 168#64) ↦₆₄ ck2) ∗ ((o + 176#64) ↦₆₄ ck3) ∗
      ((o + 184#64) ↦₃₂ ck'.index) ∗
      memRegion (sp - 552#64) 144 ∗
      ((sp - 408#64) ↦₆₄ ck0) ∗ ((sp - 400#64) ↦₆₄ ck1) ∗
      ((sp - 392#64) ↦₆₄ ck2) ∗ ((sp - 384#64) ↦₆₄ ck3) ∗
      ((sp - 376#64) ↦₃₂ ck'.index) ∗
      memRegion (sp - 372#64) 116) ⊢
    (((o + 152#64) ↦ₛ chainKeyBytes ck') ∗
      memRegion (sp - 552#64) 296) := by
  have ho :
      (((o + 152#64) ↦₆₄ ck0) ∗ ((o + 160#64) ↦₆₄ ck1) ∗
        ((o + 168#64) ↦₆₄ ck2) ∗ ((o + 176#64) ↦₆₄ ck3) ∗
        ((o + 184#64) ↦₃₂ ck'.index)) ⊢
      ((o + 152#64) ↦ₛ chainKeyBytes ck') := by
    have := Entails.trans (Entails.pure_right hck (Entails.refl _))
      (chainKeyBytes_pack (o + 152#64) ck' ck0 ck1 ck2 ck3)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using this
  have h552 :
      (memRegion (sp - 552#64) 144 ∗
        ((sp - 408#64) ↦₆₄ ck0) ∗ ((sp - 400#64) ↦₆₄ ck1) ∗
        ((sp - 392#64) ↦₆₄ ck2) ∗ ((sp - 384#64) ↦₆₄ ck3) ∗
        ((sp - 376#64) ↦₃₂ ck'.index) ∗
        memRegion (sp - 372#64) 116) ⊢
      memRegion (sp - 552#64) 296 := by
    sep_interval
  simpa only [sepConj_assoc] using sepConj_mono ho h552

theorem ret120_split_ok (ret : BitVec 64) :
    memRegion ret 120 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗ (∃∗ r1 : BitVec 64, (ret + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (ret + 16#64) ↦₆₄ r2) ∗ (∃∗ r3 : BitVec 64, (ret + 24#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (ret + 32#64) ↦₆₄ r4) ∗ (∃∗ r5 : BitVec 64, (ret + 40#64) ↦₆₄ r5) ∗
      (∃∗ r6 : BitVec 64, (ret + 48#64) ↦₆₄ r6) ∗ (∃∗ r7 : BitVec 64, (ret + 56#64) ↦₆₄ r7) ∗
      (∃∗ r8 : BitVec 64, (ret + 64#64) ↦₆₄ r8) ∗ (∃∗ r9 : BitVec 64, (ret + 72#64) ↦₆₄ r9) ∗
      (∃∗ r10 : BitVec 64, (ret + 80#64) ↦₆₄ r10) ∗ (∃∗ r11 : BitVec 64, (ret + 88#64) ↦₆₄ r11) ∗
      (∃∗ r12 : BitVec 64, (ret + 96#64) ↦₆₄ r12) ∗ (∃∗ r13 : BitVec 64, (ret + 104#64) ↦₆₄ r13) ∗
      (∃∗ r14 : BitVec 64, (ret + 112#64) ↦₆₄ r14) := by
  sep_interval_eq

theorem beq_false_of_ne {x : BitVec 64} (h : x ≠ 0) : (x == 0#64) = false := by
  cases hbeq : (x == 0#64)
  · rfl
  · exact False.elim (h (by simpa using hbeq))

theorem SepWPp.join_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P Frame : SepProp} {Q Qp : State → SepProp → Prop}
    (Cond : State → Prop) (P1 P2 : SepProp)
    (hf : P = P1 ∗ Frame)
    (hstep : ∀ R,
      (∀ s', Cond s' → SepWPp prog ret s' (P2 ∗ R) Q Qp) →
      SepWPp prog ret s (P1 ∗ R) Q Qp)
    (hcont : ∀ s', Cond s' → SepWPp prog ret s' (P2 ∗ Frame) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.fold (Entails.refl P1) hf (hstep Frame hcont)

theorem msgResultAt_ok_pack (A : RustAlloc) (g : SignalMessageGhost) (ret : BitVec 64)
    (m : SignalMessage) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    ((ret ↦₆₄ g.pqCap) ∗
      ((ret + 8#64) ↦₆₄ g.pqPtr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.pqRatchet.length) ∗
      ((ret + 24#64) ↦₆₄ g.ctPtr) ∗ ((ret + 32#64) ↦₆₄ BitVec.ofNat 64 m.ciphertext.length) ∗
      ((ret + 40#64) ↦₆₄ g.serPtr) ∗ ((ret + 48#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      ((ret + 56#64) ↦₆₄ m7) ∗ ((ret + 64#64) ↦₆₄ m8) ∗
      ((ret + 72#64) ↦₆₄ m9) ∗ ((ret + 80#64) ↦₆₄ m10) ∗
      ((ret + 88#64) ↦₆₄ m11) ∗ ((ret + 96#64) ↦₆₄ m12) ∗
      ((ret + 104#64) ↦₆₄ (m.previousCounter ++ m.counter)) ∗
      ((ret + 112#64) ↦₆₄ m14) ∗
      signalMessageHeap A g m m7 m8 m9 m10 m11 m12 m14) ⊢
    signalMessageResultAt A (utf8 "encrypt") ret (.ok m) := by
  unfold signalMessageResultAt
  refine Entails.sepExists_right g ?_
  have h := signalMessageAt_pack A g ret m m7 m8 m9 m10 m11 m12 m14
  unfold signalMessageWordsAt at h
  simpa only [sepConj_assoc] using h

theorem otrAt_updated_pack (A : RustAlloc) (o newPqrCap newPqrPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (ck' : ChainKey) (newPqrState : List (BitVec 8)) :
    ((o ↦₆₄ newPqrCap) ∗ ((o + 8#64) ↦₆₄ newPqrPtr) ∗
      ((o + 16#64) ↦₆₄ BitVec.ofNat 64 newPqrState.length) ∗
      vecU8Buf A newPqrCap newPqrPtr newPqrState ∗
      ((o + 0x18#64) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
      ((o + 0x38#64) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
      ((o + 0x58#64) ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) ∗
      ((o + 0x78#64) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((o + 0x98#64) ↦ₛ chainKeyBytes ck') ∗
      ((o + 0xbc#64) ↦₃₂ ot.previousCounter) ∗
      ((o + 0xc0#64) ↦₈ ot.sessionVersion) ∗
      memRegion (o + 0xc1#64) 7) ⊢
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
      otrAt A o pqCap' pqPtr' { ot with senderChainKey := ck', pqrState := newPqrState }) := by
  simp only [otrAt, vecU8At_eq_header_sep_buf, vecHeader]
  bi_entail

theorem post_copy_stack_fold (sp : BitVec 64)
    (w592 w584 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 : BitVec 64) :
    (memRegion (sp - 640#64) 48 ∗
      ((sp - 592#64) ↦₆₄ w592) ∗ ((sp - 584#64) ↦₆₄ w584) ∗
      ((sp - 256#64) ↦₆₄ t0) ∗ ((sp - 248#64) ↦₆₄ t1) ∗
      ((sp - 240#64) ↦₆₄ t2) ∗ ((sp - 232#64) ↦₆₄ t3) ∗
      ((sp - 224#64) ↦₆₄ t4) ∗ ((sp - 216#64) ↦₆₄ t5) ∗
      ((sp - 208#64) ↦₆₄ t6) ∗ ((sp - 200#64) ↦₆₄ t7) ∗
      ((sp - 192#64) ↦₆₄ t8) ∗ ((sp - 184#64) ↦₆₄ t9) ∗
      ((sp - 176#64) ↦₆₄ t10) ∗ ((sp - 168#64) ↦₆₄ t11) ∗
      ((sp - 160#64) ↦₆₄ t12) ∗ ((sp - 152#64) ↦₆₄ t13)) ⊢
    (memRegion (sp - 640#64) 64 ∗ memRegion (sp - 256#64) 112) := by
  sep_interval

theorem pair_576_entails_memRegion (sp w576 w568 : BitVec 64) :
    (((sp - 576#64) ↦₆₄ w576) ∗ ((sp - 568#64) ↦₆₄ w568)) ⊢
    memRegion (sp - 576#64) 16 := by
  sep_interval

theorem ok_branch_epilogue_stack (sp : BitVec 64)
    (w560 s96 s88 s80 s72 s64 s56 s48 s40 s32 s24 s16 s8 : BitVec 64) :
    (stackAt (sp - 640#64) (rootStack - 640) ∗
      memRegion (sp - 640#64) 64 ∗
      memRegion (sp - 576#64) 16 ∗
      ((sp - 560#64) ↦₆₄ w560) ∗
      memRegion (sp - 552#64) 296 ∗
      memRegion (sp - 256#64) 112 ∗
      memRegion (sp - 144#64) 48 ∗
      ((sp - 96#64) ↦₆₄ s96) ∗
      ((sp - 88#64) ↦₆₄ s88) ∗
      ((sp - 80#64) ↦₆₄ s80) ∗
      ((sp - 72#64) ↦₆₄ s72) ∗
      ((sp - 64#64) ↦₆₄ s64) ∗
      ((sp - 56#64) ↦₆₄ s56) ∗
      ((sp - 48#64) ↦₆₄ s48) ∗
      ((sp - 40#64) ↦₆₄ s40) ∗
      ((sp - 32#64) ↦₆₄ s32) ∗
      ((sp - 24#64) ↦₆₄ s24) ∗
      ((sp - 16#64) ↦₆₄ s16) ∗
      ((sp - 8#64) ↦₆₄ s8)) ⊢
    stackAt sp rootStack := by
  simp only [stackAt, rootStack, Nat.reducePow, Nat.reduceSub]
  sep_interval

/-! ## Relocatable `[LibsignalPlacement]` `LsCallInv` & `SepWPp` Call Frame Helpers -/

abbrev LsCallInv (pl : Obj.MultiPlacement) (s : State) : Prop :=
  LibsignalCodeRoLoaded pl s.mem

theorem LsCallInv.of_steps {pl : Obj.MultiPlacement} {prog : Program} {s s' : State}
    (h : LsCallInv pl s) (hs : Steps prog s s') : LsCallInv pl s' :=
  h.of_keepsFrozen hs.keepsFrozen

theorem SepWPp.of_sepWP_lsCallInv {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : LsCallInv pl s)
    (h : SepWP prog mid s P (fun sm Pm => LsCallInv pl sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hinv h

theorem SepWPp.call_frame_lsInv {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hinv : LsCallInv pl s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

theorem SepWPp.call_frame_lsInv_cro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hinv : LsCallInv pl s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsCallInv pl sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hinv.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R hoom_st hpost⟩)⟩

end CryptoVerification.LibsignalTripleRatchet.Encrypt
