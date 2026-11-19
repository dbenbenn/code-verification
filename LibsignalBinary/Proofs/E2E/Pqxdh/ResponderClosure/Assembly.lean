/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage-Level Framing and `SepWPp` Combinators for `message_decrypt_prekey::<PqxdhRng>::{closure#0}`

Defines `PanicOomProp` and framed `SepWP` / `SepWPp` stage and subroutine-call composition
combinators for `message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.SessionStoreImpl
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

/-- Panic postcondition asserting OOM allocation failure between `s0` and `sf`. -/
@[expose] def PanicOomProp (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem allowPanic_oom_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

theorem eq_of_sep_emp {P Q : SepProp} (h : P = Q ∗ emp) : P = Q := by
  rwa [sepConj_emp] at h

theorem entails_anyHeap_5 {P A B C D E F : SepProp}
    (h : P = (A ∗ B ∗ C ∗ D ∗ E) ∗ F) :
    P ⊢ A ∗ B ∗ C ∗ D ∗ E ∗ anyHeap := by
  rw [h]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (entails_anyHeap F)))))

/-- Weaken a framed part `P₁ ⊢ P₂` of the precondition in `SepWPp`. -/
theorem SepWPp.weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

/-- Run a framed `SepWPp` stage to `mid`, then continue in `SepWPp` with `PanicOomProp s0`. -/
theorem SepWPp.bind_sepWPp_frame {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Final framed `SepWPp` stage reaching `ret` with `PanicOomProp s0`. -/
theorem SepWPp.ret_sepWPp_frame {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage P_stage_post F : SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sf)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running → Q_regs sf →
      Q sf (P_stage_post ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  SepWPp.bind_sepWPp_frame hstage hP fun sf hpc hrun hregs =>
    SepWPp.done hpc hrun (hret sf hpc hrun hregs)

theorem stackAt_sub_eq (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

theorem decryptPrekeySavedRegsAt_add_cd0 (sp : BitVec 64) (s0 : State) :
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 =
      ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold decryptPrekeySavedRegsAt
  have h0 : sp + 0xcd0#64 - 0x60#64 = sp + 0xc70#64 := by bv_omega
  have h1 : 8#64 + (sp + 0xc70#64) = sp + 0xc78#64 := by bv_omega
  have h2 : 16#64 + (sp + 0xc70#64) = sp + 0xc80#64 := by bv_omega
  have h3 : 24#64 + (sp + 0xc70#64) = sp + 0xc88#64 := by bv_omega
  have h4 : 32#64 + (sp + 0xc70#64) = sp + 0xc90#64 := by bv_omega
  have h5 : 40#64 + (sp + 0xc70#64) = sp + 0xc98#64 := by bv_omega
  have h6 : 48#64 + (sp + 0xc70#64) = sp + 0xca0#64 := by bv_omega
  have h7 : 56#64 + (sp + 0xc70#64) = sp + 0xca8#64 := by bv_omega
  have h8 : 64#64 + (sp + 0xc70#64) = sp + 0xcb0#64 := by bv_omega
  have h9 : 72#64 + (sp + 0xc70#64) = sp + 0xcb8#64 := by bv_omega
  have h10 : 80#64 + (sp + 0xc70#64) = sp + 0xcc0#64 := by bv_omega
  have h11 : 88#64 + (sp + 0xc70#64) = sp + 0xcc8#64 := by bv_omega
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem outPtr48_split_eq (outPtr : BitVec 64) :
    memRegion outPtr 48 =
      (∃∗ u2c : BitVec 32, ∃∗ u24 : BitVec 64, ∃∗ u1c : BitVec 64,
       ∃∗ u14 : BitVec 64, ∃∗ u0c : BitVec 64, ∃∗ u8 : BitVec 32,
       ∃∗ u0 : BitVec 64,
        ((outPtr + 0x0#64) ↦₆₄ u0) ∗
        ((outPtr + 0x8#64) ↦₃₂ u8) ∗
        ((outPtr + 0xc#64) ↦₆₄ u0c) ∗
        ((outPtr + 0x14#64) ↦₆₄ u14) ∗
        ((outPtr + 0x1c#64) ↦₆₄ u1c) ∗
        ((outPtr + 0x24#64) ↦₆₄ u24) ∗
        ((outPtr + 0x2c#64) ↦₃₂ u2c)) := by
  rw [ProofLib.memRegion_split' (b := outPtr) (n := 8) (k := 40)
        (b' := outPtr + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x8#64) (n := 4) (k := 36)
        (b' := outPtr + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0xc#64) (n := 8) (k := 28)
        (b' := outPtr + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x14#64) (n := 8) (k := 20)
        (b' := outPtr + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x1c#64) (n := 8) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outPtr,
      ProofLib.memRegion_four (outPtr + 0x8#64),
      ProofLib.memRegion_eight (outPtr + 0xc#64),
      ProofLib.memRegion_eight (outPtr + 0x14#64),
      ProofLib.memRegion_eight (outPtr + 0x1c#64),
      ProofLib.memRegion_eight (outPtr + 0x24#64),
      ProofLib.memRegion_four (outPtr + 0x2c#64),
      show (outPtr + 0x0#64) = outPtr from BitVec.add_zero outPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem outPtr48_err_fold (outPtr errTag w0c w14 w1c w24 : BitVec 64) (w8 w2c : BitVec 32) :
    ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
    ((outPtr + 0x8#64) ↦₃₂ w8) ∗
    ((outPtr + 0xc#64) ↦₆₄ w0c) ∗
    ((outPtr + 0x14#64) ↦₆₄ w14) ∗
    ((outPtr + 0x1c#64) ↦₆₄ w1c) ∗
    ((outPtr + 0x24#64) ↦₆₄ w24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w2c) ⊢
      (outPtr ↦₆₄ errTag) ∗ memRegion (outPtr + 8#64) 40 := by
  rw [BitVec.add_zero,
      ProofLib.memRegion_split' (b := outPtr + 8#64) (n := 4) (k := 36)
        (b' := outPtr + 0xc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0xc#64) (n := 8) (k := 28)
        (b' := outPtr + 0x14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x14#64) (n := 8) (k := 20)
        (b' := outPtr + 0x1c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x1c#64) (n := 8) (k := 12)
        (b' := outPtr + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outPtr + 0x24#64) (n := 8) (k := 4)
        (b' := outPtr + 0x2c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo32_entails_memRegion _ _))))))

theorem sp370_36_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 =
      (∃∗ u20 : BitVec 32, ∃∗ u18 : BitVec 64, ∃∗ u10 : BitVec 64,
       ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((sp + 0x370#64) ↦₆₄ u0) ∗
        ((sp + 0x378#64) ↦₆₄ u8) ∗
        ((sp + 0x380#64) ↦₆₄ u10) ∗
        ((sp + 0x388#64) ↦₆₄ u18) ∗
        ((sp + 0x390#64) ↦₃₂ u20)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 8) (k := 12)
        (b' := sp + 0x388#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x388#64) (n := 8) (k := 4)
        (b' := sp + 0x390#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x370#64),
      ProofLib.memRegion_eight (sp + 0x378#64),
      ProofLib.memRegion_eight (sp + 0x380#64),
      ProofLib.memRegion_eight (sp + 0x388#64),
      ProofLib.memRegion_four (sp + 0x390#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sp210_36_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x210#64) 36 =
      (∃∗ u20 : BitVec 32, ∃∗ u18 : BitVec 64, ∃∗ u10 : BitVec 64,
       ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((sp + 0x210#64) ↦₆₄ u0) ∗
        ((sp + 0x218#64) ↦₆₄ u8) ∗
        ((sp + 0x220#64) ↦₆₄ u10) ∗
        ((sp + 0x228#64) ↦₆₄ u18) ∗
        ((sp + 0x230#64) ↦₃₂ u20)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x210#64) (n := 8) (k := 28)
        (b' := sp + 0x218#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x218#64) (n := 8) (k := 20)
        (b' := sp + 0x220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x220#64) (n := 8) (k := 12)
        (b' := sp + 0x228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x228#64) (n := 8) (k := 4)
        (b' := sp + 0x230#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x210#64),
      ProofLib.memRegion_eight (sp + 0x218#64),
      ProofLib.memRegion_eight (sp + 0x220#64),
      ProofLib.memRegion_eight (sp + 0x228#64),
      ProofLib.memRegion_four (sp + 0x230#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pollOptSessionRecordNone_split_eq (A : RustAlloc) (sp : BitVec 64) :
    pollOptSessionRecordResultAt A (sp + 0x3e0#64) none =
      (∃∗ bs312 : List (BitVec 8), ∃∗ d_414 : BitVec 32, ∃∗ w_40c : BitVec 64,
       ∃∗ w_404 : BitVec 64, ∃∗ w_3fc : BitVec 64, ∃∗ w_3f4 : BitVec 64,
       ∃∗ d_3f0 : BitVec 32, ∃∗ w_3e8 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ w_3e8) ∗
        ((sp + 0x3f0#64) ↦₃₂ d_3f0) ∗
        ((sp + 0x3f4#64) ↦₆₄ w_3f4) ∗
        ((sp + 0x3fc#64) ↦₆₄ w_3fc) ∗
        ((sp + 0x404#64) ↦₆₄ w_404) ∗
        ((sp + 0x40c#64) ↦₆₄ w_40c) ∗
        ((sp + 0x414#64) ↦₃₂ d_414) ∗
        ⌜bs312.length = 312⌝ ∗
        ((sp + 0x418#64) ↦ₛ bs312)) := by
  dsimp only [pollOptSessionRecordResultAt]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 352)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 4) (k := 348)
        (b' := sp + 0x3f4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f4#64) (n := 8) (k := 340)
        (b' := sp + 0x3fc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3fc#64) (n := 8) (k := 332)
        (b' := sp + 0x404#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x404#64) (n := 8) (k := 324)
        (b' := sp + 0x40c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x40c#64) (n := 8) (k := 316)
        (b' := sp + 0x414#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x414#64) (n := 4) (k := 312)
        (b' := sp + 0x418#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x3e8#64),
      ProofLib.memRegion_four (sp + 0x3f0#64),
      ProofLib.memRegion_eight (sp + 0x3f4#64),
      ProofLib.memRegion_eight (sp + 0x3fc#64),
      ProofLib.memRegion_eight (sp + 0x404#64),
      ProofLib.memRegion_eight (sp + 0x40c#64),
      ProofLib.memRegion_four (sp + 0x414#64),
      memRegion_eq_exists_bytes (sp + 0x418#64) 312 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pollBoolTrue_split_eq (sp : BitVec 64) :
    pollBoolResultAt (sp + 0x3e0#64) true =
      (∃∗ w_408 : BitVec 64, ∃∗ w_400 : BitVec 64, ∃∗ d_3fc : BitVec 32,
       ∃∗ d_3f8 : BitVec 32, ∃∗ w_3f0 : BitVec 64, ∃∗ b_3ef : BitVec 8,
       ∃∗ h_3ed : BitVec 16, ∃∗ d_3e9 : BitVec 32,
        ((sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((sp + 0x3e8#64) ↦₈ 1#8) ∗
        ((sp + 0x3e9#64) ↦₃₂ d_3e9) ∗
        ((sp + 0x3ed#64) ↦₁₆ h_3ed) ∗
        ((sp + 0x3ef#64) ↦₈ b_3ef) ∗
        ((sp + 0x3f0#64) ↦₆₄ w_3f0) ∗
        ((sp + 0x3f8#64) ↦₃₂ d_3f8) ∗
        ((sp + 0x3fc#64) ↦₃₂ d_3fc) ∗
        ((sp + 0x400#64) ↦₆₄ w_400) ∗
        ((sp + 0x408#64) ↦₆₄ w_408)) := by
  simp only [pollBoolResultAt, ↓reduceIte]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e0#64) + 9#64 = sp + 0x3e9#64 by bv_omega,
      ProofLib.memRegion_split' (b := sp + 0x3e9#64) (n := 4) (k := 35)
        (b' := sp + 0x3ed#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ed#64) (n := 2) (k := 33)
        (b' := sp + 0x3ef#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ef#64) (n := 1) (k := 32)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 4) (k := 20)
        (b' := sp + 0x3fc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3fc#64) (n := 4) (k := 16)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (sp + 0x3e9#64),
      ProofLib.memRegion_two (sp + 0x3ed#64),
      ProofLib.memRegion_one (sp + 0x3ef#64),
      ProofLib.memRegion_eight (sp + 0x3f0#64),
      ProofLib.memRegion_four (sp + 0x3f8#64),
      ProofLib.memRegion_four (sp + 0x3fc#64),
      ProofLib.memRegion_eight (sp + 0x400#64),
      ProofLib.memRegion_eight (sp + 0x408#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem loadBox1_entails_memRegion (futPtr mp qAddrPtr : BitVec 64) :
    (futPtr ↦₆₄ mp) ∗ ((futPtr + 8#64) ↦₆₄ qAddrPtr) ∗ ((futPtr + 16#64) ↦₈ 1#8) ∗
    memRegion (futPtr + 0x11#64) 7 ⊢ memRegion futPtr 24 :=
  inMemLoadBoxAt_memRegion futPtr mp qAddrPtr 1#8

theorem trustBox1_entails_memRegion (futPtr mp qAddrPtr qKeyPtr : BitVec 64) (dir : BitVec 8) :
    (futPtr ↦₆₄ mp) ∗ ((futPtr + 8#64) ↦₆₄ qAddrPtr) ∗ ((futPtr + 16#64) ↦₆₄ qKeyPtr) ∗
    ((futPtr + 24#64) ↦₈ 1#8) ∗ ((futPtr + 25#64) ↦₈ dir) ∗
    memRegion (futPtr + 0x1a#64) 6 ⊢ memRegion futPtr 32 :=
  inMemTrustBoxAt_memRegion futPtr mp qAddrPtr qKeyPtr 1#8 dir

theorem cells25_split2_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x2c8#64) 25 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u1) ∗
        cells (coroPtr + 0x2d8#64) 23) := by
  conv_lhs =>
    rw [cells_succ, cells_succ]
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem cells25_fold2 (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x2c8#64) ↦₆₄ v0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ v1) ∗
      cells (coroPtr + 0x2d8#64) 23 ⊢ cells (coroPtr + 0x2c8#64) 25 := by
  refine Entails.trans ?_ (Entails.of_eq (cells25_split2_eq coroPtr).symm)
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.refl _))

theorem cells2_398_fold (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x398#64) ↦₆₄ v0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ v1) ⊢
      cells (coroPtr + 0x398#64) 2 := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_right]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.refl _))

end CryptoVerification.E2E.Pqxdh.ResponderClosure
