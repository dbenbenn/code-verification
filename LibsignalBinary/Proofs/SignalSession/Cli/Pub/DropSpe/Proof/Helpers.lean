/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.Entry
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.DropSpeProof.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

section

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?

private def SatEntails (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntails.refl (P : SepProp) : SatEntails P P :=
  fun _ _ hm => hm

private theorem SatEntails.of_eq {P Q : SepProp} (h : P = Q) : SatEntails P Q :=
  h ▸ SatEntails.refl P

private theorem SatEntails.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntails P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntails.trans {P Q S : SepProp}
    (h1 : SatEntails P Q) (h2 : SatEntails Q S) : SatEntails P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntails.drop_left (P Q : SepProp) : SatEntails (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.drop_right (P Q : SepProp) : SatEntails (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntails P₁ P₂) (h2 : SatEntails Q₁ Q₂) :
    SatEntails (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

private theorem SatEntails.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntails P₁ P₂) {Q : SepProp} : SatEntails (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntails.sepConj_mono h (SatEntails.refl Q)

private theorem SatEntails.sepConj_mono_right {P Q₁ Q₂ : SepProp}
    (h : SatEntails Q₁ Q₂) : SatEntails (P ∗ Q₁) (P ∗ Q₂) :=
  SatEntails.sepConj_mono (SatEntails.refl P) h

private theorem SatEntails.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, SatEntails (P x) Q) : SatEntails (∃∗ x, P x) Q := by
  intro m R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x m R hx

private theorem SatEntails.sepExists_right {α : Type} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : SatEntails P (Q x)) : SatEntails P (∃∗ y, Q y) :=
  SatEntails.trans h (SatEntails.of_entails (Entails.sepExists_right x (Entails.refl _)))

private theorem SepWP.weaken_pre_sat {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntails P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem strRefAt_entails_memRegion16 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntails.sepExists_elim
  intro p
  refine SatEntails.trans (SatEntails.sepConj_mono_right (SatEntails.drop_right _ _)) ?_
  apply SatEntails.of_entails
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) _)

private theorem spe_word8_40_entails_48 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a w)

private theorem spe_u64_at_8_entails_40 (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem spe_u8_at_8_entails_40 (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 := by
    rw [show (40 : Nat) = 1 + 39 from rfl, memRegion_split (a + 8#64) 1 39 (by decide),
        show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) v) (IsBlock.memRegion (a + 8#64) 1)
      fun _ _ => trivial)

private theorem spe_u8_at_32_entails_16 (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  have h : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) v) (IsBlock.memRegion (a + 32#64) 1)
      fun _ _ => trivial)

private theorem spe_u32x2_at_8_entails_40 (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  have h1 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  have h2 : memRegion (a + 12#64) 36 = memRegion (a + 12#64) 4 ∗ memRegion (a + 16#64) 32 := by
    rw [show (36 : Nat) = 4 + 32 from rfl, memRegion_split (a + 12#64) 4 32 (by decide),
        show a + 12#64 + 4#64 = a + 16#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v1) (IsBlock.memRegion (a + 8#64) 4)
      fun _ _ => trivial)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 12#64) v2) (IsBlock.memRegion (a + 12#64) 4)
        fun _ _ => trivial))

private theorem spe_strRef_at_8_entails_40 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    rw [show (40 : Nat) = 16 + 24 from rfl, memRegion_split (a + 8#64) 16 24 (by decide),
        show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  rw [h]
  exact SatEntails.sepConj_mono_left (strRefAt_entails_memRegion16 (a + 8#64) lit)

private theorem spe_str_words_entails_48 (a w cap ptr : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [h1, h2, h3]
  exact sepConj_mono (pointsTo64_entails_memRegion a w)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) cap)
      (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) ptr)))

private theorem spe_str_cap0_pre_weaken (a w cap ptr : BitVec 64) (ro pool rest : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗ rest)
      (memRegion a 48 ∗ pool ∗ rest) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗ rest =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono_left hro)

private theorem spe_noop_pre_weaken (a w : BitVec 64) (ro pool rest : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗ rest)
      (memRegion a 48 ∗ pool ∗ rest) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_word8_40_entails_48 a w)
  have hreord :
      (a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗ rest =
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40) ∗ ((ro ∗ pool) ∗ rest) := by ac_rfl
  rw [hreord]
  exact SatEntails.sepConj_mono ha (SatEntails.sepConj_mono_left hro)

private theorem invalidMessageStrAt_entails_vecU8 (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right tooFarInFutureStr (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right macFailedStr (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem spe_unit_pre_weaken (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (speAt A fnName a e) ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem SepWP.false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

private theorem stackAt_dropSpeX_split (sp : BitVec 64) :
    stackAt sp dropSpeStackX =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = dropSpeStackX from rfl,
      ← stackAt_dropSpeX_split sp]

private theorem cells4_entails_stack_bottomX (sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottomX sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem stack_restore_32_speX (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split sp, ← tail_stack_32_from_bottomX sp]
  exact cells4_entails_stack_bottomX sp fp lr x20 x19

private theorem spe_str_cap0_pre_weaken_fullX (a w cap ptr sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntails.trans (spe_str_cap0_pre_weaken a w cap ptr ro pool _)
    (SatEntails.of_entails
      (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX sp fp lr x20 x19))))

private theorem spe_noop_pre_weaken_fullX (a w sp fp lr x20 x19 : BitVec 64)
    (ro pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro ∗ pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)))
      (memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX) :=
  SatEntails.trans (spe_noop_pre_weaken a w ro pool _)
    (SatEntails.of_entails
      (sepConj_mono_right (sepConj_mono_right (stack_restore_32_speX sp fp lr x20 x19))))

private theorem spe_tail_dealloc_pre_weakenX (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live1 live2 pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
        (live1 ∗ live2)) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottomX sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live1 ∗ live2 ∗ pool ∗ stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) extHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ (live1 ∗ live2))) := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem spe_tail_dealloc_postX (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ memRegion a 48 ∗ memRegion (sp - 16416#64) 32 ⊢
      memRegion a 48 ∗ pool ∗ stackAt sp dropSpeStackX := by
  rw [stackAt_dropSpeX_split sp, ← tail_stack_32_from_bottomX sp]
  exact Entails.of_eq (by ac_rfl)

private theorem vecU8_at_8_exposeX (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hexp : vecU8At A (a + 8#64) cap ptr bs ⊢
      ((a + 8#64) ↦₆₄ cap) ∗ ((a + 8#64 + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 8#64 + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
    refine Entails.trans (vecU8At_entails_dealloc A (a + 8#64) cap ptr bs) ?_
    unfold vecHeader
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases hc : cap = 0
    · simp only [hc, ↓reduceIte]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
      have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
      exact Entails.pure_right hlay (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hexp) ?_
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have hm : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 24#64) 8 16 (by decide),
        show a + 24#64 + 8#64 = a + 32#64 by bv_omega]
  rw [h16, h24, hm]
  exact Entails.of_eq (by ac_rfl)

private theorem speAt_invalidState_exposeX (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro bs
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) fnName))) ?_
  apply SatEntails.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem speAt_invalidMessage_exposeX (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8 A (a + 8#64) r)
      (spe_u8_at_32_entails_16 a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_exposeX A a bs)) ?_
  simp only [sepExists_sepConj_right]
  exact Entails.refl _

private theorem spe_str_pre_weakenX (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (speAt A fnName a e)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else ⌜LayoutOk cap.toNat 1⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

end

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {entry : BitVec 64}
    {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.DropSpeProof.Helpers
