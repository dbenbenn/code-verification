/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import LibsignalBinary.Proofs.CodeLayout

/-!
# `InMemIdentityKeyStore::save_identity::{closure#0}` (`0x077cc`)

Shared separation-logic and SIMD tag-probe lemmas for `InMemIdentityKeyStore::save_identity::{closure#0}`.
-/

public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

namespace SaveIdentity

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff hashAddrBv
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := Arm64.State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) : SepWP prog pc s (∃∗ a, P a) post :=
  HashOne.sepWP_exists_elim h

theorem sepWP_pure_left_elim {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q : SepProp} {post : Arm64.State → SepProp → Prop}
    (h : P → SepWP prog pc s Q post) : SepWP prog pc s (⌜P⌝ ∗ Q) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F) (h : P → SepWP prog pc s F post) : SepWP prog pc s Q post := by
  rw [heq]; exact sepWP_pure_left_elim h

@[arm64_norm, wp_norm]
theorem sp_save_prologue_eqs (sp : BitVec 64) :
    sp + bv% (2 ^ 64 - 240) = sp - 240#64 ∧ sp - 240#64 + 8#64 = sp - 232#64 ∧
    sp - 240#64 + 16#64 = sp - 224#64 ∧ sp - 240#64 + 31#64 = sp - 209#64 ∧
    sp - 240#64 + 64#64 = sp - 176#64 ∧ sp - 240#64 + 88#64 = sp - 152#64 ∧
    sp - 240#64 + 128#64 = sp - 112#64 ∧ sp - 112#64 + 8#64 = sp - 104#64 ∧
    sp - 240#64 + 144#64 = sp - 96#64 ∧ sp - 96#64 + 8#64 = sp - 88#64 ∧
    sp - 240#64 + 144#64 + 8#64 = sp - 88#64 ∧ sp - 240#64 + 160#64 = sp - 80#64 ∧
    sp - 240#64 + 160#64 + 8#64 = sp - 72#64 ∧ sp - 240#64 + 176#64 = sp - 64#64 ∧
    sp - 240#64 + 176#64 + 8#64 = sp - 56#64 ∧ sp - 240#64 + 192#64 = sp - 48#64 ∧
    sp - 240#64 + 192#64 + 8#64 = sp - 40#64 ∧ sp - 240#64 + 208#64 = sp - 32#64 ∧
    sp - 240#64 + 208#64 + 8#64 = sp - 24#64 ∧ sp - 240#64 + 224#64 = sp - 16#64 ∧
    sp - 240#64 + 224#64 + 8#64 = sp - 8#64 ∧ sp - 240#64 + 240#64 = sp ∧
    sp - 96#64 - 48#64 = sp - 144#64 ∧ sp - 96#64 + bv% (2 ^ 64 - 48) = sp - 144#64 ∧
    sp - 144#64 + 8#64 = sp - 136#64 ∧ sp - 144#64 + 16#64 = sp - 128#64 ∧
    sp - 128#64 + 8#64 = sp - 120#64 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega⟩

theorem entails_sepExists_intro {α : Sort _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) := Entails.sepExists_right a h

theorem stackAt_save_eq (sp : BitVec 64) :
    stackAt sp saveIdentityClosureStack =
      memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
      (∃∗ c_sp8 : BitVec 64, ∃∗ c_sp16 : BitVec 64,
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) ∗
      memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
      (∃∗ c_sp88 : BitVec 8, (sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) := by
  simp only [stackAt, saveIdentityClosureStack, HashbrownBin.extHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 800)) (n := 16944) (k := 240) (b' := sp - 240#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 240#64) (n := 8) (k := 232) (b' := sp - 232#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 232#64) (n := 16) (k := 216) (b' := sp - 216#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 216#64) (n := 7) (k := 209) (b' := sp - 209#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 209#64) (n := 33) (k := 176) (b' := sp - 176#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 24) (k := 152) (b' := sp - 152#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 151) (b' := sp - 151#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 151#64) (n := 7) (k := 144) (b' := sp - 144#64) (by decide) (by bv_omega) (by decide)]
  change memRegion (sp - 17184#64) 16944 ∗ (memRegion (sp - 240#64) 8 ∗
    (memRegion (sp - 232#64) (8 * 2) ∗ (memRegion (sp - 216#64) 7 ∗
    (memRegion (sp - 209#64) 33 ∗ (memRegion (sp - 176#64) 24 ∗
    (memRegion (sp - 152#64) 1 ∗ (memRegion (sp - 151#64) 7 ∗
    memRegion (sp - 144#64) (8 * 18)))))))) = _
  rw [memRegion_cells (sp - 232#64) 2 (by decide), memRegion_one (sp - 152#64),
      memRegion_cells (sp - 144#64) 18 (by decide)]
  have hc2 : cells (sp - 232#64) 2 =
      (∃∗ c_sp8 : BitVec 64, ∃∗ c_sp16 : BitVec 64,
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) := by cells_unfold
  have hc18 : cells (sp - 144#64) 18 =
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) := by cells_unfold
  rw [hc2, hc18]

theorem stackAt_save_of_parts (sp : BitVec 64)
    (c_sp8 c_sp16 : BitVec 64) (c_sp88 : BitVec 8)
    (c_sp96 c_sp104 c_sp112 c_sp120 : BitVec 64)
    (c_d9 c_d8 c_x29 c_x30 c_x28 c_x27 c_x26 c_x25 c_x24 c_x23 c_x22 c_x21 c_x20 c_x19 : BitVec 64) :
    (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
      ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16) ∗
      memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
      ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
      ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
      ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
      ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
      ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
      ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
      ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
      ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
      ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
      ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) ⊢
    stackAt sp saveIdentityClosureStack := by
  rw [stackAt_save_eq sp]
  have h2 := entails_sepExists_intro c_sp8 (Q := fun x => ∃∗ c_sp16 : BitVec 64,
    ((sp - 232#64) ↦₆₄ x) ∗ ((sp - 224#64) ↦₆₄ c_sp16))
    (entails_sepExists_intro c_sp16 (Entails.refl _))
  have h1 : ((sp - 152#64) ↦₈ c_sp88) ⊢ (∃∗ c_sp88 : BitVec 8, (sp - 152#64) ↦₈ c_sp88) :=
    entails_sepExists_intro c_sp88 (Entails.refl _)
  have h18 :
      (((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) ⊢
      (∃∗ c_sp96 : BitVec 64, ∃∗ c_sp104 : BitVec 64, ∃∗ c_sp112 : BitVec 64, ∃∗ c_sp120 : BitVec 64,
       ∃∗ c_d9 : BitVec 64, ∃∗ c_d8 : BitVec 64, ∃∗ c_x29 : BitVec 64, ∃∗ c_x30 : BitVec 64,
       ∃∗ c_x28 : BitVec 64, ∃∗ c_x27 : BitVec 64, ∃∗ c_x26 : BitVec 64, ∃∗ c_x25 : BitVec 64,
       ∃∗ c_x24 : BitVec 64, ∃∗ c_x23 : BitVec 64, ∃∗ c_x22 : BitVec 64, ∃∗ c_x21 : BitVec 64,
       ∃∗ c_x20 : BitVec 64, ∃∗ c_x19 : BitVec 64,
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) :=
    entails_sepExists_intro c_sp96 (entails_sepExists_intro c_sp104 (entails_sepExists_intro c_sp112
      (entails_sepExists_intro c_sp120 (entails_sepExists_intro c_d9 (entails_sepExists_intro c_d8
      (entails_sepExists_intro c_x29 (entails_sepExists_intro c_x30 (entails_sepExists_intro c_x28
      (entails_sepExists_intro c_x27 (entails_sepExists_intro c_x26 (entails_sepExists_intro c_x25
      (entails_sepExists_intro c_x24 (entails_sepExists_intro c_x23 (entails_sepExists_intro c_x22
      (entails_sepExists_intro c_x21 (entails_sepExists_intro c_x20 (entails_sepExists_intro c_x19
      (Entails.refl _))))))))))))))))))
  have hgroup :
      (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
        ((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16) ∗
        memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
        ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
        ((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
        ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
        ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
        ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
        ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
        ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
        ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
        ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
        ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19)) =
      (memRegion (sp - 17184#64) 16944 ∗ memRegion (sp - 240#64) 8 ∗
        (((sp - 232#64) ↦₆₄ c_sp8) ∗ ((sp - 224#64) ↦₆₄ c_sp16)) ∗
        memRegion (sp - 216#64) 7 ∗ memRegion (sp - 209#64) 33 ∗ memRegion (sp - 176#64) 24 ∗
        ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 ∗
        (((sp - 144#64) ↦₆₄ c_sp96) ∗ ((sp - 136#64) ↦₆₄ c_sp104) ∗
          ((sp - 128#64) ↦₆₄ c_sp112) ∗ ((sp - 120#64) ↦₆₄ c_sp120) ∗
          ((sp - 112#64) ↦₆₄ c_d9) ∗ ((sp - 104#64) ↦₆₄ c_d8) ∗
          ((sp - 96#64) ↦₆₄ c_x29) ∗ ((sp - 88#64) ↦₆₄ c_x30) ∗
          ((sp - 80#64) ↦₆₄ c_x28) ∗ ((sp - 72#64) ↦₆₄ c_x27) ∗
          ((sp - 64#64) ↦₆₄ c_x26) ∗ ((sp - 56#64) ↦₆₄ c_x25) ∗
          ((sp - 48#64) ↦₆₄ c_x24) ∗ ((sp - 40#64) ↦₆₄ c_x23) ∗
          ((sp - 32#64) ↦₆₄ c_x22) ∗ ((sp - 24#64) ↦₆₄ c_x21) ∗
          ((sp - 16#64) ↦₆₄ c_x20) ∗ ((sp - 8#64) ↦₆₄ c_x19))) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h2
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h1 (sepConj_mono_right h18)))))))

theorem stackAt_save_ext_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 560 ∗ stackAt (sp - 240#64) HashbrownBin.extHookStack := by
  change memRegion (sp - 17184#64) (560 + 16384) =
    memRegion (sp - 17184#64) 560 ∗ memRegion (sp - 240#64 - 16384#64) 16384
  rw [memRegion_split (sp - 17184#64) 560 16384 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 560 = sp - 240#64 - 16384#64 by bv_omega]

theorem stackAt_save_insert_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 16 ∗ stackAt (sp - 240#64) hashMapIdInsertStack := by
  change memRegion (sp - 17184#64) (16 + 16928) =
    memRegion (sp - 17184#64) 16 ∗ memRegion (sp - 240#64 - 16928#64) 16928
  rw [memRegion_split (sp - 17184#64) 16 16928 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 16 = sp - 240#64 - 16928#64 by bv_omega]

theorem stackAt_save_hashOne_eq (sp : BitVec 64) :
    memRegion (sp - 17184#64) 16944 =
      memRegion (sp - 17184#64) 16832 ∗ stackAt (sp - 240#64) hashOneAddrStack := by
  change memRegion (sp - 17184#64) (16832 + 112) =
    memRegion (sp - 17184#64) 16832 ∗ memRegion (sp - 240#64 - 112#64) 112
  rw [memRegion_split (sp - 17184#64) 16832 112 (by decide),
      show sp - 17184#64 + BitVec.ofNat 64 16832 = sp - 240#64 - 112#64 by bv_omega]

theorem sret48_save_split_eq (sret : BitVec 64) :
    memRegion sret 48 =
      (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) ∗
      (∃∗ s_8 : BitVec 32, (sret + 8#64) ↦₃₂ s_8) ∗
      memRegion (sret + 12#64) 36 := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 8) (k := 40) (b' := sret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sret + 8#64) (n := 4) (k := 36) (b' := sret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight sret,
      ProofLib.memRegion_four (sret + 8#64)]

theorem pollIdentityChangeResultAt_of_parts (sret : BitVec 64) (replaced : Bool) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ (if replaced then 1#32 else 0#32)) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret replaced := Entails.refl _

theorem protocolAddressAt_eq_vecGhostAt_parts (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) :
    protocolAddressAt A g addr =
      vecGhostAt A g.name addr ∗ ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7 := rfl

theorem vecU8_and_dev_entails_protocolAddressAt_save (A : RustAlloc) (sp : BitVec 64)
    (bs : List (BitVec 8)) (dev : BitVec 8) :
    (vecU8 A (sp - 176#64) bs ∗ ((sp - 152#64) ↦₈ dev) ∗ memRegion (sp - 151#64) 7) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        protocolAddressAt A ⟨⟨cap, ptr, bs⟩, dev⟩ (sp - 176#64) := by
  unfold vecU8; simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e24 : sp - 176#64 + 24#64 = sp - 152#64 := by bv_omega
  have e25 : sp - 176#64 + 25#64 = sp - 151#64 := by bv_omega
  unfold protocolAddressAt vecGhostAt; rw [e24, e25]; exact Entails.of_eq (by ac_rfl)

theorem slot64_restore_parts (sp : BitVec 64) :
    memRegion (sp - 176#64) 32 ⊢
      ∃∗ c_sp88 : BitVec 8,
        memRegion (sp - 176#64) 24 ∗ ((sp - 152#64) ↦₈ c_sp88) ∗ memRegion (sp - 151#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 24) (k := 8) (b' := sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 7) (b' := sp - 151#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 152#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.of_eq (by ac_rfl)

theorem optIdentityKeyAt_none_entails_memRegion33 (a : BitVec 64) :
    optIdentityKeyAt a none ⊢ memRegion a 33 := by
  unfold optIdentityKeyAt; rw [show (33 : Nat) = 1 + 32 from rfl, memRegion_split a 1 32 (by decide)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion a 0#8)

theorem optIdentityKeyAt_some_entails_memRegion33 (a : BitVec 64) (bs : List (BitVec 8)) :
    optIdentityKeyAt a (some bs) ⊢ memRegion a 33 := by
  unfold optIdentityKeyAt; apply Entails.pure_left; intro hlen
  rw [show (33 : Nat) = 1 + 32 from rfl, memRegion_split a 1 32 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion a 1#8)
    (hlen ▸ pointsToBytes_entails_memRegion (a + 1#64) bs)

theorem pointsToBytes_32_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ loadGroupAt bs 0) ∗ ((a + 8#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((a + 16#64) ↦₆₄ loadGroupAt bs 16) ∗ ((a + 24#64) ↦₆₄ loadGroupAt bs 24) := by
  have h0 : 0 + 8 ≤ bs.length := by omega
  have h8 : 8 + 8 ≤ bs.length := by omega
  have h16 : 16 + 8 ≤ bs.length := by omega
  have h24 : 24 + 8 ≤ bs.length := by omega
  rw [pointsToBytes_take_drop a 8 bs (by omega),
      pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by simp [List.length_drop, hlen]), List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 (bs.drop 16) (by simp [List.length_drop, hlen]), List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64 + 8#64) 8 (bs.drop 24) (by simp [List.length_drop, hlen]), List.drop_drop]
  have hdrop32 : bs.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
  have h0_eq := pointsToBytes_take8_eq_pointsTo64 a bs 0 h0
  simp only [List.drop_zero] at h0_eq
  have h8_eq := pointsToBytes_take8_eq_pointsTo64 (a + 8#64) bs 8 h8
  have h16_eq := pointsToBytes_take8_eq_pointsTo64 (a + 16#64) bs 16 h16
  have h24_eq := pointsToBytes_take8_eq_pointsTo64 (a + 24#64) bs 24 h24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  simp only [Nat.reduceAdd, ha16, ha24, hdrop32, pointsToBytes_nil, sepConj_emp]
  rw [h0_eq, h8_eq, h16_eq, h24_eq, ← loadGroupAt_eq_pack64 bs 0 h0,
      ← loadGroupAt_eq_pack64 bs 8 h8, ← loadGroupAt_eq_pack64 bs 16 h16,
      ← loadGroupAt_eq_pack64 bs 24 h24]

theorem slot96_32_eq_bytes (sp : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (((sp - 144#64) ↦₆₄ loadGroupAt bs 0) ∗ ((sp - 136#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((sp - 128#64) ↦₆₄ loadGroupAt bs 16) ∗ ((sp - 120#64) ↦₆₄ loadGroupAt bs 24)) =
    ((sp - 144#64) ↦ₛ bs) := by
  rw [pointsToBytes_32_eq_cells (sp - 144#64) bs hlen]
  have e1 : sp - 144#64 + 8#64 = sp - 136#64 := by bv_omega
  have e2 : sp - 144#64 + 16#64 = sp - 128#64 := by bv_omega
  have e3 : sp - 144#64 + 24#64 = sp - 120#64 := by bv_omega
  rw [e1, e2, e3]

@[arm64_norm, wp_norm]
theorem extractLsb'_0_64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  ext i hi_lt; simp

@[arm64_norm, wp_norm]
theorem extractLsb'_64_64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  ext i hi_lt; simp

theorem trace_eq_of_eq {s0 s sf : Arm64.State} (hs : s.trace = s0.trace)
    (h : allocFailedIn s sf ∧ s.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rw [← hs]; exact h

theorem wpp_call_stringClone_save {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (p out sp' : BitVec 64) (g : VecGhost)
    (hcall : subroutine_ok prog entry (stringCloneSpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p) (hx8 : s.readReg64 .x8 = out)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' extHookStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog ret sf
        (vecGhostAt A g p ∗ vecU8 A out g.bytes ∗ A.pool ∗ stackAt sp' extHookStack ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := (p, out, g))
    (φ := s.readReg64 .x0 = p ∧ s.readReg64 .x8 = out)
    (T := vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' extHookStack)
    hcall hpc hrun hsp hlr (by dsimp only [stringCloneSpec]; rw [hsp_eq]) ⟨hx0, hx8⟩ hP
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq htr) hm)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [stringCloneSpec]; rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  conv => arg 4; simp only [sepConj_assoc]
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf (htr_f.trans htr)

theorem step_ldpSimd64_sp' {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true) (hea : s.sp + off = ea) (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1) (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64)) = s')
    (hnext : SepWP prog target_pc s' P post) : SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 hexec hnext

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem pc_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem status_setMem_pre (s : Arm64.State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_pre (s : Arm64.State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem spAligned_setMem_pre (s : Arm64.State) (m : Memory) :
    (s.setMem m).spAligned = s.spAligned := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem spAligned_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).spAligned = s.spAligned := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setMem_pre (s : Arm64.State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg64_pre (s : Arm64.State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeReg32_pre (s : Arm64.State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_writeVReg128_pre (s : Arm64.State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓]
theorem trace_setPState_pre (s : Arm64.State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl

theorem pollIdentityChangeResultAt_false_of_parts (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ 0#32) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret false := Entails.refl _

theorem pollIdentityChangeResultAt_true_of_parts (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₃₂ 1#32) ∗
      memRegion (sret + 12#64) 36) ⊢ pollIdentityChangeResultAt sret true := Entails.refl _

theorem sepWPp_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post postP : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWPp prog pc s F post postP) :
    SepWPp prog pc s Q post postP := by
  rw [heq]
  exact SepWPp.pure_elim h

theorem stackAt_save_ext_restore (sp sp' : BitVec 64)
    (h : sp' = bv% (2 ^ 64 - 240) + sp) :
    memRegion (sp - 17184#64) 560 ∗ stackAt sp' extHookStack ⊢
      memRegion (sp - 17184#64) 16944 := by
  have hsp : sp' = sp - 240#64 := by rw [h]; bv_omega
  rw [hsp, ← stackAt_save_ext_eq sp]
  exact Entails.refl _

theorem stackAt_save_insert_restore (sp sp' : BitVec 64)
    (h : sp' = sp - 240#64) :
    memRegion (sp - 17184#64) 16 ∗ stackAt sp' hashMapIdInsertStack ⊢
      memRegion (sp - 17184#64) 16944 := by
  rw [h, ← stackAt_save_insert_eq sp]
  exact Entails.refl _

theorem table4SingleAt_eq (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) :
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt =
      ⌜k < 4⌝ ∗
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          ([k].length = 4 → 2#64 = 0#64) ∧
          CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
          FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]⌝ ∗
        (mp ↦₆₄ ctrl) ∗ ((mp + 8#64) ↦₆₄ 3#64) ∗ ((mp + 16#64) ↦₆₄ 2#64) ∗ ((mp + 24#64) ↦₆₄ 1#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
        (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
        arrayAt
          (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
          (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [table4SingleAt, table4At]
  simp only [hadd]
  rfl

theorem table4SingleAt_of_parts (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) (ctrl : BitVec 64)
    (hctrl : ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      ([k].length = 4 → 2#64 = 0#64) ∧
      CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
      FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]) :
    ((mp ↦₆₄ ctrl) ∗ ((mp + 8#64) ↦₆₄ 3#64) ∗ ((mp + 16#64) ↦₆₄ 2#64) ∗ ((mp + 24#64) ↦₆₄ 1#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
      (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
      arrayAt
        (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ⊢
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt := by
  rw [table4SingleAt_eq]
  apply Entails.pure_right hk
  refine entails_sepExists_intro ctrl ?_
  exact Entails.pure_right hctrl (Entails.refl _)

@[expose] def addrRestAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (addr ↦₆₄ g.name.cap) ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length) ∗
  memRegion (addr + 25#64) 7

theorem protocolAddressAt_eq_of_len36 (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g addr =
      ((addr + 8#64) ↦₆₄ g.name.ptr) ∗ ((addr + 16#64) ↦₆₄ 36#64) ∗
      ((addr + 24#64) ↦₈ g.device) ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
      addrRestAt A g addr := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗ ((addr + 16#64) ↦₆₄ 36#64) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗ (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte, hlen36] at hlen ⊢
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      exact Entails.of_eq (by ac_rfl)
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗ (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte, hlen36]
      exact Entails.of_eq (by ac_rfl)
    exact ProofLib.sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrRestAt
  rw [hvec]
  ac_rfl

theorem sub_shl6_eq_bucketAddr_add_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - (BitVec.ofNat 64 k <<< 6) = bucketAddr ctrl 64 k + 64#64 := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

theorem bucketArray_save_eq (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (peerKeyBytes : List (BitVec 8))
    (hk : k < 4) (hlen_name : peerG.name.bytes.length = 36) (hlen_key : peerKeyBytes.length = 32) :
    arrayAt
      (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a identityBucketStride)
      identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
    ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ peerG.name.ptr) ∗
    ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 k + 24#64) ↦₈ peerG.device) ∗
    (peerG.name.ptr ↦ₛ peerG.name.bytes) ∗
    ((bucketAddr ctrl 64 k + 32#64) ↦ₛ peerKeyBytes) ∗
    addrRestAt A peerG (bucketAddr ctrl 64 k) ∗
    singleBucketRestAt 64 ctrl k := by
  change arrayAt
    (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a 64)
    64 (ctrl - BitVec.ofNat 64 (4 * 64)) (List.range 4).reverse = _
  rw [arrayAt_single_split_64 ctrl k hk (identityBucketEntryAt A peerG peerKeyBytes)]
  unfold identityBucketEntryAt
  rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 64 k) hlen_name]
  simp only [hlen_key, pure_true, emp_sepConj]
  ac_rfl

private theorem stackAt_extHookStack_split_publicKeyEq (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 16320 ∗ memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 := by
  simp only [stackAt, HashbrownBin.extHookStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64, show BitVec.ofNat 64 (2 ^ 14) = 16384#64 from rfl, show (2 ^ 14 : Nat) = 16384 from rfl,
      ProofLib.memRegion_split' (b := sp - 16384#64) (n := 16320) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16) (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  ac_rfl

structure PublicKeyEqSliceCall where
  p1 : BitVec 64
  bs1 : List (BitVec 8)
  p2 : BitVec 64
  bs2 : List (BitVec 8)
  sp : BitVec 64

@[expose] def publicKeyEqSliceSpec : Spec PublicKeyEqSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p1 ∧ s.readReg64 .x1 = x.p2 ∧ s.sp = x.sp ∧
      x.bs1.length = 32 ∧ x.bs2.length = 32⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗ stackAt x.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = (if x.bs1 = x.bs2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗ stackAt x.sp extHookStack

private theorem zext128_shr_and_255_eq_groupByte (w : BitVec 64) (i : Nat) :
    BitVec.zeroExtend 128 w >>> (i * 8) &&& 255#128 = (groupByte w i).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hw : w.toNat < 2 ^ 64 := w.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, groupByte, BitVec.toNat_setWidth]
  change ((w.toNat % 2 ^ 128) >>> (i * 8)) &&& (2 ^ 8 - 1) = ((w.toNat >>> (8 * i)) % 256) % 2 ^ 128
  have hmod1 : w.toNat % 2 ^ 128 = w.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (w.toNat >>> (8 * i)) % 256 % 2 ^ 128 = (w.toNat >>> (8 * i)) % 256 := Nat.mod_eq_of_lt (by omega)
  rw [hmod1, hmod2, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm i 8]

private theorem zext128_shr57_and_255_eq_h2Tag (h : BitVec 64) :
    BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 = (h2Tag h).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hh : (h >>> 57).toNat < 128 := by rw [BitVec.toNat_ushiftRight]; have := h.isLt; omega
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, h2Tag, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth]
  change ((h >>> 57).toNat % 2 ^ 128) &&& (2 ^ 8 - 1) = (((h >>> 57).toNat % 256) &&& (2 ^ 7 - 1)) % 2 ^ 128
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]; omega

private abbrev dupTag128 (qtag : BitVec 8) : BitVec 128 :=
  0#128 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 0 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 8 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 16 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 24 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 32 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 40 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 48 ||| (qtag.zeroExtend 128 &&& 255#128) <<< 56

private theorem dupTag128_lane_0 (qtag : BitVec 8) : dupTag128 qtag >>> 0 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_8 (qtag : BitVec 8) : dupTag128 qtag >>> 8 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_16 (qtag : BitVec 8) : dupTag128 qtag >>> 16 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_24 (qtag : BitVec 8) : dupTag128 qtag >>> 24 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_32 (qtag : BitVec 8) : dupTag128 qtag >>> 32 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_40 (qtag : BitVec 8) : dupTag128 qtag >>> 40 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_48 (qtag : BitVec 8) : dupTag128 qtag >>> 48 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_56 (qtag : BitVec 8) : dupTag128 qtag >>> 56 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel

private theorem beq_zext128_eq (a b : BitVec 8) :
    (a.zeroExtend 128 == b.zeroExtend 128) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : a.zeroExtend 128 ≠ b.zeroExtend 128 := by
      intro heq; apply h; apply BitVec.eq_of_toNat_eq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hnat
      have := a.isLt; have := b.isLt; omega
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

private theorem truncate64_or (x y : BitVec 128) :
    BitVec.truncate 64 (x ||| y) = BitVec.truncate 64 x ||| BitVec.truncate 64 y := BitVec.setWidth_or

private theorem truncate64_cmeq_0 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 0) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 := by cases c <;> rfl
private theorem truncate64_cmeq_8 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 8) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 8 := by cases c <;> rfl
private theorem truncate64_cmeq_16 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 16) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 16 := by cases c <;> rfl
private theorem truncate64_cmeq_24 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 24) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 24 := by cases c <;> rfl
private theorem truncate64_cmeq_32 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 32) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 32 := by cases c <;> rfl
private theorem truncate64_cmeq_40 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 40) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 40 := by cases c <;> rfl
private theorem truncate64_cmeq_48 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 48) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 48 := by cases c <;> rfl
private theorem truncate64_cmeq_56 (c : Bool) : BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 56) = (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 56 := by cases c <;> rfl

theorem rawMatchTagMask_eq_findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (h : BitVec 64) :
    BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 0 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 8 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 16 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 24 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 32 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 40 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 48 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 56 &&& 255#128 == (0#128 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 ||| (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h) := by
  rw [zext128_shr57_and_255_eq_h2Tag h]
  change BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (0 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 0 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (1 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 8 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (2 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 16 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (3 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 24 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (4 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 32 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (5 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 40 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (6 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 48 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (7 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 56 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h)
  rw [zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 0,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 1,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 2,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 3,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 4,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 5,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 6,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 7,
      dupTag128_lane_0, dupTag128_lane_8, dupTag128_lane_16, dupTag128_lane_24,
      dupTag128_lane_32, dupTag128_lane_40, dupTag128_lane_48, dupTag128_lane_56]
  simp only [beq_zext128_eq, truncate64_or,
    truncate64_cmeq_0, truncate64_cmeq_8, truncate64_cmeq_16, truncate64_cmeq_24,
    truncate64_cmeq_32, truncate64_cmeq_40, truncate64_cmeq_48, truncate64_cmeq_56,
    BitVec.zero_or]
  rfl

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3) &&& 3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> decide +kernel

theorem laneBit_laneOfBucket4_ne_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) ≠ 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> decide +kernel

theorem findGroupIterMask_singleCtrl4_eq_zero_imp_ne
    (k0 k1 : BitVec 64) (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask0 : findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    ¬(qName = peerName ∧ qDev = peerDev) := by
  rintro ⟨rfl, rfl⟩
  have hpos : (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 qName qDev)
  rw [findGroupIterMask_singleCtrl4 k _ hk hpos] at hmask0
  simp only [beq_self_eq_true, ↓reduceIte] at hmask0
  exact laneBit_laneOfBucket4_ne_zero k _ hk hpos hmask0

theorem findGroupIterMask_singleCtrl4_ne_zero_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne : ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = laneBit (laneOfBucket4 pos k) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne ⊢
  split at hmask_ne
  · rename_i heq; simp [heq]
  · exfalso; exact hmask_ne rfl

theorem ne_of_cbnz_bcmp {w : BitVec 32} {P Q : Prop}
    (hiff : (w = 0#32) ↔ P) (hcbnz : ¬BitVec.zeroExtend 64 w = 0#64) : ¬(P ∧ Q) := by
  intro ⟨hp, _⟩; apply hcbnz; have hw : w = 0#32 := hiff.mpr hp; subst hw; rfl

theorem dev_ne_of_not_zeroExtend {P : Prop} {d1 d2 : BitVec 8}
    (h : ¬BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) : ¬(P ∧ d1 = d2) := by
  rintro ⟨_, rfl⟩; exact h rfl

end SaveIdentity

end CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
