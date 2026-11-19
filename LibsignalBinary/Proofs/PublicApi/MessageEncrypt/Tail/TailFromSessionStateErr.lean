/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# MessageEncrypt T1 from-error (`+0x49c..+0x564`, `tailFromSessionStateErr_ok`) proof
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem satisfies_memRegion_1 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 1 ∗ R) :
    ∃ b : BitVec 8, m ⊨ (a ↦₈ b) ∗ R := by
  rw [ProofLib.memRegion_one, sepExists_sepConj_left, satisfies_sepExists] at h
  exact h

theorem satisfies_memRegion_24 {m : Memory} {a : BitVec 64} {R : SepProp}
    (h : m ⊨ memRegion a 24 ∗ R) :
    ∃ u0 u1 u2 : BitVec 64,
      m ⊨ ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2)) ∗ R := by
  rw [memRegion_24_eq_exists_vecHeader, sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u0, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u1, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u2, h⟩
  exact ⟨u0, u1, u2, h⟩

@[expose] def pollFromRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 0x11e ∗
    memRegion (sp + 0x5b8#64) 0x298 ∗
    memRegion (sp + 0x868#64) 0x168 ∗
    memRegion (sp + 0x9e8#64) 0xc8 ∗
    memRegion (sp + 0xae0#64) 0xa0

theorem pollWith_588_split (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] =
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
      memRegion (sp + 0x850#64) 24 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      memRegion (sp + 0xab0#64) 24 ∗
      memRegion (sp + 0xac8#64) 24 ∗
      pollFromRest sp := by
  unfold pollWith pollFromRest
  dsimp only [List.length_cons, List.length_nil]
  have h_off : sp + BitVec.ofNat 64 0x588 = sp + 0x588#64 := rfl
  have h_end : sp + BitVec.ofNat 64 (0x588 + 8 * 6) = sp + 0x5b8#64 := by bv_omega
  have h_words :
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] =
        ((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) := by
    dsimp only [words64At]
    have h1 : sp + 0x588#64 + 8#64 = sp + 0x590#64 := by bv_omega
    have h2 : sp + 0x590#64 + 8#64 = sp + 0x598#64 := by bv_omega
    have h3 : sp + 0x598#64 + 8#64 = sp + 0x5a0#64 := by bv_omega
    have h4 : sp + 0x5a0#64 + 8#64 = sp + 0x5a8#64 := by bv_omega
    have h5 : sp + 0x5a8#64 + 8#64 = sp + 0x5b0#64 := by bv_omega
    rw [h1, h2, h3, h4, h5, sepConj_emp]
  have h_split :
      memRegion (sp + 0x5b8#64) (0xb80 - (0x588 + 8 * 6)) =
        memRegion (sp + 0x5b8#64) 0x298 ∗
          (memRegion (sp + 0x850#64) 24 ∗
            (memRegion (sp + 0x868#64) 0x168 ∗
              (memRegion (sp + 0x9d0#64) 24 ∗
                (memRegion (sp + 0x9e8#64) 0xc8 ∗
                  (memRegion (sp + 0xab0#64) 24 ∗
                    (memRegion (sp + 0xac8#64) 24 ∗
                      memRegion (sp + 0xae0#64) 0xa0)))))) := by
    rw [memRegion_split' (b := sp + 0x5b8#64) (b' := sp + 0x850#64) (N := 0x5c8) (n := 0x298) (k := 0x330)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x850#64) (b' := sp + 0x868#64) (N := 0x330) (n := 24) (k := 0x318)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x868#64) (b' := sp + 0x9d0#64) (N := 0x318) (n := 0x168) (k := 0x1b0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0x9e8#64) (N := 0x1b0) (n := 24) (k := 0x198)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9e8#64) (b' := sp + 0xab0#64) (N := 0x198) (n := 0xc8) (k := 0xd0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xab0#64) (b' := sp + 0xac8#64) (N := 0xd0) (n := 24) (k := 0xb8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xac8#64) (b' := sp + 0xae0#64) (N := 0xb8) (n := 24) (k := 0xa0)
          (by decide) (by bv_omega) (by decide)]
  rw [h_off, h_end, h_words, h_split]
  ac_rfl

theorem pollWith_588_mem_elim {m : Memory} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {R : SepProp}
    (h : m ⊨ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ (logA ↦₆₄ 0#64) ∗ R) :
    ∃ u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64,
      m ⊨ (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R) := by
  rw [pollWith_588_split sp w0 w1 w2 w3 w4 w5] at h
  let W6 := ((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
    ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
    ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)
  have h1 : m ⊨ memRegion (sp + 0x850#64) 24 ∗
      (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
        memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        ((W6 ∗ memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x9d0#64) 24 ∗
          memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗ pollFromRest sp) ∗
         (logA ↦₆₄ 0#64) ∗ R) =
        (memRegion (sp + 0x850#64) 24 ∗
         (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
          memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, h1'⟩ := satisfies_memRegion_24 h1
  have h858_eq : sp + 0x850#64 + 8#64 = sp + 0x858#64 := by bv_omega
  have h860_eq : sp + 0x850#64 + 16#64 = sp + 0x860#64 := by bv_omega
  rw [h858_eq, h860_eq] at h1'
  let U850 := ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860)
  have h2 : m ⊨ memRegion (sp + 0x9d0#64) 24 ∗
      (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
        U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (U850 ∗ (memRegion (sp + 0x9d0#64) 24 ∗ memRegion (sp + 0xab0#64) 24 ∗
          memRegion (sp + 0xac8#64) 24 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0x9d0#64) 24 ∗
         (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
          U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨u9d0, u9d8, u9e0, h2'⟩ := satisfies_memRegion_24 h2
  have h9d8_eq : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
  have h9e0_eq : sp + 0x9d0#64 + 16#64 = sp + 0x9e0#64 := by bv_omega
  rw [h9d8_eq, h9e0_eq] at h2'
  let U9d0 := ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗ ((sp + 0x9e0#64) ↦₆₄ u9e0)
  have h3 : m ⊨ memRegion (sp + 0xab0#64) 24 ∗
      (memRegion (sp + 0xac8#64) 24 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (U9d0 ∗ (memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
          U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0xab0#64) 24 ∗
         (memRegion (sp + 0xac8#64) 24 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨uab0, uab8, uac0, h3'⟩ := satisfies_memRegion_24 h3
  have hab8_eq : sp + 0xab0#64 + 8#64 = sp + 0xab8#64 := by bv_omega
  have hac0_eq : sp + 0xab0#64 + 16#64 = sp + 0xac0#64 := by bv_omega
  rw [hab8_eq, hac0_eq] at h3'
  let Uab0 := ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗ ((sp + 0xac0#64) ↦₆₄ uac0)
  have h4 : m ⊨ memRegion (sp + 0xac8#64) 24 ∗
      (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R) := by
    have heq :
        (Uab0 ∗ (memRegion (sp + 0xac8#64) 24 ∗
          U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
        (memRegion (sp + 0xac8#64) 24 ∗
         (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨uac8, uad0, uad8, h4'⟩ := satisfies_memRegion_24 h4
  have had0_eq : sp + 0xac8#64 + 8#64 = sp + 0xad0#64 := by bv_omega
  have had8_eq : sp + 0xac8#64 + 16#64 = sp + 0xad8#64 := by bv_omega
  rw [had0_eq, had8_eq] at h4'
  refine ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, ?_⟩
  have heq :
      ((((sp + 0xac8#64) ↦₆₄ uac8) ∗ ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8)) ∗
       (Uab0 ∗ U9d0 ∗ U850 ∗ W6 ∗ (logA ↦₆₄ 0#64) ∗ pollFromRest sp ∗ R)) =
      ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) := by
    dsimp only [W6, U850, U9d0, Uab0]
    ac_rfl
  rwa [← heq]

theorem words3_weaken_memRegion24 (a b c : BitVec 64) (w0 w1 w2 : BitVec 64)
    (hb : a + 8#64 = b) (hc : a + 16#64 = c) :
    (a ↦₆₄ w0) ∗ (b ↦₆₄ w1) ∗ (c ↦₆₄ w2) ⊢ memRegion a 24 := by
  subst hb hc
  exact vecHeader_entails_memRegion a w0 w1 w2

theorem pollFrom_post_weaken (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
      (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
      (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
      (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
      (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
      (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
      pollFromRest sp ⊢
    pollWith sp 0x9d0 [w3, w4, w5] := by
  have hw1 := words3_weaken_memRegion24 (sp + 0x588#64) (sp + 0x590#64) (sp + 0x598#64)
    w0 w1 w2 (by bv_omega) (by bv_omega)
  have hw2 := words3_weaken_memRegion24 (sp + 0x5a0#64) (sp + 0x5a8#64) (sp + 0x5b0#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  have hw3 := words3_weaken_memRegion24 (sp + 0x850#64) (sp + 0x858#64) (sp + 0x860#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  have hw4 := words3_weaken_memRegion24 (sp + 0xab0#64) (sp + 0xab8#64) (sp + 0xac0#64)
    w0 w1 w2 (by bv_omega) (by bv_omega)
  have hw5 := words3_weaken_memRegion24 (sp + 0xac8#64) (sp + 0xad0#64) (sp + 0xad8#64)
    w3 w4 w5 (by bv_omega) (by bv_omega)
  refine Entails.trans
    (sepConj_mono hw1 (sepConj_mono hw2 (sepConj_mono hw3
      (sepConj_mono_right (sepConj_mono hw4 (sepConj_mono_left hw5)))))) ?_
  unfold pollWith pollFromRest
  dsimp only [List.length_cons, List.length_nil]
  have h_off : sp + BitVec.ofNat 64 0x9d0 = sp + 0x9d0#64 := rfl
  have h_end : sp + BitVec.ofNat 64 (0x9d0 + 8 * 3) = sp + 0x9e8#64 := by bv_omega
  have h_words :
      words64At (sp + 0x9d0#64) [w3, w4, w5] =
        ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5) := by
    dsimp only [words64At]
    have h1 : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
    have h2 : sp + 0x9d8#64 + 8#64 = sp + 0x9e0#64 := by bv_omega
    rw [h1, h2, sepConj_emp]
  have h_pre :
      memRegion (sp + 0x46a#64) (0x9d0 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x11e ∗
          (memRegion (sp + 0x588#64) 24 ∗
            (memRegion (sp + 0x5a0#64) 24 ∗
              (memRegion (sp + 0x5b8#64) 0x298 ∗
                (memRegion (sp + 0x850#64) 24 ∗
                  memRegion (sp + 0x868#64) 0x168)))) := by
    rw [memRegion_split' (b := sp + 0x46a#64) (b' := sp + 0x588#64) (N := 0x566) (n := 0x11e) (k := 0x448)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x588#64) (b' := sp + 0x5a0#64) (N := 0x448) (n := 24) (k := 0x430)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x5a0#64) (b' := sp + 0x5b8#64) (N := 0x430) (n := 24) (k := 0x418)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x5b8#64) (b' := sp + 0x850#64) (N := 0x418) (n := 0x298) (k := 0x180)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x850#64) (b' := sp + 0x868#64) (N := 0x180) (n := 24) (k := 0x168)
          (by decide) (by bv_omega) (by decide)]
  have h_post :
      memRegion (sp + 0x9e8#64) (0xb80 - (0x9d0 + 8 * 3)) =
        memRegion (sp + 0x9e8#64) 0xc8 ∗
          (memRegion (sp + 0xab0#64) 24 ∗
            (memRegion (sp + 0xac8#64) 24 ∗
              memRegion (sp + 0xae0#64) 0xa0)) := by
    rw [memRegion_split' (b := sp + 0x9e8#64) (b' := sp + 0xab0#64) (N := 0x198) (n := 0xc8) (k := 0xd0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xab0#64) (b' := sp + 0xac8#64) (N := 0xd0) (n := 24) (k := 0xb8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0xac8#64) (b' := sp + 0xae0#64) (N := 0xb8) (n := 24) (k := 0xa0)
          (by decide) (by bv_omega) (by decide)]
  rw [h_off, h_end, h_words, h_pre, h_post]
  have heq :
      (memRegion (sp + 0x588#64) 24 ∗ memRegion (sp + 0x5a0#64) 24 ∗
        memRegion (sp + 0x850#64) 24 ∗
        (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
        memRegion (sp + 0xab0#64) 24 ∗ memRegion (sp + 0xac8#64) 24 ∗
        (memRegion (sp + 0x46a#64) 0x11e ∗ memRegion (sp + 0x5b8#64) 0x298 ∗
          memRegion (sp + 0x868#64) 0x168 ∗ memRegion (sp + 0x9e8#64) 0xc8 ∗
          memRegion (sp + 0xae0#64) 0xa0)) =
      ((memRegion (sp + 0x46a#64) 0x11e ∗
        (memRegion (sp + 0x588#64) 24 ∗
          (memRegion (sp + 0x5a0#64) 24 ∗
            (memRegion (sp + 0x5b8#64) 0x298 ∗
              (memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x868#64) 0x168))))) ∗
       (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
       (memRegion (sp + 0x9e8#64) 0xc8 ∗
         (memRegion (sp + 0xab0#64) 24 ∗
           (memRegion (sp + 0xac8#64) 24 ∗ memRegion (sp + 0xae0#64) 0xa0)))) := by ac_rfl
  rw [heq]
  exact Entails.refl _

theorem pollFrom_post_mem_weaken {m : Memory} {sp logA : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {R : SepProp}
    (h : m ⊨ (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
        ((sp + 0x860#64) ↦₆₄ w5) ∗
        ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
        ((sp + 0x9e0#64) ↦₆₄ w5) ∗
        ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
        ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
        ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
        (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) :
    m ⊨ pollWith sp 0x9d0 [w3, w4, w5] ∗ (logA ↦₆₄ 0#64) ∗ R := by
  have h1 : m ⊨
      ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
        (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
        (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
        (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
        (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
        (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
        pollFromRest sp) ∗ ((logA ↦₆₄ 0#64) ∗ R) := by
    have heq :
        ((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (logA ↦₆₄ 0#64)) ∗ (pollFromRest sp ∗ R)) =
        (((((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗ ((sp + 0x598#64) ↦₆₄ w2)) ∗
          (((sp + 0x5a0#64) ↦₆₄ w3) ∗ ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5)) ∗
          (((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗ ((sp + 0x860#64) ↦₆₄ w5)) ∗
          (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
          (((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗ ((sp + 0xac0#64) ↦₆₄ w2)) ∗
          (((sp + 0xac8#64) ↦₆₄ w3) ∗ ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5)) ∗
          pollFromRest sp) ∗ ((logA ↦₆₄ 0#64) ∗ R)) := by ac_rfl
    rwa [← heq]
  exact Satisfies.mono (sepConj_mono_left (pollFrom_post_weaken sp w0 w1 w2 w3 w4 w5)) h1

@[expose] def encCommonRest (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
    tapeAfter ctl x.cur x.rest draws ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr
