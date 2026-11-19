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
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem memRegion_eq_exists_words64At :
    ∀ (n : Nat) (a : BitVec 64), 8 * n ≤ 2 ^ 64 →
      (∀ m R, (m ⊨ memRegion a (8 * n) ∗ R) →
        ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ R))
  | 0, a, _, m, R, hm => by
    rw [Nat.mul_zero, ProofLib.memRegion_zero] at hm
    exact ⟨[], rfl, hm⟩
  | n + 1, a, hbound, m, R, hm => by
    have hsplit : memRegion a (8 * (n + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * n) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]
      exact memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8 * n) rfl rfl (by omega)
    rw [hsplit, ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists] at hm
    obtain ⟨w, hm⟩ := hm
    rw [sepConj_comm (a ↦₆₄ w), sepConj_assoc] at hm
    obtain ⟨ws, hlen, hm⟩ :=
      memRegion_eq_exists_words64At n (a + 8#64) (by omega) m (R ∗ (a ↦₆₄ w)) hm
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    rw [words64At, sepConj_assoc]
    rw [← sepConj_assoc (words64At (a + 8#64) ws), sepConj_comm _ (a ↦₆₄ w)] at hm
    exact hm

theorem words64At_drop_succ {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : i < ws.length) :
    words64At a (ws.drop i) =
      (a ↦₆₄ ws.getD i 0#64) ∗ words64At (a + 8#64) (ws.drop (i + 1)) := by
  induction i generalizing a ws with
  | zero =>
    cases ws with
    | nil => simp at h
    | cons w ws' => rfl
  | succ i ih =>
    cases ws with
    | nil => simp at h
    | cons w ws' =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      exact ih h

theorem words64At_drop_eq_emp {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : ws.length ≤ i) :
    words64At a (ws.drop i) = emp := by
  rw [List.drop_eq_nil_of_le h, words64At]

theorem words64At_4 (a : BitVec 64) {ws : List (BitVec 64)} (h : ws.length = 4) :
    words64At a ws =
      (a ↦₆₄ ws.getD 0 0#64) ∗ ((a + 0x08#64) ↦₆₄ ws.getD 1 0#64) ∗
      ((a + 0x10#64) ↦₆₄ ws.getD 2 0#64) ∗ ((a + 0x18#64) ↦₆₄ ws.getD 3 0#64) := by
  conv => lhs; rw [← @List.drop_zero _ ws]
  repeat rw [words64At_drop_succ (by omega)]
  rw [words64At_drop_eq_emp (by omega)]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem words64At_27 (a : BitVec 64) {ws : List (BitVec 64)} (h : ws.length = 27) :
    words64At a ws =
      (a ↦₆₄ ws.getD 0 0#64) ∗ ((a + 0x08#64) ↦₆₄ ws.getD 1 0#64) ∗
      ((a + 0x10#64) ↦₆₄ ws.getD 2 0#64) ∗ ((a + 0x18#64) ↦₆₄ ws.getD 3 0#64) ∗
      ((a + 0x20#64) ↦₆₄ ws.getD 4 0#64) ∗ ((a + 0x28#64) ↦₆₄ ws.getD 5 0#64) ∗
      ((a + 0x30#64) ↦₆₄ ws.getD 6 0#64) ∗ ((a + 0x38#64) ↦₆₄ ws.getD 7 0#64) ∗
      ((a + 0x40#64) ↦₆₄ ws.getD 8 0#64) ∗ ((a + 0x48#64) ↦₆₄ ws.getD 9 0#64) ∗
      ((a + 0x50#64) ↦₆₄ ws.getD 10 0#64) ∗ ((a + 0x58#64) ↦₆₄ ws.getD 11 0#64) ∗
      ((a + 0x60#64) ↦₆₄ ws.getD 12 0#64) ∗ ((a + 0x68#64) ↦₆₄ ws.getD 13 0#64) ∗
      ((a + 0x70#64) ↦₆₄ ws.getD 14 0#64) ∗ ((a + 0x78#64) ↦₆₄ ws.getD 15 0#64) ∗
      ((a + 0x80#64) ↦₆₄ ws.getD 16 0#64) ∗ ((a + 0x88#64) ↦₆₄ ws.getD 17 0#64) ∗
      ((a + 0x90#64) ↦₆₄ ws.getD 18 0#64) ∗ ((a + 0x98#64) ↦₆₄ ws.getD 19 0#64) ∗
      ((a + 0xa0#64) ↦₆₄ ws.getD 20 0#64) ∗ ((a + 0xa8#64) ↦₆₄ ws.getD 21 0#64) ∗
      ((a + 0xb0#64) ↦₆₄ ws.getD 22 0#64) ∗ ((a + 0xb8#64) ↦₆₄ ws.getD 23 0#64) ∗
      ((a + 0xc0#64) ↦₆₄ ws.getD 24 0#64) ∗ ((a + 0xc8#64) ↦₆₄ ws.getD 25 0#64) ∗
      ((a + 0xd0#64) ↦₆₄ ws.getD 26 0#64) := by
  conv => lhs; rw [← @List.drop_zero _ ws]
  repeat rw [words64At_drop_succ (by omega)]
  rw [words64At_drop_eq_emp (by omega)]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

@[expose] def encSavedRegsAtSp (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 0xb80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xb88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0xb90#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xb98#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0xba0#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xba8#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0xbb0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xbb8#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0xbc0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xbc8#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0xbd0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xbd8#64) ↦₆₄ s0.readReg64 .x19)

theorem sub_eq_atSp (sp0 d off : BitVec 64) (h : d + off = 0xbe0#64) :
    sp0 - d = (sp0 - 0xbe0#64) + off := by
  bv_omega

theorem encSavedRegs_eq_atSp (sp0 : BitVec 64) (s0 : State) :
    encSavedRegs sp0 s0 = encSavedRegsAtSp (sp0 - 0xbe0#64) s0 := by
  simp only [encSavedRegs, encSavedRegsAtSp,
    sub_eq_atSp sp0 96#64 0xb80#64 rfl, sub_eq_atSp sp0 88#64 0xb88#64 rfl,
    sub_eq_atSp sp0 80#64 0xb90#64 rfl, sub_eq_atSp sp0 72#64 0xb98#64 rfl,
    sub_eq_atSp sp0 64#64 0xba0#64 rfl, sub_eq_atSp sp0 56#64 0xba8#64 rfl,
    sub_eq_atSp sp0 48#64 0xbb0#64 rfl, sub_eq_atSp sp0 40#64 0xbb8#64 rfl,
    sub_eq_atSp sp0 32#64 0xbc0#64 rfl, sub_eq_atSp sp0 24#64 0xbc8#64 rfl,
    sub_eq_atSp sp0 16#64 0xbd0#64 rfl, sub_eq_atSp sp0 8#64 0xbd8#64 rfl]

open CryptoVerification.LibsignalPublicApi.StoreKit

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
