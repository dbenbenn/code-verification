/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import ProofLib.Sep
public import LibsignalBinary.Proofs.CryptoGames.Ratchet.CreateChainProofDefs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `<RootKey>::create_chain`

Verifies `<libsignal_protocol::ratchet::keys::RootKey>::create_chain` (X25519 key agreement,
HKDF-SHA256 extract/expand with `"WhisperRatchet"`, stack zeroization, and shared-secret
deallocation) against `rootCreateChain` on both rebased images and `[LibsignalPlacement]`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Keys

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CreateChainFacts

theorem extractLsb'_append_zero {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2) :
    (hi ++ lo).extractLsb' 0 w2 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp [BitVec.getLsbD_append, hi']

theorem extractLsb'_append_step {w1 w2 : Nat} (hi : BitVec w1) (lo : BitVec w2)
    (s k : Nat) (h : w2 ≤ s) :
    (hi ++ lo).extractLsb' s k = hi.extractLsb' (s - w2) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have hnot : ¬(s + i < w2) := by omega
  have hsub : s - w2 + i = s + i - w2 := by omega
  simp [BitVec.getLsbD_append, hi', hnot, hsub]

theorem extractLsb'_zero_self {w : Nat} (x : BitVec w) :
    x.extractLsb' 0 w = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp [hi']

theorem unpack64_append8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  unfold unpack64
  rw [extractLsb'_append_zero,
    extractLsb'_append_step _ _ 8 8 (by decide), extractLsb'_append_zero,
    extractLsb'_append_step _ _ 16 8 (by decide), extractLsb'_append_step _ _ 8 8 (by decide),
    extractLsb'_append_zero,
    extractLsb'_append_step _ _ 24 8 (by decide), extractLsb'_append_step _ _ 16 8 (by decide),
    extractLsb'_append_step _ _ 8 8 (by decide), extractLsb'_append_zero,
    extractLsb'_append_step _ _ 32 8 (by decide), extractLsb'_append_step _ _ 24 8 (by decide),
    extractLsb'_append_step _ _ 16 8 (by decide), extractLsb'_append_step _ _ 8 8 (by decide),
    extractLsb'_append_zero,
    extractLsb'_append_step _ _ 40 8 (by decide), extractLsb'_append_step _ _ 32 8 (by decide),
    extractLsb'_append_step _ _ 24 8 (by decide), extractLsb'_append_step _ _ 16 8 (by decide),
    extractLsb'_append_step _ _ 8 8 (by decide), extractLsb'_append_zero,
    extractLsb'_append_step _ _ 48 8 (by decide), extractLsb'_append_step _ _ 40 8 (by decide),
    extractLsb'_append_step _ _ 32 8 (by decide), extractLsb'_append_step _ _ 24 8 (by decide),
    extractLsb'_append_step _ _ 16 8 (by decide), extractLsb'_append_step _ _ 8 8 (by decide),
    extractLsb'_append_zero,
    extractLsb'_append_step _ _ 56 8 (by decide), extractLsb'_append_step _ _ 48 8 (by decide),
    extractLsb'_append_step _ _ 40 8 (by decide), extractLsb'_append_step _ _ 32 8 (by decide),
    extractLsb'_append_step _ _ 24 8 (by decide), extractLsb'_append_step _ _ 16 8 (by decide),
    extractLsb'_append_step _ _ 8 8 (by decide), extractLsb'_zero_self]

end CreateChainFacts

theorem exists_unpack64_of_length_64 {bs1 bs2 : List (BitVec 8)} (h1 : bs1.length = 32)
    (h2 : bs2.length = 32) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ (bs1 ++ bs2)) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7)) := by
  obtain ⟨w0, w1, w2, w3, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w4, w5, w6, w7, _, hp2⟩ := exists_unpack64_of_length_32 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  rw [pointsToBytes_append, h1, hp1, hp2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_unpack64_of_length_80 {bs1 bs2 bs3 : List (BitVec 8)} (h1 : bs1.length = 32)
    (h2 : bs2.length = 32) (h3 : bs3.length = 16) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ (bs1 ++ bs2 ++ bs3)) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
            ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
            ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9)) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hp12⟩ := exists_unpack64_of_length_64 h1 h2
  obtain ⟨w8, w9, _, hp3⟩ := exists_unpack64_of_length_16 h3
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, fun a => ?_⟩
  have h12 : (bs1 ++ bs2).length = 64 := by simp [h1, h2]
  rw [pointsToBytes_append, h12, hp12, hp3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem shaStateBytes_length (st : ShaState) :
    (LibsignalHmac.shaStateBytes st).length = 32 := by
  rcases st with ⟨l, hl⟩
  simp [LibsignalHmac.shaStateBytes, LibsignalAesCbc.toLEBytes, List.length_flatMap,
    List.map_const', hl]

@[expose] def hmacCoreBytes (F : ShaCompress) (key : List (BitVec 8)) : List (BitVec 8) :=
  LibsignalHmac.shaStateBytes (hmacInnerInit F key) ++ unpack64 1#64 ++
    LibsignalHmac.shaStateBytes (hmacOuterInit F key) ++ unpack64 1#64

@[expose] def HmacGood (F : ShaCompress) (key : List (BitVec 8)) (ws : List (BitVec 64)) : Prop :=
  ∃ junk : List (BitVec 8), junk.length = 63 ∧ unpackL ws = junk ++ [0#8] ++ hmacCoreBytes F key

@[expose] def hmacRest (F : ShaCompress) (p : BitVec 64) (key : List (BitVec 8)) : SepProp :=
  ((p + 0x3f#64) ↦₈ 0#8) ∗
    ((p + 0x40#64) ↦ₛ LibsignalHmac.shaStateBytes (hmacInnerInit F key)) ∗
    ((p + 0x60#64) ↦₆₄ 1#64) ∗
    ((p + 0x68#64) ↦ₛ LibsignalHmac.shaStateBytes (hmacOuterInit F key)) ∗
    ((p + 0x88#64) ↦₆₄ 1#64)

theorem hmacCoreAt_nil (F : ShaCompress) (p : BitVec 64) (key : List (BitVec 8)) :
    hmacCoreAt F p key [] = (memRegion p 63 ∗ hmacRest F p key) := by
  dsimp only [hmacCoreAt, hmacStateAt, hmacRest, List.length_nil, Nat.sub_zero, BitVec.ofNat_eq_ofNat]
  rw [eq_true (by decide : 0 < 64), pure_true, emp_sepConj, pointsToBytes_nil, emp_sepConj,
    BitVec.add_zero]

theorem hmacRest_bytes (F : ShaCompress) (p : BitVec 64) (key junk : List (BitVec 8))
    (hj : junk.length = 63) :
    (p ↦ₛ (junk ++ [0#8] ++ hmacCoreBytes F key)) = ((p ↦ₛ junk) ∗ hmacRest F p key) := by
  simp only [hmacRest, hmacCoreBytes, List.append_assoc, pointsToBytes_append, hj,
    List.singleton_append, pointsToBytes_cons, shaStateBytes_length, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

theorem hmacGood_length (F : ShaCompress) (key junk : List (BitVec 8)) (hj : junk.length = 63) :
    (junk ++ [0#8] ++ hmacCoreBytes F key).length = 8 * 18 := by
  simp [hj, hmacCoreBytes, shaStateBytes_length]

theorem pointsToBytes_unpack18 (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
    w17 : BitVec 64) :
    (a ↦ₛ unpackL [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16,
      w17]) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
        ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
        ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗ ((a + 96#64) ↦₆₄ w12) ∗
        ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗
        ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17)) := by
  simp only [unpackL, List.flatMap_cons, List.flatMap_nil, List.append_nil, pointsToBytes_append,
    unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

theorem hmacCore_split (F : ShaCompress) (p : BitVec 64) (key : List (BitVec 8)) :
    hmacCoreAt F p key [] ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64,
      ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ⌜HmacGood F key [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
          w16, w17]⌝ ∗
        ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
          ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
          ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₆₄ w8) ∗ ((p + 72#64) ↦₆₄ w9) ∗
          ((p + 80#64) ↦₆₄ w10) ∗ ((p + 88#64) ↦₆₄ w11) ∗ ((p + 96#64) ↦₆₄ w12) ∗
          ((p + 104#64) ↦₆₄ w13) ∗ ((p + 112#64) ↦₆₄ w14) ∗ ((p + 120#64) ↦₆₄ w15) ∗
          ((p + 128#64) ↦₆₄ w16) ∗ ((p + 136#64) ↦₆₄ w17)) := by
  rw [hmacCoreAt_nil, memRegion_eq_exists_bytes p 63 (by decide)]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun junk => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hj => ?_
  rw [← hmacRest_bytes F p key junk hj]
  obtain ⟨ws, hl, hws⟩ := exists_unpackL 18 _ (hmacGood_length F key junk hj)
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ |
    ⟨w8, _ | ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | ⟨w16, _ |
    ⟨w17, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hl
  rw [hws, pointsToBytes_unpack18]
  refine Entails.sepExists_right w0 <| Entails.sepExists_right w1 <|
    Entails.sepExists_right w2 <| Entails.sepExists_right w3 <| Entails.sepExists_right w4 <|
    Entails.sepExists_right w5 <| Entails.sepExists_right w6 <| Entails.sepExists_right w7 <|
    Entails.sepExists_right w8 <| Entails.sepExists_right w9 <| Entails.sepExists_right w10 <|
    Entails.sepExists_right w11 <| Entails.sepExists_right w12 <| Entails.sepExists_right w13 <|
    Entails.sepExists_right w14 <| Entails.sepExists_right w15 <| Entails.sepExists_right w16 <|
    Entails.sepExists_right w17 <| Entails.pure_right ⟨junk, hj, hws.symm⟩ (Entails.refl _)

theorem hmacCore_merge (F : ShaCompress) (p : BitVec 64) (key : List (BitVec 8))
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64}
    (hg : HmacGood F key [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
      w16, w17]) :
    ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ∗
        ((p + 32#64) ↦₆₄ w4) ∗ ((p + 40#64) ↦₆₄ w5) ∗ ((p + 48#64) ↦₆₄ w6) ∗
        ((p + 56#64) ↦₆₄ w7) ∗ ((p + 64#64) ↦₆₄ w8) ∗ ((p + 72#64) ↦₆₄ w9) ∗
        ((p + 80#64) ↦₆₄ w10) ∗ ((p + 88#64) ↦₆₄ w11) ∗ ((p + 96#64) ↦₆₄ w12) ∗
        ((p + 104#64) ↦₆₄ w13) ∗ ((p + 112#64) ↦₆₄ w14) ∗ ((p + 120#64) ↦₆₄ w15) ∗
        ((p + 128#64) ↦₆₄ w16) ∗ ((p + 136#64) ↦₆₄ w17)) ⊢
      hmacCoreAt F p key [] := by
  obtain ⟨junk, hj, hws⟩ := hg
  rw [← pointsToBytes_unpack18, hws, hmacRest_bytes F p key junk hj, hmacCoreAt_nil]
  exact sepConj_mono_left (by sep_interval)

theorem hmacCore_entails_cells (F : ShaCompress) (p : BitVec 64) (key : List (BitVec 8)) :
    hmacCoreAt F p key [] ⊢ cells p 8 ∗ memRegion (p + 64#64) 80 := by
  rw [hmacCoreAt_nil]
  dsimp only [hmacRest]
  have h1 : (LibsignalHmac.shaStateBytes (hmacInnerInit F key)).length = 32 := shaStateBytes_length _
  have h2 : (LibsignalHmac.shaStateBytes (hmacOuterInit F key)).length = 32 := shaStateBytes_length _
  sep_interval

theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) (_h : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem bv_add_neg64 (x : BitVec 64) :
    x + bv% (2 ^ 64 - 64) = x - 64#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl

macro "cells_add_unfold" : tactic =>
  `(tactic| simp only [cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at *)

macro "cells_pre_unfold" : tactic =>
  `(tactic| (
    try (conv => arg 4; simp (config := { maxSteps := 200000 }) (disch := decide) only [
      cells_sub_succ, Nat.reduceSub, cells_zero, sepConj_emp])
    try (conv => arg 4; simp (config := { maxSteps := 200000 }) only [
      cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd])))

macro "cells_post_unfold" : tactic =>
  `(tactic| (
    try (conv => arg 5; simp (config := { maxSteps := 200000 }) (disch := decide) only [
      cells_sub_succ, Nat.reduceSub, cells_zero, sepConj_emp])
    try (conv => arg 5; simp (config := { maxSteps := 200000 }) only [
      cells, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd])))

macro "cells_all_unfold" : tactic =>
  `(tactic| (cells_pre_unfold; cells_post_unfold))

macro "post_exists_unfold" : tactic =>
  `(tactic| (
    conv =>
      arg 5
      simp (config := { maxSteps := 500000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]))

macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 200000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))

theorem stackAt_alloc_extract (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 3120 ∗ stackAt sp extractStack := by
  dsimp only [stackAt, allocHookStack, extractStack, newFromSliceStack]; sep_interval_eq

theorem stackAt_alloc_expand (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 3456 ∗ stackAt sp expandMultiInfoStack := by
  dsimp only [stackAt, allocHookStack, expandMultiInfoStack, finalizeFixedStack]; sep_interval_eq

theorem pointsTo_keyVec_toList (a : BitVec 64) (rk : BitVec 256) :
    (a ↦ₛ (Ratchet.keyToBytesVec32 rk).toList) = (a ↦ₛ keyToBytes32 rk) := rfl

@[expose] def expandCellsAllocStackSpec (F : ShaCompress) (k : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp allocHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp allocHookStack

@[expose] def deallocAllocStackSpec (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × BitVec 64) where
  pre := fun (p, size, align, sp) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      s.sp = sp⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp allocHookStack
  post := fun (_, _, _, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt sp allocHookStack

@[expose] def calculateAgreementCallSpec (X : Ratchet.X25519Fn) (A : RustAlloc) :
    Spec (BitVec 64 × PrivateKey × BitVec 64 × PublicKey × BitVec 64 × BitVec 64) where
  pre := fun (ourA, our, theirA, their, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStack
  post := fun (ourA, our, theirA, their, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      calculateAgreementResultAt A ret (calculateAgreement X their our) ∗
      A.pool ∗ stackAt sp calculateAgreementStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem createChain_onPanic_entails {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

open Lean Elab Tactic in
elab "wpp_call_ret " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_ret $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_ret: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact createChain_onPanic_entails (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

theorem stackAt_calc_alloc_split (sp : BitVec 64) :
    stackAt sp calculateAgreementStack =
      memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  dsimp only [stackAt, calculateAgreementStack, allocHookStack]; sep_interval_eq

private theorem stackAt_576_callStack_split (sp : BitVec 64) {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64) :
    stackAt sp (576 + callStack) =
      stackAt (sp - 576#64) callStack ∗ memRegion (sp - 576#64) 576 := by
  have hsub : sp - 576#64 - BitVec.ofNat 64 callStack = sp - BitVec.ofNat 64 (576 + callStack) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hb' : sp - BitVec.ofNat 64 (576 + callStack) + BitVec.ofNat 64 callStack = sp - 576#64 := by
    rw [← hsub, BitVec.sub_add_cancel]
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (576 + callStack)) (n := callStack) (k := 576)
      (b' := sp - 576#64) (Nat.add_comm 576 callStack) hb'.symm hbound, hsub]

theorem fnFrame_split_createChainAt_pre (sp : BitVec 64) {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64) :
    stackAt sp (576 + callStack) =
      stackAt (sp - 576#64) callStack ∗
        memRegion (sp - 576#64) 64 ∗ cells (sp - 512#64) 8 ∗ cells (sp - 448#64) 8 ∗
        cells (sp - 384#64) 4 ∗ cells (sp - 352#64) 14 ∗ memRegion (sp - 240#64) 24 ∗
        memRegion (sp - 216#64) 152 ∗ cells (sp - 64#64) 8 := by
  rw [stackAt_576_callStack_split sp hbound]; congr 1; sep_interval_eq

theorem fnFrame_split_createChainAt_err (sp : BitVec 64) {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64) :
    stackAt sp (576 + callStack) =
      stackAt (sp - 576#64) callStack ∗
        memRegion (sp - 576#64) 64 ∗ cells (sp - 512#64) 8 ∗ cells (sp - 448#64) 8 ∗
        cells (sp - 384#64) 4 ∗ cells (sp - 352#64) 14 ∗ cells (sp - 240#64) 3 ∗
        memRegion (sp - 216#64) 152 ∗ cells (sp - 64#64) 8 := by
  rw [stackAt_576_callStack_split sp hbound]; congr 1; sep_interval_eq

theorem fnFrame_split_createChainAt_ok (sp : BitVec 64) {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64) :
    stackAt sp (576 + callStack) =
      stackAt (sp - 576#64) callStack ∗
        memRegion (sp - 576#64) 64 ∗ cells (sp - 512#64) 8 ∗ cells (sp - 448#64) 8 ∗
        cells (sp - 384#64) 8 ∗ memRegion (sp - 320#64) 80 ∗ cells (sp - 240#64) 8 ∗
        cells (sp - 176#64) 14 ∗ cells (sp - 64#64) 8 := by
  rw [stackAt_576_callStack_split sp hbound]; congr 1; sep_interval_eq

theorem memRegion_68_createChain_err (out : BitVec 64) :
    memRegion (out + 4#64) 68 =
      memRegion (out + 4#64) 4 ∗ cells (out + 8#64) 2 ∗ memRegion (out + 24#64) 48 := by
  sep_interval_eq

theorem memRegion_56_createChain_err (out : BitVec 64) :
    memRegion (out + 16#64) 56 =
      (∃∗ u, (out + 16#64) ↦₆₄ u) ∗ memRegion (out + 24#64) 48 := by
  sep_interval_eq

theorem memRegion_out_createChain_err (out : BitVec 64) :
    memRegion out 72 =
      (∃∗ d0, out ↦₃₂ d0) ∗ memRegion (out + 4#64) 4 ∗
        cells (out + 8#64) 2 ∗ memRegion (out + 24#64) 48 := by
  sep_interval_eq

theorem memRegion_out_createChain_ok (out : BitVec 64) :
    memRegion out 72 =
      (∃∗ d0, out ↦₃₂ d0) ∗ cells (out + 4#64) 8 ∗ (∃∗ d1, (out + 68#64) ↦₃₂ d1) := by
  sep_interval_eq

private structure CalcResHdrSnap where
  tag : BitVec 64
  ptr : BitVec 64
  len : BitVec 64

private def CalcResHdrLayout : ProofLib.Sep.StructLayout CalcResHdrSnap where
  totalSz := 24
  fields := [.u64 0 (·.tag), .u64 8 (·.ptr), .u64 16 (·.len)]

theorem cells3_memRegion_152_merge (sp v0 v1 v2 : BitVec 64) :
    ((sp - 240#64) ↦₆₄ v0) ∗ ((sp - 232#64) ↦₆₄ v1) ∗ ((sp - 224#64) ↦₆₄ v2) ∗
      memRegion (sp - 216#64) 152 ⊢
      memRegion (sp - 240#64) 176 := by
  have h24 := CalcResHdrLayout.struct_to_memRegion (sp - 240#64) ⟨v0, v1, v2⟩
  simp (config := { decide := true }) only [CalcResHdrLayout, ProofLib.Sep.StructLayout.own,
    ProofLib.Sep.fieldsRenderAt, ProofLib.Sep.renderWithGap, ProofLib.Sep.renderTailGap,
    ProofLib.Sep.StructField.u64, ProofLib.Sep.StructField.field64,
    ProofLib.Sep.fieldAddr, ↓reduceIte] at h24
  refine Entails.trans ?_
    (Entails.trans (sepConj_mono_left (Q := memRegion (sp - 216#64) 152) h24) (by sep_interval))
  sep_interval

theorem pointsTo8_memRegion7_entails (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ b0) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_comm, sepConj_assoc]
  refine Entails.pure_left fun hbs => ?_
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hbs)
  refine Entails.sepExists_right (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1) ?_
  have heq : (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) =
      (a ↦ₛ unpack64 ((b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1) ++ b0)) := by
    rw [← pointsToBytes_cons, CreateChainFacts.unpack64_append8]
  rw [sepConj_comm, heq, ← pointsTo64_eq_pointsToBytes]
  exact Entails.refl _

theorem calculateAgreementResult_none_cells (A : RustAlloc) (a : BitVec 64) :
    calculateAgreementResultAt A a none ⊢
      (a ↦₆₄ 1#64) ∗
        (∃∗ hi : BitVec 56, (a + 8#64) ↦₆₄ (hi ++ 3#8)) ∗
        (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) := by
  dsimp only [calculateAgreementResultAt]
  have h15 : memRegion (a + 9#64) 15 =
      memRegion (a + 8#64 + 1#64) 7 ∗ (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) := by
    sep_interval_eq
  rw [h15]
  have hp := pointsTo8_memRegion7_entails (a + 8#64) 3#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp ⊢
  exact sepConj_mono_right (by rw [← sepConj_assoc]; exact sepConj_mono_left hp)

theorem boxU8At_32_split (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    boxU8At A a ptr bs ⊢
      ⌜ptr ≠ 0⌝ ∗ (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ 32#64) ∗
        A.live ptr 32 1 ∗ (ptr ↦ₛ bs) := by
  have hne : bs ≠ [] := by intro h; rw [h] at hlen; contradiction
  dsimp only [boxU8At]
  simp only [hne, ↓reduceIte, hlen, BitVec.ofNat_eq_ofNat]
  bi_entail

theorem pointsTo32_zero_eq_leBytes (a : BitVec 64) :
    (a ↦₃₂ 0#32) = (a ↦ₛ leBytes 4 0) := by
  refine IsBlock.eq (IsBlock.pointsTo32 a 0#32) (IsBlock.pointsToBytes_len (n := 4) rfl) fun m => ?_
  simp only [leBytes, List.range, List.range.loop, List.map,
    Nat.zero_div, List.length_cons, List.length_nil, Nat.reduceAdd,
    show (4 : Nat) ≤ 2 ^ 64 by decide, true_and, Memory.readBytes, Memory.read32,
    BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, List.cons.injEq, and_true]
  refine ⟨fun h => ?_, fun ⟨hb0, hb1, hb2, hb3⟩ => by rw [hb0, hb1, hb2, hb3]; rfl⟩
  have h0 := congrArg (·.extractLsb' 0 8) h
  have h1 := congrArg (·.extractLsb' 8 8) h
  have h2 := congrArg (·.extractLsb' 16 8) h
  have h3 := congrArg (·.extractLsb' 24 8) h
  rw [CreateChainFacts.extractLsb'_append_zero] at h0
  rw [CreateChainFacts.extractLsb'_append_step _ _ 8 8 (by decide), CreateChainFacts.extractLsb'_append_zero] at h1
  rw [CreateChainFacts.extractLsb'_append_step _ _ 16 8 (by decide),
    CreateChainFacts.extractLsb'_append_step _ _ 8 8 (by decide), CreateChainFacts.extractLsb'_append_zero] at h2
  rw [CreateChainFacts.extractLsb'_append_step _ _ 24 8 (by decide),
    CreateChainFacts.extractLsb'_append_step _ _ 16 8 (by decide),
    CreateChainFacts.extractLsb'_append_step _ _ 8 8 (by decide), CreateChainFacts.extractLsb'_zero_self] at h3
  exact ⟨h0, h1, h2, h3⟩

theorem createChainResultAt_ok_eq (out : BitVec 64) (p : RootKey × Ratchet.ChainKey) :
    createChainResultAt out (.ok (p.1, ⟨p.2, 0#32⟩)) =
      (out ↦₃₂ 0#32) ∗ ((out + 4#64) ↦ₛ Ratchet.keysToBytes p) ∗ ((out + 68#64) ↦₃₂ 0#32) := by
  dsimp only [createChainResultAt, chainKeyBytes, Ratchet.keysToBytes]
  have hlen1 : (keyToBytes32 p.1).length = 32 := by simp [keyToBytes32]
  have hlen2 : (keyToBytes32 p.2).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, pointsToBytes_append, hlen1, hlen2,
    BitVec.toNat_ofNat, Nat.zero_mod, ← pointsTo32_zero_eq_leBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem rootCreateChain_of_calculateAgreement_none (C : Crypto) (rk : RootKey)
    (their : PublicKey) (our : PrivateKey)
    (h : calculateAgreement C.X their our = none) :
    rootCreateChain C rk their our = .error .invalidKeyAgreement := by
  unfold calculateAgreement at h
  dsimp only at h
  split at h
  · rename_i h0
    unfold rootCreateChain Ratchet.createChain
    dsimp only
    simp only [h0, ↓reduceIte]
  · contradiction

theorem rootCreateChain_of_calculateAgreement_some (C : Crypto) (rk : RootKey)
    (their : PublicKey) (our : PrivateKey) (ss : List.Vector (BitVec 8) 32)
    (h : calculateAgreement C.X their our = some ss) :
    rootCreateChain C rk their our =
      let p := Ratchet.rootKdf C.F rk ss.toList
      .ok (p.1, ⟨p.2, 0#32⟩) := by
  unfold calculateAgreement at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hne
    injection h with hss
    subst hss
    unfold rootCreateChain Ratchet.createChain
    dsimp only
    simp only [hne, ↓reduceIte]
    rfl

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

@[simp] theorem length_hmacWith (F : ShaCompress) (key msg : List (BitVec 8)) :
    (hmacWith F key msg).length = 32 := by
  unfold hmacWith sha256With
  generalize (chunks64 _).foldl F sha256IV = st
  rcases st with ⟨l, hl⟩
  simp [toBEBytes, List.length_flatMap, hl]

theorem length_hkdfExpand_64 (F : ShaCompress) (prk info : List (BitVec 8)) :
    (hkdfExpand F prk info 64).length = 64 := by
  simp [hkdfExpand, hkdfBlocks]

theorem keysToBytes_rootKdf (F : ShaCompress) (rk : RootKey) (ikm : List (BitVec 8)) :
    Ratchet.keysToBytes (Ratchet.rootKdf F rk ikm) =
      hkdf F (Ratchet.rootSalt rk) ikm Ratchet.whisperRatchetInfo 64 := by
  have hlen := length_hkdfExpand_64 F (hkdfExtract F (Ratchet.rootSalt rk) ikm) Ratchet.whisperRatchetInfo
  unfold Ratchet.keysToBytes Ratchet.rootKdf hkdf
  generalize hkdfExpand F (hkdfExtract F (Ratchet.rootSalt rk) ikm) Ratchet.whisperRatchetInfo 64 = okm at hlen ⊢
  have h1 : (okm.take 32).length = 32 := by simp [hlen]
  have h2 : ((okm.drop 32).take 32).length = 32 := by simp [hlen]
  dsimp only
  rw [keyToBytes32_bytesToKey32 _ h1, keyToBytes32_bytesToKey32 _ h2,
    List.take_of_length_le (l := okm.drop 32) (by simp [hlen]), List.take_append_drop]

@[local simp, local arm64_norm]
theorem whisperRatchet_length : Ratchet.whisperRatchetInfo.length = 14 := rfl

@[local simp, local arm64_norm]
theorem hkdfExtract_length' (F : ShaCompress) (salt : Salt) (ikm : List (BitVec 8)) :
    (hkdfExtract F salt ikm).length = 32 := by
  cases salt <;> simp [hkdfExtract, length_hmacWith]

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8).extractLsb' 0 8 = 3#8 :=
  CreateChainFacts.extractLsb'_append_zero hi 3#8

@[local simp, local arm64_norm, local wp_norm]
theorem and_ff_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8) &&& 0xff#64 = 3#64 := by bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem and_ff32_hi56_3 (hi : BitVec 56) :
    BitVec.truncate 32 (hi ++ 3#8) &&& 0xff#32 = 3#32 := by bv_bits

@[local simp, local arm64_norm, local wp_norm]
theorem zext64_trunc32_hi56_3_and_ff (hi : BitVec 56) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (hi ++ 3#8)) &&& 255#64 = 3#64 := by bv_bits

macro "wp_simp_pre " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp (config := { decide := true }) only [$rules,*]))

macro "wp_simp_post " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 5; simp only [$rules,*]))

namespace CreateChainFacts

theorem SepWP.exists_left_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a ∗ F) post) :
    SepWP prog pc s ((∃∗ a, P a) ∗ F) post := by
  rw [sepExists_sepConj_left]; exact SepWP.exists_elim h

theorem SepWP.pure_left_elim {φ : Prop} {prog : Program} {pc : BitVec 64} {s : State}
    {P F : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s (P ∗ F) post) :
    SepWP prog pc s ((⌜φ⌝ ∗ P) ∗ F) post := by
  rw [sepConj_assoc]; exact SepWP.pure_elim h

theorem cells2_add_eq (a : BitVec 64) :
    cells a 2 = ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  sep_interval_eq

theorem cells4_add_eq (a : BitVec 64) :
    cells a 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) := by
  sep_interval_eq

theorem cells8_add_eq (a : BitVec 64) :
    cells a 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
        ((a + 56#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem cells14_add_eq (a : BitVec 64) :
    cells a 14 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
      ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
        ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
        ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗
        ((a + 104#64) ↦₆₄ v13) := by
  sep_interval_eq

theorem cells4_sub_384_eq (sp : BitVec 64) :
    cells (sp - 384#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2) ∗
        ((sp - 360#64) ↦₆₄ v3) := by
  sep_interval_eq

theorem cells8_sub_512_eq (sp : BitVec 64) :
    cells (sp - 512#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 512#64) ↦₆₄ v0) ∗ ((sp - 504#64) ↦₆₄ v1) ∗ ((sp - 496#64) ↦₆₄ v2) ∗
        ((sp - 488#64) ↦₆₄ v3) ∗ ((sp - 480#64) ↦₆₄ v4) ∗ ((sp - 472#64) ↦₆₄ v5) ∗
        ((sp - 464#64) ↦₆₄ v6) ∗ ((sp - 456#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem cells8_sub_448_eq (sp : BitVec 64) :
    cells (sp - 448#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 448#64) ↦₆₄ v0) ∗ ((sp - 440#64) ↦₆₄ v1) ∗ ((sp - 432#64) ↦₆₄ v2) ∗
        ((sp - 424#64) ↦₆₄ v3) ∗ ((sp - 416#64) ↦₆₄ v4) ∗ ((sp - 408#64) ↦₆₄ v5) ∗
        ((sp - 400#64) ↦₆₄ v6) ∗ ((sp - 392#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem cells8_sub_384_eq (sp : BitVec 64) :
    cells (sp - 384#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2) ∗
        ((sp - 360#64) ↦₆₄ v3) ∗ ((sp - 352#64) ↦₆₄ v4) ∗ ((sp - 344#64) ↦₆₄ v5) ∗
        ((sp - 336#64) ↦₆₄ v6) ∗ ((sp - 328#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem cells8_sub_64_eq (sp : BitVec 64) :
    cells (sp - 64#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem cells14_sub_352_eq (sp : BitVec 64) :
    cells (sp - 352#64) 14 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
      ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        ((sp - 352#64) ↦₆₄ v0) ∗ ((sp - 344#64) ↦₆₄ v1) ∗ ((sp - 336#64) ↦₆₄ v2) ∗
        ((sp - 328#64) ↦₆₄ v3) ∗ ((sp - 320#64) ↦₆₄ v4) ∗ ((sp - 312#64) ↦₆₄ v5) ∗
        ((sp - 304#64) ↦₆₄ v6) ∗ ((sp - 296#64) ↦₆₄ v7) ∗ ((sp - 288#64) ↦₆₄ v8) ∗
        ((sp - 280#64) ↦₆₄ v9) ∗ ((sp - 272#64) ↦₆₄ v10) ∗ ((sp - 264#64) ↦₆₄ v11) ∗
        ((sp - 256#64) ↦₆₄ v12) ∗ ((sp - 248#64) ↦₆₄ v13) := by
  sep_interval_eq

theorem cells3_of_add (a : BitVec 64) {v0 v1 v2 : BitVec 64} :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ cells a 3 := by
  sep_interval

theorem cells8_of_add (a : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ⊢ cells a 8 := by
  sep_interval

theorem cells14_of_add (a : BitVec 64)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64} :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗
      ((a + 56#64) ↦₆₄ v7) ∗ ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗
      ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗ ((a + 96#64) ↦₆₄ v12) ∗
      ((a + 104#64) ↦₆₄ v13) ⊢ cells a 14 := by
  sep_interval

theorem cells3_sub_240 (sp : BitVec 64) {v0 v1 v2 : BitVec 64} :
    ((sp - 240#64) ↦₆₄ v0) ∗ ((sp - 232#64) ↦₆₄ v1) ∗ ((sp - 224#64) ↦₆₄ v2) ⊢
      cells (sp - 240#64) 3 := by
  sep_interval

theorem cells8_sub_512 (sp : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    ((sp - 512#64) ↦₆₄ v0) ∗ ((sp - 504#64) ↦₆₄ v1) ∗ ((sp - 496#64) ↦₆₄ v2) ∗
      ((sp - 488#64) ↦₆₄ v3) ∗ ((sp - 480#64) ↦₆₄ v4) ∗ ((sp - 472#64) ↦₆₄ v5) ∗
      ((sp - 464#64) ↦₆₄ v6) ∗ ((sp - 456#64) ↦₆₄ v7) ⊢ cells (sp - 512#64) 8 := by
  sep_interval

theorem cells8_sub_448 (sp : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    ((sp - 448#64) ↦₆₄ v0) ∗ ((sp - 440#64) ↦₆₄ v1) ∗ ((sp - 432#64) ↦₆₄ v2) ∗
      ((sp - 424#64) ↦₆₄ v3) ∗ ((sp - 416#64) ↦₆₄ v4) ∗ ((sp - 408#64) ↦₆₄ v5) ∗
      ((sp - 400#64) ↦₆₄ v6) ∗ ((sp - 392#64) ↦₆₄ v7) ⊢ cells (sp - 448#64) 8 := by
  sep_interval

theorem cells8_sub_384 (sp : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2) ∗
      ((sp - 360#64) ↦₆₄ v3) ∗ ((sp - 352#64) ↦₆₄ v4) ∗ ((sp - 344#64) ↦₆₄ v5) ∗
      ((sp - 336#64) ↦₆₄ v6) ∗ ((sp - 328#64) ↦₆₄ v7) ⊢ cells (sp - 384#64) 8 := by
  sep_interval

theorem cells8_sub_240 (sp : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    ((sp - 240#64) ↦₆₄ v0) ∗ ((sp - 232#64) ↦₆₄ v1) ∗ ((sp - 224#64) ↦₆₄ v2) ∗
      ((sp - 216#64) ↦₆₄ v3) ∗ ((sp - 208#64) ↦₆₄ v4) ∗ ((sp - 200#64) ↦₆₄ v5) ∗
      ((sp - 192#64) ↦₆₄ v6) ∗ ((sp - 184#64) ↦₆₄ v7) ⊢ cells (sp - 240#64) 8 := by
  sep_interval

theorem cells8_sub_64 (sp : BitVec 64) {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64} :
    ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
      ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
      ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7) ⊢ cells (sp - 64#64) 8 := by
  sep_interval

theorem cells14_sub_176 (sp : BitVec 64)
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64} :
    ((sp - 176#64) ↦₆₄ v0) ∗ ((sp - 168#64) ↦₆₄ v1) ∗ ((sp - 160#64) ↦₆₄ v2) ∗
      ((sp - 152#64) ↦₆₄ v3) ∗ ((sp - 144#64) ↦₆₄ v4) ∗ ((sp - 136#64) ↦₆₄ v5) ∗
      ((sp - 128#64) ↦₆₄ v6) ∗ ((sp - 120#64) ↦₆₄ v7) ∗ ((sp - 112#64) ↦₆₄ v8) ∗
      ((sp - 104#64) ↦₆₄ v9) ∗ ((sp - 96#64) ↦₆₄ v10) ∗ ((sp - 88#64) ↦₆₄ v11) ∗
      ((sp - 80#64) ↦₆₄ v12) ∗ ((sp - 72#64) ↦₆₄ v13) ⊢ cells (sp - 176#64) 14 := by
  sep_interval

theorem pointsTo64_memRegion48_entails (out : BitVec 64) {u : BitVec 64} :
    ((out + 16#64) ↦₆₄ u) ∗ memRegion (out + 24#64) 48 ⊢ memRegion (out + 16#64) 56 := by
  sep_interval

theorem cells8_add_4_eq (out : BitVec 64) :
    cells (out + 4#64) 8 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((out + 4#64) ↦₆₄ v0) ∗ ((out + 12#64) ↦₆₄ v1) ∗ ((out + 20#64) ↦₆₄ v2) ∗
        ((out + 28#64) ↦₆₄ v3) ∗ ((out + 36#64) ↦₆₄ v4) ∗ ((out + 44#64) ↦₆₄ v5) ∗
        ((out + 52#64) ↦₆₄ v6) ∗ ((out + 60#64) ↦₆₄ v7) := by
  sep_interval_eq

theorem memRegion_out_createChain_ok_flat (out : BitVec 64) :
    memRegion out 72 =
      ∃∗ d1 : BitVec 32, ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64,
      ∃∗ v7 : BitVec 64, ∃∗ d0 : BitVec 32,
        (out ↦₃₂ d0) ∗ ((out + 4#64) ↦₆₄ v0) ∗ ((out + 12#64) ↦₆₄ v1) ∗
        ((out + 20#64) ↦₆₄ v2) ∗ ((out + 28#64) ↦₆₄ v3) ∗ ((out + 36#64) ↦₆₄ v4) ∗
        ((out + 44#64) ↦₆₄ v5) ∗ ((out + 52#64) ↦₆₄ v6) ∗ ((out + 60#64) ↦₆₄ v7) ∗
        ((out + 68#64) ↦₃₂ d1) := by
  sep_interval_eq

end CreateChainFacts

/-- Stack-parameterized spec of `<RootKey>::create_chain` (`576 + callStack`;
`= createChainSpec C A` at `calculateAgreementStack` by `rfl`). -/
@[expose] def createChainSpecAt (C : Crypto) (A : RustAlloc) (callStack : Nat) : Spec CreateChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.rkA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ourA ∧
      s.readReg64 .x8 = x.ret ∧ x.rkA ≠ 0#64⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ memRegion x.ret 72 ∗
      A.pool ∗ stackAt s.sp (576 + callStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗
      createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our) ∗
      A.pool ∗ stackAt s0.sp (576 + callStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def calculateAgreementCallSpecAt (X : Ratchet.X25519Fn) (A : RustAlloc) (callStack : Nat) :
    Spec (BitVec 64 × PrivateKey × BitVec 64 × PublicKey × BitVec 64 × BitVec 64) where
  pre := fun (ourA, our, theirA, their, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt sp callStack
  post := fun (ourA, our, theirA, their, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
      calculateAgreementResultAt A ret (calculateAgreement X their our) ∗
      A.pool ∗ stackAt sp callStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64

theorem stackAt_ext_alloc (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12288 ∗ stackAt sp allocHookStack := by
  simp only [stackAt, extHookStack, allocHookStack, Nat.reducePow]
  sep_interval_eq

@[expose] def expandCellsExtStackSpec (F : ShaCompress) (k : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp extHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp extHookStack

abbrev lsRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev lsExtractSym : String :=
  "_RNvMs0_NtCsfQL55365b6J_4hkdf4hkdfNtB5_11GenericHkdf7extract"

abbrev lsExpandMultiInfoSym : String :=
  "_RNvMs0_NtCsfQL55365b6J_4hkdf4hkdfNtB5_11GenericHkdf17expand_multi_info"

abbrev lsCalculateAgreementSym : String :=
  "_RNvMs5_NtCs3A3j7c9x8g_14libsignal_core5curveNtB5_10PrivateKey19calculate_agreement"

theorem SepWPp.call_allowPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LsFrozenInv pl s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LsFrozenInv pl sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  have hpre_lscro : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hpre R' hm⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_lscro hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      (SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm (hF.of_keepsFrozen hsteps.keepsFrozen)))
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hoom_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

open Lean Elab Tactic in
elab "wpp_call_ret_lscro " hcall:term:max a:term:max hF:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_lscro $hcall (x := $a) $hF)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_ret_lscro: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact createChain_onPanic_entails (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

@[expose] def extractSomePlacedAllocStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, sv, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack
  post := fun (ret, saltA, sv, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F (some sv) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some sv) ikm) [] ∗
      (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack

theorem extractSomePlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractSomePlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomePlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  refine ⟨⟨ret, saltA, some sv, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpec, ExtractGhost.prk, optSaltAt,
      extractSomePlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    rw [eq_true hsalt_ne, pure_true, emp_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def extractKey32PlacedAllocStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 256 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, rk, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack
  post := fun (ret, saltA, rk, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F (some (Ratchet.keyToBytesVec32 rk)) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some (Ratchet.keyToBytesVec32 rk)) ikm) [] ∗
      (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack

theorem extractKey32PlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractKey32PlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map (extractSomePlacedAllocStack_ok hext) ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  refine ⟨⟨ret, saltA, Ratchet.keyToBytesVec32 rk, ikmA, ikm, sp⟩, R, ?_, ?_⟩
  · dsimp only [extractSomePlacedAllocStackSpec, extractKey32PlacedAllocStackSpec] at hpre ⊢
    rw [pointsTo_keyVec_toList]
    exact hpre
  · intro sf hpost
    dsimp only [extractSomePlacedAllocStackSpec, extractKey32PlacedAllocStackSpec] at hpost ⊢
    rw [← pointsTo_keyVec_toList]
    exact hpost

@[expose] def extractNonePlacedAllocStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack

theorem extractNonePlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractNonePlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNonePlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, 0#64, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const, true_or,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx3, hx4, hikm⟩, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpec, ExtractGhost.prk, optSaltAt,
      extractNonePlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def extractEmptyPlacedAllocStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x2 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp allocHookStack

theorem extractEmptyPlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractEmptyPlacedAllocStackSpec C.F pl) := by
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyPlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx2, hx3, hx4, hsp, hikm⟩, hpre⟩
  refine ⟨⟨ret, s0.readReg64 .x1, none, ikmA, ikm⟩, memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt]
    subst hsp
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, Or.inr hx2, hx3, hx4, hikm⟩, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, extractSpec, ExtractGhost.prk, optSaltAt,
      extractEmptyPlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def expandCellsPlacedAllocStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) (k : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp allocHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp allocHookStack

theorem expandCellsPlacedAllocStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoSpec C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsPlacedAllocStackSpec C.F pl n) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsPlacedAllocStackSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA n hn] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * n⟩,
    memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [expandMultiInfoSpec]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, expandMultiInfoSpec, expandCellsPlacedAllocStackSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hcells := hmacCore_entails_cells C.F hkdfA prk
    exact ⟨htr, Satisfies.mono (Entails.trans (sepConj_mono_left hcells) (by bi_entail)) hpost⟩

@[expose] def extractKey32PlacedStackSpecAt (F : ShaCompress) (pl : Obj.MultiPlacement) (callStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 256 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, rk, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack
  post := fun (ret, saltA, rk, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F (some (Ratchet.keyToBytesVec32 rk)) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some (Ratchet.keyToBytesVec32 rk)) ikm) [] ∗
      (saltA ↦ₛ keyToBytes32 rk) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp callStack

@[expose] def expandCellsPlacedStackSpecAt (F : ShaCompress) (pl : Obj.MultiPlacement) (k : Nat) (callStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp callStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp callStack

@[expose] def deallocPlacedStackSpecAt (A : RustAlloc) (pl : Obj.MultiPlacement) (callStack : Nat) :
    Spec (BitVec 64 × Nat × Nat × BitVec 64) where
  pre := fun (p, size, align, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ 0 < size ∧ size < 2 ^ 63 ∧ align = 1 ∧
      s.sp = sp⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp callStack
  post := fun (_, _, _, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt sp callStack

theorem deallocAllocStack_of_rustDealloc_placed {A : RustAlloc} {prog : Program} {addr : BitVec 64}
    (hd : subroutine_ok prog addr (rustDeallocSpec A)) :
    subroutine_ok prog addr (deallocAllocStackSpec A) := by
  refine subroutine_ok_map hd ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [deallocAllocStackSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hsp⟩, hpre⟩
  refine ⟨(p, size, align), R, ?_, ?_⟩
  · dsimp only [rustDeallocSpec]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustDeallocSpec, deallocAllocStackSpec] at hpost ⊢
    subst hsp
    exact hpost

@[expose] def extractSomePlacedExtStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, sv, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack
  post := fun (ret, saltA, sv, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F (some sv) ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F (some sv) ikm) [] ∗
      (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack

theorem extractSomePlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractSomePlacedExtStackSpec C.F pl) := by
  refine subroutine_ok_map (extractSomePlacedAllocStack_ok hext) ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomePlacedExtStackSpec] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, saltA, sv, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractSomePlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [extractSomePlacedAllocStackSpec, extractSomePlacedExtStackSpec] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def extractNonePlacedExtStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack

theorem extractNonePlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractNonePlacedExtStackSpec C.F pl) := by
  refine subroutine_ok_map (extractNonePlacedAllocStack_ok hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNonePlacedExtStackSpec] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractNonePlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [extractNonePlacedAllocStackSpec, extractNonePlacedExtStackSpec] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def extractEmptyPlacedExtStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x2 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 0xb0 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 0x20#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp extHookStack

theorem extractEmptyPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hext : subroutine_ok prog addr (withLsCodeRoLoaded pl (extractSpec C.F))) :
    subroutine_ok prog addr (extractEmptyPlacedExtStackSpec C.F pl) := by
  refine subroutine_ok_map (extractEmptyPlacedAllocStack_ok hext) ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyPlacedExtStackSpec] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨ret, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [extractEmptyPlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [extractEmptyPlacedAllocStackSpec, extractEmptyPlacedExtStackSpec] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def expandCellsPlacedExtStackSpec (F : ShaCompress) (pl : Obj.MultiPlacement) (k : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64) where
  pre := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = hkdfA ∧ s.readReg64 .x1 = infoHdrA ∧
      s.readReg64 .x2 = okmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 (8 * k) ∧
      s.sp = sp ∧ prk.length ≤ 64 ∧ info.length < 23 ∧ (8 * k = 64 ∨ 8 * k = 80)⌝ ∗
      hmacCoreAt F hkdfA prk [] ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ cells okmA k ∗
      stackAt sp extHookStack
  post := fun (hkdfA, prk, infoHdrA, infoA, info, okmA, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      cells hkdfA 8 ∗ memRegion (hkdfA + 64#64) 80 ∗
      (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
      (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand F prk info (8 * k)) ∗
      stackAt sp extHookStack

theorem expandCellsPlacedExtStack_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {addr : BitVec 64}
    (hexp : subroutine_ok prog addr (withLsCodeRoLoaded pl (expandMultiInfoSpec C.F)))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok prog addr (expandCellsPlacedExtStackSpec C.F pl n) := by
  refine subroutine_ok_map (expandCellsPlacedAllocStack_ok hexp n hn) ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsPlacedExtStackSpec] at hpre
  rw [stackAt_ext_alloc sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
  · dsimp only [expandCellsPlacedAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
  · intro sf hpost
    dsimp only [expandCellsPlacedAllocStackSpec, expandCellsPlacedExtStackSpec] at hpost ⊢
    rw [stackAt_ext_alloc sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

@[expose] def deallocPlacedExtStackSpec (A : RustAlloc) (pl : Obj.MultiPlacement) :
    Spec (BitVec 64 × Nat × Nat × BitVec 64) where
  pre := fun (p, size, align, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ 0 < size ∧ size < 2 ^ 63 ∧ align = 1 ∧
      s.sp = sp⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp extHookStack
  post := fun (_, _, _, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt sp extHookStack

theorem deallocPlacedExtStack_of_rustDeallocExtern {A : RustAlloc} {prog : Program}
    {pl : Obj.MultiPlacement} {addr : BitVec 64}
    (hd : subroutine_ok prog addr
      (withLsCodeRoLoaded pl (rustDeallocExternSpecWithStack A extHookStack))) :
    subroutine_ok prog addr (deallocPlacedExtStackSpec A pl) := by
  refine subroutine_ok_map hd ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [deallocPlacedExtStackSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hpos, hlt, halign, hsp⟩, hpre⟩
  refine ⟨(p, size, align), R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨⟨hF.1, hF.2⟩, ?_⟩
    dsimp only [rustDeallocExternSpecWithStack]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    have hlayout : LayoutOk size align := by
      subst halign
      exact ⟨hpos, ⟨0, rfl⟩, by omega⟩
    exact ⟨⟨hx0, hx1, hx2, hlayout⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack, deallocPlacedExtStackSpec] at hpost ⊢
    subst hsp
    exact hpost

theorem calculateAgreementPlacedCall_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {A : RustAlloc} {addr : BitVec 64}
    (hag : subroutine_ok prog addr (withLsCodeRoLoaded pl (calculateAgreementSpec C.X A))) :
    subroutine_ok prog addr (withLsCodeRoLoaded pl (calculateAgreementCallSpec C.X A)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hL, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [calculateAgreementCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq⟩, hpre⟩
  subst hsp_eq
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded pl (calculateAgreementSpec C.X A)).pre
      ⟨ourA, our, theirA, their, ret⟩ s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hL, ?_⟩
    dsimp only [calculateAgreementSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hpre⟩
  exact hag.mono_outcome ⟨ourA, our, theirA, their, ret⟩ R s0 hpc hrun hpre' hsp (fun _ hout => hout)

theorem calculateAgreementPlacedCallX_ok {prog : Program} {pl : Obj.MultiPlacement}
    {C : Crypto} {A : RustAlloc} {addr : BitVec 64}
    (hag : subroutine_ok prog addr (withLsCodeRoLoaded pl (calculateAgreementSpecX C.X A))) :
    subroutine_ok prog addr
      (withLsCodeRoLoaded pl (calculateAgreementCallSpecAt C.X A calculateAgreementExtStack)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp _
  obtain ⟨hL, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [calculateAgreementCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq⟩, hpre⟩
  subst hsp_eq
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded pl (calculateAgreementSpecX C.X A)).pre
      ⟨ourA, our, theirA, their, ret⟩ s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hL, ?_⟩
    dsimp only [calculateAgreementSpecX]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hpre⟩
  exact hag.mono_outcome ⟨ourA, our, theirA, their, ret⟩ R s0 hpc hrun hpre' hsp (fun _ hout => hout)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 4000000 in
/-- Relocatable stack-parameterized `<RootKey>::create_chain` (Block `40`, 460 B): verified once
for any `callStack` (`576 + callStack ≤ 2 ^ 64`) under `LsFrozenInv`-aware call-site specs. -/
theorem createChain_placed_ok_of_hooks_gen [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} {callStack : Nat}
    (hbound : 576 + callStack ≤ 2 ^ 64)
    (hag : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (calculateAgreementCallSpecAt C.X A callStack)))
    (hext' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (extractKey32PlacedStackSpecAt C.F lsmpl callStack))
    (hexp' : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (expandCellsPlacedStackSpecAt C.F lsmpl 8 callStack))
    (hdealloc : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (deallocPlacedStackSpecAt A lsmpl callStack)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecAt C A callStack)) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata''
    (roSym := "libsignal_protocol:.rodata..Lanon.180")
    (roBytes := Ratchet.whisperRatchetInfo) (by decide) ?_
  wpp_init x s0
  obtain ⟨rkA, rk, theirA, their, ourA, our, out⟩ := x
  dsimp only at *
  change subroutine_ok _ _
    (withLsCodeRoLoaded lsmpl (calculateAgreementCallSpecAt C.X A callStack)) at hag
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = rkA› ‹s0.readReg64 (.gpr 1#5) = theirA›
    ‹s0.readReg64 (.gpr 2#5) = ourA› ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_createChainAt_pre s0.sp (by omega)]
  apply SepWPp.of_sepWP_lscro hF0
  apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells8_sub_64_eq s0.sp)) (by sep_focus)
  repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF1
  wpp_call_ret_lscro hag (s0.readReg64 (.gpr 2#5), our, s0.readReg64 (.gpr 1#5), their,
    s0.sp - 240#64, s0.sp - 576#64) hF1
  cases hdh : calculateAgreement C.X their our with
  | none =>
    have hres := rootCreateChain_of_calculateAgreement_none C rk their our hdh
    rw [memRegion_out_createChain_err (s0.readReg64 (.gpr 8#5)), CreateChainFacts.cells2_add_eq]
    wp_simp_pre [hdh, sepConj_assoc]
    apply SepWP.replace_pre
      (hPQ := calculateAgreementResult_none_cells A (s0.sp - 240#64)) (by sep_focus)
    wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells3_sub_240 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_64 s0.sp) (by sep_focus)
    apply SepWP.replace_pre
      (hPQ := CreateChainFacts.pointsTo64_memRegion48_entails (s0.readReg64 (.gpr 8#5))) (by sep_focus)
    clear hag hext' hexp' hdealloc
    rw [fnFrame_split_createChainAt_err s0.sp (by omega)]
    wp_simp_post [hres, createChainResultAt, sepConj_assoc]
    wp_done
  | some ss =>
    have hres := rootCreateChain_of_calculateAgreement_some C rk their our ss hdh
    obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32
        (hkdfExtract_length' C.F (some (Ratchet.keyToBytesVec32 rk)) ss.toList)
    have hprk_sp := hprk (s0.sp - 240#64)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hprk_sp
    have hsplit := hmacCore_split C.F (s0.sp - 208#64)
      (hkdfExtract C.F (some (Ratchet.keyToBytesVec32 rk)) ss.toList)
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hsplit
    have hokm_eq : hkdfExpand C.F (hkdfExtract C.F (some (Ratchet.keyToBytesVec32 rk)) ss.toList)
        Ratchet.whisperRatchetInfo 64 =
        Ratchet.keysToBytes (Ratchet.rootKdf C.F rk ss.toList) :=
      (keysToBytes_rootKdf C.F rk ss.toList).symm
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm⟩ :=
      exists_unpack64_of_length_64
        (bs1 := keyToBytes32 (Ratchet.rootKdf C.F rk ss.toList).1)
        (bs2 := keyToBytes32 (Ratchet.rootKdf C.F rk ss.toList).2)
        (by simp [keyToBytes32]) (by simp [keyToBytes32])
    have hokm_sp := (congrArg ((s0.sp - 512#64) ↦ₛ ·) hokm_eq).trans (hokm (s0.sp - 512#64))
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hokm_sp
    have hokm_out := hokm (s0.readReg64 (.gpr 8#5) + 4#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hokm_out
    wp_simp_pre [hdh, calculateAgreementResultAt, sepConj_assoc]
    wp_extract_exists
    rename_i ptr
    have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
    apply SepWP.replace_pre
      (hPQ := boxU8At_32_split A (s0.sp - 240#64 + 8#64) ptr ss.toList hss_len)
      (by sep_focus)
    apply CreateChainFacts.SepWP.pure_left_elim; intro hptr_ne
    apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells8_sub_512_eq s0.sp)) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    apply SepWP.of_sepWP_lscro hF_sf
    wp_steps
    apply SepWP.replace_pre
      (hPQ := cells3_memRegion_152_merge s0.sp 0#64 ptr 32#64)
      (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_512 s0.sp) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_ext
    apply SepWP.of_sepWP_lscro hF_ext
    wp_call hext' (s0.sp - 240#64, s0.readReg64 (.gpr 0#5), rk,
      ptr, ss.toList, s0.sp - 576#64)
    rw [hprk_sp]
    apply SepWP.replace_pre (hPQ := hsplit) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    apply CreateChainFacts.SepWP.pure_left_elim; intro hgood
    apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells4_sub_384_eq s0.sp)) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells14_sub_352_eq s0.sp)) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hmrg := hmacCore_merge C.F (s0.sp - 384#64) _ hgood
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hmrg
    apply SepWP.replace_pre (hPQ := hmrg) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_exp
    apply SepWP.of_sepWP_lscro hF_exp
    wp_call hexp' (s0.sp - 384#64, hkdfExtract C.F (some (Ratchet.keyToBytesVec32 rk)) ss.toList,
      s0.sp - 240#64, lsmpl.ρ "libsignal_protocol:.rodata..Lanon.180", Ratchet.whisperRatchetInfo,
      s0.sp - 512#64, s0.sp - 576#64)
    rw [hokm_sp]
    apply SepWP.replace_pre
      (hPQ := Entails.of_eq (CreateChainFacts.memRegion_out_createChain_ok_flat (s0.readReg64 (.gpr 8#5))))
      (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells8_sub_448_eq s0.sp)) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    apply SepWP.replace_pre (hPQ := Entails.of_eq (CreateChainFacts.cells8_sub_384_eq s0.sp)) (by sep_focus)
    repeat' (apply CreateChainFacts.SepWP.exists_left_elim; intro _)
    wp_simp_pre [sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells14_sub_176 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_512 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_448 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_384 s0.sp) (by sep_focus)
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_240 s0.sp) (by sep_focus)
    have hss_mem : (ptr ↦ₛ ss.toList) ⊢ memRegion ptr 32 :=
      pointsToBytes_entails_memRegion_of_eq hss_len
    apply SepWP.replace_pre (hPQ := hss_mem) (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF_dealloc
    wp_call hdealloc (ptr, 32, 1, s0.sp - 576#64)
    wp_steps
    apply SepWP.replace_pre (hPQ := CreateChainFacts.cells8_sub_64 s0.sp) (by sep_focus)
    rw [fnFrame_split_createChainAt_ok s0.sp (by omega)]
    wp_simp_post [hres,
      createChainResultAt_ok_eq (s0.readReg64 (.gpr 8#5)) (Ratchet.rootKdf C.F rk ss.toList),
      Ratchet.keysToBytes, hokm_out, sepConj_assoc]
    clear hag hext' hexp' hdealloc hprk hprk_sp hsplit hokm hokm_sp hokm_out hmrg hgood
    wp_done

theorem createChain_placed_ok_of_contracts [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec C.X A)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec C A)) := by
  have hag := calculateAgreementPlacedCall_ok hag_ok
  have hext0 := extractKey32PlacedAllocStack_ok hext
  have hext_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (extractKey32PlacedStackSpecAt C.F lsmpl calculateAgreementStack) := by
    refine subroutine_ok_map hext0 ?_
    rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
    dsimp only [extractKey32PlacedStackSpecAt] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [extractKey32PlacedAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [extractKey32PlacedAllocStackSpec, extractKey32PlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  have hexp0 := expandCellsPlacedAllocStack_ok hexp 8 (by decide)
  have hexp_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (expandCellsPlacedStackSpecAt C.F lsmpl 8 calculateAgreementStack) := by
    refine subroutine_ok_map hexp0 ?_
    rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
    dsimp only [expandCellsPlacedStackSpecAt] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [expandCellsPlacedAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [expandCellsPlacedAllocStackSpec, expandCellsPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  have hdealloc0 := deallocAllocStack_of_rustDealloc_placed hdealloc_raw
  have hdealloc_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (deallocPlacedStackSpecAt A lsmpl calculateAgreementStack) := by
    refine subroutine_ok_map hdealloc0 ?_
    rintro ⟨p, size, align, sp⟩ R s0 hpre
    dsimp only [deallocPlacedStackSpecAt] at hpre
    rw [stackAt_calc_alloc_split sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx0, hx1, hx2, _, _, _, hsp⟩, hpre⟩
    refine ⟨⟨p, size, align, sp⟩, memRegion (sp - 4256#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [deallocAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hsp⟩, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [deallocAllocStackSpec, deallocPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_alloc_split sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  exact createChain_placed_ok_of_hooks_gen (callStack := calculateAgreementStack) (by decide)
    hag hext_c hexp_c hdealloc_c

/-- Relocatable per-block verification of `<RootKey>::create_chain` (Block `40`) from
callee contracts and `HookSat` hypotheses. -/
theorem createChain_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withStack (diffieHellmanSpec C.X) 1808)))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec C A)) :=
  createChain_placed_ok_of_contracts
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hext)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp)
    (keys_ls_hook_ok_of_mem h_dealloc)

theorem stackAt_calc_ext (sp : BitVec 64) :
    stackAt sp calculateAgreementExtStack =
      memRegion (sp - 16544#64) 160 ∗ stackAt sp extHookStack := by
  simp only [stackAt, calculateAgreementExtStack, extHookStack, Nat.reducePow, Nat.reduceAdd]
  sep_interval_eq

theorem createChain_placed_ok_of_contracts_x [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (hag_ok : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX C.X A)))
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfoSpec C.F)))
    (hdealloc_raw : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H)
      (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX C A)) := by
  have hag := calculateAgreementPlacedCallX_ok hag_ok
  have hext0 := extractKey32PlacedAllocStack_ok hext
  have hext_ext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (extractKey32PlacedStackSpecAt C.F lsmpl extHookStack) := by
    refine subroutine_ok_map hext0 ?_
    rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
    dsimp only [extractKey32PlacedStackSpecAt] at hpre
    rw [stackAt_ext_alloc sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - 16384#64) 12288 ∗ R, ?_, ?_⟩
    · dsimp only [extractKey32PlacedAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [extractKey32PlacedAllocStackSpec, extractKey32PlacedStackSpecAt] at hpost ⊢
      rw [stackAt_ext_alloc sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  have hext_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (extractKey32PlacedStackSpecAt C.F lsmpl calculateAgreementExtStack) := by
    refine subroutine_ok_map hext_ext ?_
    rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
    dsimp only [extractKey32PlacedStackSpecAt] at hpre
    rw [stackAt_calc_ext sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨ret, saltA, rk, ikmA, ikm, sp⟩, memRegion (sp - 16544#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [extractKey32PlacedStackSpecAt]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [extractKey32PlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_ext sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  have hexp0 := expandCellsPlacedExtStack_ok hexp 8 (by decide)
  have hexp_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (expandCellsPlacedStackSpecAt C.F lsmpl 8 calculateAgreementExtStack) := by
    refine subroutine_ok_map hexp0 ?_
    rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
    dsimp only [expandCellsPlacedStackSpecAt] at hpre
    rw [stackAt_calc_ext sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩, memRegion (sp - 16544#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [expandCellsPlacedExtStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [expandCellsPlacedExtStackSpec, expandCellsPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_ext sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  have hdealloc0 := deallocPlacedExtStack_of_rustDeallocExtern hdealloc_raw
  have hdealloc_c : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsρ lsRustDeallocSym)
      (deallocPlacedStackSpecAt A lsmpl calculateAgreementExtStack) := by
    refine subroutine_ok_map hdealloc0 ?_
    rintro ⟨p, size, align, sp⟩ R s0 hpre
    dsimp only [deallocPlacedStackSpecAt] at hpre
    rw [stackAt_calc_ext sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hpre⟩
    refine ⟨⟨p, size, align, sp⟩, memRegion (sp - 16544#64) 160 ∗ R, ?_, ?_⟩
    · dsimp only [deallocPlacedExtStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpure, Satisfies.mono (by bi_entail) hpre⟩
    · intro sf hpost
      dsimp only [deallocPlacedExtStackSpec, deallocPlacedStackSpecAt] at hpost ⊢
      rw [stackAt_calc_ext sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩
  exact createChain_placed_ok_of_hooks_gen (callStack := calculateAgreementExtStack) (by decide)
    hag hext_c hexp_c hdealloc_c

theorem subroutine_ok_createChainSpecX_of_createChainSpec {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {C : Crypto} {A : RustAlloc}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (createChainSpec C A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (createChainSpecX C A)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _
  have hstk : stackAt s0.sp createChainStackX =
      stackAt s0.sp createChainStack ∗ memRegion (s0.sp - 17120#64) 12288 := by
    simp only [stackAt, createChainStackX, createChainExtStack, createChainStack,
      calculateAgreementExtStack, calculateAgreementStack, extHookStack, allocHookStack,
      Nat.reducePow, Nat.reduceAdd]
    sep_interval_eq
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded pl (createChainSpec C A)).pre x s0 ∗
        (memRegion (s0.sp - 17120#64) 12288 ∗ R) := by
    dsimp only [withLsCodeRoLoaded, createChainSpecX, createChainSpec] at hpre ⊢
    rw [hstk] at hpre
    exact Satisfies.mono (by bi_entail) hpre
  refine h.mono_outcome x (memRegion (s0.sp - 17120#64) 12288 ∗ R) s0 hpc hrun hpre' hsp (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, createChainSpecX, createChainSpec] at hq ⊢
    rw [hstk]
    exact Satisfies.mono (by bi_entail) hq
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeRoLoaded, createChainSpecX, createChainSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · dsimp only [withLsCodeRoLoaded, createChainSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, createChainSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem createChain_placed_ok_x [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks}
    (h_dh : HookSat H lsDhSym (withLsRet624 (withStack (diffieHellmanSpec C.X) 1808)))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked)
    (hext : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 54)
      (withLsCodeLoaded lsmpl (extractSpec C.F)))
    (hexp : subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (lsmpl.base 53)
      (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F)))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX C A)) :=
  subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic hext hexp h_dealloc)

end CryptoVerification.LibsignalTripleRatchet.Keys

