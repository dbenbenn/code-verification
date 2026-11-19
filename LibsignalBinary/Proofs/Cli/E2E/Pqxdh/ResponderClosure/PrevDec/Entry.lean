/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Entry (`+0x1ee8 → +0x216c`) of Inlined `SessionStructure::decode`

Verifies the 28-instruction entry block (`+0x1ee8..+0x1f54`) of inlined `SessionStructure::decode`
in `message_decrypt_prekey::<Coins>::{closure#0}` (`overDecEntry : OverDecEntryStmt`), initializing
`SessionStructure::default()` at `q + 0x930` and setting up the input slice cursor at `q + 0xbe8`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ prostSSGQAt prostSSGQAt_empty)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem SepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem enc_len_ofNat64_ne_zero {enc : List (BitVec 8)}
    (hne : enc ≠ []) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 enc.length ≠ 0#64 := by
  have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : enc.length < 2 ^ 64)] at hnat
  omega

private theorem overPrevElemAt_eq_of_encCap_ne_zero {A : RustAlloc}
    {prevCap prevPtr encCap encPtr : BitVec 64} {enc : List (BitVec 8)}
    (hcap : encCap ≠ 0) :
    overPrevElemAtExt A prevCap prevPtr encCap encPtr enc =
      overPrevElemRestExt A prevCap prevPtr encCap encPtr enc ∗ (encPtr ↦ₛ enc) := by
  unfold overPrevElemAtExt overPrevElemRestExt vecU8At
  simp only [hcap, ↓reduceIte]
  ac_rfl

private theorem overPrevElemAt_entails_of_ne_nil {A : RustAlloc}
    {prevCap prevPtr encCap encPtr : BitVec 64} {enc : List (BitVec 8)}
    (hne : enc ≠ []) :
    overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemRestExt A prevCap prevPtr encCap encPtr enc ∗ (encPtr ↦ₛ enc) := by
  by_cases hcap : encCap = 0
  · have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
    unfold overPrevElemAtExt vecU8At
    refine Entails.trans (Entails.of_eq (Q :=
      ⌜enc.length ≤ encCap.toNat ∧ encCap.toNat < 2 ^ 63 ∧ encPtr ≠ 0⌝ ∗
        (⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          A.live prevPtr (prevCap.toNat * 24) 8 ∗
          vecHeader prevPtr encCap encPtr (BitVec.ofNat 64 enc.length) ∗
          (if encCap = 0 then emp else
            A.live encPtr encCap.toNat 1 ∗ (encPtr ↦ₛ enc) ∗
              memRegion (encPtr + BitVec.ofNat 64 enc.length) (encCap.toNat - enc.length)) ∗
          memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24))) (by ac_rfl)) ?_
    refine Entails.pure_left fun hφ => False.elim ?_
    have hzero : encCap.toNat = 0 := by subst hcap; rfl
    omega
  · exact Entails.of_eq (overPrevElemAt_eq_of_encCap_ne_zero hcap)

private theorem SepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  exact h x R hm hL

private theorem memRegion_succ8_entry (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

/-- The 26 64-bit stack cells written by `+0x1ee8..+0x1f54`. -/
private def entryScratchCells (q : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
     w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : BitVec 64) : SepProp :=
  ((q + 0x920#64) ↦₆₄ w0) ∗ ((q + 0x928#64) ↦₆₄ w1) ∗
  ((q + 0x930#64) ↦₆₄ w2) ∗ ((q + 0x938#64) ↦₆₄ w3) ∗ ((q + 0x940#64) ↦₆₄ w4) ∗
  ((q + 0x948#64) ↦₆₄ w5) ∗ ((q + 0x950#64) ↦₆₄ w6) ∗ ((q + 0x958#64) ↦₆₄ w7) ∗
  ((q + 0x960#64) ↦₆₄ w8) ∗ ((q + 0x968#64) ↦₆₄ w9) ∗ ((q + 0x970#64) ↦₆₄ w10) ∗
  ((q + 0x978#64) ↦₆₄ w11) ∗ ((q + 0x980#64) ↦₆₄ w12) ∗ ((q + 0x988#64) ↦₆₄ w13) ∗
  ((q + 0x990#64) ↦₆₄ w14) ∗ ((q + 0x998#64) ↦₆₄ w15) ∗ ((q + 0x9a0#64) ↦₆₄ w16) ∗
  ((q + 0x9a8#64) ↦₆₄ w17) ∗ ((q + 0x9b0#64) ↦₆₄ w18) ∗ ((q + 0x9b8#64) ↦₆₄ w19) ∗
  ((q + 0x9c0#64) ↦₆₄ w20) ∗ ((q + 0xa28#64) ↦₆₄ w21) ∗ ((q + 0xa58#64) ↦₆₄ w22) ∗
  ((q + 0xa78#64) ↦₆₄ w23) ∗ ((q + 0xa80#64) ↦₆₄ w24) ∗ ((q + 0xbe8#64) ↦₆₄ w25)

/-- Untouched sub-regions of `overDecScratchPre q`. -/
private def entryScratchKeep (q : BitVec 64) : SepProp :=
  memRegion (q + 0x9c8#64) 96 ∗ memRegion (q + 0xa30#64) 40 ∗
  memRegion (q + 0xa60#64) 24 ∗ memRegion (q + 0xa88#64) 8 ∗
  memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbf0#64) 128

set_option maxHeartbeats 400000 in
private theorem overDecScratchPre_split (q : BitVec 64) :
    overDecScratchPre q =
      (∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
       ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
       ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
       ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
       ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        entryScratchCells q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
      entryScratchKeep q := by
  unfold overDecScratchPre entryScratchKeep
  rw [memRegion_split (q + 0x990#64) 56 200 (by decide),
      memRegion_split (q + 0x990#64 + 56#64) 96 104 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64) 8 96 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64) 40 56 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64) 8 48 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 24 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 16 8 (by decide),
      memRegion_split (q + 0xbe8#64) 8 128 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1; arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (q + 0xa28#64),
      ProofLib.memRegion_eight (q + 0xa58#64),
      ProofLib.memRegion_eight (q + 0xbe8#64)]
  conv_lhs =>
    arg 2; arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  unfold entryScratchCells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

/-- The 23 `SessionStructure::default()` cells at `q + 0x930`. -/
private def ssRawCells_entry (q : BitVec 64) : SepProp :=
  (((q + 0x930#64) ↦₆₄ 0#64) ∗ ((q + 0x938#64) ↦₆₄ 1#64) ∗ ((q + 0x940#64) ↦₆₄ 0#64)) ∗
  (((q + 0x948#64) ↦₆₄ 0#64) ∗ ((q + 0x950#64) ↦₆₄ 1#64) ∗ ((q + 0x958#64) ↦₆₄ 0#64)) ∗
  (((q + 0x960#64) ↦₆₄ 0#64) ∗ ((q + 0x968#64) ↦₆₄ 1#64) ∗ ((q + 0x970#64) ↦₆₄ 0#64)) ∗
  (((q + 0x978#64) ↦₆₄ 0#64) ∗ ((q + 0x980#64) ↦₆₄ 8#64) ∗ ((q + 0x988#64) ↦₆₄ 0#64)) ∗
  (((q + 0x990#64) ↦₆₄ 0#64) ∗ ((q + 0x998#64) ↦₆₄ 1#64) ∗ ((q + 0x9a0#64) ↦₆₄ 0#64)) ∗
  (((q + 0x9a8#64) ↦₆₄ 0#64) ∗ ((q + 0x9b0#64) ↦₆₄ 1#64) ∗ ((q + 0x9b8#64) ↦₆₄ 0#64)) ∗
  ((q + 0x9c0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa28#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa58#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa78#64) ↦₆₄ 0#64) ∗
  ((q + 0xa80#64) ↦₆₄ 0#64)

private theorem empty_vecU8_intro_entry (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]
  exact Entails.pure_right hp (Entails.refl _)

private theorem empty_vecChainG_intro_entry (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun c a => prostChainGAt A a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
    arrayAt (fun c a => prostChainGAt A a c) 104 8#64 [] ∗
    memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
      (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ ∗
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]
  exact Entails.pure_right hp (Entails.refl _)

private theorem pointsTo64_zero_split32_entry (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private theorem prostSSGQAt_empty_intro_entry (A : RustAlloc) (q : BitVec 64) :
    ssRawCells_entry q ∗
      memRegion (q + 0x9c8#64) 96 ∗
      memRegion (q + 0xa30#64) 40 ∗
      memRegion (q + 0xa60#64) 24 ⊢
      prostSSGQAt A (q + 0x930#64) SSGQ.empty := by
  rw [show SSGQ.empty = ⟨SSG.empty, ExtraGQ.empty⟩ from rfl,
      prostSSGQAt_empty A (q + 0x930#64) SSG.empty]
  unfold ssRawCells_entry prostSSGAt SSG.empty
  dsimp only
  have h1 := empty_vecU8_intro_entry A (q + 0x930#64)
  have h2 := empty_vecU8_intro_entry A (q + 0x930#64 + 0x18#64)
  have h3 := empty_vecU8_intro_entry A (q + 0x930#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_entry A (q + 0x930#64 + 0x48#64)
  have h5 := empty_vecU8_intro_entry A (q + 0x930#64 + 0x60#64)
  have h6 := empty_vecU8_intro_entry A (q + 0x930#64 + 0x78#64)
  have hnone : (0xffffffffffffffff#64 : BitVec 64) = noneCap := rfl
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_entry (q + 0xa78#64), hnone]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

private theorem sliceCursorAfter_self (slot ptr : BitVec 64) (bs : List (BitVec 8)) :
    (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) =
      Prost.sliceCursorAfter slot ptr bs bs := by
  unfold Prost.sliceCursorAfter
  rw [Nat.sub_self, show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
