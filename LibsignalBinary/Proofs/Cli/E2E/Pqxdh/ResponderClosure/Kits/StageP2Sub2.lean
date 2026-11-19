/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty

/-!
# Stage P2 Substage P2.2

Proves 4 KiB-stacked CPS `stageP2_sub2_kits_ext` (`+0x0f14 → +0x1460` on `Ok`, or `+0x0f38` Arm 1
on `spkKit.getPoll` error) on `tripleRatchetProgAtExt img.base ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_sepWPp_weaken_eq {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog target s P' Q Qp)
    (hP : P = P' ∗ emp) :
    SepWPp prog target s P Q Qp := by
  rw [hP, sepConj_emp]; exact hw

theorem p2_sepWPp_pure_elim_frame {prog : Program} {target : BitVec 64} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (φ : Prop)
    (hP : P = ⌜φ⌝ ∗ F)
    (h : φ → SepWPp prog target s F Q Qp) :
    SepWPp prog target s P Q Qp := by
  rw [hP]; exact SepWPp.pure_elim h

private theorem extract56_8_0_s (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  ext i hi
  rw [BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_append]
  simp [hi]

private theorem extract56_8_hi_s (x y : BitVec 64) (k : Nat) (hk : 8 ≤ k) (hk2 : k + 8 ≤ 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  ext i hi
  have h1 : ¬ (k + i < 8) := by omega
  have h3 : k + i - 8 = k - 8 + i := by omega
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [BitVec.getLsbD_extractLsb', h1, h3]; omega

theorem bytes7_word_shift_std3 (a x y : BitVec 64) :
    bytes7At a (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (y.extractLsb' 0 56 ++ x.extractLsb' 56 8)) =
    (a ↦₆₄ x) ∗ bytes7At (a + 0x08#64) (y.extractLsb' 0 8) (y.extractLsb' 8 8)
      (y.extractLsb' 16 8) (y.extractLsb' 24 8) (y.extractLsb' 32 8) (y.extractLsb' 40 8) (y.extractLsb' 48 8) := by
  simp only [bytes7At, pointsTo64, extract56_8_0_s, extract56_8_hi_s x y 8 (by decide) (by decide),
    extract56_8_hi_s x y 16 (by decide) (by decide), extract56_8_hi_s x y 24 (by decide) (by decide),
    extract56_8_hi_s x y 32 (by decide) (by decide), extract56_8_hi_s x y 40 (by decide) (by decide),
    extract56_8_hi_s x y 48 (by decide) (by decide), extract56_8_hi_s x y 56 (by decide) (by decide),
    Nat.reduceSub, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem keyPair39_eq_words4_bytes7_std3 (a ik0 ik1 ik2 ik3 ik4 : BitVec 64) :
    bytes7At a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
    ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
    ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
    ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
    (a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
    bytes7At (a + 0x20#64) (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8)
      (ik4.extractLsb' 24 8) (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
  have h1 := bytes7_word_shift_std3 a ik0 ik1; have h2 := bytes7_word_shift_std3 (a + 0x08#64) ik1 ik2
  have h3 := bytes7_word_shift_std3 (a + 0x10#64) ik2 ik3; have h4 := bytes7_word_shift_std3 (a + 0x18#64) ik3 ik4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc, ← sepConj_assoc (bytes7At (a + 8#64) _ _ _ _ _ _ _), h2,
      sepConj_assoc, ← sepConj_assoc (bytes7At (a + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc, h4]

theorem keyPair32Hi_eq_words4_std3 (b ik4 ik5 ik6 ik7 : BitVec 64) :
    bytes7At b (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
    ((b + 0x07#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
    ((b + 0x0f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
    ((b + 0x17#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗ ((b + 0x1f#64) ↦₈ (ik7.extractLsb' 56 8)) =
    (b ↦₆₄ ik4) ∗ ((b + 0x08#64) ↦₆₄ ik5) ∗ ((b + 0x10#64) ↦₆₄ ik6) ∗ ((b + 0x18#64) ↦₆₄ ik7) := by
  have h1 := bytes7_word_shift_std3 b ik4 ik5; have h2 := bytes7_word_shift_std3 (b + 0x08#64) ik5 ik6
  have h3 := bytes7_word_shift_std3 (b + 0x10#64) ik6 ik7; have h4 := bytes7_byte_fold (b + 0x18#64) ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc, ← sepConj_assoc (bytes7At (b + 8#64) _ _ _ _ _ _ _), h2,
      sepConj_assoc, ← sepConj_assoc (bytes7At (b + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc, h4]

theorem words8_eq_keyPair64UnalignedAt_std3 (a ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 : BitVec 64) :
    ((a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
     ((a + 0x20#64) ↦₆₄ ik4) ∗ ((a + 0x28#64) ↦₆₄ ik5) ∗ ((a + 0x30#64) ↦₆₄ ik6) ∗ ((a + 0x38#64) ↦₆₄ ik7)) =
    keyPair64UnalignedAt a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8)
      (ik0.extractLsb' 24 8) (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8) (ik7.extractLsb' 56 8) := by
  have hlo := keyPair39_eq_words4_bytes7_std3 a ik0 ik1 ik2 ik3 ik4
  have hhi := keyPair32Hi_eq_words4_std3 (a + 0x20#64) ik4 ik5 ik6 ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhi; unfold keyPair64UnalignedAt; rw [← hhi]; symm
  calc _ = (bytes7At a (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
      ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
      ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
      ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
      ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8))) ∗
      (((a + 0x27#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
      ((a + 0x2f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
      ((a + 0x37#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
      ((a + 0x3f#64) ↦₈ (ik7.extractLsb' 56 8))) := by ac_rfl
    _ = _ := by rw [hlo]; ac_rfl

theorem memRegion64_entails_exists_keyPair64UnalignedAt_std3 (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ b4 : BitVec 8,
        ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8, ∃∗ b63 : BitVec 8,
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
  rw [ProofLib.memRegion_cells a 8 (by decide)]
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 => Entails.sepExists_elim
    fun u2 => Entails.sepExists_elim fun u3 => Entails.sepExists_elim fun u4 =>
    Entails.sepExists_elim fun u5 => Entails.sepExists_elim fun u6 => Entails.sepExists_elim fun u7 => ?_
  rw [words8_eq_keyPair64UnalignedAt_std3 a u0 u1 u2 u3 u4 u5 u6 u7]
  refine Entails.sepExists_right (u0.extractLsb' 0 8)
    (Entails.sepExists_right (u0.extractLsb' 8 8) (Entails.sepExists_right (u0.extractLsb' 16 8)
    (Entails.sepExists_right (u0.extractLsb' 24 8) (Entails.sepExists_right (u0.extractLsb' 32 8)
    (Entails.sepExists_right (u0.extractLsb' 40 8) (Entails.sepExists_right (u0.extractLsb' 48 8)
    (Entails.sepExists_right (u7.extractLsb' 56 8) (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

theorem coro798_64_entails_unaligned_std3 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x798#64) 64 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64, ∃∗ c63 : BitVec 8,
        bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
        ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗ ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
        ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗ ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
        ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗ ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
        ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗ ((coroPtr + 0x7d7#64) ↦₈ c63) := by
  rw [ProofLib.memRegion_cells (coroPtr + 0x798#64) 8 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
    Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 =>
    Entails.sepExists_elim fun u6 => Entails.sepExists_elim fun u7 => ?_
  have hw := words8_eq_keyPair64UnalignedAt_std3 (coroPtr + 0x798#64) u0 u1 u2 u3 u4 u5 u6 u7
  unfold keyPair64UnalignedAt at hw
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hw
  rw [hw]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _)))))))))))))))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
