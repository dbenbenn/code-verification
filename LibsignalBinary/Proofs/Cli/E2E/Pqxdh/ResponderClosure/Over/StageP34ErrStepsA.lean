/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34Defs -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDrop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P3 and Stage P4 1-Element `previous_sessions` Error Drop Basic Blocks

Proves basic-block specifications for `+0x359c → retAddr`, dropping a 1-element `previous_sessions`
vector `prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]` on the Stage P3 / P4 error epilogue.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem prevVecAt_one_cap0_false (A : RustAlloc) (r q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r 0#64 q [enc] ⊢ ⌜False⌝ := by
  rw [prevVecAt_eq]
  unfold RustHeap.vecBuf
  rw [sepConj_left_comm]
  refine Entails.pure_left fun ⟨hlen, _, _⟩ => ?_
  nomatch hlen

theorem prevVecAt_one_drop_split_p34 (A : RustAlloc) (r cap q : BitVec 64)
    (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗
        HdrP r cap q 1#64 ∗
        A.live q (cap.toNat * 24) 8 ∗
        (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat) ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  refine Entails.trans (prevVecAt_one_drop_split A r cap q enc hcap) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
  exact Entails.of_eq (by ac_rfl)

theorem hdrP_coro_344_entails_368 (coroPtr prevCap prevPtr prevLen : BitVec 64) :
    HdrP (coroPtr + 0xe0#64) prevCap prevPtr prevLen ∗ memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 := by
  rw [hdrP_coro_eq]
  have h24 :
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ prevLen) ⊢
        memRegion (coroPtr + 0xe0#64) 24 := by
    rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 8 16 (by decide),
        ProofLib.memRegion_split (coroPtr + 0xe0#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  rw [ProofLib.memRegion_split (coroPtr + 0xe0#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left h24

theorem entails_replace_sub_p34 {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

theorem sepWP_exists_elim_p34 {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

theorem sepWP_pure_elim_p34 {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s P post) :
    SepWP prog pc s (⌜φ⌝ ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

theorem mul24_shift_eq {prevCap : BitVec 64} (_h : prevCap.toNat * 24 < 2 ^ 63) :
    ((prevCap + (prevCap <<< 1)) <<< 3) = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    ((prevCap + (prevCap <<< 1#64)) <<< 3#64) = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) ∧
    prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
  have hs : ((prevCap + (prevCap <<< 1)) <<< 3) = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  exact ⟨hs, hs, by bv_omega, by bv_omega⟩

/-! ## Stage P3 and Stage P4 Error Epilogue (`+0x359c → retAddr`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
