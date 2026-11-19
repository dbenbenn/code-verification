/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.StoreNew.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Prog -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP.Access
import LibsignalBinary.Proofs.CodeLayout

/-!
# GOT, `.data.rel.ro`, hook, and memory-splitting lemmas for `StoreNew`

Provides 64-bit little-endian byte-slice bridges, `hashmap_random_keys` hook lookup, and memory
decompositions for the 24-byte TLS cell, 48-byte `HashMap`, and 120-byte `InMemIdentityKeyStore`.
-/

public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem bytesLE_8_eq_unpack64 (v : BitVec 64) : Obj.bytesLE 8 v = unpack64 v := rfl

theorem pointsToBytesRO_bytesLE8_eq (a v : BitVec 64) :
    (a ↦ᵣ Obj.bytesLE 8 v) = (a ↦₆₄ᵣ v) := by
  rw [bytesLE_8_eq_unpack64, ← pointsTo64RO_eq_pointsToBytesRO]

theorem bytesLE8_length_le (w : BitVec 64) : (Obj.bytesLE 8 w).length ≤ 2 ^ 64 := by
  change 8 ≤ 2 ^ 64
  decide

open ProofLib.ProgramReflection in
theorem tripleRatchetExterns_randomKeys (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Rust.withPanics (tripleRatchetExterns C ctl abs) randomKeysName = abs randomKeysName := by
  rfl_kernel

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v : BitVec 64, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_48_eq_cells (out : BitVec 64) : memRegion out 48 = cells out 6 :=
  memRegion_cells out 6 (by decide)

theorem memRegion_120_split (out : BitVec 64) :
    memRegion out 120 =
      cells out 14 ∗ (∃∗ v : BitVec 32, (out + 112#64) ↦₃₂ v) ∗ memRegion (out + 116#64) 4 := by
  rw [show (120 : Nat) = 112 + (4 + 4) from rfl,
    memRegion_split out 112 8 (by decide),
    memRegion_cells out 14 (by decide),
    memRegion_split (out + 112#64) 4 4 (by decide),
    memRegion_four (out + 112#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem stackAt_32_eq_cells (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewFrame = cells (sp - 32#64) 4 := by
  simp only [stackAt, inMemSessionStoreNewFrame]
  exact memRegion_cells (sp - 32#64) 4 (by decide)

theorem stackAt_48_eq_cells (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewFrame = cells (sp - 48#64) 6 := by
  simp only [stackAt, inMemIdentityStoreNewFrame]
  exact memRegion_cells (sp - 48#64) 6 (by decide)

theorem stackAt_sessionStoreNew_split (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show inMemSessionStoreNewStack = extHookStack + 8 * 4 by decide]
  exact stackAt_split_cells sp extHookStack 4 (by decide)

theorem stackAt_identityStoreNew_split (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  rw [show inMemIdentityStoreNewStack = extHookStack + 8 * 6 by decide]
  exact stackAt_split_cells sp extHookStack 6 (by decide)

/-- The `i`-th 64-bit little-endian word of a byte list `bs`. -/
@[expose] def word64At (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  pack64 (bs.getD (8 * i + 0) 0#8) (bs.getD (8 * i + 1) 0#8)
    (bs.getD (8 * i + 2) 0#8) (bs.getD (8 * i + 3) 0#8)
    (bs.getD (8 * i + 4) 0#8) (bs.getD (8 * i + 5) 0#8)
    (bs.getD (8 * i + 6) 0#8) (bs.getD (8 * i + 7) 0#8)

theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take n) ∗
        ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop (off + n)) := by
  have hlen : ((bs.drop off).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  conv => lhs; rw [← List.take_append_drop n (bs.drop off), List.drop_drop]
  rw [pointsToBytes_append, hlen]

/-- Any 64-byte slice `a ↦ₛ bs` (`bs.length = 64`) decomposes into 8 consecutive 64-bit words. -/
theorem pointsToBytes_64_eq_words (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    (a ↦ₛ bs) =
      (a ↦₆₄ word64At bs 0) ∗
      ((a + 8#64) ↦₆₄ word64At bs 1) ∗
      ((a + 16#64) ↦₆₄ word64At bs 2) ∗
      ((a + 24#64) ↦₆₄ word64At bs 3) ∗
      ((a + 32#64) ↦₆₄ word64At bs 4) ∗
      ((a + 40#64) ↦₆₄ word64At bs 5) ∗
      ((a + 48#64) ↦₆₄ word64At bs 6) ∗
      ((a + 56#64) ↦₆₄ word64At bs 7) := by
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 8 (by omega),
      pointsToBytes_drop_split _ bs 8 8 (by omega),
      pointsToBytes_drop_split _ bs 16 8 (by omega),
      pointsToBytes_drop_split _ bs 24 8 (by omega),
      pointsToBytes_drop_split _ bs 32 8 (by omega),
      pointsToBytes_drop_split _ bs 40 8 (by omega),
      pointsToBytes_drop_split _ bs 48 8 (by omega),
      pointsToBytes_drop_split _ bs 56 8 (by omega)]
  have hdrop64 : bs.drop 64 = [] := by simp [h]
  rw [hdrop64, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 8 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 16 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 24 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 32 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 40 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 48 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 56 (by omega)]
  change _ = _
  simp only [word64At, Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- A zeroed 24-byte TLS block `(t ↦₆₄ 0#64) ∗ ((t + 8#64) ↦₆₄ 0#64) ∗ ((t + 16#64) ↦₆₄ 0#64)`
entails `tlsKeysRawAt t 0#64 0#64 0#8` (and hence `tlsKeysUninitAt t`). -/
theorem zeroWords_entails_tlsKeysRawAt (t : BitVec 64) :
    ((t ↦₆₄ 0#64) ∗ ((t + 8#64) ↦₆₄ 0#64) ∗ ((t + 16#64) ↦₆₄ 0#64)) ⊢
      tlsKeysRawAt t 0#64 0#64 0#8 := by
  unfold tlsKeysRawAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [pointsTo64_eq_pointsToBytes (t + 16#64) 0#64]
  have hu : unpack64 0#64 = 0#8 :: List.replicate 7 0#8 := rfl
  rw [hu, pointsToBytes_cons]
  have ha : t + 16#64 + 1#64 = t + 17#64 := by bv_arith
  rw [ha]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (t + 17#64) (List.replicate 7 0#8))

end CryptoVerification.E2E.StoreNew
