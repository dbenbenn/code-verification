/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.LibsignalTripleRatchetProst -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.GrowOne
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of In-Image `<DecodeError>::push`

Verifies `<prost::error::DecodeError>::push`, dispatching to `grow_one` when
`len = cap` and appending a `(description, field)` entry.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack and `Vec` buffer lemmas for `<prost::error::DecodeError>::push` -/

@[expose] def pushStackPad (sp : BitVec 64) : SepProp :=
  memRegion (sp - 8192#64) 3920

theorem stackAt_push (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      pushStackPad sp ∗
      stackAt (sp - 176#64) allocHookStack ∗
      cells (sp - 176#64) 4 ∗
      cells (sp - 144#64) 8 ∗
      cells (sp - 80#64) 2 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_bottom sp 4272 3920 (by decide)
  change stackAt sp decodeErrorHookStack = pushStackPad sp ∗ stackAt sp 4272 at h1
  have h2 := stackAt_split_cells sp 4208 8 (by decide)
  change stackAt sp 4272 = stackAt (sp - 64#64) 4208 ∗ cells (sp - 64#64) 8 at h2
  have h3 := stackAt_split_cells (sp - 64#64) 4192 2 (by decide)
  have h3' : sp - 64#64 - BitVec.ofNat 64 (2 * 8) = sp - 80#64 := by bv_omega
  rw [h3'] at h3
  change stackAt (sp - 64#64) 4208 = stackAt (sp - 80#64) 4192 ∗ cells (sp - 80#64) 2 at h3
  have h4 := stackAt_split_cells (sp - 80#64) 4128 8 (by decide)
  have h4' : sp - 80#64 - BitVec.ofNat 64 (8 * 8) = sp - 144#64 := by bv_omega
  rw [h4'] at h4
  change stackAt (sp - 80#64) 4192 = stackAt (sp - 144#64) 4128 ∗ cells (sp - 144#64) 8 at h4
  have h5 := stackAt_split_cells (sp - 144#64) 4096 4 (by decide)
  have h5' : sp - 144#64 - BitVec.ofNat 64 (4 * 8) = sp - 176#64 := by bv_omega
  rw [h5'] at h5
  change stackAt (sp - 144#64) 4128 =
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 at h5
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, h3, h4, h5, hc8]
  ac_rfl

theorem arrayAt_stackEntryAt_replicate :
    ∀ (n : Nat) (ptr : BitVec 64), n * 32 ≤ 2 ^ 64 →
      arrayAt stackEntryAt 32 ptr (List.replicate n ()) = memRegion ptr (n * 32)
  | 0, ptr, _ => by
      simp only [List.replicate_zero, arrayAt, Nat.zero_mul]
      exact (memRegion_zero ptr).symm
  | n + 1, ptr, h => by
      have hn : n * 32 ≤ 2 ^ 64 := by omega
      have h1 : (n + 1) * 32 = 32 + n * 32 := by omega
      rw [List.replicate_succ, arrayAt, stackEntryAt, arrayAt_stackEntryAt_replicate n _ hn,
        h1, memRegion_split ptr 32 (n * 32) (by omega)]

theorem vecBuf_stackEntryAt_memRegion (A : RustAlloc) (k : Nat) (cap ptr : BitVec 64)
    (hle : k ≤ cap.toNat) (hbound : cap.toNat * 32 < 2 ^ 63) :
    A.live ptr (cap.toNat * 32) 8 ∗
      arrayAt stackEntryAt 32 ptr (List.replicate k ()) ∗
      memRegion (ptr + BitVec.ofNat 64 (k * 32)) ((cap.toNat - k) * 32) =
    A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) := by
  congr 1
  have hk : k * 32 ≤ 2 ^ 64 := by omega
  have hsplit : cap.toNat * 32 = k * 32 + (cap.toNat - k) * 32 := by
    have hsub : k + (cap.toNat - k) = cap.toNat := Nat.add_sub_of_le hle
    calc cap.toNat * 32 = (k + (cap.toNat - k)) * 32 := by rw [hsub]
      _ = k * 32 + (cap.toNat - k) * 32 := Nat.add_mul k (cap.toNat - k) 32
  rw [arrayAt_stackEntryAt_replicate k ptr hk, hsplit,
    ← memRegion_split ptr (k * 32) ((cap.toNat - k) * 32) (by omega)]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
    memRegion_split a 8 (8 + (8 + 8)) (by decide),
    memRegion_split (a + 8#64) 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem ofNat_lsl5_eq {n : Nat} (hn : n * 32 < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< 5) = BitVec.ofNat 64 (n * 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofNat_add_one_eq (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]

theorem memRegion_split_entry (ptr : BitVec 64) (n capNat : Nat)
    (hlt : n < capNat) (hbound : capNat * 32 < 2 ^ 63) :
    memRegion ptr (capNat * 32) =
      memRegion ptr (n * 32) ∗
      memRegion (ptr + (BitVec.ofNat 64 n <<< 5) + 32#64) ((capNat - (n + 1)) * 32) ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((ptr + (BitVec.ofNat 64 n <<< 5)) ↦₆₄ v3) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 8#64) ↦₆₄ v2) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 16#64) ↦₆₄ v1) ∗
        ((ptr + (BitVec.ofNat 64 n <<< 5) + 24#64) ↦₆₄ v0)) := by
  have hlsl : (BitVec.ofNat 64 n <<< 5) = BitVec.ofNat 64 (n * 32) := ofNat_lsl5_eq (by omega)
  have hsplit1 : capNat * 32 = n * 32 + (32 + (capNat - (n + 1)) * 32) := by
    have hsub : (n + 1) + (capNat - (n + 1)) = capNat := Nat.add_sub_of_le hlt
    calc capNat * 32 = ((n + 1) + (capNat - (n + 1))) * 32 := by rw [hsub]
      _ = (n + 1) * 32 + (capNat - (n + 1)) * 32 := Nat.add_mul (n + 1) (capNat - (n + 1)) 32
      _ = n * 32 + (32 + (capNat - (n + 1)) * 32) := by omega
  rw [hsplit1,
    memRegion_split ptr (n * 32) (32 + (capNat - (n + 1)) * 32) (by omega),
    memRegion_split (ptr + BitVec.ofNat 64 (n * 32)) 32 ((capNat - (n + 1)) * 32) (by omega),
    ← hlsl, memRegion_32_cells (ptr + (BitVec.ofNat 64 n <<< 5))]
  ac_rfl

theorem bv_sub_64_sub (sp : BitVec 64) :
    sp - 64#64 - 16#64 = sp - 80#64 ∧
    sp - 64#64 - 80#64 = sp - 144#64 ∧
    sp - 64#64 - 112#64 = sp - 176#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega⟩

/-! ## Verification of `<prost::error::DecodeError>::push` -/

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
