/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.StoreNew.RoData -- proof-setup: allow-public-import
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Proofs for `RandomState::new` and `HashMap::new` TLS lazy initialization

Proves base-rebased and image-level contracts for `<InMemSignedPreKeyStore>::new` /
`<InMemSessionStore>::new` (`0x127d8`) and `<InMemIdentityKeyStore>::new` (`0x0c238`) across both
initialized (`tag = 1`) and uninitialized (`tag ≠ 1`) TLS `KEYS` states.
-/

public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PreSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end PreSimp

/-! ## `ADRP` page-resolution and SIMD extract helpers -/

theorem memRegion_48_unfold (out : BitVec 64) :
    memRegion out 48 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗ ((out + 16#64) ↦₆₄ v2) ∗
        ((out + 24#64) ↦₆₄ v3) ∗ ((out + 32#64) ↦₆₄ v4) ∗ ((out + 40#64) ↦₆₄ v5) := by
  rw [memRegion_48_eq_cells]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem emptyHashMapAt_unfold (ctrlPtr out k0 k1 : BitVec 64) :
    emptyHashMapAt ctrlPtr out k0 k1 =
      (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
      ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64) ∗
      ((out + 32#64) ↦₆₄ k0) ∗ ((out + 40#64) ↦₆₄ k1) := by
  simp only [emptyHashMapAt, emptyRawTableAt, randomStateAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem stackAt_sessionStoreNew_eq (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - BitVec.ofNat 64 32) 4 := by
  rw [show inMemSessionStoreNewStack = extHookStack + 8 * 4 from rfl]
  exact stackAt_split_cells sp extHookStack 4 (by decide)

theorem memRegion_120_unfold (out : BitVec 64) :
    memRegion out 120 =
      ∃∗ v14 : BitVec 32,
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
      ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
      ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
      ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗ ((out + 16#64) ↦₆₄ v2) ∗
        ((out + 24#64) ↦₆₄ v3) ∗ ((out + 32#64) ↦₆₄ v4) ∗ ((out + 40#64) ↦₆₄ v5) ∗
        ((out + 48#64) ↦₆₄ v6) ∗ ((out + 56#64) ↦₆₄ v7) ∗ ((out + 64#64) ↦₆₄ v8) ∗
        ((out + 72#64) ↦₆₄ v9) ∗ ((out + 80#64) ↦₆₄ v10) ∗ ((out + 88#64) ↦₆₄ v11) ∗
        ((out + 96#64) ↦₆₄ v12) ∗ ((out + 104#64) ↦₆₄ v13) ∗
        ((out + 112#64) ↦₃₂ v14) ∗ memRegion (out + 116#64) 4 := by
  rw [memRegion_120_split]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem emptyIdentityKeyStoreAt_unfold (ctrlPtr out k0 k1 : BitVec 64)
    {kpBytes : List (BitVec 8)} (regId : BitVec 32) (hlen : kpBytes.length = 64) :
    emptyIdentityKeyStoreAt ctrlPtr out k0 k1 kpBytes regId =
      (out ↦₆₄ ctrlPtr) ∗ ((out + 8#64) ↦₆₄ 0#64) ∗
      ((out + 16#64) ↦₆₄ 0#64) ∗ ((out + 24#64) ↦₆₄ 0#64) ∗
      ((out + 32#64) ↦₆₄ k0) ∗ ((out + 40#64) ↦₆₄ k1) ∗
      ((out + 48#64) ↦₆₄ word64At kpBytes 0) ∗
      ((out + 56#64) ↦₆₄ word64At kpBytes 1) ∗
      ((out + 64#64) ↦₆₄ word64At kpBytes 2) ∗
      ((out + 72#64) ↦₆₄ word64At kpBytes 3) ∗
      ((out + 80#64) ↦₆₄ word64At kpBytes 4) ∗
      ((out + 88#64) ↦₆₄ word64At kpBytes 5) ∗
      ((out + 96#64) ↦₆₄ word64At kpBytes 6) ∗
      ((out + 104#64) ↦₆₄ word64At kpBytes 7) ∗
      ((out + 112#64) ↦₃₂ regId) ∗
      memRegion (out + 116#64) 4 := by
  simp only [emptyIdentityKeyStoreAt, emptyHashMapAt_unfold,
    pointsToBytes_64_eq_words (out + 48#64) hlen,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem stackAt_identityStoreNew_eq (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - BitVec.ofNat 64 48) 6 := by
  rw [show inMemIdentityStoreNewStack = extHookStack + 8 * 6 from rfl]
  exact stackAt_split_cells sp extHookStack 6 (by decide)

theorem memRegion_sepConj_pure (a : BitVec 64) (n : Nat) (φ : Prop) (Q : SepProp) :
    memRegion a n ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (memRegion a n ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm (memRegion a n) ⌜φ⌝, sepConj_assoc]

theorem pointsToBytes_sepConj_pure (a : BitVec 64) (bs : List (BitVec 8)) (φ : Prop) (Q : SepProp) :
    (a ↦ₛ bs) ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ ((a ↦ₛ bs) ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm (a ↦ₛ bs) ⌜φ⌝, sepConj_assoc]

theorem stackAt_add_eq (sp : BitVec 64) (n k : Nat) (h : n + k ≤ 2 ^ 64) :
    stackAt sp (k + n) =
      stackAt sp k ∗ stackAt (sp - BitVec.ofNat 64 k) n := by
  rw [Nat.add_comm k n, sepConj_comm]
  simp only [stackAt]
  rw [memRegion_split _ n k h]
  have e1 : sp - BitVec.ofNat 64 (n + k) = sp - BitVec.ofNat 64 k - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + k) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 k := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem stackAt_sessionStoreNew_frame_split (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt sp inMemSessionStoreNewFrame ∗ stackAt (sp - 32#64) extHookStack :=
  stackAt_add_eq sp extHookStack inMemSessionStoreNewFrame (by decide)

theorem stackAt_identityStoreNew_frame_split (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt sp inMemIdentityStoreNewFrame ∗ stackAt (sp - 48#64) extHookStack :=
  stackAt_add_eq sp extHookStack inMemIdentityStoreNewFrame (by decide)

end CryptoVerification.E2E.StoreNew

