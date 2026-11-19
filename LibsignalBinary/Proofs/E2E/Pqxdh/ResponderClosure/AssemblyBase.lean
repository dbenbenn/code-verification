/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OneKeyVtables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.OneKeyStore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.SepLogic.WP
public import ProofLib
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Vtable Bundles and `OneKeyStore` Error-Path Closures for `message_decrypt_prekey::{closure#0}`

Provides `.rodata` `"decryption failed"` and `.data.rel.ro` store-vtable introduction bundles,
error-path contracts for the `OneKeyStore` prekey poll closures (`0x75b08`, `0x75c04`, `0x75d9c`),
and callee-saved GPR preservation helpers across `message_decrypt_prekey::{closure#0}` stages.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
theorem cond_ne_subs32_of_ne {a b : BitVec 32} (h : a ≠ b) :
    ConditionHolds .NE (subsPState32 a b) = true := by
  rw [conditionHolds_ne_subsPState32, bne_iff_ne]
  exact h

theorem cond_eq_adds64_of_ne_neg1' {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds .EQ (addsPState64 w 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  apply h
  have h2 := congrArg (· - 1#64) heq
  simpa [BitVec.add_sub_cancel] using h2

theorem stackAt_208_cells (sp : BitVec 64) :
    stackAt sp 208 = cells (sp - 208#64) 26 := by
  unfold stackAt
  exact ProofLib.memRegion_cells (sp - 208#64) 26 (by decide)

theorem stackAt_80_cells (sp : BitVec 64) :
    stackAt sp 80 = cells (sp - 80#64) 10 := by
  unfold stackAt
  exact ProofLib.memRegion_cells (sp - 80#64) 10 (by decide)

local macro "cells_unfold_26" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) (disch := decide) only [
    ProofLib.cells_sub_succ, Nat.reduceSub, ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at *)

theorem words5_pack_w32_4w64_w32 (p : BitVec 64) (lo : BitVec 32)
    (u0 u1 u2 u3 : BitVec 64) (hi : BitVec 32) :
    ((p + 16#64) ↦₃₂ lo) ∗ ((p + 20#64) ↦₆₄ u0) ∗ ((p + 28#64) ↦₆₄ u1) ∗
        ((p + 36#64) ↦₆₄ u2) ∗ ((p + 44#64) ↦₆₄ u3) ∗ ((p + 52#64) ↦₃₂ hi) =
      ((p + 16#64) ↦₆₄ (u0.extractLsb' 0 32 ++ lo)) ∗
        ((p + 24#64) ↦₆₄ (u1.extractLsb' 0 32 ++ u0.extractLsb' 32 32)) ∗
        ((p + 32#64) ↦₆₄ (u2.extractLsb' 0 32 ++ u1.extractLsb' 32 32)) ∗
        ((p + 40#64) ↦₆₄ (u3.extractLsb' 0 32 ++ u2.extractLsb' 32 32)) ∗
        ((p + 48#64) ↦₆₄ (hi ++ u3.extractLsb' 32 32)) := by
  rw [← pointsTo32_pair (p + 16#64), ← pointsTo32_pair (p + 24#64),
      ← pointsTo32_pair (p + 32#64), ← pointsTo32_pair (p + 40#64),
      ← pointsTo32_pair (p + 48#64)]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem words5_pack_w32_4w64_w32_assoc (p : BitVec 64) (lo : BitVec 32)
    (u0 u1 u2 u3 : BitVec 64) (hi : BitVec 32) (R : SepProp) :
    ((p + 16#64) ↦₃₂ lo) ∗ ((p + 20#64) ↦₆₄ u0) ∗ ((p + 28#64) ↦₆₄ u1) ∗
        ((p + 36#64) ↦₆₄ u2) ∗ ((p + 44#64) ↦₆₄ u3) ∗ ((p + 52#64) ↦₃₂ hi) ∗ R =
      ((p + 16#64) ↦₆₄ (u0.extractLsb' 0 32 ++ lo)) ∗
        ((p + 24#64) ↦₆₄ (u1.extractLsb' 0 32 ++ u0.extractLsb' 32 32)) ∗
        ((p + 32#64) ↦₆₄ (u2.extractLsb' 0 32 ++ u1.extractLsb' 32 32)) ∗
        ((p + 40#64) ↦₆₄ (u3.extractLsb' 0 32 ++ u2.extractLsb' 32 32)) ∗
        ((p + 48#64) ↦₆₄ (hi ++ u3.extractLsb' 32 32)) ∗ R := by
  have h := congrArg (· ∗ R) (words5_pack_w32_4w64_w32 p lo u0 u1 u2 u3 hi)
  simpa only [sepConj_assoc] using h

structure GetSpkClosureErrArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  retPtr : BitVec 64
  reqId : BitVec 32
  storeId : BitVec 32
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 64
  u38 : BitVec 64
  u40 : BitVec 64
  u48 : BitVec 64
  u50 : BitVec 64

/-- Error-path contract for `<OneKeyStore as SignedPreKeyStore>::get_signed_pre_key::{closure#0}`
(`0x75b08`) when `storeId ≠ reqId`: writes `(-1, 0x800000000000000e#64)` (`InvalidSignedPreKeyId`)
at `retPtr + 0x0..0x10`, marks `[boxPtr + 0xc] = 1#8`, and returns without heap allocation. -/
@[expose] def oneKeyGetSpkClosureErrSpec : Spec GetSpkClosureErrArgs where
  pre := fun x s =>
    ⌜x.storeId ≠ x.reqId ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp 208 ∗
    oneKeyBox16At x.boxPtr x.storePtr x.reqId 0#8 ∗
    ((x.storePtr + 0x50#64) ↦₃₂ x.storeId) ∗
    spkPollOutUninitAt x.retPtr x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
    ∃∗ w10 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      stackAt s0.sp 208 ∗
      oneKeyBox16At x.boxPtr x.storePtr x.reqId 1#8 ∗
      ((x.storePtr + 0x50#64) ↦₃₂ x.storeId) ∗
      (x.retPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.retPtr + 0x08#64) ↦₆₄ 0x800000000000000e#64) ∗
      ((x.retPtr + 0x10#64) ↦₆₄ w2) ∗
      ((x.retPtr + 0x18#64) ↦₆₄ w3) ∗
      ((x.retPtr + 0x20#64) ↦₆₄ w4) ∗
      ((x.retPtr + 0x28#64) ↦₆₄ w5) ∗
      ((x.retPtr + 0x30#64) ↦₆₄ w6) ∗
      ((x.retPtr + 0x38#64) ↦₆₄ w7) ∗
      ((x.retPtr + 0x40#64) ↦₆₄ w8) ∗
      ((x.retPtr + 0x48#64) ↦₆₄ w9) ∗
      ((x.retPtr + 0x50#64) ↦₆₄ w10)

/-- Error-path contract for `<OneKeyStore as KyberPreKeyStore>::get_kyber_pre_key::{closure#0}`
(`0x75c04`) when `storeId ≠ reqId`: writes `(-1, 0x800000000000000f#64)` (`InvalidKyberPreKeyId`)
at `retPtr + 0x0..0x10`, marks `[boxPtr + 0xc] = 1#8`, and returns without heap allocation. -/
@[expose] def oneKeyGetKyberClosureErrSpec : Spec GetSpkClosureErrArgs where
  pre := fun x s =>
    ⌜x.storeId ≠ x.reqId ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp 208 ∗
    oneKeyBox16At x.boxPtr x.storePtr x.reqId 0#8 ∗
    ((x.storePtr + 0xa8#64) ↦₃₂ x.storeId) ∗
    spkPollOutUninitAt x.retPtr x.u0 x.u8 x.u10 x.u18 x.u20 x.u28 x.u30 x.u38 x.u40 x.u48 x.u50
  post := fun x s0 sf =>
    ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64,
    ∃∗ w10 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      stackAt s0.sp 208 ∗
      oneKeyBox16At x.boxPtr x.storePtr x.reqId 1#8 ∗
      ((x.storePtr + 0xa8#64) ↦₃₂ x.storeId) ∗
      (x.retPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.retPtr + 0x08#64) ↦₆₄ 0x800000000000000f#64) ∗
      ((x.retPtr + 0x10#64) ↦₆₄ w2) ∗
      ((x.retPtr + 0x18#64) ↦₆₄ w3) ∗
      ((x.retPtr + 0x20#64) ↦₆₄ w4) ∗
      ((x.retPtr + 0x28#64) ↦₆₄ w5) ∗
      ((x.retPtr + 0x30#64) ↦₆₄ w6) ∗
      ((x.retPtr + 0x38#64) ↦₆₄ w7) ∗
      ((x.retPtr + 0x40#64) ↦₆₄ w8) ∗
      ((x.retPtr + 0x48#64) ↦₆₄ w9) ∗
      ((x.retPtr + 0x50#64) ↦₆₄ w10)

structure GetPreKeyClosureErrArgs where
  boxPtr : BitVec 64
  storePtr : BitVec 64
  retPtr : BitVec 64
  reqId : BitVec 32
  storeId : BitVec 32
  opkPubCap : BitVec 64
  u0 : BitVec 64
  u8 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u20 : BitVec 64
  u28 : BitVec 64
  u30 : BitVec 32

/-- Error-path contract for `<OneKeyStore as PreKeyStore>::get_pre_key::{closure#0}` (`0x75d9c`)
when `k.opk = none` (`opkPubCap = 0xffffffffffffffff#64`): writes `(-1, 0x800000000000000d#64)`
(`InvalidPreKeyId`) at `retPtr + 0x0..0x10`, marks `[boxPtr + 0xc] = 1#8`, and returns. -/
@[expose] def oneKeyGetPreKeyClosureNoneErrSpec : Spec GetPreKeyClosureErrArgs where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp 80 ∗
    oneKeyBox16At x.boxPtr x.storePtr x.reqId 0#8 ∗
    ((x.storePtr + 0xb0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (x.retPtr ↦₆₄ x.u0) ∗
    ((x.retPtr + 0x08#64) ↦₆₄ x.u8) ∗
    ((x.retPtr + 0x10#64) ↦₆₄ x.u10) ∗
    ((x.retPtr + 0x18#64) ↦₆₄ x.u18) ∗
    ((x.retPtr + 0x20#64) ↦₆₄ x.u20) ∗
    ((x.retPtr + 0x28#64) ↦₆₄ x.u28) ∗
    ((x.retPtr + 0x30#64) ↦₃₂ x.u30)
  post := fun x s0 sf =>
    ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ w6 : BitVec 32,
      ⌜sf.trace = s0.trace⌝ ∗
      stackAt s0.sp 80 ∗
      oneKeyBox16At x.boxPtr x.storePtr x.reqId 1#8 ∗
      ((x.storePtr + 0xb0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (x.retPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.retPtr + 0x08#64) ↦₆₄ 0x800000000000000d#64) ∗
      ((x.retPtr + 0x10#64) ↦₆₄ w2) ∗
      ((x.retPtr + 0x18#64) ↦₆₄ w3) ∗
      ((x.retPtr + 0x20#64) ↦₆₄ w4) ∗
      ((x.retPtr + 0x28#64) ↦₆₄ w5) ∗
      ((x.retPtr + 0x30#64) ↦₃₂ w6)

/-- Error-path contract for `<OneKeyStore as PreKeyStore>::get_pre_key::{closure#0}` (`0x75d9c`)
when `opkPubCap ≠ 0xffffffffffffffff#64 ∧ storeId ≠ reqId`: writes `(-1, 0x800000000000000d#64)`
(`InvalidPreKeyId`) at `retPtr + 0x0..0x10`, marks `[boxPtr + 0xc] = 1#8`, and returns. -/
@[expose] def oneKeyGetPreKeyClosureMismatchErrSpec : Spec GetPreKeyClosureErrArgs where
  pre := fun x s =>
    ⌜x.opkPubCap ≠ 0xffffffffffffffff#64 ∧
      x.storeId ≠ x.reqId ∧
      s.readReg64 .x0 = x.boxPtr ∧
      s.readReg64 .x8 = x.retPtr⌝ ∗
    stackAt s.sp 80 ∗
    oneKeyBox16At x.boxPtr x.storePtr x.reqId 0#8 ∗
    ((x.storePtr + 0xb0#64) ↦₆₄ x.opkPubCap) ∗
    ((x.storePtr + 0xe0#64) ↦₃₂ x.storeId) ∗
    (x.retPtr ↦₆₄ x.u0) ∗
    ((x.retPtr + 0x08#64) ↦₆₄ x.u8) ∗
    ((x.retPtr + 0x10#64) ↦₆₄ x.u10) ∗
    ((x.retPtr + 0x18#64) ↦₆₄ x.u18) ∗
    ((x.retPtr + 0x20#64) ↦₆₄ x.u20) ∗
    ((x.retPtr + 0x28#64) ↦₆₄ x.u28) ∗
    ((x.retPtr + 0x30#64) ↦₃₂ x.u30)
  post := fun x s0 sf =>
    ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ w6 : BitVec 32,
      ⌜sf.trace = s0.trace⌝ ∗
      stackAt s0.sp 80 ∗
      oneKeyBox16At x.boxPtr x.storePtr x.reqId 1#8 ∗
      ((x.storePtr + 0xb0#64) ↦₆₄ x.opkPubCap) ∗
      ((x.storePtr + 0xe0#64) ↦₃₂ x.storeId) ∗
      (x.retPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.retPtr + 0x08#64) ↦₆₄ 0x800000000000000d#64) ∗
      ((x.retPtr + 0x10#64) ↦₆₄ w2) ∗
      ((x.retPtr + 0x18#64) ↦₆₄ w3) ∗
      ((x.retPtr + 0x20#64) ↦₆₄ w4) ∗
      ((x.retPtr + 0x28#64) ↦₆₄ w5) ∗
      ((x.retPtr + 0x30#64) ↦₃₂ w6)

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_subs32_4_0 :
    ConditionHolds CondCode.EQ (subsPState32 4#32 0#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs32_4_4 :
    ConditionHolds CondCode.NE (subsPState32 4#32 4#32) = false := by
  simp only [ConditionHolds, subsPState32]; decide

theorem cond_ne_subs32_4_of_ne {v : BitVec 32} (h : v ≠ 4#32) :
    ConditionHolds CondCode.NE (subsPState32 4#32 v) = true := by
  rw [conditionHolds_ne_subsPState32, bne_iff_ne]
  exact Ne.symm h

/-- Callee-saved GPR preservation (`x19`–`x29`) across `decryptPrekeyClosure` stages,
with a 12th `True` conjunct matching the shape of `CalleeSavedPreserved`. -/
@[expose] def ClosureCalleeSaved (s0 sf : State) : Prop :=
  sf.readReg64 .x19 = s0.readReg64 .x19 ∧
  sf.readReg64 .x20 = s0.readReg64 .x20 ∧
  sf.readReg64 .x21 = s0.readReg64 .x21 ∧
  sf.readReg64 .x22 = s0.readReg64 .x22 ∧
  sf.readReg64 .x23 = s0.readReg64 .x23 ∧
  sf.readReg64 .x24 = s0.readReg64 .x24 ∧
  sf.readReg64 .x25 = s0.readReg64 .x25 ∧
  sf.readReg64 .x26 = s0.readReg64 .x26 ∧
  sf.readReg64 .x27 = s0.readReg64 .x27 ∧
  sf.readReg64 .x28 = s0.readReg64 .x28 ∧
  sf.readReg64 .fp = s0.readReg64 .fp ∧
  True

end CryptoVerification.E2E.Pqxdh.ResponderClosure
