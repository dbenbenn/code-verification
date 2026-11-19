/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.IsTrusted
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreEmptyHelpers
import LibsignalBinary.Proofs.E2E.InMem.IdentityKeyStoreImpl.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Empty-Table `InMemSessionStore` and `InMemIdentityKeyStore` Poll Closures

Proves `subroutine_ok` for the empty-table (`emptyTableAt`) fast paths of
`InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`) and
`InMemSessionStore::load_session::{closure#0}` (`0x08ce4`), together with
`get_identity_key_pair` (`0x2de88`, `0x07b34`), `get_local_registration_id` (`0x2ded4`, `0x07b7c`),
and unaligned 64-byte `KeyPair` repack helpers.
-/

public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
open CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.IsTrusted
open CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_sp_storeEmpty (s : Arm64.State) (v : BitVec 64) :
    (s.writeReg64 .sp v).sp = v := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_storeEmpty (s : Arm64.State) (pc : BitVec 64) (m : Memory)
  (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

/-! ## 1. `is_trusted_identity::{closure#0}` (`0x079c4`) on `emptyTableAt` -/

/-- Ghost parameters for `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`)
on an empty table (`emptyTableAt`). -/
structure IsTrustedIdentityEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64
  qKeyPtr : BitVec 64
  direction : BitVec 8

/-- Ghost parameters for `InMemSessionStore::load_session::{closure#0}` (`0x08ce4`)
on an empty table (`emptyTableAt`). -/
structure LoadSessionEmptyGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  base : BitVec 64
  mp : BitVec 64
  k0 : BitVec 64
  k1 : BitVec 64
  qAddrPtr : BitVec 64

open ProofLib.ProgramReflection
open CryptoVerification.E2E.InMem.IdentityKeyStoreImpl

abbrev getIdentityKeyPairClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::\
    storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"

abbrev getLocalRegistrationIdClosureName : String :=
  "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::\
    storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}"

/-- 16-byte boxed future for `get_identity_key_pair` and `get_local_registration_id`:
`[self, state : u8, 7 uninitialized bytes]`. -/
@[expose] def inMemId16BoxAt (box self : BitVec 64) (st : BitVec 8) : SepProp :=
  (box ↦₆₄ self) ∗ ((box + 8#64) ↦₈ st) ∗ memRegion (box + 9#64) 7

theorem inMemId16BoxAt_memRegion (box self : BitVec 64) (st : BitVec 8) :
    inMemId16BoxAt box self st ⊢ memRegion box 16 := by
  unfold inMemId16BoxAt
  rw [show (16 : Nat) = 8 + (1 + 7) from rfl,
    memRegion_split box 8 8 (by decide),
    memRegion_split (box + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

private theorem memRegion_16_id_box (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

/-- Stack budget for `get_identity_key_pair` and `get_local_registration_id` shims
(`allocHookStack + 32`). -/
abbrev inMemId16ShimStack : Nat := allocHookStack + 32

private theorem stackAt_inMemId16Shim (sp : BitVec 64) :
    stackAt sp inMemId16ShimStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem sepWPp_pure_mid_storeEmpty {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {A B C : SepProp} {φ : Prop} {Q Qp : Arm64.State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

structure GetIdentityKeyPairPollGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  self : BitVec 64
  ik0 : BitVec 64
  ik1 : BitVec 64
  ik2 : BitVec 64
  ik3 : BitVec 64
  ik4 : BitVec 64
  ik5 : BitVec 64
  ik6 : BitVec 64
  ik7 : BitVec 64
  b_sret0 : BitVec 8
  u0 : BitVec 64
  u1 : BitVec 64
  u2 : BitVec 64
  u3 : BitVec 64
  u4 : BitVec 64
  u5 : BitVec 64
  u6 : BitVec 64
  u7 : BitVec 64

/-- Specification of `<InMemIdentityKeyStore as
IdentityKeyStore>::get_identity_key_pair::{closure#0}` (`0x07b34`). -/
@[expose] def getIdentityKeyPairPollSpec : Spec GetIdentityKeyPairPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 0#8) ∗
      ((x.self + 0x30#64) ↦₆₄ x.ik0) ∗ ((x.self + 0x38#64) ↦₆₄ x.ik1) ∗
      ((x.self + 0x40#64) ↦₆₄ x.ik2) ∗ ((x.self + 0x48#64) ↦₆₄ x.ik3) ∗
      ((x.self + 0x50#64) ↦₆₄ x.ik4) ∗ ((x.self + 0x58#64) ↦₆₄ x.ik5) ∗
      ((x.self + 0x60#64) ↦₆₄ x.ik6) ∗ ((x.self + 0x68#64) ↦₆₄ x.ik7) ∗
      (x.sret ↦₈ x.b_sret0) ∗
      ((x.sret + 0x01#64) ↦₆₄ x.u0) ∗ ((x.sret + 0x09#64) ↦₆₄ x.u1) ∗
      ((x.sret + 0x11#64) ↦₆₄ x.u2) ∗ ((x.sret + 0x19#64) ↦₆₄ x.u3) ∗
      ((x.sret + 0x21#64) ↦₆₄ x.u4) ∗ ((x.sret + 0x29#64) ↦₆₄ x.u5) ∗
      ((x.sret + 0x31#64) ↦₆₄ x.u6) ∗ ((x.sret + 0x39#64) ↦₆₄ x.u7)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 1#8) ∗
      ((x.self + 0x30#64) ↦₆₄ x.ik0) ∗ ((x.self + 0x38#64) ↦₆₄ x.ik1) ∗
      ((x.self + 0x40#64) ↦₆₄ x.ik2) ∗ ((x.self + 0x48#64) ↦₆₄ x.ik3) ∗
      ((x.self + 0x50#64) ↦₆₄ x.ik4) ∗ ((x.self + 0x58#64) ↦₆₄ x.ik5) ∗
      ((x.self + 0x60#64) ↦₆₄ x.ik6) ∗ ((x.self + 0x68#64) ↦₆₄ x.ik7) ∗
      (x.sret ↦₈ 0#8) ∗
      ((x.sret + 0x01#64) ↦₆₄ x.ik0) ∗ ((x.sret + 0x09#64) ↦₆₄ x.ik1) ∗
      ((x.sret + 0x11#64) ↦₆₄ x.ik2) ∗ ((x.sret + 0x19#64) ↦₆₄ x.ik3) ∗
      ((x.sret + 0x21#64) ↦₆₄ x.ik4) ∗ ((x.sret + 0x29#64) ↦₆₄ x.ik5) ∗
      ((x.sret + 0x31#64) ↦₆₄ x.ik6) ∗ ((x.sret + 0x39#64) ↦₆₄ x.ik7)

structure GetLocalRegIdPollGhost where
  futPtr : BitVec 64
  sret : BitVec 64
  self : BitVec 64
  regId : BitVec 32
  u_sret0 : BitVec 64
  u_sret8 : BitVec 32

/-- Specification of `<InMemIdentityKeyStore as
IdentityKeyStore>::get_local_registration_id::{closure#0}` (`0x07b7c`). -/
@[expose] def getLocalRegIdPollSpec : Spec GetLocalRegIdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.futPtr ∧ s.readReg64 .x8 = x.sret⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 0#8) ∗
      ((x.self + 0x70#64) ↦₃₂ x.regId) ∗
      (x.sret ↦₆₄ x.u_sret0) ∗ ((x.sret + 8#64) ↦₃₂ x.u_sret8)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.futPtr ↦₆₄ x.self) ∗ ((x.futPtr + 8#64) ↦₈ 1#8) ∗
      ((x.self + 0x70#64) ↦₃₂ x.regId) ∗
      (x.sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((x.sret + 8#64) ↦₃₂ x.regId)

/-- Pure std3 helper for byte extraction at offsets `8..56` of `y[0..56] ++ x[56..64]`. -/
private theorem extract56_8_hi (x y : BitVec 64) (k : Nat) (hk : 8 ≤ k) (hk2 : k + 8 ≤ 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  ext i hi
  have h1 : ¬ (k + i < 8) := by omega
  have h3 : k + i - 8 = k - 8 + i := by omega
  have hlt : k - 8 + i < 56 := by omega
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb', h1, ↓reduceIte, h3, hlt, decide_true, Bool.true_and,
    Nat.zero_add]

private theorem extract56_8_0 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  ext i hi
  rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb', hi, ↓reduceIte, decide_true, Bool.true_and]
private theorem extract56_8_8 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 8 8 = y.extractLsb' 0 8 :=
  extract56_8_hi x y 8 (by decide) (by decide)
private theorem extract56_8_16 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 16 8 = y.extractLsb' 8 8 :=
  extract56_8_hi x y 16 (by decide) (by decide)
private theorem extract56_8_24 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 24 8 = y.extractLsb' 16 8 :=
  extract56_8_hi x y 24 (by decide) (by decide)
private theorem extract56_8_32 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 32 8 = y.extractLsb' 24 8 :=
  extract56_8_hi x y 32 (by decide) (by decide)
private theorem extract56_8_40 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 40 8 = y.extractLsb' 32 8 :=
  extract56_8_hi x y 40 (by decide) (by decide)
private theorem extract56_8_48 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 48 8 = y.extractLsb' 40 8 :=
  extract56_8_hi x y 48 (by decide) (by decide)
private theorem extract56_8_56 (x y : BitVec 64) :
    (y.extractLsb' 0 56 ++ x.extractLsb' 56 8).extractLsb' 56 8 = y.extractLsb' 48 8 :=
  extract56_8_hi x y 56 (by decide) (by decide)

theorem bytes7_byte_fold (a x : BitVec 64) :
    bytes7At a
      (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₈ (x.extractLsb' 56 8)) =
    (a ↦₆₄ x) := by
  simp only [bytes7At, pointsTo64, BitVec.add_zero, sepConj_assoc]

theorem bytes7_word_shift (a x y : BitVec 64) :
    bytes7At a
      (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8) (x.extractLsb' 24 8)
      (x.extractLsb' 32 8) (x.extractLsb' 40 8) (x.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (y.extractLsb' 0 56 ++ x.extractLsb' 56 8)) =
    (a ↦₆₄ x) ∗
    bytes7At (a + 0x08#64)
      (y.extractLsb' 0 8) (y.extractLsb' 8 8) (y.extractLsb' 16 8) (y.extractLsb' 24 8)
      (y.extractLsb' 32 8) (y.extractLsb' 40 8) (y.extractLsb' 48 8) := by
  simp only [bytes7At, pointsTo64,
    extract56_8_0, extract56_8_8, extract56_8_16, extract56_8_24,
    extract56_8_32, extract56_8_40, extract56_8_48, extract56_8_56,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem keyPair39_eq_words4_bytes7 (a ik0 ik1 ik2 ik3 ik4 : BitVec 64) :
    bytes7At a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
    ((a + 0x07#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
    ((a + 0x0f#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
    ((a + 0x17#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
    ((a + 0x1f#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
    (a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
    bytes7At (a + 0x20#64)
      (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
  have h1 := bytes7_word_shift a ik0 ik1
  have h2 := bytes7_word_shift (a + 0x08#64) ik1 ik2
  have h3 := bytes7_word_shift (a + 0x10#64) ik2 ik3
  have h4 := bytes7_word_shift (a + 0x18#64) ik3 ik4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (a + 8#64) _ _ _ _ _ _ _), h2, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (a + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc]
  rw [h4]

theorem keyPair32Hi_eq_words4 (b ik4 ik5 ik6 ik7 : BitVec 64) :
    bytes7At b
      (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
      (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
    ((b + 0x07#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
    ((b + 0x0f#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
    ((b + 0x17#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
    ((b + 0x1f#64) ↦₈ (ik7.extractLsb' 56 8)) =
    (b ↦₆₄ ik4) ∗ ((b + 0x08#64) ↦₆₄ ik5) ∗ ((b + 0x10#64) ↦₆₄ ik6) ∗ ((b + 0x18#64) ↦₆₄ ik7) := by
  have h1 := bytes7_word_shift b ik4 ik5
  have h2 := bytes7_word_shift (b + 0x08#64) ik5 ik6
  have h3 := bytes7_word_shift (b + 0x10#64) ik6 ik7
  have h4 := bytes7_byte_fold (b + 0x18#64) ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2 h3 h4
  rw [← sepConj_assoc, h1, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (b + 8#64) _ _ _ _ _ _ _), h2, sepConj_assoc]
  rw [← sepConj_assoc (bytes7At (b + 16#64) _ _ _ _ _ _ _), h3, sepConj_assoc]
  rw [h4]

theorem words8_eq_keyPair64UnalignedAt (a ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 : BitVec 64) :
    ((a ↦₆₄ ik0) ∗ ((a + 0x08#64) ↦₆₄ ik1) ∗ ((a + 0x10#64) ↦₆₄ ik2) ∗ ((a + 0x18#64) ↦₆₄ ik3) ∗
     ((a + 0x20#64) ↦₆₄ ik4) ∗ ((a + 0x28#64) ↦₆₄ ik5) ∗ ((a + 0x30#64) ↦₆₄ ik6) ∗
       ((a + 0x38#64) ↦₆₄ ik7)) =
    keyPair64UnalignedAt a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
      (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
      (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
      (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      (ik7.extractLsb' 56 8) := by
  have hlo := keyPair39_eq_words4_bytes7 a ik0 ik1 ik2 ik3 ik4
  have hhi := keyPair32Hi_eq_words4 (a + 0x20#64) ik4 ik5 ik6 ik7
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhi
  unfold keyPair64UnalignedAt
  rw [← hhi]
  symm
  calc _ = (bytes7At a
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
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

end CryptoVerification.E2E.Pqxdh.ResponderClosure
