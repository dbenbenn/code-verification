/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs

/-!
# `message::merge<Chain> [local#5]`: ChainKey Shared Definitions

Defines the inner-loop register bundle `Chain3InnerLoopRegs`, `chain3GAt` layout lemmas for tag 3,
and the four sub-step statements decomposing `Chain3ChainKeyStmt`:
- `Chain3Seg3aStmt` (`+0x0a8 → +0x368`): outer tag-3 header, niche initialization at `a + 0x48..0x68`,
  and inner limit `x25 = |afterCk|`;
- `Chain3Seg3bStmt` (`+0x368 → +0x368`): inner field 1 (`index` varint into `[a + 0x60]`);
- `Chain3Seg3cStmt` (`+0x368 → +0x368`): inner field 2 (`key` bytes via `bytes::merge` into `a + 0x48`);
- `Chain3Seg3dStmt` (`+0x368 → +0x0a8`): inner-loop exit when remaining length equals `|afterCk|`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

/-! ## 1. Alignment & `chain3GAt` layout helpers for tag 3 -/

theorem sp0_aligned_of_sub_240_aligned {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

theorem sp_sub_240_aligned {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

theorem chain3GAt_ck_none_eq_ext (A : RustAlloc) (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    chain3GAt A a c0 =
      chain3VecAt A a c0.srk ∗ chain3VecAt A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold chain3GAt chainGRest
  rw [hck]

theorem chain3GAt_ck_none_eq (a : BitVec 64) (c0 : ChainG) (hck : c0.ck = none) :
    chain3GAt A0 a c0 =
      chain3VecAt A0 a c0.srk ∗ chain3VecAt A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 :=
  chain3GAt_ck_none_eq_ext A0 a c0 hck

theorem chain3GAt_apply_ck_eq_ext (A : RustAlloc) (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    chain3GAt A a (c0.apply (ChainField.ck i key)) =
      chain3VecAt A a c0.srk ∗ chain3VecAt A (a + 0x18#64) c0.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold chain3GAt chainGRest ChainG.apply
  dsimp only

theorem chain3GAt_apply_ck_eq (a : BitVec 64) (c0 : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    chain3GAt A0 a (c0.apply (ChainField.ck i key)) =
      chain3VecAt A0 a c0.srk ∗ chain3VecAt A0 (a + 0x18#64) c0.priv ∗
      vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) c0.keys ∗
      vecU8 A0 (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 :=
  chain3GAt_apply_ck_eq_ext A0 a c0 i key

/-! ## 2. Inner loop register invariant (`+0x368`) -/

/-- Register bundle preserved across the inner `ChainKey` loop (`+0x368`) of `[local#3]`. -/
@[expose] def Chain3InnerLoopRegs (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    (s_init s : State) : Prop :=
  s.sp = sp0 - 0xf0#64 ∧
  s.readReg64 .x29 = sp0 - 0x50#64 ∧
  s.readReg64 .x19 = bufRef ∧
  s.readReg64 .x20 = a ∧
  s.readReg64 .x21 = BitVec.ofNat 64 outerTailLen ∧
  s.readReg64 .x22 = sp0 - 0xe8#64 ∧
  s.readReg64 .x23 = 1#64 ∧
  s.readReg64 .x24 = 104#64 ∧
  s.readReg64 .x25 = BitVec.ofNat 64 innerTailLen ∧
  s.readReg64 .x26 = s_init.readReg64 .x26 ∧
  s.readReg64 .x27 = s_init.readReg64 .x27 ∧
  s.readReg64 .x28 = s_init.readReg64 .x28

theorem Chain3InnerLoopRegs.of_calleeSaved {sp0 bufRef a : BitVec 64}
    {outerTailLen innerTailLen : Nat} {s_init s1 s2 : State}
    (h1 : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1)
    (hsp2 : s2.sp = sp0 - 0xf0#64) (hcs : CalleeSavedPreserved s1 s2) :
    Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s2 :=
  ⟨hsp2,
   hcs.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.1,
   hcs.1.trans h1.2.2.1,
   hcs.2.1.trans h1.2.2.2.1,
   hcs.2.2.1.trans h1.2.2.2.2.1,
   hcs.2.2.2.1.trans h1.2.2.2.2.2.1,
   hcs.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 3. Sub-step statements for `Chain3ChainKeyStmt` -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
