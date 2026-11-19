/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKCnt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKHead
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKPush
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKSeed
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Slice (`Chain3MessageKeysStmt`)

Assembles the four tag-4 (`message_keys`, `+0x0a8 → +0x0a8`) sub-steps on a canonical `MessageKey`
encoding `0x22 :: L :: (v1 ++ v2) ++ rest`:
- `Chain3MkHeadStmt` (`+0x0a8 → +0x244`): outer key `0x22`, default scratch `MessageKey` at
  `sp0 - 0xe8`, and inner limit `x25 = |rest|`;
- `Chain3MkCntStmt` (`+0x244 → +0x244`): `counter` varint field (`pbVarint 1 counter`);
- `Chain3MkSeedStmt` (`+0x244 → +0x244`): 32-byte `seed` field (`pbBytes 5 seed`);
- `Chain3MkPushStmt` (`+0x244 → +0x0a8`): push of the scratch `MessageKey` onto `Vec<MessageKey>` at
  `a + 0x30`.
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
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

set_option maxRecDepth 200000

/-! ## 1. Frame pieces -/

set_option maxHeartbeats 400000 in
theorem c3mk_sp0_aligned_of_sub_240 {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
/-- The filled scratch is `prostMsgKeyAt A mk (sp0 - 0xe8)`. -/
theorem c3mk_prostMsgKeyAt_fold {A : RustAlloc} (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8 A (sp0 - 0xe8#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
      vecU8 A (sp0 - 160#64) mk.seed ∗ ((sp0 - 136#64) ↦₃₂ mk.counter) ∗
      memRegion (sp0 - 132#64) 4 = prostMsgKeyAt A mk (sp0 - 0xe8#64) := by
  unfold prostMsgKeyAt
  have e1 : (sp0 - 0xe8#64) + 24#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 0xe8#64) + 48#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 0xe8#64) + 72#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 0xe8#64) + 96#64 = sp0 - 136#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 0xe8#64) + 100#64 = sp0 - 132#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e1, e2, e3, e4, e5]

/-- `chain3GAt` without the `Vec<MessageKey>` at `a + 0x30`: the part the tag-4 path keeps. -/
@[expose] def c3mkChainNoKeys (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

set_option maxHeartbeats 400000 in
theorem chain3GAt_keys_split (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    chain3GAt A a c =
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
        c3mkChainNoKeys A a c := by
  rcases c with ⟨srk, priv, ck, keys⟩
  rcases ck with _ | ⟨i, k⟩
  · unfold chain3GAt chainGRest c3mkChainNoKeys
    dsimp only
    ac_rfl
  · unfold chain3GAt chainGRest c3mkChainNoKeys
    dsimp only
    ac_rfl

set_option maxHeartbeats 400000 in
theorem c3mkChainNoKeys_update_keys (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (ks : List MessageKeyGenerator) :
    c3mkChainNoKeys A a { c with keys := ks } = c3mkChainNoKeys A a c := rfl

set_option maxHeartbeats 400000 in
/-- The chain after the push of `mk`. -/
theorem chain3GAt_push_key (A : RustAlloc) (a : BitVec 64) (c : ChainG) (mk : MessageKeyGenerator) :
    chain3GAt A a { c with keys := c.keys ++ [mk] } =
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) (c.keys ++ [mk]) ∗
        c3mkChainNoKeys A a c := by
  rw [chain3GAt_keys_split, c3mkChainNoKeys_update_keys]

set_option maxHeartbeats 400000 in
/-- `chain3SavedRegs` with the 104 scratch bytes `[sp0 - 0xe8, sp0 - 0x80)` split out. -/
theorem chain3SavedRegs_c3mk_split (sp0 : BitVec 64) (s0 : State) :
    chain3SavedRegs sp0 s0 =
      memRegion (sp0 - 0xe8#64) 104 ∗
        (memRegion (sp0 - 0xf0#64) 8 ∗ memRegion (sp0 - 0x80#64) 48 ∗
          ((sp0 - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((sp0 - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((sp0 - 0x40#64) ↦₆₄ s0.readReg64 .x25) ∗
          memRegion (sp0 - 0x38#64) 8 ∗
          ((sp0 - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((sp0 - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((sp0 - 0x8#64) ↦₆₄ s0.readReg64 .x19)) := by
  have s1 := ProofLib.memRegion_split (sp0 - 0xf0#64) 8 152 (by decide)
  have s2 := ProofLib.memRegion_split (sp0 - 0xe8#64) 104 48 (by decide)
  have e1 : (sp0 - 0xf0#64) + BitVec.ofNat 64 8 = sp0 - 0xe8#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 0xe8#64) + BitVec.ofNat 64 104 = sp0 - 0x80#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 152 = 160 by decide, e1] at s1
  rw [show (104 : Nat) + 48 = 152 by decide, e2] at s2
  unfold chain3SavedRegs
  rw [s1, s2]
  ac_rfl

/-! ## 2. Assembly -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
