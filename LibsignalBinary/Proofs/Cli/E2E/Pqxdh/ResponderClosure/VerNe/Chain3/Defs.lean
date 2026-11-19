/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Specs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs

/-!
# `message::merge<Chain> [local#5]` Definitions and Loop Assembly

Defines the intermediate chain representation `chain3GAt`, top-level specification
`chainMerge3SpecAtWExt` (`Chain3OkAtWExt`), loop invariant `Chain3LoopAtWExt`, per-field slice
statements (`Chain3EntryStmtExt`, `Chain3SrkStmtExt`, `Chain3ChainKeyStmtExt`,
`Chain3MessageKeysStmtExt`, `Chain3ExitStmtExt`), and loop induction `chainMerge3W_ok_ext`.
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

/-! ## 1. Stack Budgets -/

/-- Callee budget below the `0xf0` frame: `bytes::merge [local#4]`'s `bytesMerge3Stack` (`33120` B),
the largest in-scope callee (`decode_varint [local#3]`: `32896` B, `grow_one`: `16896` B). -/
abbrev chainMerge3SubStackX : Nat := bytesMerge3Stack

/-- Stack budget of `message::merge<Chain> [local#3]`: frame `0xf0` + `chainMerge3SubStackX`
(`33360` B). -/
abbrev chainMerge3StackX : Nat := 0xf0 + chainMerge3SubStackX

theorem chainMerge3SubStackX_eq : chainMerge3SubStackX = 33120 := rfl

theorem chainMerge3StackX_eq : chainMerge3StackX = 33360 := rfl

/-! ## 2. Chain Layout (`chain3GAt`) During Merge -/

/-- A `Vec<u8>` at `v` holding `bs`, with capacity 0 while `bs` is empty (the `Vec::new()` of
`Chain::default()`), so that `bytes::merge [local#4]`'s `BytesMergeCapOk` holds at the merge. -/
@[expose] def chain3VecAt (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜bs = [] → cap = 0#64⌝ ∗ vecU8At A v cap ptr bs

/-- The `message_keys` and `chain_key` fields of `prostChainGAt A a c` (a literal copy of its
tail). -/
@[expose] def chainGRest (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-- Chain layout at `a` during `message::merge<Chain>`, representing `srk` and `priv` via `chain3VecAt`. -/
@[expose] def chain3GAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ chainGRest A a c

theorem prostChainGAt_eq_rest (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c = vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗ chainGRest A a c := by
  unfold prostChainGAt chainGRest
  rfl

theorem chain3VecAt_entails_vecU8 (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    chain3VecAt A v bs ⊢ vecU8 A v bs := by
  unfold chain3VecAt vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem chain3GAt_entails_prostChainGAt (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    chain3GAt A a c ⊢ prostChainGAt A a c := by
  rw [prostChainGAt_eq_rest]
  unfold chain3GAt
  exact sepConj_mono (chain3VecAt_entails_vecU8 A a c.srk)
    (sepConj_mono_left (chain3VecAt_entails_vecU8 A (a + 0x18#64) c.priv))

/-- A non-empty `Vec<u8>` is a `chain3VecAt` (the pure side condition is vacuous). -/
theorem chain3VecAt_of_ne_nil (A : RustAlloc) (v cap ptr : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs ≠ []) :
    vecU8At A v cap ptr bs ⊢ chain3VecAt A v bs := by
  unfold chain3VecAt
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.pure_right (fun h => absurd h hbs) (Entails.refl _)))

/-- An empty `chain3VecAt` has capacity 0. -/
theorem chain3VecAt_nil_elim (A : RustAlloc) (v : BitVec 64) :
    chain3VecAt A v [] ⊢ ∃∗ ptr : BitVec 64, vecU8At A v 0#64 ptr [] := by
  unfold chain3VecAt
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun h => ?_
  rw [h rfl]
  exact Entails.sepExists_right ptr (Entails.refl _)

theorem chain3VecAt_nil_intro (A : RustAlloc) (v ptr : BitVec 64) :
    vecU8At A v 0#64 ptr [] ⊢ chain3VecAt A v [] := by
  unfold chain3VecAt
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right ptr
    (Entails.pure_right (fun _ => rfl) (Entails.refl _)))

/-- `Chain::default()`'s cells at `v` (`cap = 0`, `ptr = 1`, `len = 0`) are an empty `chain3VecAt`. -/
theorem default_cells_entail_chain3VecAt (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ chain3VecAt A v [] := by
  refine Entails.trans ?_ (chain3VecAt_nil_intro A v 1#64)
  unfold vecU8At vecHeader
  have hp : (⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj, List.length_nil]
  exact Entails.of_eq (by simp)

/-- `Chain::default()`'s empty `Vec<MessageKey>` cells at `v` (`cap = 0`, `ptr = 8`, `len = 0`). -/
theorem default_cells_entail_c3Keys (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) v [] := by
  unfold RustHeap.vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold RustHeap.vecAt vecHeader RustHeap.vecBuf
  have hp : (⌜([] : List MessageKeyGenerator).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-- `Chain::default()` cells at `a` form `chain3GAt A a ChainG.empty` (used at both tag-6 `ss + 0x90`
and tag-7 `sp0 - 232` call sites). -/
theorem default_cells_entail_chain3GAt (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ 1#64) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
    ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ 8#64) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
    ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 ⊢
      chain3GAt A a ChainG.empty := by
  have h1 : a + 0x18#64 + 8#64 = a + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have h2 : a + 0x18#64 + 16#64 = a + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  have h3 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have h4 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hv1 := default_cells_entail_chain3VecAt A a
  have hv2 := default_cells_entail_chain3VecAt A (a + 0x18#64)
  have hv3 := default_cells_entail_c3Keys A (a + 0x30#64)
  rw [h1, h2] at hv2
  rw [h3, h4] at hv3
  unfold chain3GAt chainGRest ChainG.empty
  dsimp only
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv3)))
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Top-Level Contract -/

abbrev chainMerge5SubStackX : Nat := chainMerge3SubStackX
abbrev chainMerge5StackX : Nat := chainMerge3StackX
/-- The 160-byte local frame `[sp0 - 0xf0, sp0 - 0x50)` and the 9 register words saved by the
prologue (`+0x004..+0x014`) at `[sp0 - 0x50, sp0)`, with the 8-byte hole at `sp0 - 0x38`. -/
@[expose] def chain3SavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  memRegion (sp0 - 0xf0#64) 160 ∗
  ((sp0 - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 0x40#64) ↦₆₄ s0.readReg64 .x25) ∗
  memRegion (sp0 - 0x38#64) 8 ∗
  ((sp0 - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 0x8#64) ↦₆₄ s0.readReg64 .x19)

/-- The sub-stack is exactly `bytes::merge [local#4]`'s budget. -/
theorem stackAt_c3Sub_eq_bytesMerge (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      stackAt sp bytesMerge3Stack := rfl

/-- Split of the sub-stack for a `decode_varint [local#3]` call. -/
theorem stackAt_c3Sub_to_decodeVarint (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMerge3SubStackX)
          (chainMerge3SubStackX - decodeVarint2StackX) ∗
        stackAt sp decodeVarint2StackX :=
  stackAt_sub_split_seedChain sp decodeVarint2StackX
    chainMerge3SubStackX

/-- Split of the sub-stack for a `grow_one<MessageKey>` call. -/
theorem stackAt_c3Sub_to_growOne (sp : BitVec 64) :
    stackAt sp chainMerge3SubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMerge3SubStackX)
          (chainMerge3SubStackX - Proofs.libsignal.Stage1X.growOneChainStackX) ∗
        stackAt sp Proofs.libsignal.Stage1X.growOneChainStackX :=
  stackAt_sub_split_seedChain sp Proofs.libsignal.Stage1X.growOneChainStackX chainMerge3SubStackX

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
