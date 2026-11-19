/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.CodeLayout

/-!
# Tag-4 Field Leaf (`chainMessageKeysG_ok`) for General `message::merge<Chain>`

Proves `chainMessageKeysG_ok` (`+0x120 → +0x120`, `k → k + 1`) for nested `MessageKey` entries
(tag `4`, decoding optional `counter` tag `1` and 32-byte `seed` tag `5` and pushing into
`Vec<MessageKey>` at `a + 0x30`, growing capacity via `RawVec<Chain>::grow_one` when `len = cap`).
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Pure `ChainG`, `ChainField`, and `encMessageKey` Helpers -/

theorem chainField_eq_key_of_tag4 {fl : ChainField} (h : fl.tag = 4) :
    ∃ mk : MessageKeyGenerator, fl = .key mk := by
  cases fl <;> simp [ChainField.tag] at h; exact ⟨_, rfl⟩

theorem mem_keys_of_key_mem_fields {c : ChainG} {mk : MessageKeyGenerator}
    (h : ChainField.key mk ∈ c.fields) : mk ∈ c.keys := by
  unfold ChainG.fields at h
  simp only [List.mem_append, List.mem_map, ChainField.key.injEq, exists_eq_right] at h
  rcases h with ((h1 | h2) | h3) | h4
  · split at h1 <;> simp at h1
  · split at h2 <;> simp at h2
  · split at h3 <;> simp at h3
  · exact h4

@[expose] def chainFieldKeys : ChainField → List MessageKeyGenerator
  | .key m => [m]
  | _ => []

theorem chainG_apply_keys (c : ChainG) (fl : ChainField) :
    (c.apply fl).keys = c.keys ++ chainFieldKeys fl := by
  cases fl <;> simp [ChainG.apply, chainFieldKeys]

theorem foldl_chainG_apply_keys (fs : List ChainField) (c : ChainG) :
    (fs.foldl ChainG.apply c).keys = c.keys ++ fs.flatMap chainFieldKeys := by
  induction fs generalizing c with
  | nil => simp
  | cons fl fs ih => simp only [List.foldl_cons, List.flatMap_cons, ih, chainG_apply_keys, List.append_assoc]

theorem chainG_fields_flatMap_keys (c : ChainG) :
    c.fields.flatMap chainFieldKeys = c.keys := by
  unfold ChainG.fields
  have h1 : (if c.srk = [] then [] else [ChainField.srk c.srk]).flatMap chainFieldKeys = [] := by split <;> rfl
  have h2 : (if c.priv = [] then [] else [ChainField.priv c.priv]).flatMap chainFieldKeys = [] := by split <;> rfl
  have h4 : ∀ ks : List MessageKeyGenerator, (ks.map ChainField.key).flatMap chainFieldKeys = ks := by
    intro ks; induction ks with | nil => rfl | cons m ks ih => simp [chainFieldKeys, ih]
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, h1, h2, h4]
  rcases c.ck with _ | ⟨i, k⟩ <;> rfl

theorem chainGAfter_keys_length_le (c : ChainG) (k : Nat) :
    (chainGAfter c k).keys.length ≤ c.keys.length := by
  unfold chainGAfter; rw [foldl_chainG_apply_keys]; dsimp only [ChainG.empty]
  rw [List.nil_append, ← chainG_fields_flatMap_keys c]
  conv => rhs; rw [← List.take_append_drop k c.fields]
  rw [List.flatMap_append, List.length_append]; omega

theorem chainGAfter_succ_of_key {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {mk : MessageKeyGenerator} (hfl : c.fields[k]'hk = .key mk) :
    chainGAfter c (k + 1) = { chainGAfter c k with keys := (chainGAfter c k).keys ++ [mk] } := by
  unfold chainGAfter
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, hfl]; rfl

theorem drop_fields_flatMap_enc_of_key {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    {mk : MessageKeyGenerator} (hfl : c.fields[k]'hk = .key mk) (tail : List (BitVec 8)) :
    (c.fields.drop k).flatMap ChainField.enc ++ tail =
      lenField 4 (encMessageKey mk) ++ ((c.fields.drop (k + 1)).flatMap ChainField.enc ++ tail) := by
  rw [List.drop_eq_getElem_cons hk, hfl, List.flatMap_cons, ChainField.enc, List.append_assoc]

theorem uint32Field_1_eq_pbVarint (i : BitVec 32) : uint32Field 1 i = pbVarint 1 i.toNat := by
  unfold uint32Field pbVarint pbKey
  by_cases hi : i = 0
  · subst hi; rfl
  · have hne : i.toNat ≠ 0 := by intro h; apply hi; exact BitVec.eq_of_toNat_eq (by simpa using h)
    simp only [hi, hne, ↓reduceIte]
    have hkey : encodeKey 1 .varint = [0x08#8] := rfl
    rw [hkey, pbVarintBody_u32_eq_encodeVarint_seedChain]

theorem bytesField_5_eq_pbBytes {b : List (BitVec 8)} (hb : b.length = 32) :
    bytesField 5 b = pbBytes 5 b := by
  have hne : b ≠ [] := by rintro rfl; simp at hb
  have hlt : b.length < 128 := by omega
  unfold bytesField lenField pbBytes pbKey; simp only [hne, ↓reduceIte]
  have hkey : encodeKey 5 .lengthDelimited = [0x2a#8] := rfl
  rw [hkey, encodeVarint_lt128_seedChain b.length hlt]

theorem encMessageKey_eq_pb {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    encMessageKey mk = pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed := by
  unfold encMessageKey; rw [uint32Field_1_eq_pbVarint, bytesField_5_eq_pbBytes hseed]

theorem encMessageKey_length_lt128 {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    (encMessageKey mk).length < 128 := by
  rw [encMessageKey_eq_pb hseed, List.length_append, pbBytes_length_seedChain, hseed]
  have := pbVarint1_length_bounds_seedChain mk.counter.toNat; omega

theorem lenField_4_encMessageKey_eq {mk : MessageKeyGenerator} (hseed : mk.seed.length = 32) :
    lenField 4 (encMessageKey mk) =
      0x22#8 :: BitVec.ofNat 8 (encMessageKey mk).length ::
        (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) := by
  have hlt := encMessageKey_length_lt128 hseed; unfold lenField
  have hkey : encodeKey 4 .lengthDelimited = [0x22#8] := rfl
  rw [hkey, encodeVarint_lt128_seedChain _ hlt, encMessageKey_eq_pb hseed]; rfl

/-! ## Stack Frame, `prostMsgKeyAt` Move, and `prostChainGAt` Helpers -/

@[expose] def chainMergeSavedRegs12 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

@[expose] def chainMergePad4 (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 256#64) 8 ∗ memRegion (sp0 - 144#64) 48

theorem chainMergeSavedRegs_eq_split (sp0 : BitVec 64) (s0 : State) :
    chainMergeSavedRegs sp0 s0 =
      memRegion (sp0 - 248#64) 104 ∗ chainMergePad4 sp0 ∗ chainMergeSavedRegs12 sp0 s0 := by
  unfold chainMergeSavedRegs chainMergePad4 chainMergeSavedRegs12
  have s1 := memRegion_split (sp0 - 256#64) 8 152 (by decide)
  have e1 : (sp0 - 256#64) + BitVec.ofNat 64 8 = sp0 - 248#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 152 = 160 by decide, e1] at s1
  have s2 := memRegion_split (sp0 - 248#64) 104 48 (by decide)
  have e2 : (sp0 - 248#64) + BitVec.ofNat 64 104 = sp0 - 144#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (104 : Nat) + 48 = 152 by decide, e2] at s2; rw [s1, s2]; ac_rfl

theorem memRegion104_sp248_split (sp0 : BitVec 64) :
    memRegion (sp0 - 248#64) 104 =
      memRegion (sp0 - 248#64) 80 ∗ (∃∗ c10 : BitVec 64, (sp0 - 168#64) ↦₆₄ c10) ∗
      (∃∗ c11 : BitVec 64, (sp0 - 160#64) ↦₆₄ c11) ∗ (∃∗ wc : BitVec 32, (sp0 - 152#64) ↦₃₂ wc) ∗
      memRegion (sp0 - 148#64) 4 := by
  have s80 := memRegion_split (sp0 - 248#64) 80 24 (by decide)
  have e80 : (sp0 - 248#64) + BitVec.ofNat 64 80 = sp0 - 168#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (80 : Nat) + 24 = 104 by decide, e80] at s80
  have h24 := memRegion24_split_ck_seedChain (sp0 - 248#64)
  have eb0 : (sp0 - 248#64) + 0x50#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb1 : (sp0 - 248#64) + 0x58#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb2 : (sp0 - 248#64) + 0x60#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have eb3 : (sp0 - 248#64) + 0x64#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [eb0, eb1, eb2, eb3] at h24; rw [s80, h24]

theorem memRegion80_sp248_eq_cells10 (sp0 : BitVec 64) :
    memRegion (sp0 - 248#64) 80 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp0 - 248#64) ↦₆₄ c0) ∗ ((sp0 - 240#64) ↦₆₄ c1) ∗ ((sp0 - 232#64) ↦₆₄ c2) ∗
        ((sp0 - 224#64) ↦₆₄ c3) ∗ ((sp0 - 216#64) ↦₆₄ c4) ∗ ((sp0 - 208#64) ↦₆₄ c5) ∗
        ((sp0 - 200#64) ↦₆₄ c6) ∗ ((sp0 - 192#64) ↦₆₄ c7) ∗ ((sp0 - 184#64) ↦₆₄ c8) ∗
        ((sp0 - 176#64) ↦₆₄ c9) := by
  have h80 := memRegion80_chainInit_eq_cells10_receiverChains (sp0 - 16#64)
  have ea0 : sp0 - 16#64 - 232#64 = sp0 - 248#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea1 : sp0 - 16#64 - 224#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea2 : sp0 - 16#64 - 216#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea3 : sp0 - 16#64 - 208#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea4 : sp0 - 16#64 - 200#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea5 : sp0 - 16#64 - 192#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea6 : sp0 - 16#64 - 184#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea7 : sp0 - 16#64 - 176#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea8 : sp0 - 16#64 - 168#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ea9 : sp0 - 16#64 - 160#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [ea0, ea1, ea2, ea3, ea4, ea5, ea6, ea7, ea8, ea9] at h80; exact h80

theorem prostMsgKeyAt_fold (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗ vecU8 A0 (sp0 - 200#64) [] ∗
      vecU8 A0 (sp0 - 176#64) mk.seed ∗ ((sp0 - 152#64) ↦₃₂ mk.counter) ∗
      memRegion (sp0 - 148#64) 4 = prostMsgKeyAt A0 mk (sp0 - 248#64) := by
  unfold prostMsgKeyAt
  have e1 : (sp0 - 248#64) + 24#64 = sp0 - 224#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 248#64) + 48#64 = sp0 - 200#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 248#64) + 72#64 = sp0 - 176#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 248#64) + 96#64 = sp0 - 152#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 248#64) + 100#64 = sp0 - 148#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e1, e2, e3, e4, e5]

theorem prostMsgKeyAt_move_bytes (A : RustAlloc) (mk : MessageKeyGenerator) (a : BitVec 64) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostMsgKeyAt A mk b⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_receiverChains (P1 := fun b => vecU8 A b []) (P2 := fun b => vecU8 A b [])
    (n1 := 24) (n2 := 24) (off := 24#64) rfl (fun b => vecU8_move_bytes_receiverChains A b [])
    (fun b => vecU8_move_bytes_receiverChains A b [])
  have h123 := move_bytes_pair_receiverChains (P1 := fun b => vecU8 A b [] ∗ vecU8 A (b + 24#64) [])
    (P2 := fun b => vecU8 A b []) (n1 := 48) (n2 := 24) (off := 48#64) rfl h12
    (fun b => vecU8_move_bytes_receiverChains A b [])
  have h1234 := move_bytes_pair_receiverChains
    (P1 := fun b => (vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) [])
    (P2 := fun b => vecU8 A b mk.seed) (n1 := 72) (n2 := 24) (off := 72#64) rfl h123
    (fun b => vecU8_move_bytes_receiverChains A b mk.seed)
  have h12345 := move_bytes_pair_receiverChains
    (P1 := fun b => ((vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) []) ∗ vecU8 A (b + 72#64) mk.seed)
    (P2 := fun b => (b ↦₃₂ mk.counter) ∗ memRegion (b + 4#64) 4) (n1 := 96) (n2 := 8) (off := 96#64) rfl
    h1234 (prostCkTailSome_move_bytes_receiverChains mk.counter) a
  have heq : ∀ b : BitVec 64, prostMsgKeyAt A mk b =
      (((vecU8 A b [] ∗ vecU8 A (b + 24#64) []) ∗ vecU8 A (b + 48#64) []) ∗ vecU8 A (b + 72#64) mk.seed) ∗
      (((b + 96#64) ↦₃₂ mk.counter) ∗ memRegion ((b + 96#64) + 4#64) 4) := fun b => by
    unfold prostMsgKeyAt
    have e100 : (b + 96#64) + 4#64 = b + 100#64 := by rw [BitVec.add_assoc]; rfl
    rw [e100]; ac_rfl
  simp only [show (96 : Nat) + 8 = 104 from rfl, ← heq] at h12345; exact h12345

theorem prostMsgKeyAt_move_chunks104 (A : RustAlloc) (a : BitVec 64) (mk : MessageKeyGenerator) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128, ∃∗ q3 : BitVec 128,
      ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128, ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64, (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostMsgKeyAt A mk b⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostMsgKeyAt_move_bytes A mk a) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _); rw [← hchunks b]; exact hmov b

theorem chunks104_6QWAt_sp248_eq (sp0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (sp0 - 248#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp0 - 248#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((sp0 - 240#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 232#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((sp0 - 224#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((sp0 - 216#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((sp0 - 208#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((sp0 - 200#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((sp0 - 192#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((sp0 - 184#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((sp0 - 176#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((sp0 - 168#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((sp0 - 160#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((sp0 - 152#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, sepConj_assoc]; rfl

theorem arrayAt_prostMsgKeyAt_move_bytes (A : RustAlloc) (keys : List MessageKeyGenerator) :
    ∀ a : BitVec 64,
      arrayAt (fun mk b => prostMsgKeyAt A mk b) 104 a keys ⊢
        ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
          ⌜bs.length = keys.length * 104 ∧
            ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun mk d => prostMsgKeyAt A mk d) 104 b keys⌝ ∗
          (a ↦ₛ bs) ∗ H := by
  induction keys with
  | nil =>
    intro a; rw [arrayAt_nil]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, sepConj_emp]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp, arrayAt_nil]; exact Entails.refl _
  | cons mk ks ih =>
    intro a; rw [arrayAt_cons]
    have hm := move_bytes_pair_receiverChains (P1 := fun b => prostMsgKeyAt A mk b)
      (P2 := fun b => arrayAt (fun m d => prostMsgKeyAt A m d) 104 b ks)
      (n1 := 104) (n2 := ks.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostMsgKeyAt_move_bytes A mk) ih a
    have hlen : 104 + ks.length * 104 = (mk :: ks).length * 104 := by simp only [List.length_cons]; omega
    rw [hlen] at hm; exact hm

@[expose] def prostChainGRest (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4

theorem prostChainGAt_eq_keys_sep_rest (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗ prostChainGRest A a c := by
  unfold prostChainGAt prostChainGRest; ac_rfl

theorem prostChainGRest_update_keys (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (ks : List MessageKeyGenerator) :
    prostChainGRest A a { c with keys := ks } = prostChainGRest A a c := rfl

theorem vecOf_keys_open (a : BitVec 64) (keys : List MessageKeyGenerator) :
    vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (a + 0x30#64) keys ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp
         else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  unfold vecOf vecAt vecHeader
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  rw [e38, e40]
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) cap ptr keys)) ?_
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  have hif : (if cap = 0 then emp else A0.live ptr (cap.toNat * 104) 8 ∗
      memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) =
      (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
    rw [hlive]
    change (if cap = 0#64 then emp else emp ∗ memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) = _
    by_cases h0 : cap = 0#64 <;> simp [h0]
  rw [hif]
  have hpull : (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
      (⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ keys.length * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) =
      ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ keys.length * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        arrayAt (fun mk b => prostMsgKeyAt A0 mk b) 104 ptr keys ∗
        (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104))) := by ac_rfl
  rw [hpull]; apply Entails.pure_left; rintro ⟨hlen, hcap_lt, _, hptr⟩
  exact Entails.pure_right ⟨hlen, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecOf_keys_push_fold (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mk : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
      prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) ⊢
    vecOf A0 104 8 (fun m b => prostMsgKeyAt A0 m b) (a + 0x30#64) (keys ++ [mk]) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mk]).length = keys.length + 1 := by simp
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hif : (if cap = 0 then emp else A0.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr (keys ++ [mk]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys ++ [mk]).length * 104)) ((cap.toNat - (keys ++ [mk]).length) * 104)) =
      (arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
        prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104) := by
    rw [hlive, hlen, arrayAt_concat]; change (if cap = 0#64 then emp else _) = _; simp [hne0]
  rw [e38, e40, hif, hlen]
  have hgrp : (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1))) ∗
      (⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
            prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗ ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        arrayAt (fun m b => prostMsgKeyAt A0 m b) 104 ptr keys ∗
        prostMsgKeyAt A0 mk (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104)) ((cap.toNat - (keys.length + 1)) * 104)) := by ac_rfl
  rw [hgrp]; exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

theorem stackAt_sub_to_growOne_seedChain (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack) (chainMergeSubStack - 4608) ∗ stackAt sp 4608 :=
  stackAt_sub_split_seedChain sp 4608 chainMergeSubStack

theorem memRegion_spare_eq_emp_of_full (cap ptr : BitVec 64) (n : Nat) (hfull : n = cap.toNat) :
    (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) = emp := by
  rw [hfull, Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero]
  by_cases h0 : cap = 0#64 <;> simp [h0]

theorem memRegion_spare_split_of_lt (cap ptr : BitVec 64) (n : Nat)
    (hlt : n + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp else memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) =
      memRegion (ptr + BitVec.ofNat 64 (n * 104)) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((n + 1) * 104)) ((cap.toNat - (n + 1)) * 104) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  simp only [hne0, ↓reduceIte]
  have hmul : (cap.toNat - n) * 104 = 104 + (cap.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 (n * 104)) 104 ((cap.toNat - (n + 1)) * 104) (by omega)
  have haddr : ptr + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 = ptr + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [← hmul, haddr] at hsplit; exact hsplit

theorem mk_hdr_pointsTo_combine_seedChain (ptr : BitVec 64) (n : Nat) :
    (ptr ↦₈ 0x22#8) ∗ ((ptr + 1#64) ↦₈ BitVec.ofNat 8 n) = (ptr ↦ₛ [0x22#8, BitVec.ofNat 8 n]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem msgKey_default_of_cells (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
      ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
      ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
      ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) ⊢
    vecU8 A0 (sp0 - 248#64) [] ∗ vecU8 A0 (sp0 - 224#64) [] ∗ vecU8 A0 (sp0 - 200#64) [] ∗ vecU8 A0 (sp0 - 176#64) [] := by
  have v0 := emptyVec_entails_vecU8_seedChain (sp0 - 248#64); have v1 := emptyVec_entails_vecU8_seedChain (sp0 - 224#64)
  have v2 := emptyVec_entails_vecU8_seedChain (sp0 - 200#64); have v3 := emptyVec_entails_vecU8_seedChain (sp0 - 176#64)
  have e0a : (sp0 - 248#64) + 8#64 = sp0 - 240#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e0b : (sp0 - 248#64) + 16#64 = sp0 - 232#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1a : (sp0 - 224#64) + 8#64 = sp0 - 216#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e1b : (sp0 - 224#64) + 16#64 = sp0 - 208#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2a : (sp0 - 200#64) + 8#64 = sp0 - 192#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2b : (sp0 - 200#64) + 16#64 = sp0 - 184#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3a : (sp0 - 176#64) + 8#64 = sp0 - 168#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3b : (sp0 - 176#64) + 16#64 = sp0 - 160#64 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e0a, e0b] at v0; rw [e1a, e1b] at v1; rw [e2a, e2b] at v2; rw [e3a, e3b] at v3
  have hgrp :
      ((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
        ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64) ∗
        ((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
        ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64) =
      (((sp0 - 248#64) ↦₆₄ 0#64) ∗ ((sp0 - 240#64) ↦₆₄ 1#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 1#64) ∗ ((sp0 - 208#64) ↦₆₄ 0#64)) ∗
      ((((sp0 - 200#64) ↦₆₄ 0#64) ∗ ((sp0 - 192#64) ↦₆₄ 1#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64)) ∗
       (((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 1#64) ∗ ((sp0 - 160#64) ↦₆₄ 0#64)))) := by ac_rfl
  rw [hgrp]; exact sepConj_mono v0 (sepConj_mono v1 (sepConj_mono v2 v3))

theorem spAligned_of_sp_eq {s1 s2 : State} (h : s1.sp = s2.sp) (ha : s2.spAligned = true) :
    s1.spAligned = true := by unfold State.spAligned at ha ⊢; rwa [h]

theorem ult_ofNat_add_right_false_seedChain {m k : Nat} (h : m + k < 2 ^ 64) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64), decide_eq_false_iff_not]; omega

theorem sp0_aligned_of_sp_sub_256 {s : State} {sp0 : BitVec 64}
    (hsp : s.sp = sp0 - 256#64) (hal : s.spAligned = true) :
    sp0 &&& 15#64 = 0#64 := by
  have h : (sp0 - 256#64) &&& 15#64 = 0#64 := by rw [← hsp]; exact eq_of_beq hal
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt; omega

@[expose] def dummyChainMergeGhost : ChainMergeGhost :=
  ⟨0#64, ⟨[], [], none⟩, 0#64, 0#64, 0#64, [], []⟩

theorem beq_ofNat_cap_false {n : Nat} {cap : BitVec 64}
    (hle : n ≤ cap.toNat) (hne : n ≠ cap.toNat) : (BitVec.ofNat 64 n == cap) = false := by
  cases hb : (BitVec.ofNat 64 n == cap)
  · rfl
  · have heq := congrArg BitVec.toNat (eq_of_beq hb)
    have hlt : n < 2 ^ 64 := lt_of_le_of_lt hle cap.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at heq; exact False.elim (hne heq)

theorem ptr_madd_104_eq (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 104#64 = ptr + BitVec.ofNat 64 (n * 104) := by rw [← BitVec.ofNat_mul]

theorem ofNat_add_one_eq (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by rw [← BitVec.ofNat_add]

theorem SepWPp.focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s (P' ∗ F) Q Qp) (hf : P = P' ∗ F := by sep_focus) :
    SepWPp prog ret s P Q Qp :=
  hf ▸ h

theorem segStepG_of_sepWPp {α : Type} {prog : Program} {spec : Spec α} {x : α}
    {R P : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → Prop} (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog ret s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Q sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    SegStepG prog spec x R s0 s Q := by
  intro hL; obtain ⟨sf, hsteps, ⟨-, -, Pf, hmf, hq⟩ | ⟨hpan, Pf, hmf, hp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq hmf)⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, hp hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem chainG_enc_eq_fields_local (c : ChainG) : c.enc = c.fields.flatMap ChainField.enc := by
  have h1 : (if c.srk = [] then [] else [ChainField.srk c.srk]).flatMap ChainField.enc = bytesField 1 c.srk := by
    by_cases h : c.srk = [] <;> simp [h, bytesField, ChainField.enc]
  have h2 : (if c.priv = [] then [] else [ChainField.priv c.priv]).flatMap ChainField.enc = bytesField 2 c.priv := by
    by_cases h : c.priv = [] <;> simp [h, bytesField, ChainField.enc]
  have h4 : ∀ ks : List MessageKeyGenerator,
      (ks.map ChainField.key).flatMap ChainField.enc = (ks.map fun m => lenField 4 (encMessageKey m)).flatten := by
    intro ks; induction ks with | nil => rfl | cons m ks ih => simp [ChainField.enc, ih]
  rcases hck : c.ck with _ | ⟨i, k⟩ <;>
    simp [ChainG.enc, ChainG.fields, h1, h2, h4, hck, ChainField.enc, msgField]

theorem chainG_payload_split (c : ChainG) (k : Nat) (tail : List (BitVec 8)) :
    c.payload ++ tail =
      (encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.fields.take k).flatMap ChainField.enc) ++
        ((c.fields.drop k).flatMap ChainField.enc ++ tail) := by
  unfold ChainG.payload
  conv => lhs; arg 1; arg 2; rw [chainG_enc_eq_fields_local c, ← List.take_append_drop k c.fields, List.flatMap_append]
  simp only [List.append_assoc]

theorem sliceCursorAfter_tag4_combine (slot ptr : BitVec 64)
    (full pfx v1 v2 rest : List (BitVec 8))
    (hfull : full = pfx ++ (0x22#8 :: BitVec.ofNat 8 (v1 ++ v2).length :: ((v1 ++ v2) ++ rest))) :
    (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ v1) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) ↦ₛ v2) ∗
      Prost.sliceCursorAt slot
        (ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length)
        rest = Prost.sliceCursorAfter slot ptr full rest := by
  let fld : List (BitVec 8) := [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length] ++ v1 ++ v2
  have hfull' : full = (pfx ++ fld) ++ rest := by rw [hfull]; simp [fld, List.append_assoc]
  rw [hfull', sliceCursorAfter_append_eq_seedChain]
  have hpfx : (ptr ↦ₛ (pfx ++ fld)) = (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ fld) :=
    pointsToBytes_append ptr pfx fld
  have hfld1 : ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ fld) =
      ((ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length]) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ v1) ∗
      ((ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length) ↦ₛ v2) := by
    dsimp only [fld]; rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append]
    have h2 : BitVec.ofNat 64 [0x22#8, BitVec.ofNat 8 (v1 ++ v2).length].length = 2#64 := rfl
    rw [h2]
  have hptr_eq : ptr + BitVec.ofNat 64 (pfx ++ fld).length =
      ptr + BitVec.ofNat 64 pfx.length + 2#64 + BitVec.ofNat 64 v1.length + BitVec.ofNat 64 v2.length := by
    simp only [fld, List.length_append, List.length_cons, List.length_nil]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 2; omega
  rw [hpfx, hfld1, hptr_eq]; ac_rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
