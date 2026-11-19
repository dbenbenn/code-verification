/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLen
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.VecVecClone
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false

/-!
# Pure Serialization Length and Empty-Clone Leaves

Verifies the stub-free serialization helpers `<Vec<Vec<u8>> as Clone>::clone` on an empty vector
(Block `117`), `<MessageKey as prost::Message>::encoded_len` (`0x2d6bc`, Block `118`), and
`<Chain as prost::Message>::encoded_len` (`0x26aa0`, Block `88`) on `SP2Ext` and under relocatable
`[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  hwVarintLen_eq_encodeVarint_length' hwVarintLen_bvShift_eq_encodeVarint_length'
  hwVarintLen_mix1_eq_encodeVarint_length hwVarintLen_mix2_eq_encodeVarint_length
  ule_zero_64 ult_zero_64

/-! ## `Vec<Vec<u8>>::clone` on an empty vector -/

private theorem stackAt_vecVecClone (sp : BitVec 64) :
    stackAt sp vecVecCloneStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        stackAt (sp - 96#64) allocHookStack ∗
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp allocHookStack 12 (by decide)
  have hadd : allocHookStack + 8 * 12 = vecVecCloneStack := by decide
  rw [hadd] at h1
  change stackAt sp vecVecCloneStack =
    stackAt (sp - 96#64) allocHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]
  simp only [sepExists_sepConj_right]

private theorem memRegion_24_cells (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

private def msgKeyCells (a : BitVec 64) (mk : MessageKeyGenerator) : SepProp :=
  ((a + 16#64) ↦₆₄ 0#64) ∗
  ((a + 40#64) ↦₆₄ 0#64) ∗
  ((a + 64#64) ↦₆₄ 0#64) ∗
  ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗
  ((a + 96#64) ↦₃₂ mk.counter)

private def msgKeyRest (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
  (a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗ RustHeap.vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗ RustHeap.vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗ RustHeap.vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗ RustHeap.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
  memRegion (a + 100#64) 4

private theorem messageKeyAt_eq_cells_sep_rest (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a = msgKeyCells a gk.2 ∗ msgKeyRest A gk a := by
  simp only [messageKeyAt, msgKeyCells, msgKeyRest, RustHeap.vecU8At_eq_header_sep_buf, vecHeader,
    List.length_nil, sepConj_assoc, arm64_norm]
  ac_rfl

private theorem msgKeyRest_seed_bounds {A : RustAlloc} {gk : MessageKeyGhost × MessageKeyGenerator}
    {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ msgKeyRest A gk a ∗ R) :
    gk.2.seed ≠ [] ∧ gk.2.seed.length < 2 ^ 63 := by
  unfold msgKeyRest at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  refine ⟨hm.1, ?_⟩
  have hbuf : m ⊨ RustHeap.vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      ((a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
        RustHeap.vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
        RustHeap.vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
        ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
        RustHeap.vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
        ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
        memRegion (a + 100#64) 4 ∗ R) := by
    convert hm.2 using 1; ac_rfl
  unfold RustHeap.vecU8Buf at hbuf
  rw [sepConj_assoc, satisfies_pure_sepConj] at hbuf
  have h1 := hbuf.1.1
  have h2 := hbuf.1.2.1
  omega

private theorem seed_len_beq_zero_false {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h := congrArg BitVec.toNat heq
  change bs.length % 2 ^ 64 = 0 at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem bv_uint32Field_1_ne_zero {v : BitVec 32} (h : (v == 0#32) = false) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  have hv : v ≠ 0 := by rwa [beq_eq_false_iff_ne] at h
  have hkey : (encodeKey 1 .varint).length = 1 := rfl
  simp only [uint32Field, hv, ↓reduceIte, List.length_append, hkey,
    ← BitVec.ofNat_add, Nat.add_comm]

private theorem uint32Field_1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  unfold uint32Field
  split
  · simp
  · have hkey : (encodeKey 1 .varint).length = 1 := rfl
    have hb := (encodeVarint_length_bounds (v.setWidth 64)).2
    simp only [List.length_append, hkey]
    omega

private theorem bv_bytesField_5_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField 5 bs).length := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey, ← BitVec.ofNat_add]
  congr 1
  omega

private theorem bytesField_5_length_lt {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (bytesField 5 bs).length ≤ bs.length + 11 := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  have hb := (encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).2
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey]
  omega

private theorem encMessageKey_length_eq (mk : MessageKeyGenerator) :
    (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
  simp only [encMessageKey, List.length_append]

private theorem stackAt_msgKeyLen_eq (sp : BitVec 64) :
    stackAt sp msgKeyLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) :=
  stackAt_encodedLen_eq sp

@[local simp, local arm64_norm]
private theorem ule_self_64 (x : BitVec 64) : BitVec.ule x x = true := by
  simp [BitVec.ule]

@[local simp, local arm64_norm]
private theorem ult_self_64 (x : BitVec 64) : BitVec.ult x x = false := by
  simp [BitVec.ult]

section Placed

open CryptoVerification.E2E.Record.Placed

/-- Block `117` (`Vec<Vec<u8>>::clone` on empty source) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem vecVecCloneEmpty_placed_ok_ext [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_117 H) (blkPl_117).base
      (withLsCodeLoaded lsmpl vecVecCloneEmptySpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (vecVecCloneEmpty_placed_ok H)

theorem vecVecCloneEmpty_placed_ok_cl [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 117)
      (withLsCl lsmpl vecVecCloneEmptySpec) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (vecVecCloneEmpty_placed_ok_ext H)

/-- Block `118` (`MessageKey::encoded_len`) wrapped in `withLsCodeLoaded lsmpl`. -/
theorem msgKeyLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A H)

theorem msgKeyLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 118)
      (withLsCl lsmpl (msgKeyLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (msgKeyLen_placed_ok_ext A H)

/-- Block `88` (`Chain::encoded_len`) under `[LibsignalPlacement]`. -/
theorem chainLen_placed_ok_ext [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) :
    subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
  chainLen_placed_ok A H

theorem chainLen_placed_ok_cl [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 88)
      (withLsCl lsmpl (chainLenSpec A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (chainLen_placed_ok A H)

end Placed

end CryptoVerification.E2E.Record.Serialization
