/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.TryFromDefsX
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.WireTypeBv -- shake: keep
public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_Int32MergeX : True := trivial

/-! ## Stack layout lemmas -/

theorem stackAt_int32MergeX (sp : BitVec 64) :
    stackAt sp int32MergeStackW =
      stackAt (sp - 80#64) decodeVarintSliceStackW ∗
        memRegion (sp - 80#64) 48 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
          ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp decodeVarintSliceStackW 10 (by decide)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 10)) 10 (by decide)] at h0
  change stackAt sp int32MergeStackW =
    stackAt (sp - 80#64) decodeVarintSliceStackW ∗ memRegion (sp - 80#64) 80 at h0
  have s1 := memRegion_split (sp - 80#64) 48 32 (by decide)
  rw [bv_sub_add_lit sp 80 48] at s1
  have s2 := memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s2
  have s3 := memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s3
  have s4 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s4
  rw [h0, s1, s2, s3, s4,
    memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
    memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stackAt_slice_eq_errorHookX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackW =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSliceStackW) 80 ∗
        stackAt sp decodeErrorHookStackW :=
  ProofLib.stackAt_split_bottom sp decodeErrorHookStackW 80 (by decide)

theorem stackAt_errorHook_entails_sliceX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 int32MergeStackW) 80 ∗ stackAt (sp - 80#64) decodeErrorHookStackW ⊢
      stackAt (sp - 80#64) decodeVarintSliceStackW := by
  have h := stackAt_slice_eq_errorHookX (sp - 80#64)
  have hsub : sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 int32MergeStackW := by
    change sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 (80 + decodeVarintSliceStackW)
    bv_lin
  rw [hsub] at h
  exact Entails.of_eq h.symm

theorem stackAt_slice_eq_slowX (sp : BitVec 64) :
    stackAt sp decodeVarintSliceStackW =
      memRegion (sp - BitVec.ofNat 64 decodeVarintSliceStackW) 16 ∗
        stackAt sp varintSlowStackX :=
  ProofLib.stackAt_split_bottom sp varintSlowStackX 16 (by decide)

theorem stackAt_slow_entails_sliceX (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 int32MergeStackW) 16 ∗ stackAt (sp - 80#64) varintSlowStackX ⊢
      stackAt (sp - 80#64) decodeVarintSliceStackW := by
  have h := stackAt_slice_eq_slowX (sp - 80#64)
  have hsub : sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 int32MergeStackW := by
    change sp - 80#64 - BitVec.ofNat 64 decodeVarintSliceStackW = sp - BitVec.ofNat 64 (80 + decodeVarintSliceStackW)
    bv_lin
  rw [hsub] at h
  exact Entails.of_eq h.symm

/-! ## Arithmetic and list bounds for W (< 2^63) -/

private theorem cbz_len_cons_falseW {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1

private theorem ult_10_of_ge_11W {n : Nat} (h11 : 11 ≤ n) (hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

private theorem ult_10_of_lt_11W {n : Nat} (h11 : ¬ 11 ≤ n) (_hlt : n < 2 ^ 63) :
    (10#64).ult (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem len_ult_consumed_falseW {bs rest : List (BitVec 8)} (_hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : bs.length - rest.length < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

/-! ## Callee helpers -/

section Placed

open CryptoVerification

/-- Relocatable `prost::encoding::int32::merge::<&mut &[u8]>` (Block `8`) meets
`Int32MergePlacedOkW A H` given placed contracts for `DecodeError::from`,
`decode_varint_slow`, and `decode_varint_slice`. -/
theorem int32Merge_placed_okW [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hFrom : DecodeErrorFromPlacedOkW A H)
    (hSlow : DecodeVarintSlowPlacedOkW A H)
    (hSlice : DecodeVarintSlicePlacedOkW A H) :
    Int32MergePlacedOkW A H :=
  CryptoVerification.LibsignalTripleRatchet.Prost.int32_merge_placed_ok_gen
    (errStack := decodeErrorHookStackW) (by decide)
    (WireX.decodeErrorFrom_placed_ok_cl (callerProg := (blkPC_8).rebase (blkPl_8).base H) hFrom)
    (ls_subroutine_ok_cl_of_callee (callerProg := (blkPC_8).rebase (blkPl_8).base H)
      (CryptoVerification.LibsignalTripleRatchet.Prost.decodeVarintSlowGen_lscl_ok_of_session2 hSlow))
    (ls_subroutine_ok_cl_of_callee (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
