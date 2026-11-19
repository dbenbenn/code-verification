/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainDefs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.BodyDefs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Entry Segment Leaf (`chainEntryG_ok`) for General `message::merge<Chain>`

Proves `chainEntryG_ok` (`+0x000 → +0x120`, `k = 0`) for `prost::encoding::message::merge::<Chain>`
(`0x3974`), covering both the 1-byte (`< 128`) and multi-byte (`decode_varint_slice`) length paths.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## Callee Offsets, Stack Splitting, and Varint Helpers -/

theorem stackAt_sub_to_varintSlice_cme (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack)
        (chainMergeSubStack - Prost.decodeVarintSliceStack) ∗
        stackAt sp Prost.decodeVarintSliceStack :=
  stackAt_sub_split_seedChain sp Prost.decodeVarintSliceStack chainMergeSubStack

theorem memRegion160_split_varint_cme (sp0 : BitVec 64) :
    memRegion (sp0 - 256#64) 160 =
      memRegion (sp0 - 256#64) 8 ∗
      memRegion (sp0 - 248#64) 24 ∗
      memRegion (sp0 - 224#64) 128 := by
  have h1 := memRegion_split (sp0 - 256#64) 8 152 (by decide)
  have h2 := memRegion_split (sp0 - 248#64) 24 128 (by decide)
  have ha1 : (sp0 - 256#64) + BitVec.ofNat 64 8 = sp0 - 248#64 := by bv_omega
  have ha2 : (sp0 - 248#64) + BitVec.ofNat 64 24 = sp0 - 224#64 := by bv_omega
  rw [show (8 : Nat) + 152 = 160 by decide, ha1] at h1
  rw [show (24 : Nat) + 128 = 152 by decide, ha2] at h2
  rw [h1, h2]

theorem pointsTo64_zero_split32_cme (sp0 : BitVec 64) :
    ((sp0 - 248#64) ↦₆₄ 0#64) =
      ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) := by
  have hs := pointsTo64_split32 (sp0 - 248#64) 0#64
  have ha : (sp0 - 248#64) + 4#64 = sp0 - 244#64 := by bv_omega
  simpa [ha] using hs

theorem cells24_entails_memRegion24_cme (sp0 w1 w2 : BitVec 64) :
    ((sp0 - 248#64) ↦₃₂ 0#32) ∗ ((sp0 - 244#64) ↦₃₂ 0#32) ∗
      ((sp0 - 240#64) ↦₆₄ w1) ∗ ((sp0 - 232#64) ↦₆₄ w2) ⊢
    memRegion (sp0 - 248#64) 24 := by
  rw [← sepConj_assoc, ← pointsTo64_zero_split32_cme sp0]
  have h1 := memRegion_split (sp0 - 248#64) 8 16 (by decide)
  have h2 := memRegion_split (sp0 - 240#64) 8 8 (by decide)
  have ha1 : (sp0 - 248#64) + BitVec.ofNat 64 8 = sp0 - 240#64 := by bv_omega
  have ha2 : (sp0 - 240#64) + BitVec.ofNat 64 8 = sp0 - 232#64 := by bv_omega
  rw [show (8 : Nat) + 16 = 24 by decide, ha1] at h1
  rw [show (8 : Nat) + 8 = 16 by decide, ha2] at h2
  rw [h1, h2, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  exact sepConj_mono (Entails.sepExists_right 0#64 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

private theorem signExtend64_lsr56_of_gt_0x7f_cme (b0 : BitVec 8) (h : 0x7F < b0.toNat) :
    (b0.signExtend 64) >>> 56 = 0xff#64 := by
  revert b0 h; decide

theorem encodeVarint_ge128_cons_cme {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 32) :
    ∃ vtail : List (BitVec 8),
      encodeVarint (BitVec.ofNat 64 n) = BitVec.ofNat 8 (n % 128 + 128) :: vtail := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlt : ¬ (BitVec.ofNat 64 n).toNat < 0x80 := by omega
  refine ⟨encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7), ?_⟩
  unfold encodeVarint encodeVarintAux
  simp only [hnlt, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  have hand : (BitVec.ofNat 64 n &&& 0x7F).toNat = n % 128 := by
    rw [BitVec.toNat_and, htoNat, show (0x7F : BitVec 64).toNat = 127 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod n 7
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, hand,
    show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

theorem signExtend64_contByte_lsr56_cme (n : Nat) :
    (BitVec.signExtend 64 (BitVec.ofNat 8 (n % 128 + 128))) >>> 56 = 0xff#64 := by
  apply signExtend64_lsr56_of_gt_0x7f_cme
  rw [BitVec.toNat_ofNat]
  omega

theorem ult_10_of_gt_cme {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 32) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ule_10_of_gt_false_cme {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ule 10#64 = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

private theorem allocFailedIn_of_trace_eq_cme {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_cme {s0 sm sf : State} {F R : SepProp}
    (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_cme htr) h

/-! ## Single-Byte Length Path (`body.length < 128`): `+0x000 → +0x120` -/

private theorem chainG_enc_eq_fields_cme (c : ChainG) :
    c.enc = c.fields.flatMap ChainField.enc := by
  rcases c with ⟨srk, priv, ck, keys⟩
  unfold ChainG.enc ChainG.fields
  simp only [List.flatMap_append, List.flatMap_map]
  have h1 : bytesField 1 srk =
      List.flatMap ChainField.enc (if srk = [] then [] else [ChainField.srk srk]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h2 : bytesField 2 priv =
      List.flatMap ChainField.enc (if priv = [] then [] else [ChainField.priv priv]) := by
    unfold bytesField; split <;> simp [ChainField.enc]
  have h3 : msgField 3 (Option.map (fun ik => uint32Field 1 ik.1 ++ bytesField 2 ik.2) ck) =
      List.flatMap ChainField.enc (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG
