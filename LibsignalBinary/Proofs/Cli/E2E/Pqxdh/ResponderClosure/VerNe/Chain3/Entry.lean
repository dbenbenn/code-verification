/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `message::merge<Chain> [local#5]`: Entry Slice

Verifies `Chain3EntryStmtExt` (`+0x000 → +0x0a8`, `k = 0`), covering the `0xf0`-byte frame prologue,
wire-type check (`wt == 2`), delimited length `decode_varint` call at `+0x034`, and loop-limit setup
(`x21 = |tail|`, `x22 = sp + 8`, `w23 = 1`, `w24 = 104`).
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

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Pure helpers -/

set_option maxHeartbeats 400000 in
private theorem w0_and_255_eq_two_c3 {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_and, BitVec.toNat_ofNat] at h' ⊢
  rw [show 255 % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 400000 in
private theorem bv_ofNat_add_sub_left_c3 (m k : Nat) :
    BitVec.ofNat 64 (m + k) - BitVec.ofNat 64 m = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]

set_option maxHeartbeats 400000 in
private theorem ult_ofNat_add_left_false_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

set_option maxHeartbeats 400000 in
private theorem ule_ofNat_add_right_true_c3 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

set_option maxHeartbeats 400000 in
private theorem sp_sub_f0_aligned_c3 {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0xf0#64) &&& 15#64 = 0#64 := by
  have := sp_and_15_sub_aligned sp0 0xf0#64 (by decide)
  simpa only [show (0b1111#64 : BitVec 64) = 15#64 from rfl, h] using this

set_option maxHeartbeats 400000 in
private theorem allocFailedIn_of_trace_eq_c3 {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

set_option maxHeartbeats 400000 in
private theorem chainG_enc_eq_fields_c3 (c : ChainG) :
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
      List.flatMap ChainField.enc
        (match ck with | some (i, k) => [ChainField.ck i k] | none => []) := by
    cases ck <;> simp [msgField, ChainField.enc]
  have h4 : (List.map (fun m => lenField 4 (encMessageKey m)) keys).flatten =
      List.flatMap (fun a => (ChainField.key a).enc) keys := by
    rw [← List.flatMap_def]; rfl
  rw [h1, h2, h3, h4]; rfl

/-! ## 2. Pre-call segment `+0x000 → bl decode_varint [local#3]` -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
