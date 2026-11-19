/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P2 Matched-Session Alignment, Error Reassembly, and `.rodata` Helpers

Pure 32-byte chunk realignment (`chunks32At`), `InvalidMessage` result reassembly, and `.rodata`
mismatch-string helpers for matched-session Stage P2, re-exporting `M2StepsD..E`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

scoped macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## Pure realignment and `InvalidMessage` reassembly -/

/-- Base-generic 32-byte chunk bundle `(4B, 2B, 8B, 8B, 8B, 2B)` matching `+0x1064..+0x10c4`. -/
@[expose] def chunks32At (base : BitVec 64) (w0 : BitVec 32) (h1 : BitVec 16)
    (q2 q3 q4 : BitVec 64) (h5 : BitVec 16) : SepProp :=
  (base ↦₃₂ w0) ∗
  ((base + 4#64) ↦₁₆ h1) ∗
  ((base + 6#64) ↦₆₄ q2) ∗
  ((base + 14#64) ↦₆₄ q3) ∗
  ((base + 22#64) ↦₆₄ q4) ∗
  ((base + 30#64) ↦₁₆ h5)

@[expose] def pack16LE : List (BitVec 8) → BitVec 16
  | [b0, b1] => b1 ++ b0
  | _ => 0#16

@[expose] def pack32LE : List (BitVec 8) → BitVec 32
  | [b0, b1, b2, b3] => b3 ++ b2 ++ b1 ++ b0
  | _ => 0#32

@[expose] def pack64LE : List (BitVec 8) → BitVec 64
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0
  | _ => 0#64

theorem pointsTo16_eq_bytes_pack16LE (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 2) :
    (a ↦ₛ bs) = (a ↦₁₆ pack16LE bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try (simp at h)
  exact ProofLib.pointsToBytes2_eq_pointsTo16 a b0 b1

theorem pointsTo32_eq_bytes_pack32LE (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32LE bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ProofLib.pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3

theorem pointsTo64_eq_bytes_pack64LE (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64LE bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ProofLib.pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7

/-- Any 32-byte list `bs` at `base` equals `chunks32At base` for its 6 little-endian words;
used forward at `base = sp + 0x3e2` and backward at `base = sp + 0x3e0`. -/
theorem pointsToBytes_32_eq_chunks32 (base : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    (base ↦ₛ bs) =
      chunks32At base
        (pack32LE (bs.take 4))
        (pack16LE ((bs.drop 4).take 2))
        (pack64LE ((bs.drop 6).take 8))
        (pack64LE ((bs.drop 14).take 8))
        (pack64LE ((bs.drop 22).take 8))
        (pack16LE (bs.drop 30)) := by
  have h04 : bs = bs.take 4 ++ bs.drop 4 := (List.take_append_drop 4 bs).symm
  have h46 : bs.drop 4 = (bs.drop 4).take 2 ++ bs.drop 6 := by
    have h := (List.take_append_drop 2 (bs.drop 4)).symm; rwa [List.drop_drop] at h
  have h614 : bs.drop 6 = (bs.drop 6).take 8 ++ bs.drop 14 := by
    have h := (List.take_append_drop 8 (bs.drop 6)).symm; rwa [List.drop_drop] at h
  have h1422 : bs.drop 14 = (bs.drop 14).take 8 ++ bs.drop 22 := by
    have h := (List.take_append_drop 8 (bs.drop 14)).symm; rwa [List.drop_drop] at h
  have h2230 : bs.drop 22 = (bs.drop 22).take 8 ++ bs.drop 30 := by
    have h := (List.take_append_drop 8 (bs.drop 22)).symm; rwa [List.drop_drop] at h
  conv_lhs => rw [h04]
  rw [ProofLib.pointsToBytes_append]
  conv_lhs => rhs; rw [h46]
  rw [ProofLib.pointsToBytes_append]
  conv_lhs => rhs; rhs; rw [h614]
  rw [ProofLib.pointsToBytes_append]
  conv_lhs => rhs; rhs; rhs; rw [h1422]
  rw [ProofLib.pointsToBytes_append]
  conv_lhs => rhs; rhs; rhs; rhs; rw [h2230]
  rw [ProofLib.pointsToBytes_append]
  unfold chunks32At
  have l0 : (bs.take 4).length = 4 := by simp [hlen]
  have l1 : ((bs.drop 4).take 2).length = 2 := by simp [hlen]
  have l2 : ((bs.drop 6).take 8).length = 8 := by simp [hlen]
  have l3 : ((bs.drop 14).take 8).length = 8 := by simp [hlen]
  have l4 : ((bs.drop 22).take 8).length = 8 := by simp [hlen]
  have l5 : (bs.drop 30).length = 2 := by simp [hlen]
  rw [pointsTo32_eq_bytes_pack32LE _ _ l0,
      pointsTo16_eq_bytes_pack16LE _ _ l1,
      pointsTo64_eq_bytes_pack64LE _ _ l2,
      pointsTo64_eq_bytes_pack64LE _ _ l3,
      pointsTo64_eq_bytes_pack64LE _ _ l4,
      pointsTo16_eq_bytes_pack16LE _ _ l5]
  simp only [l0, l1, l2, l3, l4, BitVec.add_assoc, BitVec.reduceAdd]

/-- Reassemble `apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext)))`
from the 7 atoms written at `outPtr + 0..0x30` plus `SegUntrusted.vecU8Buf A cap ptr bs`
when `typeWord.extractLsb' 0 8 = 3#8`. -/
theorem invalidMessage_prekey_out_entails (A : RustAlloc) (outPtr cap ptr typeWord e4 : BitVec 64)
    (bs : List (BitVec 8)) (pad : List (BitVec 8))
    (hpad : pad.length = 7)
    (hw4 : (3#8 : BitVec 8) :: pad = unpack64 typeWord) :
    (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ (typeWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ typeWord.extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ⊢
      apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := by
  have h40 := (realign_40 (outPtr + 8#64) cap ptr (BitVec.ofNat 64 bs.length) typeWord e4).symm
  try simp only [BitVec.add_assoc] at h40; try simp only [BitVec.reduceAdd] at h40
  have hgrp :
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ (typeWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ typeWord.extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) =
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       (((outPtr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
        ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
        ((outPtr + 0x1c#64) ↦₆₄ (typeWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
        ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ typeWord.extractLsb' 32 32)) ∗
        ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32)) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) := by
    ac_rfl
  rw [hgrp, h40]
  have hgrp2 :
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((outPtr + 32#64) ↦₆₄ typeWord) ∗
        ((outPtr + 40#64) ↦₆₄ e4)) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) =
      ((outPtr ↦₆₄ speWord 24) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ∗
       ((outPtr + 32#64) ↦₆₄ typeWord) ∗
       ((outPtr + 40#64) ↦₆₄ e4)) := by
    have h0 : outPtr + 0x0#64 = outPtr := by bv_omega
    have htag : (0x8000000000000018#64 : BitVec 64) = speWord 24 := rfl
    rw [h0, htag]
    ac_rfl
  rw [hgrp2]
  dsimp only [apiDecResultAt, recordResultAt, vecResultAt, speAt, invalidMessageStrAt]
  have hvec :
      (((outPtr + 8#64) ↦₆₄ cap) ∗
       ((outPtr + 16#64) ↦₆₄ ptr) ∗
       ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ⊢
      ∃∗ bs' : List (BitVec 8), vecU8 A (outPtr + asm64% spePayloadOff) bs' := by
    refine Entails.sepExists_right bs ?_
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8_intro A
        (outPtr + 8#64) cap ptr bs
  have htype := CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.pointsTo64_entails_byte_memRegion7
    (outPtr + 32#64) 3#8 pad typeWord hpad hw4
  have he4 := pointsTo64_entails_memRegion (outPtr + 40#64) e4
  have hmreg :
      memRegion ((outPtr + 32#64) + 1#64) 7 ∗ memRegion (outPtr + 40#64) 8 =
        memRegion (outPtr + asm64% (speInvalidMessageTypeOff + 1))
          (asm% (speSize - (speInvalidMessageTypeOff + 1))) := by
    have ha1 : (outPtr + 32#64) + 1#64 = outPtr + 33#64 := by bv_omega
    have ha2 : (outPtr + 33#64) + 7#64 = outPtr + 40#64 := by bv_omega
    rw [ha1, ← ProofLib.memRegion_split' (b := outPtr + 33#64) (n := 7) (k := 8)
      (b' := outPtr + 40#64) rfl ha2.symm (by decide)]
  refine sepConj_mono_right (sepConj_mono hvec ?_)
  refine Entails.trans (sepConj_mono htype he4) ?_
  rw [sepConj_assoc, hmreg]
  exact Entails.of_eq rfl

/-! ## `.rodata` conjuring for the 70-byte mismatch string -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
