/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P1 Untrusted-Identity Exit Segments

Bitvector, ADRP, and memory-packing lemmas together with `SepWP` segment theorems (`+0x06e4 →
<String as Clone>::clone → +0x3588 → +0x359c → retAddr`) for the `is_trusted_identity ==
Ok(false)` exit path.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Evaluates reduced `bfi x23, x8, #8, #56` mask expression. -/
@[local simp, local wp_norm, local arm64_norm]
theorem bfi_mask_lsr8_id (cap : BitVec 64) :
    (cap &&& 255#64 ||| (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem evalBitfield_bfi_lsr8 (cap : BitVec 64) :
    evalBitfield .W64 .BFM cap (cap >>> 8) 56 55 = cap := by
  change (if (BitfieldOp.BFM == BitfieldOp.UBFM) = true then cap >>> 8 <<< 8
      else cap &&& 255#64 ||| (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap
  have h : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
  simp [h, bfi_mask_lsr8_id]

@[local simp]
theorem extractLsb_hi_lo_append (w : BitVec 64) :
    w.extractLsb' 32 32 ++ w.extractLsb' 0 32 = w := by
  bv_bits

/-- 40-byte word realignment at any base address `a` (`s.sp + 0xa98#64` or `outPtr + 8#64`). -/
theorem realign_40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    ((a ↦₆₄ w0) ∗
     ((a + 8#64) ↦₆₄ w1) ∗
     ((a + 16#64) ↦₆₄ w2) ∗
     ((a + 24#64) ↦₆₄ w3) ∗
     ((a + 32#64) ↦₆₄ w4)) =
    ((a ↦₃₂ w0.extractLsb' 0 32) ∗
     ((a + 4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
     ((a + 12#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
     ((a + 20#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
     ((a + 28#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
     ((a + 36#64) ↦₃₂ w4.extractLsb' 32 32)) := by
  simp only [pointsTo64_append32]
  rw [pointsTo64_split32 a w0, pointsTo64_split32 (a + 8#64) w1,
      pointsTo64_split32 (a + 16#64) w2, pointsTo64_split32 (a + 24#64) w3,
      pointsTo64_split32 (a + 32#64) w4]
  sep_norm

/-- Unpack `vecU8 A (sp + 0x3e0#64) bs` for `+0x07e8..+0x0804` (`cap` and `ptr` read as 64-bit words,
`len` read as two 32-bit halves). -/
theorem vecU8_unpack_3e0 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x3e0#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ cap) ∗
        ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
        ((sp + 0x3f0#64) ↦₃₂ (BitVec.ofNat 64 bs.length).extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₃₂ (BitVec.ofNat 64 bs.length).extractLsb' 32 32) ∗
        SegUntrusted.vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader SegUntrusted.vecU8Buf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  sep_norm
  rw [pointsTo64_split32 (sp + 0x3f0#64) (BitVec.ofNat 64 bs.length)]
  sep_norm
  exact Entails.refl _

/-- Split `memRegion (sp + 0x3e0#64) 368` into `memRegion (sp + 0x3e0#64) 24`,
`(sp + 0x3f8#64) ↦₈ d0 ∗ (sp + 0x3f9#64) ↦ₛ pad` (`pad.length = 7`), and
`memRegion (sp + 0x400#64) 336`. -/
theorem memRegion_368_untrusted_entails (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 ⊢
      ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
        ⌜pad.length = 7⌝ ∗
        memRegion (sp + 0x3e0#64) 24 ∗
        ((sp + 0x3f8#64) ↦₈ d0) ∗
        ((sp + 0x3f9#64) ↦ₛ pad) ∗
        memRegion (sp + 0x400#64) 336 := by
  rw [memRegion_split (sp + 0x3e0#64) 48 320 (by decide)]
  refine Entails.trans (sepConj_mono_left (SegUntrusted.memRegion_48_untrusted_entails (sp + 0x3e0#64))) ?_
  sep_norm
  apply Entails.sepExists_elim; intro d0
  apply Entails.sepExists_elim; intro pad
  refine Entails.sepExists_right d0 (Entails.sepExists_right pad ?_)
  rw [memRegion_split (sp + 0x400#64) 16 320 (by decide)]
  sep_norm
  exact Entails.refl _

/-- Reassemble `memRegion (sp + 0x3e0#64) 368` after `p1_untrusted_post_clone_wp`. -/
theorem cells_3e0_entails_memRegion_368 (sp cap ptr len devWord : BitVec 64) :
    (((sp + 0x3e0#64) ↦₆₄ cap) ∗
     ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
     ((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
     ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
     ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
     memRegion (sp + 0x400#64) 336) ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  have hlen :
      (((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32)) =
      ((sp + 0x3f0#64) ↦₆₄ len) := by
    have h4 : sp + 0x3f4#64 = (sp + 0x3f0#64) + 4#64 := by bv_omega
    rw [h4, pointsTo32_pair, extractLsb_hi_lo_append]
  rw [memRegion_split (sp + 0x3e0#64) 8 360 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64) 8 352 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64) 8 344 (by decide),
      memRegion_split (sp + 0x3e0#64 + 8#64 + 8#64 + 8#64) 8 336 (by decide)]
  sep_norm
  have hgrp :
      (((sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
       memRegion (sp + 0x400#64) 336) =
      (((sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
       (((sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
        ((sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32)) ∗
       ((sp + 0x3f8#64) ↦₆₄ devWord) ∗
       memRegion (sp + 0x400#64) 336) := by ac_rfl
  rw [hgrp, hlen]
  exact sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) cap)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e8#64) ptr)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) len)
        (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) devWord)
          (Entails.refl _))))

/-- Unpack `memRegion a 48` into the shape read/written at `outPtr + 0..0x30` by `p3_err_tail_b_wp`. -/
theorem memRegion_48_out_entails (outPtr : BitVec 64) :
    memRegion outPtr 48 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u08 : BitVec 32, ∃∗ u0c : BitVec 64,
      ∃∗ u14 : BitVec 64, ∃∗ u1c : BitVec 64, ∃∗ u24 : BitVec 64, ∃∗ u2c : BitVec 32,
        ((outPtr + 0x0#64) ↦₆₄ u0) ∗
        ((outPtr + 0x8#64) ↦₃₂ u08) ∗
        ((outPtr + 0xc#64) ↦₆₄ u0c) ∗
        ((outPtr + 0x14#64) ↦₆₄ u14) ∗
        ((outPtr + 0x1c#64) ↦₆₄ u1c) ∗
        ((outPtr + 0x24#64) ↦₆₄ u24) ∗
        ((outPtr + 0x2c#64) ↦₃₂ u2c) := by
  rw [memRegion_split outPtr 8 40 (by decide),
      memRegion_split (outPtr + 8#64) 8 32 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      memRegion_split (outPtr + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  repeat rw [ProofLib.memRegion_eight]
  sep_norm
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  have h40 := realign_40 (outPtr + 8#64) w1 w2 w3 w4 w5
  try simp only [BitVec.add_assoc] at h40; try simp only [BitVec.reduceAdd] at h40
  refine Entails.sepExists_right w0
    (Entails.sepExists_right (w1.extractLsb' 0 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
          (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
            (Entails.sepExists_right (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
              (Entails.sepExists_right (w5.extractLsb' 32 32) ?_))))))
  simp only [BitVec.add_zero]
  rw [h40]
  exact Entails.refl _

/-- Reassemble `apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val))` from the 7 atoms
written at `outPtr + 0..0x30` plus `SegUntrusted.vecU8Buf A cap ptr peer.name.bytes`. -/
theorem untrusted_out_entails (A : RustAlloc) (outPtr cap ptr devWord e4 : BitVec 64)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : peer.device :: pad = unpack64 devWord) :
    (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) ⊢
      apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) := by
  have h40 := (realign_40 (outPtr + 8#64) cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord e4).symm
  try simp only [BitVec.add_assoc] at h40; try simp only [BitVec.reduceAdd] at h40
  have hgrp :
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) =
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       (((outPtr + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
        ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
        ((outPtr + 0x1c#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
        ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
        ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32)) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) := by
    sep_norm
  rw [hgrp, h40]
  have hgrp2 :
      (((outPtr + 0x0#64) ↦₆₄ 0x800000000000000c#64) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 peer.name.bytes.length) ∗
        ((outPtr + 32#64) ↦₆₄ devWord) ∗
        ((outPtr + 40#64) ↦₆₄ e4)) ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) =
      ((outPtr ↦₆₄ speWord speUntrustedIdentity) ∗
       (((outPtr + 8#64) ↦₆₄ cap) ∗
        ((outPtr + 16#64) ↦₆₄ ptr) ∗
        ((outPtr + 24#64) ↦₆₄ BitVec.ofNat 64 peer.name.bytes.length) ∗
        SegUntrusted.vecU8Buf A cap ptr peer.name.bytes) ∗
       ((outPtr + 32#64) ↦₆₄ devWord) ∗
       ((outPtr + 40#64) ↦₆₄ e4)) := by
    have h0 : outPtr + 0x0#64 = outPtr := by bv_lin
    have htag : (0x800000000000000c#64 : BitVec 64) = speWord speUntrustedIdentity := rfl
    rw [h0, htag]
    ac_rfl
  rw [hgrp2]
  unfold apiDecResultAt apiErrAt addrCloneAt AddrGhost.val
  have hvec := SegUntrusted.vecU8_intro A (outPtr + 8#64) cap ptr peer.name.bytes
  have hdev := SegUntrusted.pointsTo64_entails_byte_memRegion7 (outPtr + 32#64) peer.device pad devWord hpad hw4
  have he4 := pointsTo64_entails_memRegion (outPtr + 40#64) e4
  try simp only [BitVec.add_assoc] at hvec hdev ⊢; try simp only [BitVec.reduceAdd] at hvec hdev ⊢
  rw [sepConj_assoc (vecU8 A (outPtr + 8#64) _)]
  exact sepConj_mono_right (sepConj_mono hvec (sepConj_mono hdev he4))

/-- Unpack `decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0` into `sp + 0xc70..0xcc8`. -/
theorem savedRegsAt_eq_sp_c70 (sp : BitVec 64) (s0 : State) :
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 =
      (((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗
       ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗
       ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗
       ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19)) := by
  unfold decryptPrekeySavedRegsAt
  have h0 : (sp + 0xcd0#64) - 0x60#64 = sp + 0xc70#64 := by bv_lin
  have h1 : 8#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc78#64 := by bv_lin
  have h2 : 16#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc80#64 := by bv_lin
  have h3 : 24#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc88#64 := by bv_lin
  have h4 : 32#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc90#64 := by bv_lin
  have h5 : 40#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xc98#64 := by bv_lin
  have h6 : 48#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xca0#64 := by bv_lin
  have h7 : 56#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xca8#64 := by bv_lin
  have h8 : 64#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcb0#64 := by bv_lin
  have h9 : 72#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcb8#64 := by bv_lin
  have h10 : 80#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcc0#64 := by bv_lin
  have h11 : 88#64 + ((sp + 0xcd0#64) - 0x60#64) = sp + 0xcc8#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h0]

theorem coro_268_split32 (coroPtr w : BitVec 64) :
    ((coroPtr + 0x268#64) ↦₆₄ w) =
      ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32 (coroPtr + 0x268#64) w]
  sep_norm

theorem vecGhostAt_eq_cap_sep (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗
      (((a + 8#64) ↦₆₄ g.ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
       (if g.cap = 0 then emp
        else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) := by
  unfold vecGhostAt vecU8At vecHeader
  ac_rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
