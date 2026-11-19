/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Prologue, Jump-Table Dispatch, and Shared Epilogues

Verifies the `4,240`-byte frame prologue (`+0 -> +36`), `.rodata` jump-table dispatch (`+36 -> arm`),
5 tail-call dealloc/drop epilogues, direct epilogue (`+19324`), and shared `Ok(V1Recv)` store epilogue (`+18940..+19324`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_4144 (sp : BitVec 64) : (sp - 4240#64) + 4144#64 = sp - 96#64 := by bv_omega

attribute [local arm64_norm, local wp_norm]
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

theorem seq_clean {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hQ)

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

theorem sepWPp_seq_clean {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Q_panic : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQm⟩ =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hQm))

/-! ## Callee Stack Bounds (`statesRecvStackX ≥ statesRecvFrame + calleeStack`) & Stack Splits -/

theorem statesRecvStackX_ge_allocHookStack :
    statesRecvFrame + allocHookStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_extHookStack :
    statesRecvFrame + extHookStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStackPoly64 :
    statesRecvFrame + dropStackPoly64 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropGluePoly16Stack :
    statesRecvFrame + dropGluePoly16Stack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack32 :
    statesRecvFrame + dropStack32 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack48 :
    statesRecvFrame + dropStack48 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_dropStack80 :
    statesRecvFrame + dropStack80 ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_noHeaderReceivedRecvHdrChunkStackX :
    statesRecvFrame + noHeaderReceivedRecvHdrChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_keysSampledRecvCt1ChunkStack :
    statesRecvFrame + keysSampledRecvCt1ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_headerSentRecvCt1ChunkStack :
    statesRecvFrame + headerSentRecvCt1ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ct1ReceivedRecvCt2ChunkStack :
    statesRecvFrame + ct1ReceivedRecvCt2ChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ct1AcknowledgedRecvEkChunkStack :
    statesRecvFrame + ct1AcknowledgedRecvEkChunkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_ekReceivedCt1SampledRecvCt1AckStack :
    statesRecvFrame + ekReceivedCt1SampledRecvCt1AckStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_recvCt2ChunkStackX :
    statesRecvFrame + RecvCt2Chunk.recvCt2ChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_addChunkStackX :
    statesRecvFrame + SpqrV1.Poly.AddChunk.addChunkStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_polyDecodedMessageStackX :
    statesRecvFrame + RecvCt2Chunk.polyDecodedMessageStackX ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_polyDecoderDecodedMessageStack :
    statesRecvFrame + polyDecoderDecodedMessageStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_unchunkedRecvEkStack :
    statesRecvFrame + unchunkedRecvEkStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_unchunkedSendCt2Stack :
    statesRecvFrame + unchunkedSendCt2Stack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_sendCt2EncoderStack :
    statesRecvFrame + sendCt2EncoderStack ≤ statesRecvStackX := by decide

theorem statesRecvStackX_ge_encodeBytesStackX :
    statesRecvFrame + SpqrV1.Poly.EncodeBytes.encodeBytesStackX ≤ statesRecvStackX := by decide

theorem stackAt_statesRecvCallee_eq_allocHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 15456 (by decide)

theorem stackAt_statesRecvCallee_eq_extHook (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack32 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32 :=
  stackAt_split_bottom fsp dropStack32 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack48 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15408 ∗ stackAt fsp dropStack48 :=
  stackAt_split_bottom fsp dropStack48 15408 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStackPoly64 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15392 ∗ stackAt fsp dropStackPoly64 :=
  stackAt_split_bottom fsp dropStackPoly64 15392 (by decide)

theorem stackAt_statesRecvCallee_eq_noHeaderReceivedRecvHdrChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 848 ∗ stackAt fsp noHeaderReceivedRecvHdrChunkStackX :=
  stackAt_split_bottom fsp noHeaderReceivedRecvHdrChunkStackX 848 (by decide)

theorem stackAt_statesRecvCallee_eq_keysSampledRecvCt1Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 1632 ∗ stackAt fsp keysSampledRecvCt1ChunkStack :=
  stackAt_split_bottom fsp keysSampledRecvCt1ChunkStack 1632 (by decide)

theorem stackAt_statesRecvCallee_eq_headerSentRecvCt1Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 928 ∗ stackAt fsp headerSentRecvCt1ChunkStack :=
  stackAt_split_bottom fsp headerSentRecvCt1ChunkStack 928 (by decide)

theorem stackAt_statesRecvCallee_eq_ct1ReceivedRecvCt2Chunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2576 ∗ stackAt fsp ct1ReceivedRecvCt2ChunkStack :=
  stackAt_split_bottom fsp ct1ReceivedRecvCt2ChunkStack 2576 (by decide)

theorem stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack :=
  stackAt_split_bottom fsp ct1AcknowledgedRecvEkChunkStack 336 (by decide)

theorem stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 1920 ∗ stackAt fsp ekReceivedCt1SampledRecvCt1AckStack :=
  stackAt_split_bottom fsp ekReceivedCt1SampledRecvCt1AckStack 1920 (by decide)

theorem stackAt_statesRecvCallee_eq_addChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3072 ∗ stackAt fsp SpqrV1.Poly.AddChunk.addChunkStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.AddChunk.addChunkStackX 3072 (by decide)

theorem stackAt_statesRecvCallee_eq_polyDecodedMessage (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2496 ∗ stackAt fsp RecvCt2Chunk.polyDecodedMessageStackX :=
  stackAt_split_bottom fsp RecvCt2Chunk.polyDecodedMessageStackX 2496 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedRecvEk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2960 ∗ stackAt fsp unchunkedRecvEkStack :=
  stackAt_split_bottom fsp unchunkedRecvEkStack 2960 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedSendCt2 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2832 ∗ stackAt fsp unchunkedSendCt2Stack :=
  stackAt_split_bottom fsp unchunkedSendCt2Stack 2832 (by decide)

theorem stackAt_statesRecvCallee_eq_sendCt2Encoder (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2096 ∗ stackAt fsp sendCt2EncoderStack :=
  stackAt_split_bottom fsp sendCt2EncoderStack 2096 (by decide)

theorem stackAt_statesRecvCallee_eq_encodeBytes (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2608 ∗ stackAt fsp SpqrV1.Poly.EncodeBytes.encodeBytesStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.EncodeBytes.encodeBytesStackX 2608 (by decide)

/-! ## Prologue (`+0 -> +36`, `0x55454 -> 0x55478`) -/

theorem stackAt_statesRecvStackX_eq_allocHook (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19696 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 19696 (by decide)

theorem stackAt_statesRecvStackX_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropStack32 :=
  stackAt_split_bottom sp dropStack32 19664 (by decide)

theorem stackAt_statesRecvStackX_eq_dropStackPoly64 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19632 ∗ stackAt sp dropStackPoly64 :=
  stackAt_split_bottom sp dropStackPoly64 19632 (by decide)

theorem stackAt_statesRecvStackX_eq_dropGluePoly16 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropGluePoly16Stack :=
  stackAt_split_bottom sp dropGluePoly16Stack 19664 (by decide)

/-- Jump-table target offset from `entry` for each `States` discriminant `tag`. -/
@[expose] def statesRecvArmOffset (tag : BitVec 64) : BitVec 64 :=
  if tag == 2#64 then 96#64         -- idx 0 -> 0x554b4 (+96)
  else if tag == 3#64 then 1796#64  -- idx 1 -> 0x55b58 (+1796)
  else if tag == 4#64 then 780#64   -- idx 2 -> 0x55760 (+780)
  else if tag == 5#64 then 1204#64  -- idx 3 -> 0x55908 (+1204)
  else if tag == 6#64 then 228#64   -- idx 4 -> 0x55538 (+228)
  else if tag == 7#64 then 2132#64  -- idx 5 -> 0x55ca8 (+2132)
  else if tag == 8#64 then 2268#64  -- idx 6 -> 0x55d30 (+2268)
  else if tag == 10#64 then 3392#64 -- idx 8 -> 0x56194 (+3392)
  else if tag == 11#64 then 588#64  -- idx 9 -> 0x556a0 (+588)
  else if tag == 12#64 then 2396#64 -- idx 10 -> 0x55db0 (+2396)
  else 1528#64                      -- idx 7 (tag ∈ {0, 1, 9}) -> 0x55a4c (+1528)

/-- Jump-table index `x8` computed by `sub x8, x12, #2; cmp x12, #1; csel x8, x8, x9, hi` (`x9 = 7`). -/
@[expose] def statesRecvJumpIdx (tag : BitVec 64) : BitVec 64 :=
  if tag == 2#64 then 0#64
  else if tag == 3#64 then 1#64
  else if tag == 4#64 then 2#64
  else if tag == 5#64 then 3#64
  else if tag == 6#64 then 4#64
  else if tag == 7#64 then 5#64
  else if tag == 8#64 then 6#64
  else if tag == 10#64 then 8#64
  else if tag == 11#64 then 9#64
  else if tag == 12#64 then 10#64
  else 7#64

/-- Valid `States` discriminant predicate (`tag ∈ {0..12}`). -/
@[expose] def ValidStatesTag (tag : BitVec 64) : Prop :=
  tag = 0#64 ∨ tag = 1#64 ∨ tag = 2#64 ∨ tag = 3#64 ∨ tag = 4#64 ∨ tag = 5#64 ∨
  tag = 6#64 ∨ tag = 7#64 ∨ tag = 8#64 ∨ tag = 9#64 ∨ tag = 10#64 ∨ tag = 11#64 ∨ tag = 12#64

@[local arm64_norm, local wp_norm]
theorem out_488_add_8 (out : BitVec 64) : out + 488#64 + 8#64 = out + 496#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_8 (out : BitVec 64) : out + 888#64 + 8#64 = out + 896#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_888_add_16 (out : BitVec 64) : out + 888#64 + 16#64 = out + 904#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_904_add_8 (out : BitVec 64) : out + 904#64 + 8#64 = out + 912#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem bv376_toNat : (376#64 : BitVec 64).toNat = 376 := rfl

/-- `out` cells written in Step A (`+18996 -> +19128`, 33 instructions). -/
@[expose] def epilogueRecvOutPartA (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64) : SepProp :=
  (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w8) ∗ ((out + 16#64) ↦₆₄ w16) ∗ ((out + 24#64) ↦₆₄ w24) ∗
  ((out + 32#64) ↦₆₄ w32) ∗ ((out + 40#64) ↦₆₄ w40) ∗ ((out + 48#64) ↦₆₄ w48) ∗ ((out + 56#64) ↦₆₄ w56) ∗
  ((out + 64#64) ↦₆₄ w64) ∗ ((out + 72#64) ↦₆₄ w72) ∗ ((out + 80#64) ↦₆₄ w80) ∗ ((out + 88#64) ↦₆₄ w88) ∗
  ((out + 96#64) ↦₆₄ w96) ∗ ((out + 104#64) ↦₆₄ w104) ∗ ((out + 112#64) ↦₆₄ w112) ∗
  ((out + 264#64) ↦₆₄ w264) ∗ ((out + 272#64) ↦₆₄ w272) ∗ ((out + 280#64) ↦₆₄ w280) ∗ ((out + 288#64) ↦₆₄ w288) ∗
  ((out + 296#64) ↦₆₄ w296) ∗ ((out + 304#64) ↦₆₄ w304) ∗ ((out + 312#64) ↦₆₄ w312) ∗ ((out + 320#64) ↦₆₄ w320) ∗
  ((out + 328#64) ↦₆₄ w328) ∗ ((out + 336#64) ↦₆₄ w336) ∗ ((out + 344#64) ↦₆₄ w344) ∗ ((out + 352#64) ↦₆₄ w352) ∗
  ((out + 392#64) ↦₆₄ w392) ∗ ((out + 400#64) ↦₆₄ w400) ∗ ((out + 424#64) ↦₆₄ w424) ∗ ((out + 432#64) ↦₆₄ w432)

/-- Stack cells read in Step A (`+18996 -> +19128`). -/
@[expose] def epilogueRecvStackPartA (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (q960 : BitVec 128) : SepProp :=
  ((fsp + 224#64) ↦₆₄ w224) ∗
  ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
  ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗
  ((fsp + 368#64) ↦₆₄ w368) ∗ ((fsp + 376#64) ↦₆₄ w376) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗
  ((fsp + 408#64) ↦₆₄ w408) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ w456) ∗
  ((fsp + 496#64) ↦₆₄ w496) ∗ ((fsp + 504#64) ↦₆₄ w504) ∗
  ((fsp + 960#64) ↦₁₂₈ q960)

/-- `out` cells written in Step B (`+19128 -> +19280`, 38 instructions). -/
@[expose] def epilogueRecvOutPartB (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64)
    (q488 : BitVec 128) (w504 : BitVec 64) : SepProp :=
  ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
  ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
  ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
  ((out + 216#64) ↦₆₄ w216) ∗ ((out + 224#64) ↦₆₄ w224) ∗ ((out + 232#64) ↦₆₄ w232) ∗ ((out + 240#64) ↦₆₄ w240) ∗
  ((out + 248#64) ↦₆₄ w248) ∗ ((out + 256#64) ↦₆₄ w256) ∗
  ((out + 360#64) ↦₆₄ w360) ∗ ((out + 368#64) ↦₆₄ w368) ∗ ((out + 376#64) ↦₆₄ w376) ∗ ((out + 384#64) ↦₆₄ w384) ∗
  ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480) ∗
  ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w504)

/-- Stack cells read in Step B (`+19128 -> +19280`). -/
@[expose] def epilogueRecvStackPartB (fsp : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64) : SepProp :=
  ((fsp + 248#64) ↦₆₄ w248) ∗ ((fsp + 256#64) ↦₆₄ w256) ∗
  ((fsp + 264#64) ↦₆₄ w264) ∗ ((fsp + 272#64) ↦₆₄ w272) ∗ ((fsp + 280#64) ↦₆₄ w280) ∗
  ((fsp + 304#64) ↦₆₄ w304) ∗ ((fsp + 312#64) ↦₆₄ w312) ∗ ((fsp + 320#64) ↦₆₄ w320) ∗ ((fsp + 328#64) ↦₆₄ w328) ∗
  ((fsp + 344#64) ↦₆₄ w344) ∗ ((fsp + 360#64) ↦₆₄ w360) ∗
  ((fsp + 392#64) ↦₆₄ w392) ∗ ((fsp + 400#64) ↦₆₄ w400) ∗
  ((fsp + 416#64) ↦₆₄ w416) ∗ ((fsp + 424#64) ↦₆₄ w424) ∗
  ((fsp + 440#64) ↦₆₄ w440) ∗ ((fsp + 448#64) ↦₆₄ w448) ∗
  ((fsp + 464#64) ↦₆₄ w464) ∗ ((fsp + 472#64) ↦₆₄ w472) ∗
  ((fsp + 480#64) ↦₆₄ w480) ∗ ((fsp + 488#64) ↦₆₄ w488)

end CryptoVerification.SpqrV1.States.Recv
