/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 6 (Path 5c)

**Checked by Lean.** Verifies `Split928` reconstruction of `States.ct2Sampled` (`tag = 12#64`) and
Path 5c (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`: `<Ct1SentEkReceived>::send_ct2`,
`send_ct2_encoder`, deallocations, and epilogue convergence `+16596 -> +18996`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff polyDecoderAt polyEncoderAt unchunkedCt1SentAt chunkAt statesRecvSavedCells statesRecvJumpTableAt
attribute [-simp, -arm64_norm]
  statesRecv_fnOff

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-- Builds the `Split928` for `States.ct2Sampled` (`tag = 12#64`) from:
    - `c_enc : Words50` (`400`B `PolyEncoder` at `+8..+408`),
    - `g : AuthWords` and `epoch : BitVec 64` (`56`B `Unchunked.SendCt.Ct2Sent` at `+408..+464`),
    - trailing padding words `w10, w11, w13, w14, w15`, `mid : List (BitVec 8)` (`376`B), and `tail : Words5` (`40`B). -/
@[expose] def mkSplit928Ct2Sampled (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) (mid : List (BitVec 8)) (tail : Words5) : Split928 where
  c0 := {
    w0 := 12#64
    w1 := c_enc.c0.w0
    w2 := c_enc.c0.w1
    w3 := c_enc.c0.w2
    w4 := c_enc.c0.w3
    w5 := c_enc.c0.w4
    w6 := c_enc.c0.w5
    w7 := c_enc.c0.w6
    w8 := c_enc.c0.w7
    w9 := c_enc.c0.w8
    w10 := c_enc.c0.w9
    w11 := c_enc.c0.w10
    w12 := c_enc.c0.w11
    w13 := c_enc.c0.w12
    w14 := c_enc.c0.w13
    w15 := c_enc.c0.w14
  }
  c1 := {
    w0 := c_enc.c0.w15
    w1 := c_enc.c1.w0
    w2 := c_enc.c1.w1
    w3 := c_enc.c1.w2
    w4 := c_enc.c1.w3
    w5 := c_enc.c1.w4
    w6 := c_enc.c1.w5
    w7 := c_enc.c1.w6
    w8 := c_enc.c1.w7
    w9 := c_enc.c1.w8
    w10 := c_enc.c1.w9
    w11 := c_enc.c1.w10
    w12 := c_enc.c1.w11
    w13 := c_enc.c1.w12
    w14 := c_enc.c1.w13
    w15 := c_enc.c1.w14
  }
  c2 := {
    w0 := c_enc.c1.w15
    w1 := c_enc.c2.w0
    w2 := c_enc.c2.w1
    w3 := c_enc.c2.w2
    w4 := c_enc.c2.w3
    w5 := c_enc.c2.w4
    w6 := c_enc.c2.w5
    w7 := c_enc.c2.w6
    w8 := c_enc.c2.w7
    w9 := c_enc.c2.w8
    w10 := c_enc.c2.w9
    w11 := c_enc.c2.w10
    w12 := c_enc.c2.w11
    w13 := c_enc.c2.w12
    w14 := c_enc.c2.w13
    w15 := c_enc.c2.w14
  }
  c3 := {
    w0 := c_enc.c2.w15
    w1 := c_enc.w48
    w2 := c_enc.w49
    w3 := g.v1.w0
    w4 := g.v1.w1
    w5 := g.v1.w2
    w6 := g.v2.w0
    w7 := g.v2.w1
    w8 := g.v2.w2
    w9 := epoch
    w10 := w10
    w11 := w11
    w12 := c_enc.c2.w2
    w13 := w13
    w14 := w14
    w15 := w15
  }
  mid := mid
  tail := tail

theorem mkSplit928Ct2Sampled_mid_length (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) {mid : List (BitVec 8)} (tail : Words5)
    (h : mid.length = 376) :
    (mkSplit928Ct2Sampled c_enc g epoch w10 w11 w13 w14 w15 mid tail).mid.length = 376 := h

theorem split928At_mkSplit928Ct2Sampled_eq (outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) (mid : List (BitVec 8)) (tail : Words5) :
    split928At outA (mkSplit928Ct2Sampled c_enc g epoch w10 w11 w13 w14 w15 mid tail) =
      ((outA ↦₆₄ 12#64) ∗
        words50At (outA + 8#64) c_enc ∗
        wordsAt (outA + 408#64) (ct2SentWordsList g epoch) ∗
        wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) := by
  dsimp only [split928At, mkSplit928Ct2Sampled, words50At, ct2SentWordsList, authWordsList,
    vecWordsList, Words16.toList, Words5.toList]
  simp only [List.cons_append, List.nil_append,
    wordsAt_16, wordsAt_7, wordsAt_6, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem split928At_reconstruct_ct2Sampled (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64)
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (outEnc : PolyEncoder)
    (c_enc : Words50) (g : AuthWords)
    (w10 w11 w13 w14 w15 : BitVec 64) {mid : List (BitVec 8)} (tail : Words5)
    (hmid : mid.length = 376) :
    split928At outA (mkSplit928Ct2Sampled c_enc g outUc.epoch w10 w11 w13 w14 w15 mid tail) ∗
      relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
    chunkedStatesAt A outA (.ct2Sampled { uc := outUc, sending_ct2 := outEnc }) := by
  rw [split928At_mkSplit928Ct2Sampled_eq]
  have henc :
      words50At (outA + 8#64) c_enc ∗
        relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ⊢
      polyEncoderAt A (outA + 8#64) outEnc := by
    rw [words50At_eq_pointsToBytes]
    exact relocatedHeap_recompose (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes (outA + 8#64)
  have huc :
      wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (outA + 408#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose (fun dst => unchunkedCt2SentAt A dst outUc)
      (wordsBytes (ct2SentWordsList g outUc.epoch)) (outA + 408#64)
  have h48 :
      wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ⊢
      memRegion (outA + 464#64) 48 :=
    wordsAt_entails_memRegion [w10, w11, c_enc.c2.w2, w13, w14, w15] (outA + 464#64) 48 rfl
  have h376 :
      ((outA + 512#64) ↦ₛ mid) ⊢ memRegion (outA + 512#64) 376 := by
    rw [← hmid]
    exact ProofLib.pointsToBytes_entails_memRegion (outA + 512#64) mid
  have h40 :
      wordsAt (outA + 888#64) tail.toList ⊢ memRegion (outA + 888#64) 40 :=
    wordsAt_entails_memRegion tail.toList (outA + 888#64) 40 rfl
  have h464 :
      wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList ⊢
      memRegion (outA + 464#64) 464 := by
    refine Entails.trans (sepConj_mono h48 (sepConj_mono h376 h40)) ?_
    rw [← ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
          (b' := outA + 888#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
          (b' := outA + 512#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hrearr :
      ((outA ↦₆₄ 12#64) ∗
        words50At (outA + 8#64) c_enc ∗
        wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) ∗
      relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) =
      (outA ↦₆₄ 12#64) ∗
      ((words50At (outA + 8#64) c_enc ∗
        relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes) ∗
       (wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g outUc.epoch)))) ∗
      (wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) := by ac_rfl
  rw [hrearr]
  have hdest :
      chunkedStatesAt A outA (.ct2Sampled { uc := outUc, sending_ct2 := outEnc }) =
      (outA ↦₆₄ 12#64) ∗
        (polyEncoderAt A (outA + 8#64) outEnc ∗
          unchunkedCt2SentAt A (outA + 408#64) outUc) ∗
        memRegion (outA + 464#64) 464 := by
    dsimp only [chunkedStatesAt, chunkedCt2SampledAt]
    have h408 : (outA + 8#64) + 400#64 = outA + 408#64 := by bv_omega
    rw [h408]
  rw [hdest]
  exact sepConj_mono_right (sepConj_mono (sepConj_mono henc huc) h464)

/-- Scratch staging layout for Path 5c (`States.ct2Sampled`), where `c0.w11` (`fsp + 88`) and
    `w90` (`fsp + 144`) retain their prior values from `sc`. -/
@[expose] def copyFullScratchCt2 (sc : CopyScratchStack) (d : Split928) : CopyScratchStack :=
  { (copyFullScratch sc d) with
    c0 := { (copyFullScratch sc d).c0 with w11 := sc.c0.w11 }
    w90 := sc.w90 }

section SendCt2AndEncode

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi

@[local arm64_norm] private theorem mem_writeReg64_ct1s6 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local arm64_norm] private theorem symtab_writeReg64_ct1s6 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl
@[local arm64_norm] private theorem mem_setPC_ct1s6 (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := by cases s; rfl
@[local arm64_norm] private theorem symtab_setPC_ct1s6 (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

abbrev ct1SampledSendCt2Cont (prog : Program) (s0 : State) (P_pan : Prop) (R : SepProp)
    (post : State → SepProp → Prop) : State → SepProp → Prop :=
  fun sm Pm =>
    SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))

end SendCt2AndEncode

end CryptoVerification.SpqrV1.States.Recv
