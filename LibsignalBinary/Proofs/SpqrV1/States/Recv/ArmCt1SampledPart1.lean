/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3856 (sp : BitVec 64) : (sp - 4240#64) + 3856#64 = sp - 384#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3272 (sp : BitVec 64) : (sp - 4240#64) + 3272#64 = sp - 968#64 := by bv_omega

/-! ## 1. Callee Stack Splits & Shared Direct Epilogue (`+19324 -> s0.x30`) -/

theorem stackAt_statesRecvCallee_eq_allocHook' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 15456 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack32' (fsp : BitVec 64) :

    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32 :=
  stackAt_split_bottom fsp dropStack32 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack48' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15408 ∗ stackAt fsp dropStack48 :=
  stackAt_split_bottom fsp dropStack48 15408 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack80' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15376 ∗ stackAt fsp dropStack80 :=
  stackAt_split_bottom fsp dropStack80 15376 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStackPoly64' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15392 ∗ stackAt fsp dropStackPoly64 :=
  stackAt_split_bottom fsp dropStackPoly64 15392 (by decide)

theorem stackAt_statesRecvCallee_eq_dropGluePoly16' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack :=
  stackAt_split_bottom fsp dropGluePoly16Stack 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_addChunk' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3072 ∗ stackAt fsp SpqrV1.Poly.AddChunk.addChunkStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.AddChunk.addChunkStackX 3072 (by decide)

theorem stackAt_statesRecvCallee_eq_polyDecodedMessage' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2496 ∗ stackAt fsp RecvCt2Chunk.polyDecodedMessageStackX :=
  stackAt_split_bottom fsp RecvCt2Chunk.polyDecodedMessageStackX 2496 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedRecvEk' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2960 ∗ stackAt fsp unchunkedRecvEkStack :=
  stackAt_split_bottom fsp unchunkedRecvEkStack 2960 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedSendCt2' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2832 ∗ stackAt fsp unchunkedSendCt2Stack :=
  stackAt_split_bottom fsp unchunkedSendCt2Stack 2832 (by decide)

theorem stackAt_statesRecvCallee_eq_sendCt2Encoder' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2096 ∗ stackAt fsp sendCt2EncoderStack :=
  stackAt_split_bottom fsp sendCt2EncoderStack 2096 (by decide)

theorem unchunkedCt1Sent400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (a + 400#64) st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  refine Entails.trans (unchunkedCt1SentAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fiveVec128HeadersAt_400_eq]
  exact Entails.refl _

theorem unchunkedCt1SentAt_epoch_expose (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (selfA + 400#64) uc =
      (authenticatorAt A (selfA + 400#64) uc.auth ∗
       vecU8 A (selfA + 448#64) uc.hdr ∗
       vecU8 A (selfA + 472#64) uc.es ∗
       vecU8 A (selfA + 496#64) uc.ct1) ∗
      ((selfA + 520#64) ↦₆₄ uc.epoch) := by
  dsimp only [unchunkedCt1SentAt]
  have h448 : (selfA + 400#64) + 48#64 = selfA + 448#64 := by bv_omega
  have h472 : (selfA + 400#64) + 72#64 = selfA + 472#64 := by bv_omega
  have h496 : (selfA + 400#64) + 96#64 = selfA + 496#64 := by bv_omega
  have h520 : (selfA + 400#64) + 120#64 = selfA + 520#64 := by bv_omega
  rw [h448, h472, h496, h520]
  ac_rfl

theorem epoch_cmp_b_eq_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_b_ne_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_b_eq_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_b_ne_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = true := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_b_eq_of_eq (ep : BitVec 64) :
    (BitVec.truncate 32 ((if ep.ule ep = true then if ep.ule ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = true := by
  have h1 : ep.ule ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp [h1]

theorem stackAt_statesRecvStackX_from_dropGluePoly16 (sp : BitVec 64) :
    memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropGluePoly16Stack ⊢
      stackAt sp statesRecvStackX := by
  rw [← stackAt_statesRecvStackX_eq_dropGluePoly16 sp]
  exact Entails.refl _

theorem stackAt_statesRecvCallee_from_allocHook (fsp : BitVec 64) :
    memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack ⊢
      stackAt fsp statesRecvCalleeStackX := by
  rw [← stackAt_statesRecvCallee_eq_allocHook' fsp]
  exact Entails.refl _

theorem stackAt_statesRecvCallee_from_dropGluePoly16 (fsp : BitVec 64) :
    memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack ⊢
      stackAt fsp statesRecvCalleeStackX := by
  rw [← stackAt_statesRecvCallee_eq_dropGluePoly16' fsp]
  exact Entails.refl _

theorem ct1Sampled_join_928 (selfA : BitVec 64) :
    memRegion selfA 528 ∗ memRegion (selfA + 528#64) polyArrayBytes ∗
      memRegion ((selfA + 528#64) + 384#64) 16 ⊢
    memRegion selfA chunkedStatesSize := by
  have hdec := polyDecoder_post_join (selfA + 528#64)
  refine Entails.trans (sepConj_mono_right hdec) ?_
  unfold chunkedStatesSize polyDecoderSize
  rw [ProofLib.memRegion_split' (b := selfA) (n := 528) (k := 400)
    (b' := selfA + 528#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.Recv

