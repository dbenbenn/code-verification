/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

/-!
# `<States>::recv` — `.keysSampled` Arm, Part 1

**Checked by Lean.** Post-call writeback helpers, the `msg.epoch > st.uc.epoch` and
`msg.epoch < st.uc.epoch` branches of `.keysSampled` (`0x55b58`, `+1796`), and their
`AllocContractsX` corollaries.
-/

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

/-! ## 1. `.keysSampled` (`0x55b58`, `+1796`): Helpers & `msg.epoch > st.uc.epoch` -/

theorem words63_keysSampled_entails_ct1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) (w : Words63) :
    words63At a w ∗
      relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ⊢
      chunkedCt1ReceivedAt A a (chunkedKeysSampledToCt1Received st) := by
  rw [← chunkedKeysSampledAt_eq_ct1ReceivedAt]
  exact recompose63 a w

theorem stackAt_statesRecvCallee_split_keysSampledRecvCt1 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX)
        (statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) ∗
      stackAt sp keysSampledRecvCt1ChunkStack := by
  have hdiff : BitVec.ofNat 64 statesRecvCalleeStackX -
      BitVec.ofNat 64 (statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) =
      BitVec.ofNat 64 keysSampledRecvCt1ChunkStack := rfl
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - keysSampledRecvCt1ChunkStack) (k := keysSampledRecvCt1ChunkStack)
    (b' := sp - BitVec.ofNat 64 keysSampledRecvCt1ChunkStack) rfl
    (by rw [← hdiff]; bv_omega)
    (by decide)

end CryptoVerification.SpqrV1.States.Recv

