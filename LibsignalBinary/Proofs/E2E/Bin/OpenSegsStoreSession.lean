/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base

/-!
# Store-Session Segment Proof for `libsignal_e2e::open` (`0x43c6c..0x43ca0`)

Proves segment 7 (`open_seg_store_session'`, `+0x234..+0x268`) of `libsignal_e2e::open`.
-/

public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

/-! ## Segment 7: `open_seg_store_session'` (`+0x234..+0x268`, 13 insns) -/

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

private theorem exists_mem_zip_of_mem_left :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := exists_mem_zip_of_mem_left hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

private theorem binCanonSession_of_canonSession_storeSession {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Record.Serialization.CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender; unfold Record.Serialization.CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := exists_mem_zip_of_mem_left hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 := by
      unfold PublicKey.serialize; simp [List.Vector.toList_length]
    exact ⟨hcc.1 ▸ hser_len, hcc.2⟩

private theorem if_entry_mono (c : Prop) [Decidable c] {P Q R : SepProp} (h : P ⊢ Q) :
    (if c then P else R) ⊢ (if c then Q else R) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h
  · simp only [hc, ↓reduceIte]; exact Entails.refl _

private theorem arrayAt_mono_entry4 (stride : Nat) (base : BitVec 64) (k : Nat)
    {entry1 entry2 : BitVec 64 → SepProp} (he : ∀ a, entry1 a ⊢ entry2 a) :
    arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base (List.range 4).reverse ⊢
      arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base (List.range 4).reverse := by
  change arrayAt (fun i a => if i ∈ [k] then entry1 a else memRegion a stride) stride base [3, 2, 1, 0] ⊢
    arrayAt (fun i a => if i ∈ [k] then entry2 a else memRegion a stride) stride base [3, 2, 1, 0]
  dsimp only [arrayAt]
  exact sepConj_mono (if_entry_mono _ (he _))
    (sepConj_mono (if_entry_mono _ (he _))
      (sepConj_mono (if_entry_mono _ (he _))
        (sepConj_mono (if_entry_mono _ (he _)) (Entails.refl _))))

end CryptoVerification.E2E.Bin
