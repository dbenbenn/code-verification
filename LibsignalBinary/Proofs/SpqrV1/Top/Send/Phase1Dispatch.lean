/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>` Phase 1c: `<States>::from_pb` Call, Error Path, and Jump-Table Dispatch

**Checked by Lean.**

Verifies the pre-call setup at `+224`, the `.error (.err err)` cleanup return path at `+248`,
and the `.ok st0` `32 + 896`B relocation (`sp + 0x1260 -> sp + 0x950`) and 11-way jump-table 1
dispatch (`0x30954..0x309cc`) to `spqrSendEntry b + statesSendArmOffset st0`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

/-! ## Pre-Call Step (`+224 -> statesFromPb`, `0x3093c..0x30950`) -/

@[local arm64_norm, local wp_norm]
theorem sp_add_30_add_80 (sp : BitVec 64) : (sp + 0x30#64) + 128#64 = sp + 0xb0#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_8 (sp : BitVec 64) : (sp + 0x1260#64) + 8#64 = sp + 0x1268#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_16 (sp : BitVec 64) : (sp + 0x1260#64) + 16#64 = sp + 0x1270#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_24 (sp : BitVec 64) : (sp + 0x1260#64) + 24#64 = sp + 0x1278#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_32 (sp : BitVec 64) : (sp + 0x1260#64) + 32#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_8 (sp : BitVec 64) : (sp + 0x1268#64) + 8#64 = sp + 0x1270#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_16 (sp : BitVec 64) : (sp + 0x1268#64) + 16#64 = sp + 0x1278#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_24 (sp : BitVec 64) : (sp + 0x1268#64) + 24#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_930_add_8 (sp : BitVec 64) : (sp + 0x930#64) + 8#64 = sp + 0x938#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_930_add_16 (sp : BitVec 64) : (sp + 0x930#64) + 16#64 = sp + 0x940#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_8 (sp : BitVec 64) : (sp + 0x950#64) + 8#64 = sp + 0x958#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_16 (sp : BitVec 64) : (sp + 0x950#64) + 16#64 = sp + 0x960#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_24 (sp : BitVec 64) : (sp + 0x950#64) + 24#64 = sp + 0x968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_32 (sp : BitVec 64) : (sp + 0x950#64) + 32#64 = sp + 0x970#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_8 (sp : BitVec 64) : (sp + 0x958#64) + 8#64 = sp + 0x960#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_16 (sp : BitVec 64) : (sp + 0x958#64) + 16#64 = sp + 0x968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_24 (sp : BitVec 64) : (sp + 0x958#64) + 24#64 = sp + 0x970#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_608 (sp : BitVec 64) : (sp + 4096#64) + 608#64 = sp + 0x1260#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_640 (sp : BitVec 64) : (sp + 4096#64) + 640#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_96 (sp : BitVec 64) : (sp + 4096#64) + 96#64 = sp + 0x1060#64 := by bv_omega
@[local arm64_norm, local wp_norm]
private theorem bv_add_add_lit_p1d (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

theorem resultChunkedStatesAt_err_entails_head32_896 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : LibsignalSpqrV1.Error) :
    resultChunkedStatesAt A (F := F) a (.error (.err err)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 896 := by
  unfold resultChunkedStatesAt
  have hm8 : ((a + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (a + 9#64) 919 ⊢
      memRegion (a + 8#64) 920 := by
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 919) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 8#64) (spqrErrorByte err))
  refine Entails.trans (sepConj_mono_right hm8) ?_
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 912) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 904) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 896) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_sp_930_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x930#64) 24 =
      (∃∗ d0 : BitVec 64, ((sp + 0x930#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x938#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x940#64) ↦₆₄ d2)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 8) (k := 16)
        (b' := sp + 0x938#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x938#64) (n := 8) (k := 8)
        (b' := sp + 0x940#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x930#64),
      ProofLib.memRegion_eight (sp + 0x938#64),
      ProofLib.memRegion_eight (sp + 0x940#64)]

theorem words3_930_entails_memRegion_24 (sp w1 w2 w3 : BitVec 64) :
    ((sp + 0x930#64) ↦₆₄ w1) ∗ ((sp + 0x938#64) ↦₆₄ w2) ∗ ((sp + 0x940#64) ↦₆₄ w3) ⊢
      memRegion (sp + 0x930#64) 24 := by
  rw [memRegion_sp_930_split_24 sp]
  exact sepConj_mono (Entails.sepExists_intro w1)
    (sepConj_mono (Entails.sepExists_intro w2) (Entails.sepExists_intro w3))

theorem words4_and_896_1260_entails_memRegion_928 (sp w0 w1 w2 w3 : BitVec 64) :
    ((sp + 0x1260#64) ↦₆₄ w0) ∗ ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗ ((sp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (sp + 0x1280#64) 896 ⊢
      memRegion (sp + 0x1260#64) 928 := by
  have h928 : memRegion (sp + 0x1260#64) 928 =
      (∃∗ d0 : BitVec 64, ((sp + 0x1260#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x1268#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x1270#64) ↦₆₄ d2)) ∗
      (∃∗ d3 : BitVec 64, ((sp + 0x1278#64) ↦₆₄ d3)) ∗
      memRegion (sp + 0x1280#64) 896 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 8) (k := 920)
          (b' := sp + 0x1268#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1268#64) (n := 8) (k := 912)
          (b' := sp + 0x1270#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1270#64) (n := 8) (k := 904)
          (b' := sp + 0x1278#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1278#64) (n := 8) (k := 896)
          (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (sp + 0x1260#64),
        ProofLib.memRegion_eight (sp + 0x1268#64),
        ProofLib.memRegion_eight (sp + 0x1270#64),
        ProofLib.memRegion_eight (sp + 0x1278#64)]
  rw [h928]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1)
      (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono_left (Entails.sepExists_intro w3))))

theorem memRegion_b0_to_1260_split_930 (fsp : BitVec 64) :
    memRegion (fsp + 0xb0#64) (0x1260 - 0xb0) ⊢
      ∃∗ s0_930 : BitVec 64, ∃∗ s1_938 : BitVec 64, ∃∗ s2_940 : BitVec 64,
        memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
        ((fsp + 0x930#64) ↦₆₄ s0_930) ∗
        ((fsp + 0x938#64) ↦₆₄ s1_938) ∗
        ((fsp + 0x940#64) ↦₆₄ s2_940) ∗
        memRegion (fsp + 0x948#64) (0x1260 - 0x948) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 0x1260 - 0x930)
        (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 0x1260 - 0x948)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide),
      memRegion_sp_930_split_24 fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro s2_940
  apply Entails.sepExists_elim; intro s1_938
  apply Entails.sepExists_elim; intro s0_930
  refine Entails.sepExists_right s0_930
    (Entails.sepExists_right s1_938 (Entails.sepExists_right s2_940 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem rejoin_b0_to_1f20_after_states_err (fsp w0 w1 w2 w3 : BitVec 64) :
    memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      ((fsp + 0x930#64) ↦₆₄ w1) ∗
      ((fsp + 0x938#64) ↦₆₄ w2) ∗
      ((fsp + 0x940#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1280#64) 896 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) ⊢
      memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) := by
  have h930 := words3_930_entails_memRegion_24 fsp w1 w2 w3
  have h1260 := words4_and_896_1260_entails_memRegion_928 fsp w0 w1 w2 w3
  have hreord :
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      ((fsp + 0x930#64) ↦₆₄ w1) ∗
      ((fsp + 0x938#64) ↦₆₄ w2) ∗
      ((fsp + 0x940#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1280#64) 896 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) =
      (((fsp + 0x930#64) ↦₆₄ w1) ∗ ((fsp + 0x938#64) ↦₆₄ w2) ∗ ((fsp + 0x940#64) ↦₆₄ w3)) ∗
      (((fsp + 0x1260#64) ↦₆₄ w0) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
       ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗
       memRegion (fsp + 0x1280#64) 896) ∗
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h930 (sepConj_mono_left h1260)) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 0x1f20 - 0x930)
        (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 0x1f20 - 0x948)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x948#64) (n := 0x1260 - 0x948) (k := 0x1f20 - 0x1260)
        (b' := fsp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 928) (k := 0x1f20 - 0x1600)
        (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

@[simp, arm64_norm, wp_norm]
theorem chunkedStatesWord0_add_one_beq_zero {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    (chunkedStatesWord0 st0 + 1#64 == 0#64) = false := by
  cases st0 with
  | ct1Sampled s => exact polyEncoderTagVal_add_one_beq_zero s.sending_ct1.s
  | _ => rfl

theorem pointsToBytes_8_eq_one_cell (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 8) :
    (a ↦ₛ bs) ⊢ ∃∗ w : BitVec 64, ⌜bs = unpack64 w⌝ ∗ (a ↦₆₄ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length] at hlen; omega)
  refine Entails.sepExists_right (pack64 b0 b1 b2 b3 b4 b5 b6 b7) ?_
  have hpack : unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
    dsimp only [pack64]
    exact ProofLib.unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  rw [hpack]
  apply Entails.pure_right rfl
  rw [ProofLib.pointsTo64_eq_pointsToBytes, hpack]
  exact Entails.refl _

theorem pointsToBytes_920_split_3words_896 (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 920) :
    (a ↦ₛ bs) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) := by
  let b16 := bs.take 16
  let r16 := bs.drop 16
  let b8 := r16.take 8
  let bs896 := r16.drop 8
  have hb16 : b16.length = 16 := by simp [b16, hlen]
  have hr16 : r16.length = 904 := by simp [r16, hlen]
  have hb8 : b8.length = 8 := by simp [b8, hr16]
  have hbs896 : bs896.length = 896 := by simp [bs896, hr16]
  have hsplit : (a ↦ₛ bs) = (a ↦ₛ b16) ∗ ((a + 16#64) ↦ₛ b8) ∗ ((a + 24#64) ↦ₛ bs896) := by
    have hbs1 : bs = b16 ++ (b8 ++ bs896) := by
      simp only [b16, r16, b8, bs896, List.take_append_drop]
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append a b16, hb16,
        ProofLib.pointsToBytes_append (a + 16#64) b8, hb8]
    have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
    rw [ha24]
  rw [hsplit]
  refine Entails.trans
    (sepConj_mono (pointsToBytes_16_eq_two_cells a hb16)
      (sepConj_mono_left (pointsToBytes_8_eq_one_cell (a + 16#64) hb8))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  have hpull :
      ((⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2)) ∗
       (⌜b8 = unpack64 w3⌝ ∗ ((a + 16#64) ↦₆₄ w3)) ∗
       ((a + 24#64) ↦ₛ bs896)) =
      ⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ ⌜b8 = unpack64 w3⌝ ∗
        ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw12
  apply Entails.pure_left; intro hw3
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_)))
  have hbs_eq : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
    calc bs = b16 ++ (b8 ++ bs896) := by simp only [b16, r16, b8, bs896, List.take_append_drop]
      _ = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
          rw [hw12, hw3]
          simp only [List.append_assoc]
  exact Entails.pure_right ⟨hbs_eq, hbs896⟩ (Entails.refl _)

theorem words3_and_896_entails_pointsToBytes_920 (a w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) ⊢
      (a ↦ₛ bs) := by
  subst hbs
  simp only [List.append_assoc]
  rw [pointsToBytes_append a (unpack64 w1), unpack64_length, ← pointsTo64_eq_pointsToBytes a w1,
      pointsToBytes_append (a + 8#64) (unpack64 w2), unpack64_length,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) w2,
      pointsToBytes_append ((a + 8#64) + 8#64) (unpack64 w3), unpack64_length,
      ← pointsTo64_eq_pointsToBytes ((a + 8#64) + 8#64) w3]
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedStatesAt_1260_entails_reloc (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A (sp + 0x1260#64) st0 ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        ((sp + 0x1280#64) ↦ₛ bs896) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x1260#64) st0, sp_add_1260_add_8 sp]
  refine Entails.trans (sepConj_mono_right (Relocatable.of_chunkedStatesTail920At A st0 (sp + 0x1268#64))) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hlen920
  have hsplit := pointsToBytes_920_split_3words_896 (sp + 0x1268#64) hlen920
  rw [sp_add_1268_add_8 sp, sp_add_1268_add_16 sp, sp_add_1268_add_24 sp] at hsplit
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsplit)) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs896
  refine Entails.sepExists_right bs (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_sp_950_split_4words_896 (sp : BitVec 64) :
    memRegion (sp + 0x950#64) 928 =
      (∃∗ d0 : BitVec 64, ((sp + 0x950#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x958#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x960#64) ↦₆₄ d2)) ∗
      (∃∗ d3 : BitVec 64, ((sp + 0x968#64) ↦₆₄ d3)) ∗
      memRegion (sp + 0x970#64) 896 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x950#64) (n := 8) (k := 920)
        (b' := sp + 0x958#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x958#64) (n := 8) (k := 912)
        (b' := sp + 0x960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 8) (k := 904)
        (b' := sp + 0x968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x968#64) (n := 8) (k := 896)
        (b' := sp + 0x970#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x950#64),
      ProofLib.memRegion_eight (sp + 0x958#64),
      ProofLib.memRegion_eight (sp + 0x960#64),
      ProofLib.memRegion_eight (sp + 0x968#64)]

theorem reassemble_chunkedStatesAt_950 (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
      ((sp + 0x958#64) ↦₆₄ w1) ∗
      ((sp + 0x960#64) ↦₆₄ w2) ∗
      ((sp + 0x968#64) ↦₆₄ w3) ∗
      ((sp + 0x970#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ⊢
      chunkedStatesAt A (sp + 0x950#64) st0 := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) st0, sp_add_950_add_8 sp]
  refine sepConj_mono_right ?_
  have h920 := words3_and_896_entails_pointsToBytes_920 (sp + 0x958#64) w1 w2 w3 hbs
  rw [sp_add_958_add_8 sp, sp_add_958_add_16 sp, sp_add_958_add_24 sp] at h920
  have hreord :
      ((sp + 0x958#64) ↦₆₄ w1) ∗ ((sp + 0x960#64) ↦₆₄ w2) ∗
      ((sp + 0x968#64) ↦₆₄ w3) ∗ ((sp + 0x970#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs =
      (((sp + 0x958#64) ↦₆₄ w1) ∗ ((sp + 0x960#64) ↦₆₄ w2) ∗
       ((sp + 0x968#64) ↦₆₄ w3) ∗ ((sp + 0x970#64) ↦ₛ bs896)) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left h920) ?_
  exact relocatedHeap_recompose (fun dst => chunkedStatesTail920At A dst st0) bs (sp + 0x958#64)

theorem reassemble_1260_after_memcpy (sp w0 w1 w2 w3 : BitVec 64)
    {bs896 : List (BitVec 8)} (hlen896 : bs896.length = 896) :
    ((sp + 0x1260#64) ↦₆₄ w0) ∗ ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗ ((sp + 0x1278#64) ↦₆₄ w3) ∗
      ((sp + 0x1280#64) ↦ₛ bs896) ⊢
      memRegion (sp + 0x1260#64) 928 := by
  have hm : ((sp + 0x1280#64) ↦ₛ bs896) ⊢ memRegion (sp + 0x1280#64) 896 := by
    rw [← hlen896]; exact pointsToBytes_entails_memRegion (sp + 0x1280#64) bs896
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm)))) ?_
  exact words4_and_896_1260_entails_memRegion_928 sp w0 w1 w2 w3

end CryptoVerification.SpqrV1.Top.Send
