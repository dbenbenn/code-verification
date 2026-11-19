/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 6 (`HeaderReceived`, `+1464`) — Part C
Cloning (`+3796 -> +8812 -> +9852`) and deallocation (`+9852 -> +9936`, `+10416`, `+10492`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.defProp false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append


/-! ## 1. `SepWPp` & `vecU8Payload` Helpers (`v6hr_*`) -/

theorem v6hr_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v6hr_sepWP_exists_post {α : Type} {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : α → State → SepProp → Prop} (a : α)
    (h : SepWP prog target s P (Q a)) :
    SepWP prog target s P (fun sm Pm => ∃ x : α, Q x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨a, hq⟩

theorem v6hr_pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

theorem v6hr_live_bytes_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) (hc : c ≠ 0#64) (hle : bs.length ≤ c.toNat) :
    A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  have hcf : (c == 0#64) = false := beq_false_of_ne hc
  simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  apply sepConj_mono_right
  have h1 := ProofLib.pointsToBytes_entails_memRegion p bs
  have hadd : bs.length + (c.toNat - bs.length) = c.toNat := Nat.add_sub_of_le hle
  have h2 : memRegion p bs.length ∗ memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length) =
      memRegion p c.toNat := by
    rw [← ProofLib.memRegion_split' (b := p) (n := bs.length) (k := c.toNat - bs.length)
      (b' := p + BitVec.ofNat 64 bs.length) hadd.symm rfl (by omega)]
  rw [← h2]; exact sepConj_mono_left h1

theorem v6hr_ite_nil_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64) :
    (if c = 0#64 then emp
     else A.live p c.toNat 1 ∗ (p ↦ₛ ([] : List (BitVec 8))) ∗
       memRegion (p + 0#64) (c.toNat - 0)) ⊢
      vecCapPtrDealloc A c p := by
  unfold vecCapPtrDealloc
  by_cases hc : c = 0#64
  · subst hc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · have hcf : (c == 0#64) = false := beq_false_of_ne hc
    simp only [hc, hcf, Bool.false_eq_true, ↓reduceIte,
      ProofLib.pointsToBytes_nil, emp_sepConj, BitVec.add_zero, Nat.sub_zero]
    exact Entails.refl _

theorem v6hr_vecU8Payload_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Payload A c p bs ⊢ vecCapPtrDealloc A c p := by
  unfold vecU8Payload
  apply Entails.pure_left; intro ⟨hle, _, _⟩
  by_cases hc : c = 0#64
  · subst hc; simp only [↓reduceIte]; unfold vecCapPtrDealloc; simp only [beq_self_eq_true, ↓reduceIte]; exact Entails.refl _
  · simp only [hc, ↓reduceIte]; exact v6hr_live_bytes_entails_vecCapPtrDealloc A c p bs hc hle

theorem v6hr_from_pb_ptsNeeded_ne (F : ShaCompress)
    (uc : Option V1State.Unchunked.HeaderReceived) (decPb : PolynomialDecoder)
    (hne : decPb.ptsNeeded ≠ 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := uc, receivingEk := some decPb }) } =
    .error (.err .msgDecode) := by
  have hne_nat : decPb.ptsNeeded.toNat ≠ 576 := fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h))
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, hne_nat, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem v6hr_from_pb_uc_none_dec_none (F : ShaCompress) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := none, receivingEk := none }) } =
    .error (.err .stateDecode) := rfl

theorem v6hr_from_pb_uc_none_dec_some (F : ShaCompress) (decPb : PolynomialDecoder)
    (heq : decPb.ptsNeeded = 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := none, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, heq, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_auth_none_dec_none (F : ShaCompress)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := none, epoch := epoch }, receivingEk := none }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  by_cases hlen : (hdr.length == HEADER_SIZE) = true <;> simp [hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_auth_none_dec_some (F : ShaCompress)
    (hdr : List (BitVec 8)) (epoch : BitVec 64) (decPb : PolynomialDecoder) (heq : decPb.ptsNeeded = 576#32) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := none, epoch := epoch }, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  by_cases hlen : (hdr.length == HEADER_SIZE) = true <;>
    simp [ENCAPSULATION_KEY_SIZE, heq, hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_ne64_dec_none (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64) (hne : hdr.length ≠ 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := some authPb, epoch := epoch }, receivingEk := none }) } =
    .error (.err .stateDecode) := by
  have hlen : (hdr.length == HEADER_SIZE) = false := beq_false_of_ne hne
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [hlen, bind, Except.bind, pure, Except.pure]

theorem v6hr_from_pb_hdr_ne64_dec_some (F : ShaCompress)
    (hdr : List (BitVec 8)) (authPb : ProtoAuthenticator) (epoch : BitVec 64)
    (decPb : PolynomialDecoder) (heq : decPb.ptsNeeded = 576#32) (hne : hdr.length ≠ 64) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.headerReceived { uc := some { hdr := hdr, auth := some authPb, epoch := epoch }, receivingEk := some decPb }) } =
    .error (.err .stateDecode) := by
  have hlen : (hdr.length == HEADER_SIZE) = false := beq_false_of_ne hne
  unfold States.from_pb Chunked.SendCt.HeaderReceived.from_pb Unchunked.SendCt.HeaderReceived.from_pb
  simp [ENCAPSULATION_KEY_SIZE, heq, hlen, bind, Except.bind, pure, Except.pure]

end CryptoVerification.SpqrV1.States.FromPb

