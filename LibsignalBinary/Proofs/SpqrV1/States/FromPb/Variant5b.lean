/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 5 (`NoHeaderReceived`, `+1344`) — Part B

Header validation (`+1344 -> +3744 | +1396`), early error paths, and `Authenticator` key
cloning and input-buffer deallocation (`+3744 -> +6064`).
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

theorem v5b_memRegion_2304_split_224_232 (fsp : BitVec 64) :
    memRegion fsp 2304 ⊢
      memRegion fsp 224 ∗
      (∃∗ z224 : BitVec 64, ((fsp + 224#64) ↦₆₄ z224)) ∗
      (∃∗ z232 : BitVec 32, ((fsp + 232#64) ↦₃₂ z232)) ∗
      memRegion (fsp + 236#64) 2068 := by
  exact split_top <|
    split_step0 (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem32_entails _) <|
    Entails.refl _

theorem v5b_memRegion_2304_join_224_232 (fsp w224 : BitVec 64) (d232 : BitVec 32) :
    memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
      ((fsp + 232#64) ↦₃₂ d232) ∗ memRegion (fsp + 236#64) 2068 ⊢
      memRegion fsp 2304 := by
  exact collapse_top <|
    collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (pointsTo32_entails_memRegion_4 _ _) <|
    Entails.refl _

theorem v5b_c1_add_two_uge_two {c1 : BitVec 64} (h : c1.toNat < 2 ^ 63) :
    (BitVec.ult (c1 + 2#64) 2#64) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem v5b_cond_ls_none2Cap :
    ConditionHolds CondCode.LS (addsPState64 18446744073709551614#64 3#64) = false := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  decide

@[local simp, local arm64_norm, local wp_norm]
theorem v5b_cond_ls_noneCap :
    ConditionHolds CondCode.LS (addsPState64 18446744073709551615#64 3#64) = false := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  decide

theorem v5b_live_bytes_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64)
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
  rw [← h2]
  exact sepConj_mono_left h1

theorem v5b_ite_nil_entails_vecCapPtrDealloc (A : RustAlloc) (c p : BitVec 64) :
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

theorem v5b_sepWP_exists_post {α : Type} {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q : α → State → SepProp → Prop} (a : α)
    (h : SepWP prog target s P (Q a)) :
    SepWP prog target s P (fun sm Pm => ∃ x : α, Q x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hq => ⟨a, hq⟩

theorem v5b_c1_cmn3_ls_true {c1 : BitVec 64} (h : c1.toNat < 2 ^ 63) :
    ConditionHolds CondCode.LS (addsPState64 c1 3#64) = true := by
  unfold ConditionHolds addsPState64 AddWithCarry64
  have hmsb : ((if false = true then 1#65 else 0#65) +
      (BitVec.zeroExtend 65 3#64 + BitVec.zeroExtend 65 c1)).msb = false := by
    revert h; bv_bits
  dsimp only
  rw [hmsb]
  rfl

theorem v5b_stackAt_encoderFromPb_split_7552 (sp0 : BitVec 64) :
    stackAt (sp0 - 2400#64) encoderFromPbStack =
      memRegion (sp0 - 7552#64) 1056 ∗ stackAt (sp0 - 2400#64) allocHookStack := by
  have h := ProofLib.stackAt_split_bottom (sp0 - 2400#64) allocHookStack 1056 (by decide)
  change stackAt (sp0 - 2400#64) encoderFromPbStack =
    memRegion ((sp0 - 2400#64) - 5152#64) 1056 ∗ stackAt (sp0 - 2400#64) allocHookStack at h
  have haddr : (sp0 - 2400#64) - 5152#64 = sp0 - 7552#64 := by bv_omega
  rw [h, haddr]

end CryptoVerification.SpqrV1.States.FromPb
