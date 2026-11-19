/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainFromVNNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem memRegion_88_err_split (out : BitVec 64) :
    memRegion out 88 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      (∃∗ bs7 : List (BitVec 8), ⌜bs7.length = 7⌝ ∗ ((out + 9#64) ↦ₛ bs7)) ∗
      (∃∗ w1 : BitVec 64, (out + 16#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (out + 24#64) ↦₆₄ w2) ∗
      memRegion (out + 32#64) 56 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 80)
      (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 79)
      (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 72)
      (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 64)
      (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 56)
      (b' := out + 32#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_eq_exists_bytes (out + 9#64) 7 (by decide),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

theorem byte_bs7_word_to_pointsTo128 (a : BitVec 64) (b0 : BitVec 8)
    {bs7 : List (BitVec 8)} (hbs7 : bs7.length = 7) (w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs7) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢
      ∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = b0⌝ ∗ (a ↦₁₂₈ q0) := by
  have hlen8 : (b0 :: bs7).length = 8 := by simp [hbs7]
  obtain ⟨w0, hw0_bytes⟩ := exists_unpack64_of_length_8 hlen8
  have hcons : ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs7)) = (a ↦₆₄ w0) := by
    rw [← pointsToBytes_cons, hw0_bytes, ← pointsTo64_eq_pointsToBytes]
  have hb0 : BitVec.truncate 8 (w1 ++ w0) = b0 := by
    have hhead : (b0 :: bs7).head? = (unpack64 w0).head? := congrArg List.head? hw0_bytes
    simp only [unpack64, List.head?_cons, Option.some.injEq] at hhead
    have htr : BitVec.truncate 8 (w1 ++ w0) = BitVec.extractLsb' 0 8 w0 := by bv_kernel
    rw [htr, ← hhead]
  have hp128 : ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
    unfold pointsTo128
    have hlo : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
    have hhi : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
    rw [hlo, hhi]
  rw [← sepConj_assoc, hcons, hp128]
  exact Entails.sepExists_right (w1 ++ w0) (Entails.pure_right hb0 (Entails.refl _))

theorem fold_chainErrorAt (out : BitVec 64) (err : Error) (tag : BitVec 8)
    (htag : tag = spqrErrorTag err)
    {bs7 : List (BitVec 8)} (hbs7 : bs7.length = 7) (w1 w2 : BitVec 64) :
    (out ↦₆₄ 18446744073709551615#64) ∗ ((out + 8#64) ↦₈ tag) ∗ ((out + 9#64) ↦ₛ bs7) ∗
      ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err := by
  subst htag
  change (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗
      ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err
  have h1 := byte_bs7_word_to_pointsTo128 (out + 8#64) (spqrErrorTag err) hbs7 w1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  have h2 : (out ↦₆₄ noneCap) ∗
      (((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗ ((out + 16#64) ↦₆₄ w1)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      (out ↦₆₄ noneCap) ∗
      (∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 :=
    sepConj_mono_right (sepConj_mono_left h1)
  have h3 : (out ↦₆₄ noneCap) ∗
      (∃∗ q0 : BitVec 128, ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
      ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 ⊢
      chainErrorAt out err := by
    simp only [chainErrorAt, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro q0
    refine Entails.sepExists_right q0 (Entails.sepExists_right w2 ?_)
    have heq :
        (out ↦₆₄ noneCap) ∗ (⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ ((out + 8#64) ↦₁₂₈ q0)) ∗
          ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 =
        ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗ (out ↦₆₄ noneCap) ∗
          ((out + 0x08#64) ↦₁₂₈ q0) ∗ ((out + 0x18#64) ↦₆₄ w2) ∗
          memRegion (out + 0x20#64) 56 := by ac_rfl
    rw [heq]
    exact Entails.refl _
  have hassoc :
      (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗
        ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 =
      (out ↦₆₄ noneCap) ∗
        (((out + 8#64) ↦₈ spqrErrorTag err) ∗ ((out + 9#64) ↦ₛ bs7) ∗ ((out + 16#64) ↦₆₄ w1)) ∗
        ((out + 24#64) ↦₆₄ w2) ∗ memRegion (out + 32#64) 56 := by ac_rfl
  rw [hassoc]
  exact Entails.trans h2 h3

@[expose] def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (len : Nat) : SepProp :=
  ⌜len ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 len) (cap.toNat - len))

theorem vecU8At_entails_header_bytesAt_rest (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      ⌜bs.length < 2 ^ 63⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false ptr bs ∗ vecU8BufRest A cap ptr bs.length := by
  unfold vecU8At vecHeader vecU8BufRest bytesAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ ptr ↦ₛ bs ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  have hlen64 : bs.length < 2 ^ 63 := by omega
  refine Entails.pure_right hlen64 ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    rw [show ((v ↦₆₄ (0 : BitVec 64)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
        ⌜([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
          (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝) =
      ⌜([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ (0 : BitVec 64)) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem header_bytesAt_rest_entails_vecU8At (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false ptr bs ∗ vecU8BufRest A cap ptr bs.length ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader vecU8BufRest bytesAt
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [show ((v ↦₆₄ cap ∗ (v + 8#64) ↦₆₄ ptr ∗ (v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗ ptr ↦ₛ bs ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

/-- `Direction.fromI32? d` characterization via unsigned comparison `(1#32).ult d`. -/
theorem direction_fromI32_or (d : BitVec 32) :
    (∃ dir : Direction,
      d = dir.toI32 ∧
      Direction.fromI32? d = some dir ∧
      (1#32).ult d = false) ∨
    (Direction.fromI32? d = none ∧
      (1#32).ult d = true) := by
  by_cases h0 : d = 0#32
  · subst h0
    exact Or.inl ⟨.a2b, rfl, rfl, rfl⟩
  · by_cases h1 : d = 1#32
    · subst h1
      exact Or.inl ⟨.b2a, rfl, rfl, rfl⟩
    · refine Or.inr ⟨by simp [Direction.fromI32?, h0, h1], ?_⟩
      rw [BitVec.ult_eq_decide, decide_eq_true_eq]
      have h0' : d.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      have h1' : d.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
      change 1 < d.toNat
      omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_toI32 (dir : Direction) : (1#32).ult dir.toI32 = false := by
  cases dir <;> rfl

theorem onPanic_entails_of_trace_eq {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem SepWPp.pure_left_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem chainNew_post_entails_chainRepr (A : RustAlloc) (out : BitVec 64) (ch : Chain) :
    (∃∗ G : ChainGhost, ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗ chainAt A out G ch) ⊢
      chainRepr A out ch := by
  unfold chainRepr
  refine Entails.sepExists_elim fun G => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right G (Entails.refl _)

theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} (heq : P = P')
    (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  heq ▸ h

end ChainFromVNNorm

open ChainFromVNNorm

end CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
