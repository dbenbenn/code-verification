/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Base
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Top-Level Verification of `<Message>::deserialize`

Proves the `format_inner` unknown-tag error branch (`0x5f6f0..0x5f780`, `+700..+844`), entry
dispatch, and top-level correctness theorems (`MessageDeserializeOkX`) for
`<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`).
-/

public section

namespace CryptoVerification.SpqrV1.Layout.L25

open Lean Meta Elab Term Command Tactic ProofLib ProofLib.CodeLookup
open CryptoVerification.CodeLayout

scoped elab (name := codeFetchesRangeLenDeser) "code_fetches_range_len " codeId:ident decPrefix:ident b:term:max H:term:max
    hfn:ident sym:str k0:num len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches_range $codeId $decPrefix $b $H $hfn $offStx $k0 $len))

end CryptoVerification.SpqrV1.Layout.L25

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open ChainFromVNNorm
open CryptoVerification.LibsignalSpqr
open CryptoVerification.SpqrV1.Layout.L25

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem add_one_beq_zero_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by bv_omega
  subst h1
  revert h; decide

theorem vecU8_live_entails_dealloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (cap : BitVec 64) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hm1 := pointsToBytes_entails_memRegion ptr bs
  have hm2 : memRegion ptr bs.length ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion ptr cap.toNat := by
    rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (N := cap.toNat) (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
  rw [← hm2]
  exact sepConj_mono_right (sepConj_mono_left hm1)

theorem stackAt_extHookStack_split_alloc (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12288 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 12288 (by decide)

/-- Framed call rule for `formatInnerSpec A` inside `SepWPp` when the continuation after
    `format_inner` does not panic (`SepWP`). -/
theorem SepWPp.call_formatInner_then_sepWP {prog : Program} {A : RustAlloc}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (formatInnerSpec A))
    (ret sp_cur : BitVec 64) {s0 s : State} {P F R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ret)
    (hP : P = (memRegion ret 24 ∗ A.pool ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ (sf : State) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWP prog target_pc sf
        (((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWPp.call (x := ret) (F := F) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [formatInnerSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx8, ?_⟩
    rwa [← sepConj_assoc, ← hP]
  · intro sm _ R' _ hpost
    dsimp only [formatInnerSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm _ hm'
    exact Satisfies.mono (sepConj_mono_left (onPanic_entails_of_trace_eq htr)) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [formatInnerSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [htr] at htrm
    rw [hsp] at hspm
    dsimp only [vecU8, vecU8At, vecHeader] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, cap, ptr, hpost⟩
    have hpost' : sm.mem ⊨
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt sp_cur extHookStack) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨⟨hle, hlt, hptr⟩, hpost'⟩
    exact (SepWPp.of_sepWP_ret (hnext sm bs cap ptr hpcm hrunm hspm htrm hcsm hle hlt hptr)) R' hpost' hL
  · intro sm R' _ hpost
    dsimp only [formatInnerSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Framed call rule for `rustDeallocSpec A` inside `SepWP` using `extHookStack`. -/
theorem SepWP.call_dealloc {prog : Program} {A : RustAlloc}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr sp_cur : BitVec 64) (size : Nat) {s0 s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hP : P = (A.live ptr size 1 ∗ memRegion ptr size ∗ A.pool ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf ((A.pool ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  let F_ext := memRegion (sp_cur - 16384#64) 12288 ∗ F
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame (x := (ptr, size, 1)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [hP, stackAt_extHookStack_split_alloc sp_cur] at hm
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [F_ext]; ac_rfl
  · intro R' sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm
    unfold SepWP
    intro R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [rustDeallocSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [htr] at htrm
    rw [hsp] at hspm
    have hpost' : sm.mem ⊨ ((A.pool ∗ stackAt sp_cur extHookStack) ∗ F) ∗ R' := by
      rw [stackAt_extHookStack_split_alloc sp_cur]
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [F_ext]; ac_rfl
    have hnext' := hnext sm hpcm hrunm hspm htrm hcsm
    unfold SepWP at hnext'
    exact hnext' R' hpost' hL
  · intro R' sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem tag_cases (tag : BitVec 8) :
    tag = 0#8 ∨ tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨
      tag = 4#8 ∨ tag = 5#8 ∨ tag = 6#8 ∨ 6 < tag.toNat := by
  by_cases h0 : tag = 0#8; · exact Or.inl h0
  by_cases h1 : tag = 1#8; · exact Or.inr (Or.inl h1)
  by_cases h2 : tag = 2#8; · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : tag = 3#8; · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : tag = 4#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  by_cases h5 : tag = 5#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  by_cases h6 : tag = 6#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  have h0' : tag.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have h1' : tag.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
  have h2' : tag.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h)
  have h3' : tag.toNat ≠ 3 := fun h => h3 (BitVec.eq_of_toNat_eq h)
  have h4' : tag.toNat ≠ 4 := fun h => h4 (BitVec.eq_of_toNat_eq h)
  have h5' : tag.toNat ≠ 5 := fun h => h5 (BitVec.eq_of_toNat_eq h)
  have h6' : tag.toNat ≠ 6 := fun h => h6 (BitVec.eq_of_toNat_eq h)
  omega

theorem deserialize_err_of_gt_6 (P : PolyApi) (epoch : Epoch) (tag : BitVec 8)
    (rest : List (BitVec 8)) (htag : 6 < tag.toNat) :
    Message.deserialize P epoch (tag :: rest) = .error .msgDecode := by
  have h0 : (tag == 0#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h1 : (tag == 1#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h2 : (tag == 2#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h3 : (tag == 3#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h4 : (tag == 4#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h5 : (tag == 5#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h6 : (tag == 6#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  unfold Message.deserialize MessageType.tryFromU8
  simp [h0, h1, h2, h3, h4, h5, h6]

theorem ofNat_cons_length_beq_zero (tag : BitVec 8) (rest : List (BitVec 8))
    (hlen : (tag :: rest).length < 2 ^ 63) :
    (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h0 : (BitVec.ofNat 64 (tag :: rest).length).toNat = 0 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0
  simp at h0

theorem toNat_sub_five_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    (BitVec.zeroExtend 32 tag - 5#32).toNat = tag.toNat - 5 := by
  have hle : 5#32 ≤ BitVec.zeroExtend 32 tag := by
    rw [BitVec.le_def]
    change 5 ≤ (BitVec.zeroExtend 32 tag).toNat
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    omega
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_setWidth_of_le (by decide)]
  rfl

@[local simp, local arm64_norm, local wp_norm]
theorem ule_five_64_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule 5#64 (BitVec.zeroExtend 64 tag) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  change 5 ≤ (BitVec.zeroExtend 64 tag).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ule_five_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule 5#32 (BitVec.zeroExtend 32 tag) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  change 5 ≤ (BitVec.zeroExtend 32 tag).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_five_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult (BitVec.zeroExtend 32 tag) 5#32 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  change ¬ (BitVec.zeroExtend 32 tag).toNat < 5
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ule_sub_five_one_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule (BitVec.zeroExtend 32 tag - 5#32) 1#32 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (BitVec.zeroExtend 32 tag - 5#32).toNat ≤ 1
  rw [toNat_sub_five_of_gt_6 tag htag]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_sub_five_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult 1#32 (BitVec.zeroExtend 32 tag - 5#32) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  change 1 < (BitVec.zeroExtend 32 tag - 5#32).toNat
  rw [toNat_sub_five_of_gt_6 tag htag]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_sub_five_64_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult 1#64 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 tag - 5#32)) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  change 1 < (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 tag - 5#32)).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide), toNat_sub_five_of_gt_6 tag htag]
  omega

theorem memRegion_48_eq_rawOutBufAt (out : BitVec 64) :
    memRegion out 48 =
      ∃∗ idx16 : BitVec 16, ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64,
      ∃∗ c4 : BitVec 8, ∃∗ c3 : BitVec 64, ∃∗ c2 : BitVec 8,
      ∃∗ c1 : BitVec 16, ∃∗ c0 : BitVec 32, ∃∗ b9 : BitVec 8,
      ∃∗ b8 : BitVec 8, ∃∗ w0 : BitVec 64,
        rawOutBufAt out w0 b8 b9 c0 c1 c2 c3 c4 c5 c6 idx16 := by
  rw [memRegion_48_ok_split out]
  simp only [rawOutBufAt, chunk32AtomsAt, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem spqrPolyApi_chunkLaw : PolyApiChunkLaw spqrPolyApi :=
  fun _ _ => ⟨rfl, rfl⟩

attribute [local irreducible] rawOutBufAt msgDeserFramePad msgDeserScratchAt
  msgDeserSavedAt messageResultAt Message.deserialize

end CryptoVerification.SpqrV1.Top.MessageDeserialize

