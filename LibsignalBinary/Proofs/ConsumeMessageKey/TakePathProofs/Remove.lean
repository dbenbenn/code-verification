/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

section RemoveSepHelpers

set_option autoImplicit false

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

structure VecHeaderSnap where
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64

def vecHeaderRep (v : BitVec 64) (h : VecHeaderSnap) : SepProp :=
  vecHeader v h.cap h.ptr h.len

register_sep_key vecHeaderRep [0]

theorem vecHeader_eq_rep (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = vecHeaderRep v ⟨cap, ptr, len⟩ := rfl

@[sep_lens]
theorem vecHeaderRep_cap_lens (v : BitVec 64) :
    ProofLib.Sep.LawfulSepLens (vecHeaderRep v)
      (fun cap => v ↦₆₄ cap)
      (fun h => ((v + 8#64) ↦₆₄ h.ptr) ∗ ((v + 16#64) ↦₆₄ h.len))
      (·.cap) (fun h cap' => { h with cap := cap' }) where
  open_entails _ := by unfold vecHeaderRep vecHeader; bi_entail
  close_entails _ _ := by unfold vecHeaderRep vecHeader; bi_entail
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

@[sep_lens]
theorem vecHeaderRep_ptr_lens (v : BitVec 64) :
    ProofLib.Sep.LawfulSepLens (vecHeaderRep v)
      (fun ptr => (v + 8#64) ↦₆₄ ptr)
      (fun h => (v ↦₆₄ h.cap) ∗ ((v + 16#64) ↦₆₄ h.len))
      (·.ptr) (fun h ptr' => { h with ptr := ptr' }) where
  open_entails _ := by unfold vecHeaderRep vecHeader; bi_entail
  close_entails _ _ := by unfold vecHeaderRep vecHeader; bi_entail
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

@[sep_lens]
theorem vecHeaderRep_len_lens (v : BitVec 64) :
    ProofLib.Sep.LawfulSepLens (vecHeaderRep v)
      (fun len => (v + 16#64) ↦₆₄ len)
      (fun h => (v ↦₆₄ h.cap) ∗ ((v + 8#64) ↦₆₄ h.ptr))
      (·.len) (fun h len' => { h with len := len' }) where
  open_entails _ := by unfold vecHeaderRep vecHeader; bi_entail
  close_entails _ _ := by unfold vecHeaderRep vecHeader; bi_entail
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

@[sep_footprint]
theorem vecHeader_footprint (v cap ptr len : BitVec 64) :
    ProofLib.Sep.HasFootprint (vecHeader v cap ptr len) true v 24 where
  owns_at x hx := by
    simpa using OwnsRW.of_entails (by unfold vecHeader; sep_interval) (ownsRW_memRegion v 24 x hx)

@[sep_footprint]
theorem stackAt_footprint (sp : BitVec 64) (n : Nat) :
    ProofLib.Sep.HasFootprint (stackAt sp n) true (sp - BitVec.ofNat 64 n) n := by
  unfold stackAt; infer_instance

@[sep_footprint]
theorem messageKeyAt_footprint (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    ProofLib.Sep.HasFootprint (messageKeyAt A gk a) true a 104 where
  owns_at x hx := by
    have hent : messageKeyAt A gk a ⊢ memRegion a 104 ∗ messageKeyHeap A gk := by
      rw [messageKeyAt_eq_headers_sep_heap]; unfold vecHeader; sep_interval
    simpa using OwnsRW.of_entails hent (ownsRW_sepConj_left (ownsRW_memRegion a 104 x hx))

theorem dealloc_opt_join (A : RustAlloc) (cap ptr sp0 slotAddr : BitVec 64) :
    ProofLib.Sep.SepJoinLub (cap == 0#64)
      (A.pool ∗ emp ∗ stackAt (sp0 - 480#64) allocHookStack ∗ (slotAddr ↦₆₄ ptr))
      (A.pool ∗ stackAt (sp0 - 480#64) allocHookStack ∗ (slotAddr ↦₆₄ ptr))
      (emp ∗ A.pool ∗ stackAt (sp0 - 480#64) allocHookStack ∗ (slotAddr ↦₆₄ ptr)) := by
  sep_join_lub

end RemoveSepHelpers

public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib ProofLib.SepSolver CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession

namespace RemoveBvArith

theorem bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bv_add_add_eq {x : BitVec 64} {a b c : Nat} (h : a + b = c := by rfl) :
    x + BitVec.ofNat 64 c = (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h]

theorem bv_sub_add_eq {x : BitVec 64} {a b c : Nat}
    (h : b < a := by decide) (ha : a < 2 ^ 64 := by decide) (h2 : a - b = c := by rfl) :
    x - BitVec.ofNat 64 c = (x - BitVec.ofNat 64 a) + BitVec.ofNat 64 b := by
  rw [bv_sub_add_lit x a b h ha, h2]

end RemoveBvArith

theorem messageKeyAt_eq_cells_sep_heap (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a =
      ((a ↦₆₄ gk.1.cipher.cap) ∗
       ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
       ((a + 16#64) ↦₆₄ 0#64) ∗
       ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗
       ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
       ((a + 40#64) ↦₆₄ 0#64) ∗
       ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗
       ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
       ((a + 64#64) ↦₆₄ 0#64) ∗
       ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗
       ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
       ((a + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
       ((a + 96#64) ↦₃₂ gk.2.counter) ∗
       memRegion (a + 100#64) 4) ∗
      messageKeyHeap A gk := by
  rw [messageKeyAt_eq_headers_sep_heap]
  unfold vecHeader
  sep_interval_eq

theorem memRegion_384_entails_pre_memmove_slots (sp0 : BitVec 64) :
    memRegion (sp0 - 480#64) 384 ⊢
      memRegion (sp0 - 480#64) 56 ∗
      (∃∗ v424 : BitVec 64, ((sp0 - 424#64) ↦₆₄ v424)) ∗
      (∃∗ v416 : BitVec 64, ((sp0 - 416#64) ↦₆₄ v416)) ∗
      (∃∗ v408 : BitVec 64, ((sp0 - 408#64) ↦₆₄ v408)) ∗
      (∃∗ v400 : BitVec 64, ((sp0 - 400#64) ↦₆₄ v400)) ∗
      memRegion (sp0 - 392#64) 4 ∗
      (∃∗ v388 : BitVec 32, ((sp0 - 388#64) ↦₃₂ v388)) ∗
      (∃∗ v384 : BitVec 64, ((sp0 - 384#64) ↦₆₄ v384)) ∗
      (∃∗ v376 : BitVec 64, ((sp0 - 376#64) ↦₆₄ v376)) ∗
      (∃∗ v368 : BitVec 64, ((sp0 - 368#64) ↦₆₄ v368)) ∗
      memRegion (sp0 - 360#64) 136 ∗
      (∃∗ v224 : BitVec 64, ((sp0 - 224#64) ↦₆₄ v224)) ∗
      (∃∗ v216 : BitVec 64, ((sp0 - 216#64) ↦₆₄ v216)) ∗
      memRegion (sp0 - 208#64) 112 := by
  sep_interval

/-- Split `(a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr)` into the five unaligned sub-cells accessed at `+0x650 .. +0x66c`. -/
theorem pointsTo64_pair_eq_unaligned_16 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr)) =
      ((a ↦₁₆ (cap.extractLsb' 8 8 ++ cap.extractLsb' 0 8)) ∗
       ((a + 2#64) ↦₈ cap.extractLsb' 16 8) ∗
       ((a + 3#64) ↦₆₄
         (ptr.extractLsb' 16 8 ++ ptr.extractLsb' 8 8 ++ ptr.extractLsb' 0 8 ++
          cap.extractLsb' 56 8 ++ cap.extractLsb' 48 8 ++ cap.extractLsb' 40 8 ++
          cap.extractLsb' 32 8 ++ cap.extractLsb' 24 8)) ∗
       ((a + 11#64) ↦₃₂
         (ptr.extractLsb' 48 8 ++ ptr.extractLsb' 40 8 ++
          ptr.extractLsb' 32 8 ++ ptr.extractLsb' 24 8)) ∗
       ((a + 15#64) ↦₈ ptr.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_pointsToBytes a cap, pointsTo64_eq_pointsToBytes (a + 8#64) ptr,
      ← pointsToBytes2_eq_pointsTo16, ← pointsToBytes8_eq_pointsTo64, ← pointsToBytes4_eq_pointsTo32]
  simp only [unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  sep_interval_eq

theorem cipher_cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

theorem seed_len_ofNat_ne_zero {seed : List (BitVec 8)} {cap : BitVec 64}
    (hne : seed ≠ []) (hle : seed.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    BitVec.ofNat 64 seed.length ≠ 0#64 := by
  have hpos : 0 < seed.length := List.length_pos_of_ne_nil hne
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
  change seed.length = 0 at hnat
  omega

@[local simp] theorem zeroExtend_64_truncate_32_zeroExtend_64 (x : BitVec 32) :
    ((x.zeroExtend 64).truncate 32).zeroExtend 64 = x.zeroExtend 64 := by
  bv_kernel

theorem sepWP_seq_frame {prog : Program} {mid target : BitVec 64}
    {s : State} {P P1 Frame : SepProp}
    {Post1 : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hP : P = P1 ∗ Frame)
    (h1 : SepWP prog mid s P1 Post1)
    (h2 : ∀ s1 P_out, s1.pc = mid → s1.status = .Running → Post1 s1 P_out →
      SepWP prog target s1 (P_out ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hP]
  unfold SepWP at h1 ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  refine reaches_pc_seq (h1 (Frame ∗ R) hm) ?_
  intro s1 hpc1 hrun1 ⟨P_out, hm1, hPost1⟩
  rw [← sepConj_assoc] at hm1
  have h2' := h2 s1 P_out hpc1 hrun1 hPost1
  unfold SepWP at h2'
  exact h2' R hm1

theorem sepWP_weaken_left {prog : Program} {target : BitVec 64}
    {s : State} {P_out P1' Frame : SepProp} {post : State → SepProp → Prop}
    (hent : P_out ⊢ P1')
    (h : SepWP prog target s (P1' ∗ Frame) post) :
    SepWP prog target s (P_out ∗ Frame) post :=
  SepWP.weaken_pre (sepConj_mono_left hent) h

private meta partial def flattenSepConj (e : Lean.Expr) : List Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``sepConj 2 then
    flattenSepConj e.appFn!.consumeMData.appArg! ++ flattenSepConj e.appArg!
  else
    [e]

private meta def removeFirstDefEq (x : Lean.Expr) : List Lean.Expr → Lean.MetaM (List Lean.Expr)
  | [] => return []
  | y :: ys => do
    if ← Lean.Meta.isDefEq x y then return ys
    else return y :: (← removeFirstDefEq x ys)

private meta def mkSepConjChain : List Lean.Expr → Lean.MetaM Lean.Expr
  | [] => Lean.Meta.mkConstWithFreshMVarLevels ``emp
  | [x] => return x
  | x :: xs => do
    let rest ← mkSepConjChain xs
    Lean.Meta.mkAppM ``sepConj #[x, rest]

theorem entails_of_eq {P Q R : SepProp} (h : P = Q) (hQR : Q ⊢ R) : P ⊢ R := by
  rw [h]; exact hQR

/-- Compute the `sepConj` frame automatically and apply `sepWP_seq_frame`. -/
elab "wp_seq_frame " h:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
    let P := (goalType.getAppArgs)[3]!.consumeMData
    let hExpr ← Lean.Elab.Tactic.elabTerm h none
    let hType := (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr)).consumeMData
    let P1 := (hType.getAppArgs)[3]!.consumeMData
    let pAtoms := flattenSepConj P
    let p1Atoms := flattenSepConj P1
    let _ ← Lean.Meta.isDefEq (goalType.getAppArgs)[0]! (hType.getAppArgs)[0]!
    let remAtoms ← p1Atoms.foldlM (fun acc x => removeFirstDefEq x acc) pAtoms
    let frameExpr ← mkSepConjChain remAtoms
    let frameExpr ← Lean.instantiateMVars frameExpr
    let hInst ← Lean.instantiateMVars hExpr
    let hTypeInst ← Lean.instantiateMVars hType
    let g ← Lean.Elab.Tactic.getMainGoal
    let (_, g1) ← (← g.define `_wp_seq_frame (Lean.mkConst ``SepProp) frameExpr).intro1P
    let (_, g2) ← (← g1.assert `_wp_seq_h hTypeInst hInst).intro1P
    Lean.Elab.Tactic.replaceMainGoal [g2]
    let fId := Lean.mkIdent `_wp_seq_frame
    let hId := Lean.mkIdent `_wp_seq_h
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      refine SepWP.weaken_pre ?_ (sepWP_seq_frame (Frame := $fId) rfl $hId ?_)
      · dsimp only [$fId:ident]; bi_entail
      dsimp only [$fId:ident]; clear $hId $fId)))

theorem pointsTo64_eq_unaligned_2_1_4_1 (a len : BitVec 64) :
    (a ↦₆₄ len) =
      ((a ↦₁₆ (len.extractLsb' 8 8 ++ len.extractLsb' 0 8)) ∗
       ((a + 2#64) ↦₈ len.extractLsb' 16 8) ∗
       ((a + 3#64) ↦₃₂
         (len.extractLsb' 48 8 ++ len.extractLsb' 40 8 ++
          len.extractLsb' 32 8 ++ len.extractLsb' 24 8)) ∗
       ((a + 7#64) ↦₈ len.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_pointsToBytes a len,
      ← pointsToBytes2_eq_pointsTo16, ← pointsToBytes4_eq_pointsTo32]
  simp only [unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  sep_interval_eq

theorem memRegion_seven_32_left (a : BitVec 64) :
    memRegion a 7 = (∃∗ v : BitVec 32, a ↦₃₂ v) ∗ memRegion (a + 4#64) 3 := by
  sep_interval_eq

theorem memRegion_seven_32_right (a : BitVec 64) :
    memRegion a 7 = memRegion a 3 ∗ (∃∗ v : BitVec 32, (a + 3#64) ↦₃₂ v) := by
  sep_interval_eq

theorem pointsTo32_sep_memRegion_3_entails (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ∗ memRegion (a + 4#64) 3 ⊢
      memRegion a 3 ∗ (∃∗ w : BitVec 32, (a + 3#64) ↦₃₂ w) := by
  sep_interval

theorem memRegion_3_sep_pointsTo32_entails_seven (a : BitVec 64) (v : BitVec 32) :
    memRegion a 3 ∗ ((a + 3#64) ↦₃₂ v) ⊢ memRegion a 7 := by
  sep_interval

@[local simp] theorem getLsbD_mask24 (i : Nat) (hi : i < 32) :
    (16777215#64).getLsbD i = decide (i < 24) := by
  revert i hi; decide

theorem shiftLeft_40_eq_and_mask24 (v : BitVec 64) :
    v <<< 40 = (v &&& 16777215#64) <<< 40 := by
  ext i hi
  by_cases h40 : i < 40
  · simp [h40]
  · simp [h40, getLsbD_mask24 (i - 40) (by omega), show i - 40 < 24 by omega]

private theorem decide_eq_ite (p : Prop) [Decidable p] :
    decide p = if p then true else false := by
  by_cases h : p <;> simp [h]

theorem seed_ptr_reassemble (ptr cap : BitVec 64) :
    ((ptr.extractLsb' 16 8 ++ ptr.extractLsb' 8 8 ++
      ptr.extractLsb' 0 8 ++ cap.extractLsb' 56 8 ++
      cap.extractLsb' 48 8 ++ cap.extractLsb' 40 8 ++
      cap.extractLsb' 32 8 ++ cap.extractLsb' 24 8) >>> 40) |||
    ((((ptr.extractLsb' 48 8 ++ ptr.extractLsb' 40 8 ++
        ptr.extractLsb' 32 8 ++ ptr.extractLsb' 24 8).zeroExtend 64) |||
      (((ptr.extractLsb' 56 8).zeroExtend 64) <<< 32)) <<< 24) = ptr := by
  have hshr :
      ((ptr.extractLsb' 16 8 ++ ptr.extractLsb' 8 8 ++
        ptr.extractLsb' 0 8 ++ cap.extractLsb' 56 8 ++
        cap.extractLsb' 48 8 ++ cap.extractLsb' 40 8 ++
        cap.extractLsb' 32 8 ++ cap.extractLsb' 24 8) >>> 40) =
      (ptr.extractLsb' 16 8 ++ ptr.extractLsb' 8 8 ++ ptr.extractLsb' 0 8).zeroExtend 64 := by
    generalize ptr.extractLsb' 16 8 ++ ptr.extractLsb' 8 8 ++ ptr.extractLsb' 0 8 = lo24
    generalize cap.extractLsb' 56 8 = c5
    generalize cap.extractLsb' 48 8 = c4
    generalize cap.extractLsb' 40 8 = c3
    generalize cap.extractLsb' 32 8 = c2
    generalize cap.extractLsb' 24 8 = c1
    bv_bits
  rw [hshr]
  bv_bits

theorem seed_len_lo16_eq (len : BitVec 64) :
    ((((len &&& 16777215#64) <<< 40) >>> 40).truncate 32).truncate 16 =
      len.extractLsb' 8 8 ++ len.extractLsb' 0 8 := by
  bv_kernel

theorem seed_len_b2_eq (len : BitVec 64) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (((len &&& 16777215#64) <<< 40) >>> 40)) >>> 16) =
      len.extractLsb' 16 8 := by
  bv_kernel

theorem seed_len_b3456_eq (len : BitVec 64) :
    (len >>> 24).truncate 32 =
      len.extractLsb' 48 8 ++ len.extractLsb' 40 8 ++
      len.extractLsb' 32 8 ++ len.extractLsb' 24 8 := by
  bv_kernel

theorem seed_len_b7_eq (len : BitVec 64) :
    BitVec.zeroExtend 8 (len >>> 56) =
      len.extractLsb' 56 8 := by
  bv_kernel

theorem memRegion_56_entails_write_ok_slots (sp0 : BitVec 64) :
    memRegion (sp0 - 480#64) 56 ⊢
      memRegion (sp0 - 480#64) 16 ∗
      (∃∗ v464 : BitVec 64, ((sp0 - 464#64) ↦₆₄ v464)) ∗
      memRegion (sp0 - 456#64) 4 ∗
      (∃∗ v452 : BitVec 32, ((sp0 - 452#64) ↦₃₂ v452)) ∗
      (∃∗ v448 : BitVec 64, ((sp0 - 448#64) ↦₆₄ v448)) ∗
      memRegion (sp0 - 440#64) 4 ∗
      (∃∗ v436 : BitVec 32, ((sp0 - 436#64) ↦₃₂ v436)) ∗
      (∃∗ v432 : BitVec 64, ((sp0 - 432#64) ↦₆₄ v432)) := by
  sep_interval

theorem write_ok_slots_entails_memRegion_64 (sp0 : BitVec 64)
    (v464 v448 v432 v424 : BitVec 64) (v452 v436 : BitVec 32) :
    (memRegion (sp0 - 480#64) 16 ∗
      ((sp0 - 464#64) ↦₆₄ v464) ∗
      memRegion (sp0 - 456#64) 4 ∗
      ((sp0 - 452#64) ↦₃₂ v452) ∗
      ((sp0 - 448#64) ↦₆₄ v448) ∗
      memRegion (sp0 - 440#64) 4 ∗
      ((sp0 - 436#64) ↦₃₂ v436) ∗
      ((sp0 - 432#64) ↦₆₄ v432) ∗
      ((sp0 - 424#64) ↦₆₄ v424)) ⊢
      memRegion (sp0 - 480#64) 64 := by
  sep_interval

theorem memRegion_80_entails_write_ok_slots (sp0 : BitVec 64) :
    memRegion (sp0 - 304#64) 80 ⊢
      memRegion (sp0 - 304#64) 48 ∗
      (∃∗ v256 : BitVec 32, ((sp0 - 256#64) ↦₃₂ v256)) ∗
      memRegion (sp0 - 252#64) 3 ∗
      memRegion (sp0 - 249#64) 1 ∗
      (∃∗ v248 : BitVec 64, ((sp0 - 248#64) ↦₆₄ v248)) ∗
      (∃∗ v240 : BitVec 8, ((sp0 - 240#64) ↦₈ v240)) ∗
      memRegion (sp0 - 239#64) 7 ∗
      (∃∗ v232 : BitVec 16, ((sp0 - 232#64) ↦₁₆ v232)) ∗
      (∃∗ v230 : BitVec 8, ((sp0 - 230#64) ↦₈ v230)) ∗
      memRegion (sp0 - 229#64) 5 := by
  sep_interval

theorem write_ok_slots_entails_memRegion_88 (sp0 : BitVec 64)
    (v253 : BitVec 32) (v248 v224 : BitVec 64) (v240 v230 : BitVec 8) (v232 : BitVec 16) :
    (memRegion (sp0 - 304#64) 48 ∗
      memRegion (sp0 - 256#64) 3 ∗
      ((sp0 - 253#64) ↦₃₂ v253) ∗
      memRegion (sp0 - 249#64) 1 ∗
      ((sp0 - 248#64) ↦₆₄ v248) ∗
      ((sp0 - 240#64) ↦₈ v240) ∗
      memRegion (sp0 - 239#64) 7 ∗
      ((sp0 - 232#64) ↦₁₆ v232) ∗
      ((sp0 - 230#64) ↦₈ v230) ∗
      memRegion (sp0 - 229#64) 5 ∗
      ((sp0 - 224#64) ↦₆₄ v224)) ⊢
      memRegion (sp0 - 304#64) 88 := by
  sep_interval

theorem memRegion_88_entails_ret_ok_slots (ret : BitVec 64) :
    memRegion ret 88 ⊢
      (∃∗ r0 : BitVec 32, (ret ↦₃₂ r0)) ∗
      (∃∗ r4 : BitVec 32, ((ret + 4#64) ↦₃₂ r4)) ∗
      (∃∗ r8 : BitVec 64, ((ret + 8#64) ↦₆₄ r8)) ∗
      (∃∗ r16 : BitVec 64, ((ret + 16#64) ↦₆₄ r16)) ∗
      (∃∗ r24 : BitVec 64, ((ret + 24#64) ↦₆₄ r24)) ∗
      (∃∗ r32 : BitVec 32, ((ret + 32#64) ↦₃₂ r32)) ∗
      (∃∗ r36 : BitVec 32, ((ret + 36#64) ↦₃₂ r36)) ∗
      (∃∗ r40 : BitVec 16, ((ret + 40#64) ↦₁₆ r40)) ∗
      (∃∗ r42 : BitVec 8, ((ret + 42#64) ↦₈ r42)) ∗
      (∃∗ r43 : BitVec 64, ((ret + 43#64) ↦₆₄ r43)) ∗
      (∃∗ r51 : BitVec 64, ((ret + 51#64) ↦₆₄ r51)) ∗
      (∃∗ r59 : BitVec 64, ((ret + 59#64) ↦₆₄ r59)) ∗
      (∃∗ r67 : BitVec 8, ((ret + 67#64) ↦₈ r67)) ∗
      (∃∗ r68 : BitVec 32, ((ret + 68#64) ↦₃₂ r68)) ∗
      memRegion (ret + 72#64) 3 ∗
      (∃∗ r75 : BitVec 64, ((ret + 75#64) ↦₆₄ r75)) ∗
      (∃∗ r83 : BitVec 8, ((ret + 83#64) ↦₈ r83)) ∗
      (∃∗ r84 : BitVec 32, ((ret + 84#64) ↦₃₂ r84)) := by
  sep_interval

theorem ret_tail_slots_entails_memRegion_52 (ret : BitVec 64)
    (r36 r71 r84 : BitVec 32) (r40 : BitVec 16) (r42 r67 r83 : BitVec 8)
    (r43 r51 r59 r75 : BitVec 64) :
    (((ret + 36#64) ↦₃₂ r36) ∗
      ((ret + 40#64) ↦₁₆ r40) ∗
      ((ret + 42#64) ↦₈ r42) ∗
      ((ret + 43#64) ↦₆₄ r43) ∗
      ((ret + 51#64) ↦₆₄ r51) ∗
      ((ret + 59#64) ↦₆₄ r59) ∗
      ((ret + 67#64) ↦₈ r67) ∗
      memRegion (ret + 68#64) 3 ∗
      ((ret + 71#64) ↦₃₂ r71) ∗
      ((ret + 75#64) ↦₆₄ r75) ∗
      ((ret + 83#64) ↦₈ r83) ∗
      ((ret + 84#64) ↦₃₂ r84)) ⊢
      memRegion (ret + 36#64) 52 := by
  sep_interval

@[local simp] theorem bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem shift_sp_256 (sp0 : BitVec 64) {v : BitVec 32} {R : SepProp} :
    ((sp0 - 256#64) ↦₃₂ v) ∗ (memRegion (sp0 - 252#64) 3 ∗ R) ⊢
      memRegion (sp0 - 256#64) 3 ∗ ((∃∗ w : BitVec 32, (sp0 - 253#64) ↦₃₂ w) ∗ R) := by
  sep_interval

theorem shift_ret_68 (ret : BitVec 64) {v : BitVec 32} {R : SepProp} :
    ((ret + 68#64) ↦₃₂ v) ∗ (memRegion (ret + 72#64) 3 ∗ R) ⊢
      memRegion (ret + 68#64) 3 ∗ ((∃∗ w : BitVec 32, (ret + 71#64) ↦₃₂ w) ∗ R) := by
  sep_interval

theorem write_ok_post_entails {A : RustAlloc} (sp0 ret : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    {v464 v448 v432 v424 v248 v224 r43 r51 r59 r75 : BitVec 64}
    {v452 v436 v253 r4 r36 r71 r84 : BitVec 32}
    {v232 r40 : BitVec 16}
    {v240 v230 r42 r67 r83 : BitVec 8} :
    let len := BitVec.ofNat 64 gk.2.seed.length
    (memRegion (sp0 - 480#64) 16 ∗
      ((sp0 - 464#64) ↦₆₄ v464) ∗
      memRegion (sp0 - 456#64) 4 ∗
      ((sp0 - 452#64) ↦₃₂ v452) ∗
      ((sp0 - 448#64) ↦₆₄ v448) ∗
      memRegion (sp0 - 440#64) 4 ∗
      ((sp0 - 436#64) ↦₃₂ v436) ∗
      ((sp0 - 432#64) ↦₆₄ v432) ∗
      ((sp0 - 424#64) ↦₆₄ v424) ∗
      memRegion (sp0 - 304#64) 48 ∗
      memRegion (sp0 - 256#64) 3 ∗
      ((sp0 - 253#64) ↦₃₂ v253) ∗
      memRegion (sp0 - 249#64) 1 ∗
      ((sp0 - 248#64) ↦₆₄ v248) ∗
      ((sp0 - 240#64) ↦₈ v240) ∗
      memRegion (sp0 - 239#64) 7 ∗
      ((sp0 - 232#64) ↦₁₆ v232) ∗
      ((sp0 - 230#64) ↦₈ v230) ∗
      memRegion (sp0 - 229#64) 5 ∗
      ((sp0 - 224#64) ↦₆₄ v224) ∗
      (ret ↦₃₂ 1#32) ∗
      ((ret + 4#64) ↦₃₂ r4) ∗
      ((ret + 8#64) ↦₆₄ gk.1.seed.cap) ∗
      ((ret + 16#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((ret + 24#64) ↦₁₆ (len.extractLsb' 8 8 ++ len.extractLsb' 0 8)) ∗
      ((ret + 26#64) ↦₈ len.extractLsb' 16 8) ∗
      ((ret + 27#64) ↦₃₂
        (len.extractLsb' 48 8 ++ len.extractLsb' 40 8 ++
         len.extractLsb' 32 8 ++ len.extractLsb' 24 8)) ∗
      ((ret + 31#64) ↦₈ len.extractLsb' 56 8) ∗
      ((ret + 32#64) ↦₃₂ gk.2.counter) ∗
      ((ret + 36#64) ↦₃₂ r36) ∗
      ((ret + 40#64) ↦₁₆ r40) ∗
      ((ret + 42#64) ↦₈ r42) ∗
      ((ret + 43#64) ↦₆₄ r43) ∗
      ((ret + 51#64) ↦₆₄ r51) ∗
      ((ret + 59#64) ↦₆₄ r59) ∗
      ((ret + 67#64) ↦₈ r67) ∗
      memRegion (ret + 68#64) 3 ∗
      ((ret + 71#64) ↦₃₂ r71) ∗
      ((ret + 75#64) ↦₆₄ r75) ∗
      ((ret + 83#64) ↦₈ r83) ∗
      ((ret + 84#64) ↦₃₂ r84) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed) ⊢
      memRegion (sp0 - 480#64) 64 ∗
      memRegion (sp0 - 304#64) 88 ∗
      consumeMessageKeyResultAt A ret (.ok gk.2) := by
  intro len
  have h24 :
      (((ret + 24#64) ↦₁₆ (len.extractLsb' 8 8 ++ len.extractLsb' 0 8)) ∗
        ((ret + 26#64) ↦₈ len.extractLsb' 16 8) ∗
        ((ret + 27#64) ↦₃₂
          (len.extractLsb' 48 8 ++ len.extractLsb' 40 8 ++
           len.extractLsb' 32 8 ++ len.extractLsb' 24 8)) ∗
        ((ret + 31#64) ↦₈ len.extractLsb' 56 8)) =
      ((ret + 24#64) ↦₆₄ len) := by
    symm
    simpa [bv_add_add_lit] using pointsTo64_eq_unaligned_2_1_4_1 (ret + 24#64) len
  have hlen_rest : ∀ R : SepProp,
      ((ret + 24#64) ↦₁₆ (len.extractLsb' 8 8 ++ len.extractLsb' 0 8)) ∗
        (((ret + 26#64) ↦₈ len.extractLsb' 16 8) ∗
          (((ret + 27#64) ↦₃₂
            (len.extractLsb' 48 8 ++ len.extractLsb' 40 8 ++
             len.extractLsb' 32 8 ++ len.extractLsb' 24 8)) ∗
            (((ret + 31#64) ↦₈ len.extractLsb' 56 8) ∗ R))) =
      ((ret + 24#64) ↦₆₄ len) ∗ R :=
    fun R => by simpa only [sepConj_assoc] using congrArg (· ∗ R) h24
  rw [hlen_rest]
  refine Entails.trans (Q :=
      memRegion (sp0 - 480#64) 64 ∗
      memRegion (sp0 - 304#64) 88 ∗
      (ret ↦₃₂ 1#32) ∗
      memRegion (ret + 4#64) 4 ∗
      (vecHeader (ret + 8#64) gk.1.seed.cap gk.1.seed.ptr len ∗
       vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed) ∗
      ((ret + 32#64) ↦₃₂ gk.2.counter) ∗
      memRegion (ret + 36#64) 52)
    (by unfold vecHeader; sep_interval) ?_
  dsimp only [len]
  have hvec : vecHeader (ret + 8#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ⊢ vecU8 A (ret + 8#64) gk.2.seed := by
    unfold vecU8
    exact Entails.sepExists_right gk.1.seed.cap
      (Entails.sepExists_right gk.1.seed.ptr (Entails.of_eq (vecU8At_eq_header_sep_buf ..).symm))
  generalize hvh : vecHeader (ret + 8#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) = vVh at hvec ⊢
  generalize hvb : vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed = vVb at hvec ⊢
  refine' Entails.trans (Entails.trans ?_ (sepConj_mono_left hvec)) ?_
  · bi_frame
  · unfold consumeMessageKeyResultAt; dsimp only
    generalize hvu : vecU8 A (ret + 8#64) gk.2.seed = vVu
    bi_entail

/-- `libcMemmoveSpec` strengthened with `sf.trace = s0.trace`. -/
@[expose] def memmoveTraceSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec hookStack).pre
  post := fun x s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (libcMemmoveSpec hookStack).post x s0 sf

theorem hookMemmove_trace_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (memmoveTraceSpec hookStack) := by
  intro x R s0 hrun hpre hsp
  rcases hookMemmove_ok hookStack x R s0 hrun hpre hsp with
    ⟨hkf, hsym, ⟨hmeta, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hmeta, hcc, ?_⟩⟩
    have htr : (hookMemmove s0).trace = s0.trace := rfl
    rw [memmoveTraceSpec.eq_def, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hexit)
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem memRegion_136_entails_post_memmove_slots (sp0 : BitVec 64) :
    memRegion (sp0 - 360#64) 136 ⊢
      memRegion (sp0 - 360#64) 40 ∗
      (∃∗ v320 : BitVec 64, ((sp0 - 320#64) ↦₆₄ v320)) ∗
      (∃∗ v312 : BitVec 64, ((sp0 - 312#64) ↦₆₄ v312)) ∗
      memRegion (sp0 - 304#64) 80 := by
  sep_interval

theorem remove_final_stack_entails_memRegion_384 (sp0 : BitVec 64)
    (v320 v312 v216 : BitVec 64) :
    (memRegion (sp0 - 480#64) 64 ∗
      memRegion (sp0 - 416#64) 56 ∗
      memRegion (sp0 - 360#64) 40 ∗
      ((sp0 - 320#64) ↦₆₄ v320) ∗
      ((sp0 - 312#64) ↦₆₄ v312) ∗
      memRegion (sp0 - 304#64) 88 ∗
      ((sp0 - 216#64) ↦₆₄ v216) ∗
      memRegion (sp0 - 208#64) 112) ⊢
      memRegion (sp0 - 480#64) 384 := by
  sep_interval

theorem messageKeyHeap_entails_remove_resources (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) :
    messageKeyHeap A gk ⊢
      ⌜gk.2.seed ≠ [] ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63⌝ ∗
      (if gk.1.cipher.cap = 0 then emp
       else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
         memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
      (if gk.1.mac.cap = 0 then emp
       else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
         memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
      (if gk.1.iv.cap = 0 then emp
       else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
         memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed := by
  unfold messageKeyHeap
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_dealloc A gk.1.cipher.cap gk.1.cipher.ptr [])
        (sepConj_mono (vecU8Buf_entails_dealloc A gk.1.mac.cap gk.1.mac.ptr [])
          (sepConj_mono_left (vecU8Buf_entails_dealloc A gk.1.iv.cap gk.1.iv.ptr []))))) ?_
  unfold vecU8Buf
  simp only [sepConj_assoc]
  apply Entails.pure_left; intro hseed_ne
  apply Entails.pure_left; rintro ⟨_, hcipher_lt, _⟩
  rw [sepConj_pure_left_comm]; apply Entails.pure_left; intro _
  rw [← sepConj_assoc, sepConj_pure_left_comm]; apply Entails.pure_left; intro _
  rw [← sepConj_assoc, sepConj_pure_left_comm]; apply Entails.pure_left
  rintro ⟨hseed_le, hseed_lt, hseed_ptr⟩
  bi_entail

theorem vecBuf_reassemble_self {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    {i : Nat} (hi : i < xs.length) :
    (elem xs[i] (ptr + BitVec.ofNat 64 (i * stride)) ∗
      (⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
        A.live ptr (cap.toNat * stride) align ∗
        (arrayAt elem stride ptr (xs.take i) ∗
         arrayAt elem stride (ptr + BitVec.ofNat 64 ((i + 1) * stride)) (xs.drop (i + 1))) ∗
        memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))) ⊢
      vecBuf A stride align elem cap ptr xs := by
  have h := vecBuf_set A stride align elem cap ptr xs hi xs[i]
  rwa [List.set_getElem_self] at h

theorem vecBuf_split_entails_remove_ready (A : RustAlloc) (mkCap mkPtr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {p : Nat} (hp : p < gks.length) :
    (messageKeyAt A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
      (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.live mkPtr (mkCap.toNat * 104) 8 ∗
        (arrayAt (messageKeyAt A) 104 mkPtr (gks.take p) ∗
         arrayAt (messageKeyAt A) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1))) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧
          gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧
          gks[p].2.seed ≠ [] ∧ gks[p].1.cipher.cap.toNat < 2 ^ 63 ∧
          gks[p].2.seed.length ≤ gks[p].1.seed.cap.toNat ∧ gks[p].1.seed.cap.toNat < 2 ^ 63⌝ ∗
        A.live mkPtr (mkCap.toNat * 104) 8 ∗
        (mkPtr ↦ₛ bs) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104) ∗
        (if gks[p].1.cipher.cap = 0 then emp
         else A.live gks[p].1.cipher.ptr gks[p].1.cipher.cap.toNat 1 ∗
           memRegion gks[p].1.cipher.ptr gks[p].1.cipher.cap.toNat) ∗
        (if gks[p].1.mac.cap = 0 then emp
         else A.live gks[p].1.mac.ptr gks[p].1.mac.cap.toNat 1 ∗
           memRegion gks[p].1.mac.ptr gks[p].1.mac.cap.toNat) ∗
        (if gks[p].1.iv.cap = 0 then emp
         else A.live gks[p].1.iv.ptr gks[p].1.iv.cap.toNat 1 ∗
           memRegion gks[p].1.iv.ptr gks[p].1.iv.cap.toNat) ∗
        vecU8Buf A gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].2.seed ∗
        messageKeyHeaps A (gks.eraseIdx p) := by
  refine Entails.trans (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  refine Entails.trans (vecBuf_messageKeyAt_expose_for_remove A mkCap mkPtr gks hp) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; rintro ⟨hbs, hbs_len, hlen, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (messageKeyHeap_entails_remove_resources A gks[p]))))) ?_
  simp only [sepConj_assoc]
  rw [← sepConj_assoc (A.live _ _ _) (mkPtr ↦ₛ bs),
      ← sepConj_assoc _ (memRegion _ _),
      sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hseed_ne, hcipher_lt, hseed_le, hseed_lt⟩
  apply Entails.sepExists_right bs
  have hpure : MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧
      gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧
      gks[p].2.seed ≠ [] ∧ gks[p].1.cipher.cap.toNat < 2 ^ 63 ∧
      gks[p].2.seed.length ≤ gks[p].1.seed.cap.toNat ∧ gks[p].1.seed.cap.toNat < 2 ^ 63 :=
    ⟨hbs, hbs_len, hlen, hcap_lt, hptr, hseed_ne, hcipher_lt, hseed_le, hseed_lt⟩
  bi_entail

theorem deallocVecs_slots_entails_memRegion_56 (sp0 : BitVec 64)
    (v416 v408 v400 v384 v376 v368 : BitVec 64) (v388 : BitVec 32) :
    (((sp0 - 416#64) ↦₆₄ v416) ∗
      ((sp0 - 408#64) ↦₆₄ v408) ∗
      ((sp0 - 400#64) ↦₆₄ v400) ∗
      memRegion (sp0 - 392#64) 4 ∗
      ((sp0 - 388#64) ↦₃₂ v388) ∗
      ((sp0 - 384#64) ↦₆₄ v384) ∗
      ((sp0 - 376#64) ↦₆₄ v376) ∗
      ((sp0 - 368#64) ↦₆₄ v368)) ⊢
      memRegion (sp0 - 416#64) 56 := by
  sep_interval

theorem elemAddr_add_104 (mkPtr : BitVec 64) (p : Nat) :
    mkPtr + BitVec.ofNat 64 (p * 104) + 104#64 =
      mkPtr + BitVec.ofNat 64 ((p + 1) * 104) := by
  rw [BitVec.add_assoc, show (104#64 : BitVec 64) = BitVec.ofNat 64 104 from rfl,
      ← BitVec.ofNat_add, show p * 104 + 104 = (p + 1) * 104 by omega]

theorem remBytes_toNat_eq {p mkLen cap : Nat}
    (hlen : mkLen ≤ cap) (hcap : cap * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 ((mkLen - 1 - p) * 104)).toNat = (mkLen - 1 - p) * 104 := by
  have : (mkLen - 1 - p) * 104 ≤ cap * 104 := Nat.mul_le_mul_right 104 (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ofNat_mkLen_sub_one {p mkLen : Nat} (hp : p < mkLen) :
    BitVec.ofNat 64 mkLen - 1#64 = BitVec.ofNat 64 (mkLen - 1) := by
  have h : mkLen = (mkLen - 1) + 1 := by omega
  conv => lhs; lhs; rw [h]
  rw [BitVec.ofNat_add]
  bv_omega

theorem zip_eraseIdx_eq {α β : Type} (xs : List α) (ys : List β) (p : Nat) :
    (xs.eraseIdx p).zip (ys.eraseIdx p) = (xs.zip ys).eraseIdx p := by
  induction xs generalizing ys p with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      cases p with
      | zero => simp
      | succ k => simp [ih]

@[expose, irreducible] def DeallocPlacedAt [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) addr (rustDeallocSpec A)

theorem deallocPlacedAt_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H) :
    DeallocPlacedAt A H (lsρ cmkRustDeallocSym) := by
  unfold DeallocPlacedAt
  exact dealloc_placed_ok_at hA

theorem call_dealloc_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {target_pc : BitVec 64}
    (hdealloc : DeallocPlacedAt A H (lsρ cmkRustDeallocSym))
    (p : BitVec 64) (size align : Nat) (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hpc : s.pc = lsρ cmkRustDeallocSym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc sf (A.pool ∗ stackAt sp_val allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc s
      ((A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp_val allocHookStack) ∗ Frame) post := by
  unfold DeallocPlacedAt at hdealloc
  refine SepWP.call_subroutine_frame hdealloc (x := (p, size, align)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [rustDeallocSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro R' sf _ hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [rustDeallocSpec, hsp, sepConj_assoc]
    exact SepWP.pure_elim (fun htr => hnext sf h1 h2 (h3.trans hsp) h4 htr)

@[expose, irreducible] def MemmovePlacedAt [LibsignalPlacement]
    (H : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) addr (memmoveTraceSpec allocHookStack)

set_option maxRecDepth 200000 in
theorem memmovePlacedAt_eq [LibsignalPlacement]
    {H : String → Option (State → State)} (hmemmove : H cmkMemmoveSym = some hookMemmove) :
    MemmovePlacedAt H (lsρ cmkMemmoveSym) := by
  unfold MemmovePlacedAt
  exact cmk_hook_ok_of_mem ⟨hookMemmove, hmemmove, hookMemmove_trace_ok allocHookStack⟩

theorem call_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    {target_pc : BitVec 64}
    (hmemmove : MemmovePlacedAt H (lsρ cmkMemmoveSym))
    (base : BitVec 64) (bs : List (BitVec 8)) (dst src len : Nat)
    (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hx0 : s.readReg64 .x0 = base + BitVec.ofNat 64 dst)
    (hx1 : s.readReg64 .x1 = base + BitVec.ofNat 64 src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hdst : dst + len ≤ bs.length)
    (hsrc : src + len ≤ bs.length)
    (hpc : s.pc = lsρ cmkMemmoveSym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc sf
        (((base ↦ₛ listMove bs dst src len) ∗ stackAt sp_val allocHookStack) ∗ Frame) post) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) target_pc s
      (((base ↦ₛ bs) ∗ stackAt sp_val allocHookStack) ∗ Frame) post := by
  unfold MemmovePlacedAt at hmemmove
  refine SepWP.call_subroutine_frame hmemmove (x := (base, bs, dst, src, len)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [memmoveTraceSpec, libcMemmoveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hdst, hsrc⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro R' sf _ hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [memmoveTraceSpec, libcMemmoveSpec, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => SepWP.pure_elim fun _ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 htr

theorem cmk_remove_pre_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)} {A : RustAlloc}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (elemAddr chAddr ret : BitVec 64)
    (remBytes mkLen : BitVec 64)
    (v424 v416 v408 v400 v384 v376 v368 v224 v216 : BitVec 64)
    (v388 : BitVec 32)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = remBytes)
    (hx8 : s.readReg64 .x8 = elemAddr + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = mkLen)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1580#64) s
      (messageKeyAt A gk elemAddr ∗
       ((s0.sp - 424#64) ↦₆₄ v424) ∗
       ((s0.sp - 416#64) ↦₆₄ v416) ∗
       ((s0.sp - 408#64) ↦₆₄ v408) ∗
       ((s0.sp - 400#64) ↦₆₄ v400) ∗
       ((s0.sp - 388#64) ↦₃₂ v388) ∗
       ((s0.sp - 384#64) ↦₆₄ v384) ∗
       ((s0.sp - 376#64) ↦₆₄ v376) ∗
       ((s0.sp - 368#64) ↦₆₄ v368) ∗
       ((s0.sp - 224#64) ↦₆₄ v224) ∗
       ((s0.sp - 216#64) ↦₆₄ v216))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = elemAddr ∧
        s1.readReg64 .x1 = elemAddr + 104#64 ∧
        s1.readReg64 .x2 = remBytes ∧
        s1.readReg64 .x19 = chAddr ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = s0.sp - 224#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = mkLen ∧
        s1.readReg64 .x25 = 0#64 ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          messageKeyAt A gk elemAddr ∗
          ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
          ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
          ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
          ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
          ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
          ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
          ((s0.sp - 368#64) ↦₆₄ ret) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  wp_disjoint _hdisj_elem_sp : DisjointRegions elemAddr 104 (s0.sp - 424#64) 8
  rw [messageKeyAt_eq_headers_sep_heap, vecHeader_eq_rep (elemAddr + 48#64)]
  simp only [sepConj_assoc]
  lens_open at (elemAddr + 56#64)
  lens_switch at (elemAddr + 48#64)
  lens_close
  dsimp only [vecHeaderRep]
  unfold vecHeader
  simp only [RemoveBvArith.bv_add_add_lit, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx8], by simp only [wp_norm, arm64_norm, hx8],
    by simp only [wp_norm, arm64_norm, hx2], by simp only [wp_norm, arm64_norm, hx19],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hsp],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx24],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, ?_⟩
  bi_entail

theorem cmk_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
    (mkPtr : BitVec 64) (bs : List (BitVec 8)) (p mkLen : Nat)
    (v19 v21 v22 v24 v26 v29 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = mkPtr + BitVec.ofNat 64 (p * 104))
    (hx1 : s.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104))
    (hx2 : (s.readReg64 .x2).toNat = (mkLen - 1 - p) * 104)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx26 : s.readReg64 .x26 = v26)
    (hx29 : s.readReg64 .x29 = v29)
    (hp : p < mkLen)
    (hbs_len : bs.length = mkLen * 104) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1584#64) s
      ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) allocHookStack)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ (mkPtr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((mkLen - 1 - p) * 104)) ∗
              stackAt (s0.sp - 480#64) allocHookStack)) := by
  have hmemmove : MemmovePlacedAt H (lsρ cmkMemmoveSym) := memmovePlacedAt_eq hmemmove_eq
  have hdst : p * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  have hsrc : (p + 1) * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  wp_step
  rw [← sepConj_emp ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) allocHookStack)]
  refine call_memmove_placed_wp hmemmove mkPtr bs (p * 104) ((p + 1) * 104) ((mkLen - 1 - p) * 104)
    (s0.sp - 480#64) ((blkPl_24).base + 1584#64)
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx1]) (by simp only [wp_norm, arm64_norm, hx2])
    hdst hsrc (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp]) (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
  have hsp_align' : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf]
    simpa [State.spAligned, hsp] using hsp_align
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm,
    hx19, hx21, hx22, hx24, hx26, hx29] at hcs
  rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
  rw [sepConj_emp]
  refine SepWP.done hpc_sf hrun_sf ?_
  refine ⟨hsp_sf, hsp_align', hcs19, hcs21, hcs22, hcs24, hcs26, hcs29, ⟨htr_sf, hcsv⟩, Entails.refl _⟩

theorem cmk_remove_post_memmove_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (chAddr : BitVec 64) (mkLen : Nat)
    (v320 v312 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length)
    (hx22 : s.readReg64 .x22 = s0.sp - 224#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 mkLen)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hcipher_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_ne : gk.2.seed ≠ [])
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1648#64) s
      (((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen) ∗
       ((s0.sp - 320#64) ↦₆₄ v320) ∗
       ((s0.sp - 312#64) ↦₆₄ v312) ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 =
          (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
           gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
           gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
           gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = (gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64 ∧
        s1.readReg64 .x23 =
          (gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
           gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 mkLen ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          ((chAddr + 64#64) ↦₆₄ (BitVec.ofNat 64 mkLen - 1#64)) ∗
          ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  have hcipher_ne : gk.1.cipher.cap + 1#64 ≠ 0#64 := cipher_cap_add_one_ne_zero hcipher_lt
  have hseed_nz : BitVec.ofNat 64 gk.2.seed.length ≠ 0#64 :=
    seed_len_ofNat_ne_zero hseed_ne hseed_le hseed_lt
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hcipher_ne])
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hseed_nz])
  have h312 : (s0.sp - 320#64) + 8#64 = s0.sp - 312#64 := (RemoveBvArith.bv_sub_add_eq).symm
  have h216 : (s0.sp - 224#64) + 8#64 = s0.sp - 216#64 := (RemoveBvArith.bv_sub_add_eq).symm
  wp_simp_pre only [arm64_norm]
  conv =>
    arg 4
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx24], by simp only [wp_norm, arm64_norm, hx26],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, ?_⟩
  conv =>
    rhs
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  simp only [arm64_norm, truncate_16_zeroExtend_32]
  exact Entails.refl _

theorem cmk_dealloc_cipher_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (cap ptr : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = cap) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1668#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 400#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 400#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx26]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm],
      Entails.trans ((ProofLib.Sep.sepJoinLub_and_pair (dealloc_opt_join A 0 ptr s0.sp (s0.sp - 400#64))).1 rfl)
        (by bi_entail)⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    refine SepWP.weaken_pre ?_ <|
      call_dealloc_placed_wp (Frame := (s0.sp - 400#64) ↦₆₄ ptr) hdealloc ptr cap.toNat 1 (s0.sp - 480#64) ((blkPl_24).base + 1668#64)
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx26])
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hpc])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    · bi_entail
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      have hcap_beq : (cap == 0#64) = false := by
        cases h : (cap == 0#64)
        · rfl
        · exact absurd (eq_of_beq h) hcap
      refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf],
        Entails.trans ((ProofLib.Sep.sepJoinLub_and_pair (dealloc_opt_join A cap ptr s0.sp (s0.sp - 400#64))).2 hcap_beq)
          (by bi_entail)⟩
      simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_mac_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (cap ptr : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1704#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 416#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 416#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm], Entails.refl _⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    refine SepWP.weaken_pre ?_ <|
      call_dealloc_placed_wp (Frame := (s0.sp - 416#64) ↦₆₄ ptr) hdealloc ptr cap.toNat 1 (s0.sp - 480#64) ((blkPl_24).base + 1704#64)
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx1])
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hpc])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    · bi_entail
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf], Entails.refl _⟩
      simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_iv_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (cap ptr v19 v22 v23 v26 v27 v29 : BitVec 64) (counter : BitVec 32) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap)
    (hx9 : s.readReg64 .x9 = counter.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx25 : s.readReg64 .x25 = counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1768#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       ((s0.sp - 408#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x23 = v23 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) allocHookStack ∗ ((s0.sp - 408#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocPlacedAt_of_hooks hA
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22],
      by simp only [wp_norm, arm64_norm, hx23], by simp only [wp_norm, arm64_norm, hx25],
      by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
      by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, Entails.refl _⟩
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    refine SepWP.weaken_pre ?_ <|
      call_dealloc_placed_wp (Frame := (s0.sp - 408#64) ↦₆₄ ptr) hdealloc ptr cap.toNat 1 (s0.sp - 480#64) ((blkPl_24).base + 1752#64)
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx1])
        (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hpc])
        (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
        (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    · bi_entail
    · intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
      have hsp_align' : sf.spAligned = true := by
        rw [State.spAligned, hsp_sf]
        simpa [State.spAligned, hsp] using hsp_align
      simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm,
        hx9, hx19, hx22, hx23, hx26, hx27, hx29] at hcs
      rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc_sf]) (by simp only [wp_norm, arm64_norm, hrun_sf]) ?_
      refine ⟨by simp only [wp_norm, arm64_norm, hsp_sf], by simpa only [wp_norm, arm64_norm] using hsp_align',
        by simp only [wp_norm, arm64_norm, hcs19], by simp only [wp_norm, arm64_norm, hcs22],
        by simp only [wp_norm, arm64_norm, hcs23], by simp only [wp_norm, arm64_norm, hcs25],
        by simp only [wp_norm, arm64_norm, hcs26], by simp only [wp_norm, arm64_norm, hcs27],
        by simp only [wp_norm, arm64_norm, hcs29], ⟨by simp only [wp_norm, arm64_norm, htr_sf], by simp only [wp_norm, arm64_norm, hcsv]⟩, Entails.refl _⟩

theorem cmk_remove_prep_mac_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (v19 v21 v22 v23 v29 macCap v424 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1688#64) s
      (((s0.sp - 424#64) ↦₆₄ v424) ∗ ((s0.sp - 384#64) ↦₆₄ macCap))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = macCap ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
              ((s0.sp - 384#64) ↦₆₄ macCap))) := by
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22, hx23],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, ?_⟩
  rw [shiftLeft_40_eq_and_mask24 v21]
  exact Entails.refl _

theorem cmk_remove_prep_iv_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)}
    (v21 v26 v27 v29 ivCap ret : BitVec 64) (counter : BitVec 32) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = v21)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1724#64) s
      (((s0.sp - 388#64) ↦₃₂ counter) ∗
       ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = ivCap ∧
        s1.readReg64 .x9 = counter.zeroExtend 64 ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((s0.sp - 388#64) ↦₃₂ counter) ∗
              ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
              ((s0.sp - 368#64) ↦₆₄ ret))) := by
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, Entails.refl _⟩

theorem cmk_remove_deallocVecs_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret v19 v21 v22 v23 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1768#64) s
      (A.pool ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       (if gk.1.cipher.cap = 0 then emp
        else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
          memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
       (if gk.1.mac.cap = 0 then emp
        else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
          memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
       (if gk.1.iv.cap = 0 then emp
        else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
          memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
       ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
       ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
       ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
       memRegion (s0.sp - 392#64) 4 ∗
       ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
       ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
       ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = gk.2.counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          A.pool ∗
          stackAt (s0.sp - 480#64) allocHookStack ∗
          ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
          memRegion (s0.sp - 416#64) 56)) := by
  wp_seq_frame
    (cmk_dealloc_cipher_placed_wp hA gk.1.cipher.cap gk.1.cipher.ptr s0 s hpc hrun hsp hsp_align hx26)
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, halign1, hcs1, htr1, hP1⟩
  refine sepWP_weaken_left hP1 ?_
  wp_seq_frame
    (cmk_remove_prep_mac_placed_wp v19 v21 v22 v23 (s0.sp - 96#64) gk.1.mac.cap 0#64 s0 s1
      hpc1 hrun1 hsp1 halign1 (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      (by reg_chain))
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, halign2, hx1_2, h21_2, h26_2, h27_2, h29_2, htr2, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  wp_seq_frame
    (cmk_dealloc_mac_placed_wp hA gk.1.mac.cap gk.1.mac.ptr s0 s2 hpc2 hrun2 hsp2 halign2 hx1_2)
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, halign3, hcs3, htr3, hP3⟩
  refine sepWP_weaken_left hP3 ?_
  wp_seq_frame
    (cmk_remove_prep_iv_placed_wp v21 (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64)
      gk.1.iv.cap ret gk.2.counter s0 s3 hpc3 hrun3 hsp3 halign3
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain))
  rintro s4 P4 hpc4 hrun4 ⟨hsp4, halign4, hx1_4, hx9_4, h19_4, h22_4, h23_4, h25_4, h26_4, h27_4, h29_4, htr4, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  wp_seq_frame
    (cmk_dealloc_iv_placed_wp hA gk.1.iv.cap gk.1.iv.ptr 1#64 ret
      (v21 >>> 24) (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64) gk.2.counter
      s0 s4 hpc4 hrun4 hsp4 halign4 hx1_4 hx9_4 h19_4 h22_4 h23_4 h25_4 h26_4 h27_4 h29_4)
  rintro s5 P5 hpc5 hrun5 ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5, htr5, hP5⟩
  refine sepWP_weaken_left hP5 ?_
  refine SepWP.done hpc5 hrun5 ?_
  refine ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5, by reg_chain, ?_⟩
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (deallocVecs_slots_entails_memRegion_56 s0.sp gk.1.mac.ptr gk.1.iv.ptr gk.1.cipher.ptr
        gk.1.mac.cap gk.1.iv.cap ret gk.2.counter))))
  · bi_entail

theorem cmk_remove_write_ok_placed_wp [LibsignalPlacement]
    {H : String → Option (State → State)} {A : RustAlloc}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret : BitVec 64) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx22 : s.readReg64 .x22 = ret)
    (hx23 : s.readReg64 .x23 = (BitVec.ofNat 64 gk.2.seed.length) >>> 24)
    (hx25 : s.readReg64 .x25 = gk.2.counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 =
      (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
       gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
       gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
       gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) >>> 40)
    (hx27 : s.readReg64 .x27 =
      ((gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
        gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64) |||
      (((gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64) <<< 32))
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (memRegion (s0.sp - 480#64) 56 ∗
       ((s0.sp - 424#64) ↦₆₄ (((BitVec.ofNat 64 gk.2.seed.length) &&& 16777215#64) <<< 40)) ∗
       memRegion (s0.sp - 304#64) 80 ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       memRegion ret 88 ∗
       vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          memRegion (s0.sp - 480#64) 64 ∗
          memRegion (s0.sp - 304#64) 88 ∗
          consumeMessageKeyResultAt A ret (.ok gk.2))) := by
  generalize hv : vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed = vBuf
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_56_entails_write_ok_slots s0.sp)
      (sepConj_mono_right
        (sepConj_mono (memRegion_80_entails_write_ok_slots s0.sp)
          (sepConj_mono_right
            (sepConj_mono_left (memRegion_88_entails_ret_ok_slots ret)))))) ?_
  wp_pull_exists
  conv =>
    arg 4
    rw [pointsTo64_eq_unaligned_2_1_4_1 (ret + 24#64)]
    simp only [bv_add_add_lit, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine' SepWP.weaken_pre (Entails.trans ?_ (shift_sp_256 s0.sp)) ?_
  · bi_frame
  wp_pull_exists
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine' SepWP.weaken_pre (Entails.trans ?_ (shift_ret_68 ret)) ?_
  · bi_frame
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm]⟩, ?_⟩
  simp only [arm64_norm, seed_ptr_reassemble, seed_len_lo16_eq, seed_len_b2_eq,
    seed_len_b3456_eq, seed_len_b7_eq]
  subst hv
  exact entails_of_eq (by ac_rfl) (write_ok_post_entails (A := A) s0.sp ret gk)

theorem cmk_remove_0x5e4_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (hmemmove_eq : H cmkMemmoveSym = some hookMemmove)
    (mkCap mkPtr chAddr ret : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((gks.length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 gks.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1916#64) s
      (A.pool ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          A.pool ∗
          stackAt (s0.sp - 480#64) allocHookStack ∗
          memRegion (s0.sp - 480#64) 384 ∗
          consumeMessageKeyResultAt A ret (.ok gks[p].2) ∗
          ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr (gks.eraseIdx p))) := by
  wp_disjoint _hdisj_sp_ret : DisjointRegions (s0.sp - 480#64) 384 ret 88
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_384_entails_pre_memmove_slots s0.sp)
        (sepConj_mono_right (sepConj_mono_right
          (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)))))) ?_
  wp_pull_exists
  wp_seq_frame
    (cmk_remove_pre_memmove_placed_wp (A := A) gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) chAddr ret
      (BitVec.ofNat 64 ((gks.length - 1 - p) * 104)) (BitVec.ofNat 64 gks.length)
      _ _ _ _ _ _ _ _ _ _ s0 s
      hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, halign1, hx0_1, hx1_1, hx2_1, hx19_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx29_1, htr1, hP1⟩
  refine sepWP_weaken_left hP1 ?_
  refine' SepWP.weaken_pre
    (Entails.trans ?_ (sepConj_mono_left (vecBuf_split_entails_remove_ready A mkCap mkPtr gks hp))) ?_
  · bi_frame
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hbs, hbs_len, hlen_le, hcap_lt, hptr_ne, hseed_ne, hcipher_lt, hseed_le, hseed_lt⟩
  generalize hv : vecU8Buf A gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].2.seed = vBuf
  refine' SepWP.weaken_pre
    (Entails.trans ?_ (sepConj_mono_left (memRegion_136_entails_post_memmove_slots s0.sp))) ?_
  · bi_frame
  wp_pull_exists
  have hx1_1' : s1.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) := by
    rw [hx1_1, elemAddr_add_104]
  have hx2_1' : (s1.readReg64 .x2).toNat = (gks.length - 1 - p) * 104 := by
    rw [hx2_1, remBytes_toNat_eq hlen_le hcap_lt]
  wp_seq_frame
    (cmk_memmove_placed_wp hmemmove_eq mkPtr _ p gks.length chAddr (BitVec.ofNat 64 gks[p].2.seed.length)
      (s0.sp - 224#64) (BitVec.ofNat 64 gks.length) gks[p].1.cipher.cap (s0.sp - 96#64)
      s0 s1 hpc1 hrun1 hsp1 halign1 hx0_1 hx1_1' hx2_1'
      hx19_1 hx21_1 hx22_1 hx24_1 hx26_1 hx29_1 hp hbs_len)
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, halign2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx29_2, htr2, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  wp_seq_frame
    (cmk_remove_post_memmove_placed_wp gks[p] chAddr gks.length _ _ s0 s2
      hpc2 hrun2 hsp2 halign2 hx19_2 hx21_2 hx22_2 hx24_2 hx26_2 hx29_2
      hcipher_lt hseed_ne hseed_le hseed_lt)
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, halign3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx29_3, htr3, hP3⟩
  refine sepWP_weaken_left hP3 ?_
  wp_seq_frame
    (cmk_remove_deallocVecs_placed_wp hA gks[p] ret _ _ _ _ s0 s3
      hpc3 hrun3 hsp3 halign3 hx19_3 hx21_3 hx22_3 hx23_3 hx26_3 hx29_3)
  rintro s4 P4 hpc4 hrun4 ⟨hsp4, halign4, hx19_4, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4, hx29_4, htr4, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  subst hv
  wp_seq_frame
    (cmk_remove_write_ok_placed_wp (A := A) gks[p] ret s0 s4
      hpc4 hrun4 hsp4 halign4 hx19_4 hx22_4 hx23_4 hx25_4 hx26_4 hx27_4 hx29_4)
  rintro s5 P5 hpc5 hrun5 ⟨hsp5, halign5, hx29_5, htr5, hP5⟩
  generalize hres : consumeMessageKeyResultAt A ret (.ok gks[p].2) = vRes at hP5 ⊢
  refine sepWP_weaken_left hP5 ?_
  refine SepWP.done hpc5 hrun5 ?_
  refine ⟨hsp5, halign5, hx29_5, by reg_chain, ?_⟩
  rw [ofNat_mkLen_sub_one hp]
  have hrem := vecBuf_messageKeyAt_of_remove A mkCap mkPtr hbs hp hlen_le hcap_lt hptr_ne
  generalize hvb : vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr (gks.eraseIdx p) = vVecBuf at hrem ⊢
  refine' Entails.trans (Entails.trans ?_
    (sepConj_mono_left (remove_final_stack_entails_memRegion_384 s0.sp
      gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].1.seed.ptr))) ?_
  · bi_frame
  refine' Entails.trans (Entails.trans ?_ (sepConj_mono_left hrem)) ?_
  · bi_frame
  · bi_entail

end CryptoVerification.LibsignalSession.TakePath

