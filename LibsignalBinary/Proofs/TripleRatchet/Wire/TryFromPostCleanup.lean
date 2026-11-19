/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp

/-!
# Shared cleanup tails (`+0x698..+0x640`, `+0x430..+0x3c8` → `+0x440`) and `post_none_wp` / `post_rk_none_wp`
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero

theorem layoutOk_align1 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 :=
  ⟨hpos, ⟨0, rfl⟩, by omega⟩

@[local simp, local arm64_norm, local wp_norm]
theorem slt_noneCap_one : BitVec.slt noneCap 1#64 = true := by decide

theorem spe_invalidProto_intro (A : RustAlloc) (x19 : BitVec 64)
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .invalidProtobufEncoding) :
    (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗ memRegion (x19 + 16#64) 104 ⊢
      signalMessageResultAt A [] x19 out := by
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  sep_interval

theorem slt_one_of_false_cap {cap : BitVec 64} (h : cap = noneCap ∨ cap = 0#64) :
    BitVec.slt cap 1#64 = true := by
  rcases h with rfl | rfl <;> decide

private theorem hi_of_false_cap {cap : BitVec 64} (h : cap = noneCap ∨ cap = 0#64) :
    ConditionHolds .HI (addsPState64 (cap - 1#64) 3#64) = true := by
  rcases h with rfl | rfl
  · exact cap_sub1_add3_hi_noneCap
  · exact cap_sub1_add3_hi_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``vecHeader, #[0]), (``vecU8Buf, #[1, 2]), (``optU32At, #[0]), (``speAt, #[2]), (``errResultAt, #[3]), (``signalMessageResultAt, #[2])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

private theorem frame_post {prog : Program} {ret : BitVec 64} {s0 s : Arm64.State}
    {P P' F Q_out R_out : SepProp} {φ : Arm64.State → Prop}
    (h : SepWPp prog ret s P' (fun sf Pf => φ sf ∧ (Pf ⊢ Q_out)) (tryFromQp s0))
    (hpre : P ⊢ P' ∗ F := by first | sep_accu | bi_frame)
    (hpost : Q_out ∗ F ⊢ R_out := by first | sep_interval | bi_entail) :
    SepWPp prog ret s P (fun sf Pf => φ sf ∧ (Pf ⊢ R_out)) (tryFromQp s0) :=
  SepWPp.mono_pre hpre
    (SepWPp.frame_tryFrom h fun _ _ ⟨hstf, hent⟩ =>
      ⟨hstf, Entails.trans (sepConj_mono_left hent) hpost⟩)

theorem optU32At_entails_memRegion8 (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢ memRegion a 8 := by
  refine Entails.trans (optU32At_entails_tag_val a opt) ?_
  refine Entails.sepExists_elim fun tag => Entails.sepExists_elim fun val => ?_
  refine Entails.pure_left fun _ => ?_
  exact pointsTo32_pair_entails_memRegion8 a tag val

theorem optVecU8At_entails_header_dealloc (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8At A pin a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64, ∃∗ act : Bool,
        vecHeader a cap ptr len ∗ deallocSlot A cap ptr act := by
  refine Entails.trans (optVecU8At_entails_header_buf A pin a opt) ?_
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
    Entails.sepExists_elim fun len => ?_
  refine Entails.trans (sepConj_mono_right (optVecU8Buf_entails_deallocSlot A cap ptr len opt)) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun act => ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right len (Entails.sepExists_right act (Entails.refl _))))

theorem wireHeaders_entails_memRegion112 (sp' rkCap rkPtr rkLen ctCap ctPtr ctLen
    pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64) :
    vecHeader (sp' + 176#64) rkCap rkPtr rkLen ∗
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
      vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
      vecHeader (sp' + 248#64) adCap adPtr adLen ∗
      memRegion (sp' + 272#64) 8 ∗ memRegion (sp' + 280#64) 8 ⊢
      memRegion (sp' + 176#64) 112 := by
  dsimp only [vecHeader]
  sep_interval

theorem memRegion120_split16 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval

theorem memRegion16_split8_8 (a : BitVec 64) :
    memRegion a 16 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval

theorem cleanup_698_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' ptr cap : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x698#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63) (_hptr : ptr ≠ 0#64) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hS.alloc.dealloc
  have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_noPanic_tryFrom_placed (ptr, cap.toNat, 1) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1696)) (by simp_all [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk cap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 _
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  refine SepWPp.of_sepWP_end_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]), ?_⟩
  simp only [hstack, hsp_eq, arm64_norm]
  bi_entail

theorem cleanup_684_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' adCap adPtr : BitVec 64} (adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x684#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 88#64) ↦₆₄ adPtr) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  cases adAct with
  | false =>
    have hdealloc : deallocSlot A adCap adPtr false = ⌜adCap = noneCap ∨ adCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hhi := hi_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_end_placed hcl ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hcl1
    exact ⟨PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]),
      Entails.refl _⟩
  | true =>
    have hdealloc : deallocSlot A adCap adPtr true =
        (⌜0 < adCap.toNat ∧ adCap.toNat < 2 ^ 63 ∧ adPtr ≠ 0#64⌝ ∗
          A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hnext := @cleanup_698_wp_placed _ A H hS s0
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1688)) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp [arm64_norm]) (by simp_all [arm64_norm]) hpos hlt hptr)

theorem cleanup_668_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' pqCap pqPtr adCap adPtr : BitVec 64} (pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x668#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_684_wp_placed _ A H hS s0 s sp' adCap adPtr
  cases pqAct with
  | false =>
    have hdealloc : deallocSlot A pqCap pqPtr false = ⌜pqCap = noneCap ∨ pqCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hhi := hi_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1668)) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]))
  | true =>
    have hdealloc : deallocSlot A pqCap pqPtr true =
        (⌜0 < pqCap.toNat ∧ pqCap.toNat < 2 ^ 63 ∧ pqPtr ≠ 0#64⌝ ∗
          A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (pqPtr, pqCap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1668)) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pqPtr = pqPtr ∧ pqCap.toNat = pqCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pqCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _⟩
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    exact frame_post
      (hnext adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx22_2)
      (by simp only [hstack, hsp_eq, arm64_norm]; bi_frame)

theorem cleanup_64c_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64} (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x64c#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := @cleanup_668_wp_placed _ A H hS s0
  cases ctAct with
  | false =>
    have hdealloc : deallocSlot A ctCap ctPtr false = ⌜ctCap = noneCap ∨ ctCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hhi := hi_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1640)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact hnext pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A ctCap ctPtr true =
        (⌜0 < ctCap.toNat ∧ ctCap.toNat < 2 ^ 63 ∧ ctPtr ≠ 0#64⌝ ∗
          A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hhi := cap_sub1_add3_hi_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (ctPtr, ctCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1640)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := ctPtr = ctPtr ∧ ctCap.toNat = ctCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk ctCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _⟩
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    refine SepWPp.mono_pre ?_
      (hnext pqAct adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx25_2 hx22_2)
    simp only [hstack, hsp_eq, arm64_norm]; bi_entail

theorem cleanup_640_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rk : List (BitVec 8)) (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x640#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = rkPtr) (hx1 : s.readReg64 .x1 = rkCap)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (vecU8Buf A rkCap rkPtr rk ∗
        deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := @cleanup_64c_wp_placed _ A H hS s0
  by_cases hcap : rkCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    refine SepWPp.pure_pre (fun _ => ?_)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1612)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx27, arm64_norm]) (by simp [hx28, arm64_norm])
      (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  · refine SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A rkCap rkPtr rk hcap)) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (rkPtr, rkCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1612)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := s.readReg64 (Reg.gpr 0#5) = rkPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = rkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk rkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨_, _, _, hx22_cs, _, _, hx25_cs, _, hx27_cs, hx28_cs, _⟩
    have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
    have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    refine SepWPp.mono_pre ?_
      (hnext ctAct pqAct adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx27_2 hx28_2 hx25_2 hx22_2)
    simp only [hstack, hsp_eq, arm64_norm]; bi_entail

theorem cleanup_430_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x24 w0 w1 : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x430#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (decodeErrorAt A x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcall := hDropErr
  clear hDropErr
  have hstack := stackAt_sub_split sp' dropDecodeErrorStackX (skipFieldStackX 100)
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropDecodeErrorName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_noPanic_tryFrom_placed x24 hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1080)) (by simp [arm64_norm])
    (T := decodeErrorAt A x24 ∗ A.pool ∗ stackAt s.sp dropDecodeErrorStackX)
    (φ := x24 = x24)
    (by simp [dropDecodeErrorSpecX, arm64_norm])
    rfl
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropDecodeErrorSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, _, _, _, _, _, _, hx26_cs, _⟩
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx26_2 : s2.readReg64 (Reg.gpr 26#5) = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
  refine SepWPp.of_sepWP_end_placed hcl2 ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  refine ⟨PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]), ?_⟩
  simp only [hstack, hsp_eq, errTag, arm64_norm]
  bi_entail

section CleanupOpaqueDecodeError
attribute [local irreducible] decodeErrorAt

theorem cleanup_408_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x24 w0 w1 adCap adPtr : BitVec 64} (adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x408#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 88#64) ↦₆₄ adPtr) ∗ (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_430_wp_placed _ A H hDropErr s0 s sp' x19 x24 w0 w1
  clear hDropErr
  cases adAct with
  | false =>
    have hdealloc : deallocSlot A adCap adPtr false = ⌜adCap = noneCap ∨ adCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1072)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm]) (by simp [hx26, arm64_norm]))
  | true =>
    have hdealloc : deallocSlot A adCap adPtr true =
        (⌜0 < adCap.toNat ∧ adCap.toNat < 2 ^ 63 ∧ adPtr ≠ 0#64⌝ ∗
          A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (adPtr, adCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1056)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live adPtr adCap.toNat 1 ∗ memRegion adPtr adCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := adPtr = adPtr ∧ adCap.toNat = adCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk adCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + bv% (1072)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hcl3
    exact frame_post (F := (sp' + 88#64) ↦₆₄ adPtr)
      (hnext
        (PostEpilogueStatePlaced.of_steps hcl3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp (by simp [htr2, htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [hx19_2, arm64_norm]) (by simp [hx24_2, arm64_norm]) (by simp [hx26_2, arm64_norm]))
      (by simp only [hstack, hsp_eq, arm64_norm]; sep_interval)

theorem cleanup_3f0_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x24 w0 w1 pqCap pqPtr adCap adPtr : BitVec 64} (pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x3f0#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_408_wp_placed _ A H hS hDropErr s0 s sp' x19 x24 w0 w1 adCap adPtr
  clear hDropErr
  cases pqAct with
  | false =>
    have hdealloc : deallocSlot A pqCap pqPtr false = ⌜pqCap = noneCap ∨ pqCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1032)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact frame_post
      (hnext adAct
        (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
        (by simp [hx26, arm64_norm]) (by simp [hx22, arm64_norm]))
  | true =>
    have hdealloc : deallocSlot A pqCap pqPtr true =
        (⌜0 < pqCap.toNat ∧ pqCap.toNat < 2 ^ 63 ∧ pqPtr ≠ 0#64⌝ ∗
          A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (pqPtr, pqCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1032)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pqPtr = pqPtr ∧ pqCap.toNat = pqCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pqCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, _, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    exact frame_post (F := (sp' + 96#64) ↦₆₄ pqPtr)
      (hnext adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx22_2)
      (by simp only [hstack, hsp_eq, arm64_norm]; sep_interval)

theorem cleanup_3d8_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x24 w0 w1 ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x3d8#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_3f0_wp_placed _ A H hS hDropErr s0 s sp' x19 x24 w0 w1 pqCap pqPtr adCap adPtr
  clear hDropErr
  cases ctAct with
  | false =>
    have hdealloc : deallocSlot A ctCap ctPtr false = ⌜ctCap = noneCap ∨ ctCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1008)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact hnext pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A ctCap ctPtr true =
        (⌜0 < ctCap.toNat ∧ ctCap.toNat < 2 ^ 63 ∧ ctPtr ≠ 0#64⌝ ∗
          A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (ctPtr, ctCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (1008)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := ctPtr = ctPtr ∧ ctCap.toNat = ctCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk ctCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, hx25_cs, hx26_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    refine SepWPp.mono_pre ?_
      (hnext pqAct adAct
        ⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx25_2 hx22_2)
    simp only [hstack, hsp_eq, arm64_norm]; sep_interval

theorem cleanup_3c8_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x24 w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr : BitVec 64}
    (rkAct ctAct pqAct adAct : Bool)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x3c8#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx24 : s.readReg64 .x24 = x24)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx0 : s.readReg64 .x0 = rkPtr) (hx1 : s.readReg64 .x1 = rkCap)
    (hx27 : s.readReg64 .x27 = ctCap) (hx28 : s.readReg64 .x28 = ctPtr)
    (hx25 : s.readReg64 .x25 = pqCap) (hx22 : s.readReg64 .x22 = adCap) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (deallocSlot A rkCap rkPtr rkAct ∗
        deallocSlot A ctCap ctPtr ctAct ∗
        deallocSlot A pqCap pqPtr pqAct ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        deallocSlot A adCap adPtr adAct ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
        decodeErrorAt A x24 ∗ (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 96#64) ↦₆₄ pqPtr) ∗ ((sp' + 88#64) ↦₆₄ adPtr) ∗
          (x19 ↦₆₄ errTag) ∗ ((x19 + 8#64) ↦₆₄ speWord 2) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_3d8_wp_placed _ A H hS hDropErr s0 s sp' x19 x24 w0 w1 ctCap ctPtr pqCap pqPtr adCap adPtr
  clear hDropErr
  cases rkAct with
  | false =>
    have hdealloc : deallocSlot A rkCap rkPtr false = ⌜rkCap = noneCap ∨ rkCap = 0#64⌝ := rfl
    rw [hdealloc]
    refine SepWPp.pure_pre (fun hcap => ?_)
    have hslt := slt_one_of_false_cap hcap
    clear hcap
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (984)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    exact hnext ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [hx27, arm64_norm])
      (by simp [hx28, arm64_norm]) (by simp [hx25, arm64_norm]) (by simp [hx22, arm64_norm])
  | true =>
    have hdealloc : deallocSlot A rkCap rkPtr true =
        (⌜0 < rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0#64⌝ ∗
          A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat) := rfl
    rw [hdealloc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hpos, hlt, hptr⟩ => ?_)
    have hslt := cap_slt_one_of_pos hpos hlt
    have hcall := hS.alloc.dealloc
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.call_noPanic_tryFrom_placed (rkPtr, rkCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by tryFromPost_sp_align hsp) hcl1
      (ret_pc := (blkPl_85).base + bv% (984)) (by simp [arm64_norm])
      (T := A.pool ∗ A.live rkPtr rkCap.toNat 1 ∗ memRegion rkPtr rkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := s.readReg64 (Reg.gpr 0#5) = rkPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = rkCap.toNat ∧
        (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk rkCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    rcases hcs2 with ⟨hx19_cs, _, _, hx22_cs, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
    have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
    have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
    have hx26_2 : s2.readReg64 .x26 = speWord 2 := by simp [hx26_cs, hx26, arm64_norm]
    have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
    have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
    have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
    have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
    have hsp2' : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
    have htr2' : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
    refine SepWPp.mono_pre ?_
      (hnext ctAct pqAct adAct
        ⟨hsp2', hsp2_align, hcl2, htr2'⟩
        hpc2 hrun2 hx19_2 hx24_2 hx26_2 hx27_2 hx28_2 hx25_2 hx22_2)
    simp only [hstack, hsp_eq, arm64_norm]; sep_interval

theorem post_none_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 x24 : BitVec 64}
    {out : Except SignalProtocolError SignalMessage}
    (herr : out = .error .invalidProtobufEncoding)
    (hst : LoopExitStatePlaced s0 sp' x19 x20 x21 x23 s)
    (hpc : s.pc = (blkPl_85).base + 0x3b0#64)
    (hrun : s.status = .Running)
    (hx24 : s.readReg64 .x24 = x24) (hx24_ne : x24 ≠ 0#64)
    (mErr : ProtoSignalMessage) :
    SepWPp (tryFromPlacedProg H) ((blkPl_85).base + 0x440#64) s
      (wireSignalMessageOf A (sp' + 176#64) mErr ∗
        decodeErrorAt A x24 ∗
        memRegion (sp' + 88#64) 16 ∗
        memRegion x19 120 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq : s.sp = sp' := hregs.sp
  have hx19 : s.readReg64 .x19 = x19 := hregs.x19_eq
  have hx26 : s.readReg64 .x26 = speWord 2 := hregs.x26
  have hnext := fun w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr {s} =>
    @cleanup_3c8_wp_placed _ A H hS hDropErr s0 s sp' x19 x24 w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr
  clear hDropErr
  unfold wireSignalMessageOf
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun g => ?_
  unfold wireSignalMessageAt
  have hent_wire :
      optVecU8At A g.rk (sp' + 176#64) mErr.ratchetKey ∗
      optVecU8At A g.ct (sp' + 176#64 + 0x18#64) mErr.ciphertext ∗
      optVecU8At A g.pq (sp' + 176#64 + 0x30#64) mErr.pqRatchet ∗
      optVecU8At A g.addr (sp' + 176#64 + 0x48#64) mErr.addresses ∗
      optU32At (sp' + 176#64 + 0x60#64) mErr.counter ∗
      optU32At (sp' + 176#64 + 0x68#64) mErr.previousCounter ⊢
      (∃∗ rkCap, ∃∗ rkPtr, ∃∗ rkLen, ∃∗ rkAct,
        vecHeader (sp' + 176#64) rkCap rkPtr rkLen ∗ deallocSlot A rkCap rkPtr rkAct) ∗
      (∃∗ ctCap, ∃∗ ctPtr, ∃∗ ctLen, ∃∗ ctAct,
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗ deallocSlot A ctCap ctPtr ctAct) ∗
      (∃∗ pqCap, ∃∗ pqPtr, ∃∗ pqLen, ∃∗ pqAct,
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗ deallocSlot A pqCap pqPtr pqAct) ∗
      (∃∗ adCap, ∃∗ adPtr, ∃∗ adLen, ∃∗ adAct,
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗ deallocSlot A adCap adPtr adAct) ∗
      memRegion (sp' + 272#64) 8 ∗ memRegion (sp' + 280#64) 8 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (optVecU8At_entails_header_dealloc A g.rk (sp' + 176#64) mErr.ratchetKey)
      (sepConj_mono (optVecU8At_entails_header_dealloc A g.ct (sp' + 200#64) mErr.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_dealloc A g.pq (sp' + 224#64) mErr.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_dealloc A g.addr (sp' + 248#64) mErr.addresses)
            (sepConj_mono (optU32At_entails_memRegion8 (sp' + 272#64) mErr.counter)
              (optU32At_entails_memRegion8 (sp' + 280#64) mErr.previousCounter)))))
  refine SepWPp.mono_pre (sepConj_mono hent_wire
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8 (sp' + 88#64))
      (sepConj_mono_left (memRegion120_split16 x19))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 =>
    SepWPp.exists_pre fun s96 => SepWPp.exists_pre fun s88 =>
    SepWPp.exists_pre fun adCap => SepWPp.exists_pre fun adPtr =>
    SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun adAct =>
    SepWPp.exists_pre fun pqCap => SepWPp.exists_pre fun pqPtr =>
    SepWPp.exists_pre fun pqLen => SepWPp.exists_pre fun pqAct =>
    SepWPp.exists_pre fun ctCap => SepWPp.exists_pre fun ctPtr =>
    SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun ctAct =>
    SepWPp.exists_pre fun rkCap => SepWPp.exists_pre fun rkPtr =>
    SepWPp.exists_pre fun rkLen => SepWPp.exists_pre fun rkAct => ?_
  have hvh :
      vecHeader (sp' + 176#64) rkCap rkPtr rkLen =
        ((sp' + 176#64) ↦₆₄ rkCap) ∗ ((sp' + 184#64) ↦₆₄ rkPtr) ∗ ((sp' + 192#64) ↦₆₄ rkLen) ∧
      vecHeader (sp' + 200#64) ctCap ctPtr ctLen =
        ((sp' + 200#64) ↦₆₄ ctCap) ∗ ((sp' + 208#64) ↦₆₄ ctPtr) ∗ ((sp' + 216#64) ↦₆₄ ctLen) ∧
      vecHeader (sp' + 224#64) pqCap pqPtr pqLen =
        ((sp' + 224#64) ↦₆₄ pqCap) ∗ ((sp' + 232#64) ↦₆₄ pqPtr) ∗ ((sp' + 240#64) ↦₆₄ pqLen) ∧
      vecHeader (sp' + 248#64) adCap adPtr adLen =
        ((sp' + 248#64) ↦₆₄ adCap) ∗ ((sp' + 256#64) ↦₆₄ adPtr) ∗ ((sp' + 264#64) ↦₆₄ adLen) := by
    simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, and_self]
  rcases hvh with ⟨hvh1, hvh2, hvh3, hvh4⟩
  rw [hvh1, hvh2, hvh3, hvh4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (968)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine frame_post
    (hnext w0 w1 rkCap rkPtr ctCap ctPtr pqCap pqPtr adCap adPtr rkAct ctAct pqAct adAct
      (PostEpilogueStatePlaced.of_steps hcl1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr, arm64_norm]))
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx24, arm64_norm])
      (by simp [hx26, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
    (by sep_accu) ?_
  rw [herr]
  dsimp only [signalMessageResultAt, errResultAt, speAt]
  sep_interval

end CleanupOpaqueDecodeError

end CryptoVerification.LibsignalTripleRatchet.Wire

