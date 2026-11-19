/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonExt
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import ProofLib.SepLogic.WPp
public meta import ProofLib
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Budget Postconditions & Stack Framing

Envelope-parametric and canonical `SepWPp` postconditions (`recvCt2ChunkBudgetPostQ*`),
stack-frame bridges (`19,552` B vs `20,272` B), and `AllocContracts4K` / `DeallocOkExt` helpers.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap sessionMemcpyRegionSpec withStack)
open CryptoVerification.LibsignalSpqrV1 (Bytes LibcruxHmacCall MlKem)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost)

open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (onPanic_entails_of_trace_eq)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (RecvCt2ChunkGhost SplitBytes stackAt_recvCt2ChunkExt_eq_X)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget SeqEnv VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (LibcruxHmacEnv libcruxHmacSha256Events withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (sliceConcat2Events sliceConcat3Events)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
  (AuthUpdateLenEnv authUpdatePinnedEvents authUpdatePinnedEvents_mem_authUpdateLenEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkSlotsEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget
  (OptSecret32AllocEnv RecvCt2ChunkEnv RecvCt2PostDecapsEnv RecvCt2ReserveCt1Env RecvCt2TailEnv
   optSecret32AllocEnv_nonempty recvCt2ChunkBudgetOnPanic recvCt2ChunkEnv_of_stillReceiving
   recvCt2HmacEvents recvCt2MacCt2AllocEvents recvCt2PostDecapsEnv_nonempty
   recvCt2PreAuthUpdateEvents recvCt2ReserveCt1Env_nonempty recvCt2TailEnv_nonempty)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local irreducible] addChunkTotal decodedMessageTotal
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Budget-Form `onPanic` and `allowPanic` Entailment Helpers -/

theorem onPanic_false_entails_recvCt2 {F : ShaCompress} {K : MlKem}
    {x : RecvCt2ChunkGhost F} {s0 sf : State} {Fr : SepProp} :
    (⌜False⌝ : SepProp) ∗ Fr ⊢ recvCt2ChunkBudgetOnPanic K x s0 sf :=
  Entails.pure_left False.elim

theorem onPanic_pure_entails_recvCt2 {P : Prop} {s0 s sf : State} {Fr : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜P ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr ⊢
      ⌜P ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun hp => ?_
  exact Entails.pure_right hp (entails_anyHeap _)

theorem onPanic_budget_entails_recvCt2 {F : ShaCompress} {K : MlKem}
    {x : RecvCt2ChunkGhost F} {s0 s sf : State} {Fr : SepProp}
    (htr : s.trace = s0.trace) :
    recvCt2ChunkBudgetOnPanic K x s sf ∗ Fr ⊢ recvCt2ChunkBudgetOnPanic K x s0 sf :=
  onPanic_pure_entails_recvCt2 htr

theorem onPanic_hmac_budget_entails_recvCt2 {P : Prop} {klen dlen : Nat}
    {s0 s sf : State} {Fr : SepProp}
    (hk : klen < 2 ^ 32) (hd : dlen < 2 ^ 32) (htr : s.trace = s0.trace) :
    (⌜(2 ^ 32 ≤ klen ∨ 2 ^ 32 ≤ dlen) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr ⊢
      ⌜P ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  refine Entails.pure_left fun ⟨hdisj, _⟩ => ?_
  rcases hdisj with hk' | hd' <;> omega

theorem allowPanic_isPanic_budget_recvCt2 {P : Prop} {s0 sf : State} {Q R : SepProp}
    (hP : P) (htr : sf.trace = s0.trace)
    (hm : (Rust.panicked sf).mem ⊨ Q ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜P ∧ s0.trace <+: (Rust.panicked sf).trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have hpref : s0.trace <+: (Rust.panicked sf).trace := by
    simp only [Rust.panicked, htr]
    exact List.prefix_refl _
  exact ⟨⟨hP, hpref⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap Q)) hm⟩

/-! ## Fixed-Offset Budget `SepWPp` Postconditions & Stack-Frame Lift -/

/-- Panic `SepWPp` postcondition for `recv_ct2_chunk` (shared across `X` and `Ext` stacks). -/
abbrev recvCt2ChunkBudgetPostQp {F : ShaCompress} (K : MlKem)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ recvCt2ChunkBudgetOnPanic K x s0 sf ∗ R)

theorem SplitBytes.memcpyVm_withStack_ok {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64)
    (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionBudgetSpec hookStack)) :
    subroutine_ok prog entry (withStack (DefsBudget.SplitBytes.memcpyVmSpec S) hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨dst, src⟩ R0 s_c hpc_c hrun_c hpre_c hsp_c => ?_
  dsimp only [withStack, DefsBudget.SplitBytes.memcpyVmSpec, withVmPreserved,
    SplitBytes.memcpySpec] at hpre_c
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_c
  rcases hpre_c with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (S.to_bytes src))) hmem
  simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  rcases h2 with ⟨bs, h3⟩
  have hpull :
      (memRegion dst n ∗ (⌜bs.length = n⌝ ∗ (src ↦ₛ bs) ∗ S.heap bs)) ∗
        (stackAt s_c.sp hookStack ∗ R0) =
      ⌜bs.length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ bs) ∗ stackAt s_c.sp hookStack ∗ (S.heap bs ∗ R0)) := by
    sep_ac_rfl
  rw [hpull, satisfies_pure_sepConj] at h3
  rcases h3 with ⟨hlen, h4⟩
  have hpre_mc :
      s_c.mem ⊨
        (withStack sessionMemcpyRegionBudgetSpec hookStack).pre (dst, src, bs) s_c ∗
          (S.heap bs ∗ R0) := by
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩, ?_⟩
    rw [hlen]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h4
  refine (hmc.to_outcome (dst, src, bs) (S.heap bs ∗ R0) s_c hpc_c hrun_c hpre_mc hsp_c).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hpost1⟩
    rw [satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hx0_sf, htr_sf⟩, hpost_mem⟩
    dsimp only [withStack, DefsBudget.SplitBytes.memcpyVmSpec, withVmPreserved,
      SplitBytes.memcpySpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨htr_sf, hx0_sf⟩, ?_⟩
    have harrange :
        (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s_c.sp hookStack ∗ S.heap bs ∗ R0 =
        (((dst ↦ₛ bs) ∗ S.heap bs) ∗ (src ↦ₛ bs)) ∗ (stackAt s_c.sp hookStack ∗ R0) := by
      sep_ac_rfl
    rw [harrange] at hpost_mem
    have hsrc_mr : (src ↦ₛ bs) ⊢ memRegion src n := hlen ▸ pointsToBytes_entails_memRegion src bs
    have hstep := Satisfies.mono
      (sepConj_mono_left (sepConj_mono (S.of_bytes dst bs hlen) hsrc_mr)) hpost_mem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hstep
  · right; left
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; left
    refine ⟨code, hex, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1
  · right; right; right
    refine ⟨hoom, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      memcpyRegionSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

theorem fitsEnv_seqEnv_left {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 : List AllocEvent → Prop} (hne2 : ∃ e2, E2 e2)
    (h : FitsEnv M lim st (SeqEnv E1 E2)) :
    FitsEnv M lim st E1 := by
  rcases hne2 with ⟨e2, he2⟩
  intro e1 he1
  exact ((fitsEvents_append M lim e1 e2 st).mp (h (e1 ++ e2) (SeqEnv.append he1 he2))).1

theorem fitsEnv_seqEnv_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 : List AllocEvent → Prop} {e1 : List AllocEvent} (he1 : E1 e1)
    (h : FitsEnv M lim st (SeqEnv E1 E2)) :
    FitsEnv M lim (M.stepEvents e1 st) E2 := by
  intro e2 he2
  exact ((fitsEvents_append M lim e1 e2 st).mp (h (e1 ++ e2) (SeqEnv.append he1 he2))).2

theorem seqEnv_nonempty {E1 E2 : List AllocEvent → Prop}
    (h1 : ∃ e1, E1 e1) (h2 : ∃ e2, E2 e2) :
    ∃ evs, SeqEnv E1 E2 evs := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  exact ⟨e1 ++ e2, SeqEnv.append he1 he2⟩

theorem authUpdateLenEnv_nonempty (rkLen kLen : Nat) :
    ∃ evs, AuthUpdateLenEnv rkLen kLen evs := by
  let g0 : AuthenticatorGhost :=
    { rootKey := { cap := 0#64, ptr := 1#64 }, macKey := { cap := 0#64, ptr := 1#64 } }
  exact ⟨authUpdatePinnedEvents g0 rkLen kLen,
    authUpdatePinnedEvents_mem_authUpdateLenEnv g0 rkLen kLen⟩

theorem freeOnlyEvs_nonempty : ∃ evs, FreeOnlyEvs evs :=
  ⟨[], FreeOnlyEvs.nil⟩

theorem freeOnlyEvs_rustDealloc1 (n : Nat) : FreeOnlyEvs (rustDeallocEvents n 1) :=
  FreeOnlyEvs.singleton 1 n

theorem freeOnlyEvs_macDealloc (ct2FullLen : Nat) :
    FreeOnlyEvs (if ct2FullLen ≤ 128 then [] else rustDeallocEvents (ct2FullLen - 128) 1) := by
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 (ct2FullLen - 128)

theorem recvCt2ChunkEnv_of_epoch_ne {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    (hne : x.epoch ≠ x.self.uc.epoch) :
    RecvCt2ChunkEnv x [] := by
  unfold RecvCt2ChunkEnv
  have hbeq : (x.epoch != x.self.uc.epoch) = true := bne_iff_ne.mpr hne
  simp only [hbeq, ↓reduceIte]

theorem recvCt2ChunkEnv_of_lt_128 {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    {ct2Full : Bytes} {eAdd eDec : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hdec_some : decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk) = some ct2Full)
    (hlt : ct2Full.length < 128)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hdec : DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk) eDec) :
    RecvCt2ChunkEnv x (eAdd ++ eDec) := by
  unfold RecvCt2ChunkEnv
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have htail :
      RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk)) [] := by
    rw [hdec_some]
    dsimp only [RecvCt2TailEnv]
    simp only [hlt, ↓reduceIte]
  simpa only [List.append_nil] using SeqEnv.append hadd (SeqEnv.append hdec htail)

theorem recvCt2ChunkEnv_of_bad_kem_len {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    {ct2Full : Bytes} {eAdd eDec : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hdec_some : decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk) = some ct2Full)
    (hge : ¬ ct2Full.length < 128)
    (hbad : x.self.uc.ct1.length ≠ 960 ∨ x.self.uc.dk.length ≠ 2400)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hdec : DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk) eDec) :
    RecvCt2ChunkEnv x (eAdd ++ eDec ++ recvCt2MacCt2AllocEvents ct2Full.length) := by
  unfold RecvCt2ChunkEnv
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hor : (x.self.uc.ct1.length != 960 || x.self.uc.dk.length != 2400) = true := by
    rcases hbad with hct1 | hdk
    · rw [bne_iff_ne.mpr hct1, Bool.true_or]
    · rw [bne_iff_ne.mpr hdk, Bool.or_true]
  have htail :
      RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk))
        (recvCt2MacCt2AllocEvents ct2Full.length) := by
    rw [hdec_some]
    dsimp only [RecvCt2TailEnv]
    simp only [hge, hor, ↓reduceIte]
  rw [List.append_assoc]
  exact SeqEnv.append hadd (SeqEnv.append hdec htail)

theorem recvCt2ChunkEnv_of_postDecaps {F : ShaCompress} (x : RecvCt2ChunkGhost F)
    {ct2Full : Bytes} {eAdd eDec ePost : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hdec_some : decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk) = some ct2Full)
    (hge : ¬ ct2Full.length < 128)
    (hct1 : x.self.uc.ct1.length = 960)
    (hdk : x.self.uc.dk.length = 2400)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hdec : DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk) eDec)
    (hpost : RecvCt2PostDecapsEnv x.self.uc.auth.rootKey.length ct2Full.length ePost) :
    RecvCt2ChunkEnv x (eAdd ++ eDec ++ ePost) := by
  unfold RecvCt2ChunkEnv
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hor : (x.self.uc.ct1.length != 960 || x.self.uc.dk.length != 2400) = false := by
    simp only [hct1, hdk, bne_self_eq_false, Bool.or_self]
  have htail :
      RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk)) ePost := by
    rw [hdec_some]
    dsimp only [RecvCt2TailEnv]
    simp only [hge, hor, Bool.false_eq_true, ↓reduceIte]
    exact hpost
  rw [List.append_assoc]
  exact SeqEnv.append hadd (SeqEnv.append hdec htail)

theorem recvCt2PostDecapsEnv_mk {rkLen ct2FullLen : Nat}
    {eUpd eRes eFree1 eSec eFree2 : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hres : RecvCt2ReserveCt1Env eRes)
    (hfree1 : FreeOnlyEvs eFree1)
    (hsec : OptSecret32AllocEnv eSec)
    (hfree2 : FreeOnlyEvs eFree2) :
    RecvCt2PostDecapsEnv rkLen ct2FullLen
      (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents ++
        eUpd ++ eRes ++ recvCt2HmacEvents ++ eFree1 ++ eSec ++ eFree2) := by
  have hseq :
      RecvCt2PostDecapsEnv rkLen ct2FullLen
        ((recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) ++
          (eUpd ++ (eRes ++ (recvCt2HmacEvents ++ (eFree1 ++ (eSec ++ eFree2)))))) :=
    SeqEnv.append rfl
      (SeqEnv.append hupd
        (SeqEnv.append hres
          (SeqEnv.append rfl
            (SeqEnv.append hfree1
              (SeqEnv.append hsec hfree2)))))
  simpa only [List.append_assoc] using hseq

theorem fitsEnv_addChunk_of_recvCt2 {F : ShaCompress} {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {x : RecvCt2ChunkGhost F}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hfit : FitsEnv M lim st (RecvCt2ChunkEnv x)) :
    FitsEnv M lim st (AddChunkSlotsEnv x.self.receiving_ct2.pts) := by
  unfold RecvCt2ChunkEnv at hfit
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq] at hfit
  simp only [Bool.false_eq_true, ↓reduceIte] at hfit
  exact fitsEnv_seqEnv_left
    (seqEnv_nonempty
      (decodedMessageEnv_nonempty (addChunkTotal x.self.receiving_ct2 x.chunk))
      (recvCt2TailEnv_nonempty x.self.uc.auth.rootKey.length
        x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk))))
    hfit

theorem fitsEnv_decodedMessage_of_recvCt2 {F : ShaCompress} {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {x : RecvCt2ChunkGhost F} {eAdd : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hfit : FitsEnv M lim st (RecvCt2ChunkEnv x)) :
    FitsEnv M lim (M.stepEvents eAdd st)
      (DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk)) := by
  unfold RecvCt2ChunkEnv at hfit
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq] at hfit
  simp only [Bool.false_eq_true, ↓reduceIte] at hfit
  exact fitsEnv_seqEnv_left
    (recvCt2TailEnv_nonempty x.self.uc.auth.rootKey.length
      x.self.uc.ct1.length x.self.uc.dk.length
      (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk)))
    (fitsEnv_seqEnv_right hadd hfit)

theorem fitsEnv_tail_of_recvCt2 {F : ShaCompress} {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {x : RecvCt2ChunkGhost F} {eAdd eDec : List AllocEvent}
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : AddChunkSlotsEnv x.self.receiving_ct2.pts eAdd)
    (hdec : DecodedMessageEnv (addChunkTotal x.self.receiving_ct2 x.chunk) eDec)
    (hfit : FitsEnv M lim st (RecvCt2ChunkEnv x)) :
    FitsEnv M lim (M.stepEvents eDec (M.stepEvents eAdd st))
      (RecvCt2TailEnv x.self.uc.auth.rootKey.length x.self.uc.ct1.length x.self.uc.dk.length
        (decodedMessageTotal (addChunkTotal x.self.receiving_ct2 x.chunk))) := by
  unfold RecvCt2ChunkEnv at hfit
  have hbeq : (x.epoch != x.self.uc.epoch) = false := by
    rw [hepoch, bne_self_eq_false]
  rw [hbeq] at hfit
  simp only [Bool.false_eq_true, ↓reduceIte] at hfit
  exact fitsEnv_seqEnv_right hdec (fitsEnv_seqEnv_right hadd hfit)

theorem fitsEvents_macCt2Alloc_of_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct1Len dkLen : Nat} {ct2Full : Bytes}
    (hge : ¬ ct2Full.length < 128)
    (htail : FitsEnv M lim st (RecvCt2TailEnv rkLen ct1Len dkLen (some ct2Full))) :
    FitsEvents M lim st (recvCt2MacCt2AllocEvents ct2Full.length) := by
  unfold RecvCt2TailEnv at htail
  simp only [hge, ↓reduceIte] at htail
  split at htail
  · exact htail _ rfl
  · have hne_rest :
        ∃ e, SeqEnv (AuthUpdateLenEnv rkLen 32)
          (SeqEnv RecvCt2ReserveCt1Env
            (SeqEnv (· = recvCt2HmacEvents)
              (SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))) e :=
      seqEnv_nonempty (authUpdateLenEnv_nonempty rkLen 32)
        (seqEnv_nonempty recvCt2ReserveCt1Env_nonempty
          (seqEnv_nonempty ⟨recvCt2HmacEvents, rfl⟩
            (seqEnv_nonempty freeOnlyEvs_nonempty
              (seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty))))
    have hpre := (fitsEnv_seqEnv_left hne_rest htail) _ rfl
    exact ((fitsEvents_append M lim _ _ st).mp hpre).1

theorem fitsEnv_postDecaps_of_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct1Len dkLen : Nat} {ct2Full : Bytes}
    (hge : ¬ ct2Full.length < 128) (hct1 : ct1Len = 960) (hdk : dkLen = 2400)
    (htail : FitsEnv M lim st (RecvCt2TailEnv rkLen ct1Len dkLen (some ct2Full))) :
    FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2Full.length) := by
  unfold RecvCt2TailEnv at htail
  have hor : (ct1Len != 960 || dkLen != 2400) = false := by
    simp only [hct1, hdk, bne_self_eq_false, Bool.or_self]
  simp only [hge, hor, Bool.false_eq_true, ↓reduceIte] at htail
  exact htail

private theorem postDecaps_tail1_nonempty (rkLen : Nat) :
    ∃ e, SeqEnv (AuthUpdateLenEnv rkLen 32)
      (SeqEnv RecvCt2ReserveCt1Env
        (SeqEnv (· = recvCt2HmacEvents)
          (SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))) e :=
  seqEnv_nonempty (authUpdateLenEnv_nonempty rkLen 32)
    (seqEnv_nonempty recvCt2ReserveCt1Env_nonempty
      (seqEnv_nonempty ⟨recvCt2HmacEvents, rfl⟩
        (seqEnv_nonempty freeOnlyEvs_nonempty
          (seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty))))

private theorem postDecaps_tail2_nonempty :
    ∃ e, SeqEnv RecvCt2ReserveCt1Env
      (SeqEnv (· = recvCt2HmacEvents)
        (SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs))) e :=
  seqEnv_nonempty recvCt2ReserveCt1Env_nonempty
    (seqEnv_nonempty ⟨recvCt2HmacEvents, rfl⟩
      (seqEnv_nonempty freeOnlyEvs_nonempty
        (seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty)))

private theorem postDecaps_tail3_nonempty :
    ∃ e, SeqEnv (· = recvCt2HmacEvents)
      (SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)) e :=
  seqEnv_nonempty ⟨recvCt2HmacEvents, rfl⟩
    (seqEnv_nonempty freeOnlyEvs_nonempty
      (seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty))

private theorem postDecaps_tail4_nonempty :
    ∃ e, SeqEnv FreeOnlyEvs (SeqEnv OptSecret32AllocEnv FreeOnlyEvs) e :=
  seqEnv_nonempty freeOnlyEvs_nonempty
    (seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty)

private theorem postDecaps_tail5_nonempty :
    ∃ e, SeqEnv OptSecret32AllocEnv FreeOnlyEvs e :=
  seqEnv_nonempty optSecret32AllocEnv_nonempty freeOnlyEvs_nonempty

theorem fitsEvents_preAuth_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat}
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEvents M lim (M.stepEvents (recvCt2MacCt2AllocEvents ct2FullLen) st)
      recvCt2PreAuthUpdateEvents := by
  unfold RecvCt2PostDecapsEnv at hpost
  have h1 := (fitsEnv_seqEnv_left (postDecaps_tail1_nonempty rkLen) hpost) _ rfl
  exact ((fitsEvents_append M lim _ _ st).mp h1).2

theorem fitsEnv_authUpdate_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat}
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEnv M lim
      (M.stepEvents (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st)
      (AuthUpdateLenEnv rkLen 32) := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact fitsEnv_seqEnv_left postDecaps_tail2_nonempty
    (fitsEnv_seqEnv_right
      (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
      rfl hpost)

theorem fitsEnv_reserveCt1_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat} {eUpd : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEnv M lim
      (M.stepEvents eUpd
        (M.stepEvents (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st))
      RecvCt2ReserveCt1Env := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact fitsEnv_seqEnv_left postDecaps_tail3_nonempty
    (fitsEnv_seqEnv_right hupd
      (fitsEnv_seqEnv_right
        (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
        rfl hpost))

theorem fitsEnv_doReserve_of_reserveCt1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (c : DoReserveCall)
    (hlen : c.bs.length = 960) (hadd : c.additional = 128)
    (hge : 960 ≤ c.cap.toNat) (hlt : c.cap.toNat < 1088)
    (hres : FitsEnv M lim st RecvCt2ReserveCt1Env) :
    FitsEnv M lim st (DoReserveEnv c) :=
  (fitsEnv_doReserve_iff c).mpr
    (hres (doReserveEvents c)
      (DefsBudget.recvCt2ReserveCt1Env_of_doReserve c hlen hadd hge hlt))

theorem fitsEvents_hmac_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat} {eUpd eRes : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hres : RecvCt2ReserveCt1Env eRes)
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEvents M lim
      (M.stepEvents eRes
        (M.stepEvents eUpd
          (M.stepEvents (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st)))
      recvCt2HmacEvents := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact (fitsEnv_seqEnv_left postDecaps_tail4_nonempty
    (fitsEnv_seqEnv_right hres
      (fitsEnv_seqEnv_right hupd
        (fitsEnv_seqEnv_right
          (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
          rfl hpost))))
    recvCt2HmacEvents rfl

theorem fitsEnv_libcruxHmacEnv_of_fitsEvents {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : LibcruxHmacCall)
    (hk : x.key.length < 2 ^ 32) (hd : x.data.length < 2 ^ 32)
    (hfit : FitsEvents M lim st libcruxHmacSha256Events) :
    FitsEnv M lim st (LibcruxHmacEnv x) := by
  intro evs hevs
  unfold LibcruxHmacEnv at hevs
  simp only [hk, hd, and_self, ↓reduceIte] at hevs
  rwa [hevs]

theorem fitsEnv_free1_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat} {eUpd eRes : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hres : RecvCt2ReserveCt1Env eRes)
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEnv M lim
      (M.stepEvents recvCt2HmacEvents
        (M.stepEvents eRes
          (M.stepEvents eUpd
            (M.stepEvents (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st))))
      FreeOnlyEvs := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact fitsEnv_seqEnv_left postDecaps_tail5_nonempty
    (fitsEnv_seqEnv_right (E1 := fun x => x = recvCt2HmacEvents) rfl
      (fitsEnv_seqEnv_right hres
        (fitsEnv_seqEnv_right hupd
          (fitsEnv_seqEnv_right
            (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
            rfl hpost))))

theorem fitsEnv_optSecret32_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat} {eUpd eRes eFree1 : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hres : RecvCt2ReserveCt1Env eRes)
    (hfree1 : FreeOnlyEvs eFree1)
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEnv M lim
      (M.stepEvents eFree1
        (M.stepEvents recvCt2HmacEvents
          (M.stepEvents eRes
            (M.stepEvents eUpd
              (M.stepEvents
                (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st)))))
      OptSecret32AllocEnv := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact fitsEnv_seqEnv_left freeOnlyEvs_nonempty
    (fitsEnv_seqEnv_right hfree1
      (fitsEnv_seqEnv_right (E1 := fun x => x = recvCt2HmacEvents) rfl
        (fitsEnv_seqEnv_right hres
          (fitsEnv_seqEnv_right hupd
            (fitsEnv_seqEnv_right
              (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
              rfl hpost)))))

theorem fitsEnv_free2_of_postDecaps {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rkLen ct2FullLen : Nat} {eUpd eRes eFree1 eSec : List AllocEvent}
    (hupd : AuthUpdateLenEnv rkLen 32 eUpd)
    (hres : RecvCt2ReserveCt1Env eRes)
    (hfree1 : FreeOnlyEvs eFree1)
    (hsec : OptSecret32AllocEnv eSec)
    (hpost : FitsEnv M lim st (RecvCt2PostDecapsEnv rkLen ct2FullLen)) :
    FitsEnv M lim
      (M.stepEvents eSec
        (M.stepEvents eFree1
          (M.stepEvents recvCt2HmacEvents
            (M.stepEvents eRes
              (M.stepEvents eUpd
                (M.stepEvents
                  (recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents) st))))))
      FreeOnlyEvs := by
  unfold RecvCt2PostDecapsEnv at hpost
  exact fitsEnv_seqEnv_right hsec
    (fitsEnv_seqEnv_right hfree1
      (fitsEnv_seqEnv_right (E1 := fun x => x = recvCt2HmacEvents) rfl
        (fitsEnv_seqEnv_right hres
          (fitsEnv_seqEnv_right hupd
            (fitsEnv_seqEnv_right
              (E1 := fun x => x = recvCt2MacCt2AllocEvents ct2FullLen ++ recvCt2PreAuthUpdateEvents)
              rfl hpost)))))

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
