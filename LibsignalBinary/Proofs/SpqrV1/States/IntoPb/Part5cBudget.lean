/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5c
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5c: Arm 9 (`States.ct1Acknowledged`)

Defines the exact allocator event envelope `Ct1AcknowledgedEnv` and its `SpqrBoundedEvs` bridges,
the `VmPreserved` `call_memcpy_keep_relocate_wp` helper over `sessionMemcpyRegionBudgetSpec`,
and verifies Arm 9 (`States.ct1Acknowledged`, tag `11`) under `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder Pt States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Acknowledged)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedCt1Acknowledged_expose ct1AcknowledgedScratchCells
   ct1AcknowledgedScratchCells_entails_memRegions epilogueStagingCells
   memRegion_1424_split_epilogue memRegion_ct1Acknowledged_scratch_split
   memcpy_keep_relocate_recombine memcpy_keep_relocate_split outWords28
   outWords28_entails_ct1Acknowledged protoPolynomialDecoderHeap relocatedHeap
   stA_ct1Acknowledged_entails_928 stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack vecU8CloneTail vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Relocatable
  (words12 words4_polyDecoderAt)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   FreeOnlyEvs RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbAllocEnv_imp_decoderIntoPbEnv decoderIntoPbAllocEvents decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)

open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents)

open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

private theorem seq_vm_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Allocator Event Envelope & Bounds for Arm 9 (`States.ct1Acknowledged`) -/

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 9 (`States.ct1Acknowledged`):
1. `ct1CloneEvents s.uc.ct1` (cloning `s.uc.ct1`),
2. `evs_d1` (`FreeOnlyEvs`, dropping the consumed `ct1` buffer `(cap_ct1, ptr_ct1)`),
3. `evs_dec` (`DecoderIntoPbEnv s.receiving_ek`, serializing and dropping `s.receiving_ek`). -/
@[expose] def Ct1AcknowledgedEnv {F : ShaCompress}
    (s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  ∃ evs_d1 evs_dec,
    evs = (ct1CloneEvents s.uc.ct1 ++ evs_d1) ++ evs_dec ∧
    FreeOnlyEvs evs_d1 ∧
    DecoderIntoPbEnv s.receiving_ek evs_dec

theorem fitsEvents_ct1Clone_of_ct1AcknowledgedEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (cap_ct1 : BitVec 64)
    (hfit : FitsEnv M lim st (Ct1AcknowledgedEnv s)) :
    FitsEvents M lim st (ct1CloneEvents s.uc.ct1) := by
  have hwit : Ct1AcknowledgedEnv s
      ((ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++
       decoderIntoPbAllocEvents s.receiving_ek) :=
    ⟨ct1DeallocEvents cap_ct1, decoderIntoPbAllocEvents s.receiving_ek, rfl,
     freeOnlyEvs_ct1DeallocEvents cap_ct1, decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  have htot := hfit _ hwit
  have h12 := ((fitsEvents_append M lim _ _ st).mp htot).1
  exact ((fitsEvents_append M lim _ _ st).mp h12).1

theorem fitsEnv_decoder_of_ct1AcknowledgedEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (cap_ct1 : BitVec 64)
    (hfit : FitsEnv M lim st (Ct1AcknowledgedEnv s)) :
    FitsEnv M lim
      (M.stepEvents (ct1DeallocEvents cap_ct1) (M.stepEvents (ct1CloneEvents s.uc.ct1) st))
      (DecoderIntoPbAllocEnv s.receiving_ek) := by
  intro evs_dec hdec_eq
  unfold DecoderIntoPbAllocEnv at hdec_eq
  subst hdec_eq
  have hwit : Ct1AcknowledgedEnv s
      ((ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1) ++
       decoderIntoPbAllocEvents s.receiving_ek) :=
    ⟨ct1DeallocEvents cap_ct1, decoderIntoPbAllocEvents s.receiving_ek, rfl,
     freeOnlyEvs_ct1DeallocEvents cap_ct1, decoderIntoPbAllocEnv_imp_decoderIntoPbEnv rfl⟩
  have htot := hfit _ hwit
  have h2 := ((fitsEvents_append M lim
    (ct1CloneEvents s.uc.ct1 ++ ct1DeallocEvents cap_ct1)
    (decoderIntoPbAllocEvents s.receiving_ek) st).mp htot).2
  rwa [M.stepEvents_append] at h2

theorem spqrBoundedEvs_ct1CloneEvents (ct1 : List (BitVec 8))
    (hmax : ct1.length ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 ct1.length (ct1CloneEvents ct1) := by
  unfold ct1CloneEvents
  by_cases h0 : ct1.length = 0
  · simp only [h0, ↓reduceIte]
    exact SpqrBoundedEvs.nil 1 0
  · have h1 : 1 ≤ ct1.length := Nat.pos_of_ne_zero h0
    have hcond : (1 ≤ 16 ∧ 1 ≤ ct1.length) := ⟨by decide, h1⟩
    simp only [h0, ↓reduceIte, rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_decoderIntoPbSlotEvents (pts : List Pt) {maxReq : Nat}
    (hmax : 4 * pts.length ≤ MallocngMaxAllocSize)
    (hreq : 4 * pts.length ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (decoderIntoPbSlotEvents pts) := by
  unfold decoderIntoPbSlotEvents
  cases pts with
  | nil =>
    exact SpqrBoundedEvs.nil 1 maxReq
  | cons pt rest =>
    have h1 : 1 ≤ 4 * (pt :: rest).length := by simp only [List.length_cons]; omega
    have hcond : (1 ≤ 16 ∧ 1 ≤ 4 * (pt :: rest).length) := ⟨by decide, h1⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_slots {α : Type} (f : α → List Pt) {maxReq : Nat} :
    ∀ (xs : List α),
      (∀ x ∈ xs, 4 * (f x).length ≤ MallocngMaxAllocSize ∧ 4 * (f x).length ≤ maxReq) →
      SpqrBoundedEvs xs.length maxReq (xs.flatMap (fun x => decoderIntoPbSlotEvents (f x)))
  | [], _ => SpqrBoundedEvs.nil 0 maxReq
  | x :: xs, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have htl := spqrBoundedEvs_flatMap_slots f xs
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h1 := spqrBoundedEvs_decoderIntoPbSlotEvents (f x) hx.1 hx.2
    have happ := SpqrBoundedEvs.append h1 htl
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_of_eq (Nat.max_self maxReq)) happ

private theorem nonFreeCount_rustAllocEvents (sz al : Nat) :
    nonFreeCount (rustAllocEvents sz al) = 1 := by
  unfold rustAllocEvents
  by_cases hc : al ≤ 16 ∧ al ≤ sz
  · simp [hc, nonFreeCount]
  · simp [hc, nonFreeCount]

private theorem nonFreeCount_ct1CloneEvents_le (ct1 : List (BitVec 8)) :
    nonFreeCount (ct1CloneEvents ct1) ≤ 1 := by
  unfold ct1CloneEvents
  by_cases h0 : ct1.length = 0
  · simp [h0, nonFreeCount]
  · simp [h0, nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_decoderIntoPbSlotEvents_le (pts : List Pt) :
    nonFreeCount (decoderIntoPbSlotEvents pts) ≤ 1 := by
  unfold decoderIntoPbSlotEvents
  cases pts with
  | nil => simp [nonFreeCount]
  | cons _ _ => simp [nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_flatMap_slots_le {α : Type} (f : α → List Pt) :
    ∀ (xs : List α),
      nonFreeCount (xs.flatMap (fun x => decoderIntoPbSlotEvents (f x))) ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.flatMap_cons, List.length_cons, nonFreeCount_append]
    have h1 := nonFreeCount_decoderIntoPbSlotEvents_le (f x)
    have h2 := nonFreeCount_flatMap_slots_le f xs
    omega

theorem nonFreeCount_ct1AcknowledgedEnv_le {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (henv : Ct1AcknowledgedEnv s evs) :
    nonFreeCount evs ≤ 2 + s.receiving_ek.pts.length := by
  rcases henv with ⟨evs_d1, evs_dec, rfl, hfree1, evs_alloc, evs_free, rfl, hdec_alloc, hfree2⟩
  unfold DecoderIntoPbAllocEnv at hdec_alloc
  subst hdec_alloc
  simp only [decoderIntoPbAllocEvents, nonFreeCount_append,
    nonFreeCount_eq_zero_of_freeOnly hfree1, nonFreeCount_eq_zero_of_freeOnly hfree2,
    nonFreeCount_rustAllocEvents]
  have h1 := nonFreeCount_ct1CloneEvents_le s.uc.ct1
  have h2 := nonFreeCount_flatMap_slots_le (fun sl => sl.vec) s.receiving_ek.pts
  omega

theorem ct1AcknowledgedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + s.receiving_ek.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : Ct1AcknowledgedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_d1, evs_dec, rfl, hfree1, evs_alloc, evs_free, rfl, hdec_alloc, hfree2⟩
  unfold DecoderIntoPbAllocEnv at hdec_alloc
  subst hdec_alloc
  have hclone : SpqrBoundedEvs 1 maxReq (ct1CloneEvents s.uc.ct1) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) hct1_req (spqrBoundedEvs_ct1CloneEvents s.uc.ct1 hct1_max)
  have hd1 : SpqrBoundedEvs 0 maxReq evs_d1 :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree1)
  have houter : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hslots : SpqrBoundedEvs s.receiving_ek.pts.length maxReq
      (s.receiving_ek.pts.flatMap (fun sl => decoderIntoPbSlotEvents sl.vec)) :=
    spqrBoundedEvs_flatMap_slots (fun sl => sl.vec) s.receiving_ek.pts hpts
  have hd2 : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree2)
  have h12 := SpqrBoundedEvs.append hclone hd1
  have hdec_alloc := SpqrBoundedEvs.append houter hslots
  have hdec := SpqrBoundedEvs.append hdec_alloc hd2
  have htot := SpqrBoundedEvs.append h12 hdec
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

/-! ## 2. `VmPreserved` `call_memcpy_keep_relocate_wp` Helper -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
