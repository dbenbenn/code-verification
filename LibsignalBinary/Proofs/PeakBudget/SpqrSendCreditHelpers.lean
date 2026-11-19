/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
import LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
import LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# SPQR `spqr::send` Sub-Phase `PhaseCreditSpec` Helpers

Exact-call-order `PhaseCreditSpec` bounds for the sub-phases of `spqr::send`: count-bounded event
envelopes (`BoundedCountEvs`), `Authenticator::mac_hdr` / `update`, `<Poly>::compute_at`,
`Poly::from_complete_points`, `<PolyEncoder>::next_chunk`, `<States>::send` across all 11 chunked
variants, `<Chain>::add_epoch`, `<Chain>::send_key`, and `<Message>::serialize`.
-/

public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendCreditHelpers

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator HkdfFn Poly PolyEncoder States chainNextInfo spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainEpochGhost ChainSendKeyGhost chainEpochAlign chainEpochSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents
   rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv FreeOnlyAlign16Evs IterConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec iterPeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrLowInterceptHyps)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
  (allocLargeLive growOrReallocEvents growOrReallocStepCum phaseCreditSpec_growOrRealloc)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
  (allocLargeLive_le_affine growOrReallocStepCum_le_affine)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (NextKeyInternalEnv nextKeyInternalEvents sliceConcat2Events vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
  (ChainSendKeyAllocEnv ChainSendKeyEnv chainEpochPopEvents chainSendKeyEvents
   chainSendKeyPopEvents)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (HkdfToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv computeAtAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)

/-! ## Count-Bounded Event Envelopes (`BoundedCountEvs`) -/

@[expose] def isFreeEv : AllocEvent → Bool
  | .free _ _ => true
  | _ => false

@[expose] def nonFreeEvCount : List AllocEvent → Nat
  | [] => 0
  | ev :: tl => if isFreeEv ev then nonFreeEvCount tl else nonFreeEvCount tl + 1

theorem nonFreeCount_eq_nonFreeEvCount :
    ∀ (evs : List AllocEvent), nonFreeCount evs = nonFreeEvCount evs
  | [] => rfl
  | .free _ _ :: tl => by
    simp only [nonFreeCount, nonFreeEvCount, isFreeEv, ↓reduceIte]
    exact nonFreeCount_eq_nonFreeEvCount tl
  | .alloc _ :: tl => by
    simp only [nonFreeCount, nonFreeEvCount, isFreeEv, Bool.false_eq_true, ↓reduceIte]
    have ih := nonFreeCount_eq_nonFreeEvCount tl
    omega
  | .aligned _ _ :: tl => by
    simp only [nonFreeCount, nonFreeEvCount, isFreeEv, Bool.false_eq_true, ↓reduceIte]
    have ih := nonFreeCount_eq_nonFreeEvCount tl
    omega
  | .realloc _ _ _ :: tl => by
    simp only [nonFreeCount, nonFreeEvCount, isFreeEv, Bool.false_eq_true, ↓reduceIte]
    have ih := nonFreeCount_eq_nonFreeEvCount tl
    omega

/-- Event envelope bounding the non-`.free` event count by `maxNonFree`, every request by `maxReq`, and every alignment by `16`.
-/
@[expose] def BoundedCountEvs (maxNonFree maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxNonFree ∧
    ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

theorem boundedCountEvs_nil (maxNonFree maxReq : Nat) :
    BoundedCountEvs maxNonFree maxReq [] :=
  ⟨Nat.zero_le _, fun _ h => nomatch h⟩

private theorem step_nonFree_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxReq + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz => obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st; omega
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := hM.smallAlloc_le hle; omega
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := hM.smallAlloc_le hle; omega
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      have hsr := hM.smallRealloc_le hnew_le; omega
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal (Nat.lt_of_not_ge hold_le) hnew_le
      have hsr := hM.smallRealloc_le hnew_le; omega

private theorem stepEvents_boundedCount_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (evs : List AllocEvent) :
    ∀ (maxNonFree : Nat) (st0 : M.σ),
      (nonFreeEvCount evs ≤ maxNonFree ∧
        ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxNonFree * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0 := by
  induction evs with
  | nil => intro _ st0 _; simp only [AllocCostModel.stepEvents_nil]; omega
  | cons ev tl ih =>
    intro maxNonFree st0 ⟨hcnt, hall⟩
    have hall0 := hall ev List.mem_cons_self
    have hall_tl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => hall e (List.mem_cons_of_mem _ he)
    simp only [AllocCostModel.stepEvents_cons]
    by_cases hf : isFreeEv ev = true
    · simp only [nonFreeEvCount, hf, ↓reduceIte] at hcnt
      cases ev <;> try contradiction
      rename_i al sz
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
      obtain ⟨hc₂, hl₂, hp₂⟩ := ih maxNonFree (M.step (.free al sz) st0) ⟨hcnt, hall_tl⟩
      omega
    · simp only [nonFreeEvCount, hf, Bool.false_eq_true, ↓reduceIte] at hcnt
      cases maxNonFree with
      | zero => omega
      | succ k =>
        rw [Nat.add_one_mul k]
        obtain ⟨hc₁, hl₁, hp₁⟩ := step_nonFree_small hM st0 hsm hall0.1 hall0.2
        obtain ⟨hc₂, hl₂, hp₂⟩ := ih k (M.step ev st0) ⟨by omega, hall_tl⟩
        omega

/-- Small-class `PhaseCreditSpec` for `BoundedCountEvs maxNonFree maxReq` when `maxReq ≤ smallMaxReq M` (`Δlive = Δpeak = 0`).
-/
theorem boundedCount_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxNonFree maxReq : Nat)
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoundedCountEvs maxNonFree maxReq)
      (maxNonFree * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ h := h.2
  credit_le st0 {_} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedCount_small hM hsm _ maxNonFree st0
      ⟨nonFreeCount_eq_nonFreeEvCount _ ▸ h.1, h.2⟩
    omega

theorem boundedCount_low_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (maxNonFree maxReq : Nat)
    (hsm : maxReq ≤ 8195) :
    PhaseCreditSpec M (BoundedCountEvs maxNonFree maxReq)
      (maxNonFree * (2 * maxReq + 9539)) 0 0 maxReq :=
  boundedCount_small_phaseCreditSpec hM maxNonFree maxReq (Nat.le_trans hsm hLow.hSmallMaxGe)

/-- Single small-allocation `PhaseCreditSpec` (`Δcum = 77 * req + 188`, `Δlive = Δpeak = 0`) when `req ≤ 8195`.
-/
theorem rustAlloc_low_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {req al : Nat} (hal : al ≤ 16) (hreq : req ≤ 8195) :
    PhaseCreditSpec M (· = rustAllocEvents req al) (77 * req + 188) 0 0 req := by
  have hsm : req ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans hreq hLow.hSmallMaxGe
  exact PhaseCreditSpec.mono
    (hLow.hSmallAlloc77 req hsm)
    (Nat.le_refl 0)
    (Nat.le_refl 0)
    (Nat.le_refl req)
    (PhaseCreditSpec.rustAlloc_small_any hM hal hsm)

theorem hkdfToVec_low_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {okmLen : Nat} (hokm : okmLen ≤ 8195) :
    PhaseCreditSpec M (HkdfToVecEnv okmLen) (77 * okmLen + 188) 0 0 okmLen :=
  rustAlloc_low_phaseCreditSpec M hM hLow (by decide) hokm

/-- `libcruxHmacSha256Events` stays in small classes under `SpqrLowInterceptHyps M` (`Δcum ≤ 18,000`, `Δlive = Δpeak = 0`).
-/
theorem libcruxHmacSha256_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) :
    PhaseCreditSpec M (· = libcruxHmacSha256Events) 18000 0 0 64 := by
  have ha64 : PhaseCreditSpec M (· = rustAllocEvents 64 1) 5116 0 0 64 :=
    rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
  have hd64 : PhaseCreditSpec M (· = rustDeallocEvents 64 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 M (by decide)
  have ha32 : PhaseCreditSpec M (· = rustAllocEvents 32 1) 2652 0 0 32 :=
    rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
  have hseq := ha64.concat (ha64.concat (ha64.concat (hd64.concat (hd64.concat (hd64.concat ha32)))))
  refine hseq.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
  intro evs hevs; subst hevs
  simp only [libcruxHmacSha256Events, List.append_assoc, ConcatEnv]
  exact ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl,
    ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩⟩⟩⟩⟩

/-! ## `Authenticator` and Small-Message `encode_bytes` Sub-Phases -/

/-- Allocator trace envelope for `Authenticator::mac_hdr` (`105`-byte concat buffer, `libcrux_hmac_sha256`, and buffer drop).
-/
@[expose] def AuthMacHdrEnv : List AllocEvent → Prop :=
  SeqEnv (SeqEnv (· = rustAllocEvents 105 1) (· = libcruxHmacSha256Events)) FreeOnlyEvs

theorem authMacHdr_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) :
    PhaseCreditSpec M AuthMacHdrEnv 26273 0 0 105 := by
  have ha105 : PhaseCreditSpec M (· = rustAllocEvents 105 1) 8273 0 0 105 :=
    rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
  have h := (ha105.seq (libcruxHmacSha256_phaseCreditSpec M hM hLow)).seq
    (PhaseCreditSpec.freeOnly_of_hyps hM)
  exact h.mono (by omega) (by omega) (by omega) (by omega)

theorem sliceConcat2_aff_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (n : Nat) :
    PhaseCreditSpec M (· = sliceConcat2Events n) (2 * n + 9539) (n + 8195) (n + 8195) n := by
  by_cases hn : n = 0
  · subst hn
    exact (PhaseCreditSpec.nil M).congr_mono (by intro _ h; simpa [sliceConcat2Events] using h)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := n) (al := 1) (by decide)).congr_mono
      (by intro _ h; simpa [sliceConcat2Events, hn] using h)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem sliceConcat2_small_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {n : Nat} (hn : n ≤ 8195) :
    PhaseCreditSpec M (· = sliceConcat2Events n) (77 * n + 188) 0 0 n := by
  by_cases h0 : n = 0
  · subst h0
    exact (PhaseCreditSpec.nil M).congr_mono (by intro _ h; simpa [sliceConcat2Events] using h)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · exact (rustAlloc_low_phaseCreditSpec M hM hLow (req := n) (al := 1) (by decide) hn).congr_mono
      (by intro _ h; simpa [sliceConcat2Events, h0] using h)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Allocator trace envelope for `Authenticator::update` (`[rootKey, k].concat()`, `53`-byte label/epoch concat, `hkdf_to_vec(64)`, and two `32`-byte output slices).
-/
@[expose] def AuthUpdateEnv (rkLen kLen : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = sliceConcat2Events (rkLen + kLen))
    (SeqEnv (· = sliceConcat2Events 53)
      (SeqEnv (HkdfToVecEnv 64)
        (SeqEnv (· = rustAllocEvents 32 1)
          (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs))))

def authUpdateDeltaCum (rkLen kLen : Nat) : Nat :=
  (2 * (rkLen + kLen) + 9539) + 14689

theorem authUpdate_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (rkLen kLen : Nat) :
    PhaseCreditSpec M (AuthUpdateEnv rkLen kLen)
      (authUpdateDeltaCum rkLen kLen)
      (rkLen + kLen + 8195)
      (rkLen + kLen + 8195)
      (max (rkLen + kLen) 64) := by
  have hs1 := sliceConcat2_aff_phaseCreditSpec M hM (rkLen + kLen)
  have hs2 : PhaseCreditSpec M (· = sliceConcat2Events 53) 4269 0 0 53 :=
    sliceConcat2_small_phaseCreditSpec M hM hLow (by decide)
  have hhkdf : PhaseCreditSpec M (HkdfToVecEnv 64) 5116 0 0 64 :=
    hkdfToVec_low_phaseCreditSpec M hM hLow (by decide)
  have ha32 : PhaseCreditSpec M (· = rustAllocEvents 32 1) 2652 0 0 32 :=
    rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
  have h := hs1.seq (hs2.seq (hhkdf.seq (ha32.seq (ha32.seq (PhaseCreditSpec.freeOnly_of_hyps hM)))))
  exact h.mono (by dsimp [authUpdateDeltaCum]; omega) (by omega) (by omega) (by omega)

private theorem iterConcatEnv_flatMap {α : Type} (f : α → List AllocEvent) :
    ∀ (xs : List α), IterConcatEnv (fun x evs => evs = f x) xs (xs.flatMap f)
  | [] => rfl
  | x :: xs => ⟨f x, xs.flatMap f, rfl, rfl, iterConcatEnv_flatMap f xs⟩

private theorem replicate_flatten_eq_flatMap (n : Nat) (evs₀ : List AllocEvent) :
    (List.replicate n evs₀).flatten = (List.replicate n ()).flatMap (fun _ => evs₀) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.flatten_cons, List.flatMap_cons, ih]

private theorem replicate_flatten_zero_live_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (n : Nat) (evs₀ : List AllocEvent) {c r : Nat}
    (h₀ : PhaseCreditSpec M (· = evs₀) c 0 0 r) :
    PhaseCreditSpec M (· = (List.replicate n evs₀).flatten) (n * c) 0 0 r := by
  have hpeak : iterPeak (fun _ : Unit => 0) (fun _ => 0) (List.replicate n ()) = 0 := by
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, iterPeak, ih]
  have hmax : (((List.replicate n ()).map (fun _ => r)).foldr max 0) ≤ r := by
    clear hpeak
    induction n with
    | zero => exact Nat.zero_le r
    | succ k ih =>
      simp only [List.replicate_succ, List.map_cons, List.foldr_cons]
      exact Nat.max_le.2 ⟨Nat.le_refl r, ih⟩
  have hiter := PhaseCreditSpec.iterConcat
    (fun _ : Unit => c) (fun _ => 0) (fun _ => 0) (fun _ => r)
    (List.replicate n ()) (fun _ _ => h₀)
  have hsum_c : ((List.replicate n ()).map (fun _ => c)).sum = n * c := by
    simp [List.map_replicate, List.sum_replicate]
  have hsum_l : ((List.replicate n ()).map (fun _ => 0)).sum = 0 := by
    simp [List.map_replicate, List.sum_replicate]
  refine (hiter.of_imp fun _ h => ?_).mono
    (Nat.le_of_eq hsum_c) (Nat.le_of_eq hsum_l) (Nat.le_of_eq hpeak) hmax
  rw [h, replicate_flatten_eq_flatMap]
  exact iterConcatEnv_flatMap (fun _ : Unit => evs₀) (List.replicate n ())

/-- Small-class `PhaseCreditSpec` for `<PolyEncoder>::encode_bytes` when `msgLen ≤ 8195`. -/
theorem encodeBytes_small_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {msgLen : Nat} (hmsg : msgLen ≤ 8195) :
    PhaseCreditSpec M (EncodeBytesEnv msgLen)
      (16 * (77 * msgLen + 188)) 0 0 msgLen := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hslot := rustAlloc_low_phaseCreditSpec M hM hLow (req := msgLen) (al := 2) (by decide) hmsg
    exact replicate_flatten_zero_live_phaseCreditSpec 16 (rustAllocEvents msgLen 2) hslot
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-! ## `<Poly>::compute_at`, `Poly::from_complete_points`, and `<PolyEncoder>::next_chunk` -/

theorem computeAtCall_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (len : Nat) :
    PhaseCreditSpec M (ComputeAtCallEnv len)
      (4 * len + 9897) (2 * len + 8195) (2 * len + 8195) (max 8 (2 * len)) := by
  have halloc :
      PhaseCreditSpec M (· = computeAtAllocEvents len)
        (4 * len + 9897) (2 * len + 8195) (2 * len + 8195) (max 8 (2 * len)) := by
    unfold computeAtAllocEvents
    by_cases h0 : len = 0
    · simp only [h0, ↓reduceIte]
      have h8 := rustAlloc_low_phaseCreditSpec M hM hLow (req := 8) (al := 2) (by decide) (by decide)
      exact h8.mono (by omega) (by omega) (by omega) (by omega)
    · simp only [h0, ↓reduceIte]
      by_cases h1 : len = 1
      · simp only [h1, ↓reduceIte]
        have ha2 : PhaseCreditSpec M (· = rustAllocEvents 2 2) 342 0 0 2 :=
          rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
        have hsm2 : 2 ≤ HasFineReallocCredit.smallMaxReq M :=
          Nat.le_trans (by decide) hLow.hSmallMaxGe
        have hsm8 : 8 ≤ HasFineReallocCredit.smallMaxReq M :=
          Nat.le_trans (by decide) hLow.hSmallMaxGe
        have hre8 := PhaseCreditSpec.rustRealloc_small_small M
          (old := 2) (new := 8) (al := 2) (by decide) (by decide) (by decide) hsm2 (by decide) hsm8
        have hsr8 := hM.smallRealloc_le hsm8
        have hcat := ha2.concat hre8
        refine hcat.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
        intro evs hevs; subst hevs
        exact ⟨rustAllocEvents 2 2, rustReallocEvents 2 8 2, rfl, rfl, rfl⟩
      · simp only [h1, ↓reduceIte]
        have ha := PhaseCreditSpec.rustAlloc_aff hM (req := 2 * len) (al := 2) (by decide)
        exact ha.mono (by omega) (by omega) (by omega) (by omega)
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Small-class `PhaseCreditSpec` for `<Poly>::compute_at` when `len ≤ 4097` (`Δlive = Δpeak = 0`).
-/
theorem computeAtCall_small_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {len : Nat} (hlen : len ≤ 4097) :
    PhaseCreditSpec M (ComputeAtCallEnv len)
      (154 * len + 9897) 0 0 (max 8 (2 * len)) := by
  have halloc :
      PhaseCreditSpec M (· = computeAtAllocEvents len)
        (154 * len + 9897) 0 0 (max 8 (2 * len)) := by
    unfold computeAtAllocEvents
    by_cases h0 : len = 0
    · simp only [h0, ↓reduceIte]
      have h8 := rustAlloc_low_phaseCreditSpec M hM hLow (req := 8) (al := 2) (by decide) (by decide)
      exact h8.mono (by omega) (by omega) (by omega) (by omega)
    · simp only [h0, ↓reduceIte]
      by_cases h1 : len = 1
      · simp only [h1, ↓reduceIte]
        have ha2 : PhaseCreditSpec M (· = rustAllocEvents 2 2) 342 0 0 2 :=
          rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
        have hsm2 : 2 ≤ HasFineReallocCredit.smallMaxReq M :=
          Nat.le_trans (by decide) hLow.hSmallMaxGe
        have hsm8 : 8 ≤ HasFineReallocCredit.smallMaxReq M :=
          Nat.le_trans (by decide) hLow.hSmallMaxGe
        have hre8 := PhaseCreditSpec.rustRealloc_small_small M
          (old := 2) (new := 8) (al := 2) (by decide) (by decide) (by decide) hsm2 (by decide) hsm8
        have hsr8 := hM.smallRealloc_le hsm8
        have hcat := ha2.concat hre8
        refine hcat.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
        intro evs hevs; subst hevs
        exact ⟨rustAllocEvents 2 2, rustReallocEvents 2 8 2, rfl, rfl, rfl⟩
      · simp only [h1, ↓reduceIte]
        have ha := rustAlloc_low_phaseCreditSpec M hM hLow
          (req := 2 * len) (al := 2) (by decide) (by omega)
        exact ha.mono (by omega) (by omega) (by omega) (by omega)
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Allocator trace envelope of `Poly::from_complete_points` interpolation on `n` buffered `GF16` points.
-/
@[expose] def PointInterpEnv (n : Nat) : List AllocEvent → Prop :=
  BoundedCountEvs (3 * n + 6) (4 * n + 4)

def pointInterpDeltaCum (n : Nat) : Nat :=
  (3 * n + 6) * (2 * (4 * n + 4) + 9539)

/-- When `n ≤ 2047`, `PointInterpEnv n` stays in small classes (`Δlive = Δpeak = 0`). -/
theorem pointInterp_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {n : Nat} (hn : n ≤ 2047) :
    PhaseCreditSpec M (PointInterpEnv n)
      (pointInterpDeltaCum n) 0 0 (4 * n + 4) :=
  boundedCount_low_phaseCreditSpec hM hLow (3 * n + 6) (4 * n + 4) (by omega)

/-- Single-polynomial interpolation, `2 * n`-byte coefficient allocation, and `compute_at` evaluation step in `<PolyEncoder>::next_chunk`.
-/
@[expose] def PolyNextChunkPtStepEnv (n : Nat) : List AllocEvent → Prop :=
  SeqEnv (PointInterpEnv n)
    (SeqEnv (· = rustAllocEvents (2 * n) 2) (ComputeAtCallEnv n))

def polyNextChunkPtStepDeltaCum (n : Nat) : Nat :=
  pointInterpDeltaCum n + (4 * n + 9539) + (4 * n + 9897)

def polyNextChunkPtStepSmallDeltaCum (n : Nat) : Nat :=
  pointInterpDeltaCum n + (154 * n + 188) + (154 * n + 9897)

theorem polyNextChunkPtStep_small_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    {n : Nat} (hn : n ≤ 2047) :
    PhaseCreditSpec M (PolyNextChunkPtStepEnv n)
      (polyNextChunkPtStepSmallDeltaCum n) 0 0 (max 8 (4 * n + 4)) := by
  have hpi := pointInterp_small_phaseCreditSpec hM hLow hn
  have hout := rustAlloc_low_phaseCreditSpec M hM hLow
    (req := 2 * n) (al := 2) (by decide) (by omega)
  have hca := computeAtCall_small_phaseCreditSpec M hM hLow (len := n) (by omega)
  have h := hpi.seq (hout.seq hca)
  exact h.mono (by unfold polyNextChunkPtStepSmallDeltaCum; omega)
    (by omega) (by omega) (by omega)

/-- Count- and length-bounded `<PolyEncoder>::next_chunk` envelope on freshly encoded `EncoderState.points`.
-/
@[expose] def PolyNextChunkPointsBoundedEnv (numSlots maxSlotLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    SeqEnv (· = rustAllocEvents 384 8)
      (SeqEnv (IterSeqEnv (fun _ : Unit => PolyNextChunkPtStepEnv maxSlotLen)
        (List.replicate numSlots ()))
        FreeOnlyEvs)
      evs

theorem polyNextChunkPointsBounded_small_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (numSlots : Nat) {maxSlotLen : Nat} (hsm : maxSlotLen ≤ 2047) :
    PhaseCreditSpec M (PolyNextChunkPointsBoundedEnv numSlots maxSlotLen)
      (29756 + numSlots * polyNextChunkPtStepSmallDeltaCum maxSlotLen)
      0 0
      (max 384 (4 * maxSlotLen + 4)) := by
  have h384 : PhaseCreditSpec M (· = rustAllocEvents 384 8) 29756 0 0 384 :=
    rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
  have hstep := polyNextChunkPtStep_small_phaseCreditSpec M hM hLow hsm
  have hiter := PhaseCreditSpec.iter_zero_live (List.replicate numSlots ()) (fun _ _ => hstep)
  have hlen : (List.replicate numSlots ()).length = numSlots := List.length_replicate
  have hfree := PhaseCreditSpec.freeOnly_of_hyps hM
  have hrhs := h384.seq (hiter.seq hfree)
  have hor := (PhaseCreditSpec.nil M).or hrhs
  refine (hor.of_imp fun _ h => h).mono ?_ (by omega) (by omega) (by omega)
  rw [hlen]; omega

/-- Sequential allocator trace envelope of `<PolyEncoder as Encoder>::next_chunk`. -/
@[expose] def PolyNextChunkEnv (enc : PolyEncoder) (evs : List AllocEvent) : Prop :=
  match enc.s with
  | .points pts =>
    evs = [] ∨
      SeqEnv (· = rustAllocEvents 384 8)
        (SeqEnv (IterSeqEnv (fun pt => PolyNextChunkPtStepEnv pt.value.length) pts) FreeOnlyEvs)
        evs
  | .polys polys =>
    SeqEnv (IterSeqEnv (fun p => ComputeAtCallEnv p.coefficients.length) polys) FreeOnlyEvs evs

/-- Combined slot-count, `.points` element-count (`≤ K`), and `.polys` byte-sum (`≤ rawCap`) bound on a `PolyEncoder`.
-/
@[expose] def EncBounded (K rawCap : Nat) (enc : PolyEncoder) : Prop :=
  match enc.s with
  | .points pts => pts.length ≤ 16 ∧ ∀ pt ∈ pts, pt.value.length ≤ K
  | .polys polys =>
    polys.length ≤ 16 ∧ (polys.map (fun p => 2 * p.coefficients.length)).sum ≤ rawCap

private theorem polys_sum_two_mul_eq :
    ∀ (polys : List Poly),
      (polys.map (fun p => 2 * p.coefficients.length)).sum =
        2 * (polys.map (fun p => p.coefficients.length)).sum
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, List.sum_cons, polys_sum_two_mul_eq ps, Nat.mul_add]

/-! ## `<States>::send` Across All 11 Chunked Variants (`StatesSendEnv`) -/

/-- Binary-call-order allocator trace envelope of `<States>::send` across all 11 chunked braid
variants (`.keysUnsampled` ML-KEM keygen + header encoding, encoder-stepping arms via
`PolyNextChunkEnv`, no-op arms, and `.headerReceived` ML-KEM encaps + ciphertext encoding). -/
def StatesSendEnv (F : ShaCompress) :
    States spqrPolyApi (spqrAuthApi F) → List AllocEvent → Prop
  | .keysUnsampled _ =>
    SeqEnv (BoundedCountEvs 8 2400)
      (SeqEnv AuthMacHdrEnv
        (SeqEnv (· = sliceConcat2Events 96)
          (SeqEnv (EncodeBytesEnv 96)
            (SeqEnv (PolyNextChunkPointsBoundedEnv 16 3) FreeOnlyEvs))))
  | .keysSampled s => PolyNextChunkEnv s.sending_hdr
  | .headerSent s => PolyNextChunkEnv s.sending_ek
  | .ct1Received s => PolyNextChunkEnv s.sending_ek
  | .ekSentCt1Received _ => (· = [])
  | .noHeaderReceived _ => (· = [])
  | .headerReceived s =>
    SeqEnv (BoundedCountEvs 8 2080)
      (SeqEnv (· = sliceConcat2Events 41)
        (SeqEnv (HkdfToVecEnv 32)
          (SeqEnv (AuthUpdateEnv (Authenticator.intoPb s.uc.auth).rootKey.length 32)
            (SeqEnv (EncodeBytesEnv 960)
              (SeqEnv (PolyNextChunkPointsBoundedEnv 16 30) FreeOnlyEvs)))))
  | .ct1Sampled s => PolyNextChunkEnv s.sending_ct1
  | .ekReceivedCt1Sampled s => PolyNextChunkEnv s.sending_ct1
  | .ct1Acknowledged _ => (· = [])
  | .ct2Sampled s => PolyNextChunkEnv s.sending_ct2

/-! ## `<Chain>::add_epoch` and `<Chain>::send_key` Credit Specs -/

private theorem optDealloc_phaseCreditSpec (M : AllocCostModel) [HasFineReallocCredit M]
    (cond : Bool) (sz : Nat) :
    PhaseCreditSpec M (· = if cond then [] else rustDeallocEvents sz 1) 0 0 0 0 := by
  cases cond
  · exact PhaseCreditSpec.rustDealloc_align16 M (by decide)
  · exact PhaseCreditSpec.nil M

private theorem vecDequeGrow_cond_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M] (hM : ModelHyps M)
    (len : Nat) (cap : BitVec 64) :
    let newBytes := max (2 * len) 4 * 112
    PhaseCreditSpec M (· = if len = cap.toNat then vecDequeGrowEvents cap else [])
      (2 * newBytes + 9539) (newBytes + 8195) (newBytes + 8195) newBytes := by
  dsimp only
  by_cases heq : len = cap.toNat
  · simp only [heq, ↓reduceIte]
    have hnew_pos : 0 < max (2 * cap.toNat) 4 * 112 := by omega
    have hev : vecDequeGrowEvents cap =
        growOrReallocEvents (cap.toNat * 112) (max (2 * cap.toNat) 4 * 112) 8 := by
      unfold vecDequeGrowEvents growOrReallocEvents
      dsimp only [chainEpochSize, chainEpochAlign]
      by_cases hc0 : cap = 0#64
      · subst hc0; rfl
      · have hne : cap.toNat * 112 ≠ 0 := by
          have hc_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun ht => hc0 (BitVec.eq_of_toNat_eq ht)
          omega
        simp [hc0, hne]
    rw [hev]
    have hgor := phaseCreditSpec_growOrRealloc M (align := 8)
      (oldReq := cap.toNat * 112) (newReq := max (2 * cap.toNat) 4 * 112) (by decide) hnew_pos
    have hc_aff := growOrReallocStepCum_le_affine M
      (fun _ hr => hM.smallAlloc_le hr) (fun _ hr => hM.smallRealloc_le hr) hM.meta_le
      (cap.toNat * 112) (max (2 * cap.toNat) 4 * 112) 8
    have hl_aff := allocLargeLive_le_affine M
      (fun _ hr => hM.largeCost_le hr) (max (2 * cap.toNat) 4 * 112)
    refine hgor.mono ?_ ?_ ?_ (Nat.le_refl _)
    · split at hc_aff <;> omega
    · split at hl_aff <;> omega
    · split at hl_aff <;> omega
  · simp only [heq, ↓reduceIte]
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- `PhaseCreditSpec` for `<Chain>::add_epoch` bounded in terms of `x.self.links.length`. -/
theorem chainAddEpoch_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (hkdf : HkdfFn) (x : ChainAddEpochGhost) :
    let newBytes := max (2 * x.self.links.length) 4 * 112
    PhaseCreditSpec M (ChainAddEpochEnv hkdf x)
      (2 * newBytes + 28959) (newBytes + 8195) (newBytes + 8195) newBytes := by
  dsimp only
  unfold ChainAddEpochEnv
  split
  · exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have ha32 : PhaseCreditSpec M (· = rustAllocEvents 32 1) 2652 0 0 32 :=
      rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
    have ha72 : PhaseCreditSpec M (· = rustAllocEvents 72 1) 5732 0 0 72 :=
      rustAlloc_low_phaseCreditSpec M hM hLow (by decide) (by decide)
    have hd1 := optDealloc_phaseCreditSpec M (x.G.nextRoot.cap == 0#64) x.G.nextRoot.cap.toNat
    have hd1' : PhaseCreditSpec M
        (· = if x.G.nextRoot.cap = 0#64 then [] else rustDeallocEvents x.G.nextRoot.cap.toNat 1)
        0 0 0 0 := by
      refine hd1.of_imp fun evs h => ?_
      rw [h]; by_cases hc : x.G.nextRoot.cap = 0#64 <;> simp [hc]
    have hd2 := optDealloc_phaseCreditSpec M (x.esPin.cap == 0#64) x.esPin.cap.toNat
    have hd2' : PhaseCreditSpec M
        (· = if x.esPin.cap = 0#64 then [] else rustDeallocEvents x.esPin.cap.toNat 1)
        0 0 0 0 := by
      refine hd2.of_imp fun evs h => ?_
      rw [h]; by_cases hc : x.esPin.cap = 0#64 <;> simp [hc]
    have hvd := vecDequeGrow_cond_phaseCreditSpec M hM x.self.links.length x.G.linksCap
    have hcat :=
      ha32.concat (hd1'.concat (ha72.concat (ha32.concat (ha72.concat (ha32.concat (hvd.concat hd2'))))))
    refine hcat.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
    intro evs hevs; subst hevs
    simp only [chainAddEpochEvents, List.append_assoc, ConcatEnv]
    refine ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨_, _, rfl, rfl, ?_⟩
    exact ⟨_, _, rfl, rfl, rfl⟩

private theorem freeOnlyAlign16_append {e₁ e₂ : List AllocEvent}
    (h₁ : FreeOnlyAlign16Evs e₁) (h₂ : FreeOnlyAlign16Evs e₂) :
    FreeOnlyAlign16Evs (e₁ ++ e₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm₁ | hm₂
  · exact h₁ ev hm₁
  · exact h₂ ev hm₂

private theorem freeOnlyAlign16_optDealloc1 (c : BitVec 64) :
    FreeOnlyAlign16Evs (if c = 0#64 then [] else rustDeallocEvents c.toNat 1) := by
  split
  · intro _ h; nomatch h
  · intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    subst hev
    exact ⟨1, by decide, c.toNat, rfl⟩

private theorem freeOnlyAlign16_chainEpochPopEvents (gce : ChainEpochGhost) :
    FreeOnlyAlign16Evs (chainEpochPopEvents gce) := by
  unfold chainEpochPopEvents
  exact freeOnlyAlign16_append
    (freeOnlyAlign16_append
      (freeOnlyAlign16_append
        (freeOnlyAlign16_optDealloc1 gce.send.next.cap)
        (freeOnlyAlign16_optDealloc1 gce.send.prev.cap))
      (freeOnlyAlign16_optDealloc1 gce.recv.next.cap))
    (freeOnlyAlign16_optDealloc1 gce.recv.prev.cap)

private theorem freeOnlyAlign16_flatMap_pop :
    ∀ (xs : List ChainEpochGhost), FreeOnlyAlign16Evs (xs.flatMap chainEpochPopEvents)
  | [] => fun _ h => nomatch h
  | x :: xs => by
    simp only [List.flatMap_cons]
    exact freeOnlyAlign16_append (freeOnlyAlign16_chainEpochPopEvents x)
      (freeOnlyAlign16_flatMap_pop xs)

private theorem freeOnlyAlign16_chainSendKeyPopEvents (x : ChainSendKeyGhost) :
    FreeOnlyAlign16Evs (chainSendKeyPopEvents x) := by
  unfold chainSendKeyPopEvents
  split
  · intro _ h; nomatch h
  · split
    · intro _ h; nomatch h
    · exact freeOnlyAlign16_flatMap_pop _

theorem nextKeyInternal_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) :
    PhaseCreditSpec M NextKeyInternalEnv 7888 0 0 100 := by
  have hlen : 4 + chainNextInfo.length ≤ 100 := by decide
  have ha := rustAlloc_low_phaseCreditSpec M hM hLow
    (req := 4 + chainNextInfo.length) (al := 1) (by decide) (by omega)
  have hd := PhaseCreditSpec.rustDealloc_align16 M (req := 4 + chainNextInfo.length) (al := 1) (by decide)
  refine (ha.concat hd).congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
  intro evs hevs
  unfold NextKeyInternalEnv nextKeyInternalEvents at hevs
  subst hevs
  exact ⟨_, _, rfl, rfl, rfl⟩

/-! ## `<Message>::serialize` (`MessageSerializeEnv`) -/

/-- Allocator trace envelope for `<Message>::serialize` (`≤ 8` small events of at most `128` bytes).
-/
@[expose] def MessageSerializeEnv : List AllocEvent → Prop :=
  BoundedCountEvs 8 128

theorem messageSerialize_phaseCreditSpec
    (M : AllocCostModel) [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) :
    PhaseCreditSpec M MessageSerializeEnv 78360 0 0 128 :=
  boundedCount_low_phaseCreditSpec hM hLow 8 128 (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrSendCreditHelpers
