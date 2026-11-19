/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageLift
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (`0x5ce20..0x5d7bc`): Top-Level `RustCliAllocBudget` Proof

Defines the exact per-variant binary allocator event envelope `StatesIntoPbExactVariantEnv` /
`StatesIntoPbExactEnv` across all 11 `States` constructors, proves `StatesIntoPbBounded` /
`StatesIntoPbWellSized` bridges to `SpqrBoundedEvs 64 (2 * (V1State.encodeRaw st.into_pb).length + 1024)`,
and combines all 11 arms on `tripleRatchetProgAtExt` and `.inImage img`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder Pt States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (EkSentCt1Received HeaderSent KeysUnsampled)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost statesIntoPbName)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbAllocEvents decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbEnv encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (SpqrBoundedEvs StatesIntoPbEnv nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget (KeysUnsampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget (Ct2SampledEnv encoderIntoPbEnv_imp_spqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3Budget (KeysSampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bBudget (Ct1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aBudget (NoHeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bBudget (HeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget (EkSentCt1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dBudget (HeaderSentEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget (Ct1AcknowledgedEnv ct1AcknowledgedEnv_imp_spqrBoundedEvs spqrBoundedEvs_ct1CloneEvents spqrBoundedEvs_decoderIntoPbSlotEvents)

open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1SampledEnv)

open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 1. Per-Variant Envelope Monotonicity & Arm-8 Lifting -/

/-- Exact binary allocator event envelope of `<spqr::v1::chunked::states::States>::into_pb`
    (`0x5ce20`) dispatched by `States` constructor. -/
@[expose] def StatesIntoPbExactVariantEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (evs : List AllocEvent) : Prop :=
  match st with
  | .keysUnsampled _ => KeysUnsampledEnv evs
  | .keysSampled s => KeysSampledEnv s evs
  | .headerSent s => HeaderSentEnv s evs
  | .ct1Received s => Ct1ReceivedEnv s evs
  | .ekSentCt1Received s => EkSentCt1ReceivedEnv s evs
  | .noHeaderReceived s => NoHeaderReceivedEnv s evs
  | .headerReceived s => HeaderReceivedEnv s evs
  | .ct1Sampled s => Ct1SampledEnv s evs
  | .ekReceivedCt1Sampled s => EkReceivedCt1SampledEnv s evs
  | .ct1Acknowledged s => Ct1AcknowledgedEnv s evs
  | .ct2Sampled s => Ct2SampledEnv s evs

/-- Exact binary allocator event envelope of `<spqr::v1::chunked::states::States>::into_pb`
    (`0x5ce20`) on `StatesIntoPbGhost F`. -/
@[expose] def StatesIntoPbExactEnv {F : ShaCompress}
    (x : StatesIntoPbGhost F) (evs : List AllocEvent) : Prop :=
  StatesIntoPbExactVariantEnv x.st evs

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

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

theorem decoderIntoPbEnv_imp_spqrBoundedEvs {dec : PolyDecoder}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + dec.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ dec.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : DecoderIntoPbEnv dec evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, hdec_alloc, hfree⟩
  unfold DecoderIntoPbAllocEnv at hdec_alloc
  subst hdec_alloc
  unfold decoderIntoPbAllocEvents
  have houter : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hslots : SpqrBoundedEvs dec.pts.length maxReq
      (dec.pts.flatMap (fun sl => decoderIntoPbSlotEvents sl.vec)) :=
    spqrBoundedEvs_flatMap_slots (fun sl => sl.vec) dec.pts hpts
  have hfr : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree)
  have h12 := SpqrBoundedEvs.append houter hslots
  have htot := SpqrBoundedEvs.append h12 hfr
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

theorem ct1CloneAndDropEnv_imp_spqrBoundedEvs {ct1 : List (BitVec 8)}
    {maxReq : Nat} {evs : List AllocEvent}
    (hmax : ct1.length ≤ MallocngMaxAllocSize)
    (hreq : ct1.length ≤ maxReq)
    (henv : Ct1CloneAndDropEnv ct1 evs) :
    SpqrBoundedEvs 1 maxReq evs := by
  have hcl : ∀ e, Ct1CloneAllocEnv ct1 e → SpqrBoundedEvs 1 maxReq e := by
    rintro _ rfl
    exact SpqrBoundedEvs.mono (Nat.le_refl 1) hreq (spqrBoundedEvs_ct1CloneEvents ct1 hmax)
  rcases henv with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact hcl evs h1
  · have hb1 := hcl e1 h1
    have hb2 : SpqrBoundedEvs 0 maxReq e2 :=
      SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly h2)
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hb1 hb2)

theorem ekReceivedCt1SampledEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ct1).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : EkReceivedCt1SampledEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with hcd | ⟨e1, e2, rfl, hcd, henc⟩
  · have hb1 := ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hb1
  · have hb1 := ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd
    have hb2 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hb1 hb2)

theorem ct1SampledEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 4 + (encoderIntoPbVecs s.sending_ct1).length + s.receiving_ek.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hct1_max : s.uc.ct1.length ≤ MallocngMaxAllocSize)
    (hct1_req : s.uc.ct1.length ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : Ct1SampledEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  have hed : ∀ e,
      SeqEnv (EncoderIntoPbEnv s.sending_ct1) (DecoderIntoPbEnv s.receiving_ek) e →
      SpqrBoundedEvs (3 + (encoderIntoPbVecs s.sending_ct1).length + s.receiving_ek.pts.length)
        maxReq e := by
    rintro e (henc | ⟨e_enc, e_dec, rfl, henc, hdec⟩)
    · have hb := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
      exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hb
    · have hb1 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
      have hb2 := decoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hpts hdec
      exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hb1 hb2)
  rcases henv with hcd | ⟨e1, e2, rfl, hcd, hrest⟩
  · have hb1 := ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hb1
  · have hb1 := ct1CloneAndDropEnv_imp_spqrBoundedEvs hct1_max hct1_req hcd
    have hb2 := hed e2 hrest
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hb1 hb2)

theorem noHeaderReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_hdr.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_hdr.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : NoHeaderReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem headerReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : HeaderReceived spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_ek.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ek.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : HeaderReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem ekSentCt1ReceivedEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 1 + s.receiving_ct2.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ct2.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : EkSentCt1ReceivedEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  decoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hpts henv

theorem headerSentEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : HeaderSent spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 3 + (encoderIntoPbVecs s.sending_ek).length + s.receiving_ct1.pts.length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ek,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (hpts : ∀ sl ∈ s.receiving_ct1.pts,
      4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
    (henv : HeaderSentEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
  · have h1 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) h1
  · have h1 := encoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hslots henc
    have h2 := decoderIntoPbEnv_imp_spqrBoundedEvs (Nat.le_refl _) h384 hpts hdec
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append h1 h2)

/-- Sufficient allocation-count and per-slot byte-length bounds on `st` ensuring
    `StatesIntoPbExactVariantEnv st evs → SpqrBoundedEvs maxAllocs maxReq evs`. -/
@[expose] def StatesIntoPbBounded {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (maxAllocs maxReq : Nat) : Prop :=
  match st with
  | .keysUnsampled _ => True
  | .keysSampled s =>
      2 + (encoderIntoPbVecs s.sending_hdr).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_hdr,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .headerSent s =>
      3 + (encoderIntoPbVecs s.sending_ek).length + s.receiving_ct1.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ek,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) ∧
      (∀ sl ∈ s.receiving_ct1.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct1Received s =>
      2 + (encoderIntoPbVecs s.sending_ek).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ek,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .ekSentCt1Received s =>
      1 + s.receiving_ct2.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ct2.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .noHeaderReceived s =>
      1 + s.receiving_hdr.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_hdr.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .headerReceived s =>
      1 + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct1Sampled s =>
      4 + (encoderIntoPbVecs s.sending_ct1).length + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ekReceivedCt1Sampled s =>
      3 + (encoderIntoPbVecs s.sending_ct1).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct1,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
  | .ct1Acknowledged s =>
      2 + s.receiving_ek.pts.length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      s.uc.ct1.length ≤ MallocngMaxAllocSize ∧
      s.uc.ct1.length ≤ maxReq ∧
      (∀ sl ∈ s.receiving_ek.pts,
        4 * sl.vec.length ≤ MallocngMaxAllocSize ∧ 4 * sl.vec.length ≤ maxReq)
  | .ct2Sampled s =>
      2 + (encoderIntoPbVecs s.sending_ct2).length ≤ maxAllocs ∧
      384 ≤ maxReq ∧
      (∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
        2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)

/-- Specialization of `StatesIntoPbBounded` to the `StatesIntoPbEnv` (`64`-alloc,
    linear-in-`encodeRaw`) parameters. -/
@[expose] def StatesIntoPbWellSized {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  StatesIntoPbBounded st 64 (2 * (V1State.encodeRaw st.into_pb).length + 1024)

theorem statesIntoPbExactVariantEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hbnd : StatesIntoPbBounded st maxAllocs maxReq)
    (henv : StatesIntoPbExactVariantEnv st evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  cases st with
  | keysUnsampled s =>
    change evs = [] at henv
    subst henv
    exact SpqrBoundedEvs.nil maxAllocs maxReq
  | keysSampled s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact encoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hslots henv
  | headerSent s =>
    rcases hbnd with ⟨hcnt, h384, hslots, hpts⟩
    exact headerSentEnv_imp_spqrBoundedEvs hcnt h384 hslots hpts henv
  | ct1Received s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact encoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hslots henv
  | ekSentCt1Received s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact ekSentCt1ReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | noHeaderReceived s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact noHeaderReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | headerReceived s =>
    rcases hbnd with ⟨hcnt, h384, hpts⟩
    exact headerReceivedEnv_imp_spqrBoundedEvs hcnt h384 hpts henv
  | ct1Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hslots, hpts⟩
    exact ct1SampledEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hslots hpts henv
  | ekReceivedCt1Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hslots⟩
    exact ekReceivedCt1SampledEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hslots henv
  | ct1Acknowledged s =>
    rcases hbnd with ⟨hcnt, h384, hct1_max, hct1_req, hpts⟩
    exact ct1AcknowledgedEnv_imp_spqrBoundedEvs hcnt h384 hct1_max hct1_req hpts henv
  | ct2Sampled s =>
    rcases hbnd with ⟨hcnt, h384, hslots⟩
    exact encoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hslots henv

theorem statesIntoPbExactVariantEnv_imp_default {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hws : StatesIntoPbWellSized st)
    (henv : StatesIntoPbExactVariantEnv st evs) :
    SpqrBoundedEvs 64 (2 * (V1State.encodeRaw st.into_pb).length + 1024) evs :=
  statesIntoPbExactVariantEnv_imp_spqrBoundedEvs hws henv

theorem statesIntoPbWellSized_keysUnsampled {F : ShaCompress}
    (s : KeysUnsampled (spqrAuthApi F)) :
    StatesIntoPbWellSized (States.keysUnsampled (P := spqrPolyApi) s) :=
  trivial

theorem statesIntoPbWellSized_noHeaderReceived_of_pts_nil {F : ShaCompress}
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (hpts : s.receiving_hdr.pts = []) :
    StatesIntoPbWellSized (.noHeaderReceived s) := by
  dsimp only [StatesIntoPbWellSized, StatesIntoPbBounded]
  rw [hpts]
  exact ⟨by decide, by omega, fun _ h => nomatch h⟩

theorem statesIntoPbWellSized_noHeaderReceived_of_pts_empty {F : ShaCompress}
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (hcnt : 1 + s.receiving_hdr.pts.length ≤ 64)
    (hempty : ∀ sl ∈ s.receiving_hdr.pts, sl.vec = []) :
    StatesIntoPbWellSized (.noHeaderReceived s) := by
  dsimp only [StatesIntoPbWellSized, StatesIntoPbBounded]
  refine ⟨hcnt, by omega, fun sl hsl => ?_⟩
  rw [hempty sl hsl]
  exact ⟨by decide, Nat.zero_le _⟩

/-! ## 4. Top-Level Fixed-Offset Verification Theorems (`0x5ce20`) -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopBudget
