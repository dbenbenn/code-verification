/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import

/-!
# Budget-Threaded `<States>::into_pb` — Part 2: Arm 10 (`States.ct2Sampled`)

Proves `EncoderIntoPbEnv` non-free count and `SpqrBoundedEvs` bounds, defines the tight envelope
`Ct2SampledEnv`, and proves fixed-offset `RustCliAllocBudget M` contracts for Arm 10
(`States.ct2Sampled`, tag `12`, `+0 -> +60 -> +1432 -> +1480 -> +1544 -> ret`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (GF16 PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb (TraceCalleeSaved authenticatorHeap bv_add_add_lit bv_sub_sub_lit chunkedCt2Sampled_expose epilogueStagingCells outWords28 outWords28_entails_ct2Sampled protoPolynomialEncoderHeap stA_ct2Sampled_entails_928 statesIntoPbJumpTableAt statesIntoPbJumpTableBytes statesIntoPbName statesIntoPbSavedCells statesIntoPbStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbAllocEvents encoderIntoPbSlotEvents encoderIntoPbVecs fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget (StatesIntoPbPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)

open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

private theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit bv_add_add_lit
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## 1. Re-Exports of `RustAlloc`-Generic `Part2` Helpers -/

abbrev bv_sub_sub_lit_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.bv_sub_sub_lit
abbrev bv_add_add_lit_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.bv_add_add_lit
abbrev chunkedCt2Sampled_expose_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedCt2Sampled_expose
abbrev stA_ct2Sampled_entails_928_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ct2Sampled_entails_928
abbrev outWords28_entails_ct2Sampled_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ct2Sampled

/-! ## 2. Shared `EncoderIntoPbEnv` Non-Free Count & `SpqrBoundedEvs` Lemmas -/

private theorem nonFreeCount_rustAllocEvents (sz al : Nat) :
    nonFreeCount (rustAllocEvents sz al) = 1 := by
  unfold rustAllocEvents
  by_cases hc : al ≤ 16 ∧ al ≤ sz
  · simp [hc, nonFreeCount]
  · simp [hc, nonFreeCount]

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_encoderIntoPbSlotEvents (cs : List GF16) {maxReq : Nat}
    (hmax : 2 * cs.length ≤ MallocngMaxAllocSize)
    (hreq : 2 * cs.length ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (encoderIntoPbSlotEvents cs) := by
  unfold encoderIntoPbSlotEvents
  cases cs with
  | nil =>
    exact SpqrBoundedEvs.nil 1 maxReq
  | cons c rest =>
    have h1 : 1 ≤ 2 * (c :: rest).length := by simp only [List.length_cons]; omega
    have hcond : (1 ≤ 16 ∧ 1 ≤ 2 * (c :: rest).length) := ⟨by decide, h1⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_encoderSlots {maxReq : Nat} :
    ∀ (xss : List (List GF16)),
      (∀ cs ∈ xss, 2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) →
      SpqrBoundedEvs xss.length maxReq (xss.flatMap encoderIntoPbSlotEvents)
  | [], _ => SpqrBoundedEvs.nil 0 maxReq
  | cs :: xss, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hcs := h cs List.mem_cons_self
    have htl := spqrBoundedEvs_flatMap_encoderSlots xss
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h1 := spqrBoundedEvs_encoderIntoPbSlotEvents cs hcs.1 hcs.2
    have happ := SpqrBoundedEvs.append h1 htl
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_of_eq (Nat.max_self maxReq)) happ

private theorem nonFreeCount_encoderIntoPbSlotEvents_le (cs : List GF16) :
    nonFreeCount (encoderIntoPbSlotEvents cs) ≤ 1 := by
  unfold encoderIntoPbSlotEvents
  cases cs with
  | nil => simp [nonFreeCount]
  | cons _ _ => simp [nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_flatMap_encoderSlots_le :
    ∀ (xss : List (List GF16)),
      nonFreeCount (xss.flatMap encoderIntoPbSlotEvents) ≤ xss.length
  | [] => Nat.le_refl 0
  | cs :: xss => by
    simp only [List.flatMap_cons, List.length_cons, nonFreeCount_append]
    have h1 := nonFreeCount_encoderIntoPbSlotEvents_le cs
    have h2 := nonFreeCount_flatMap_encoderSlots_le xss
    omega

theorem nonFreeCount_encoderIntoPbEnv_le {enc : PolyEncoder} {evs : List AllocEvent}
    (henv : EncoderIntoPbEnv enc evs) :
    nonFreeCount evs ≤ 2 + (encoderIntoPbVecs enc).length := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, henc_alloc, hfree⟩
  unfold EncoderIntoPbAllocEnv at henc_alloc
  subst henc_alloc
  simp only [encoderIntoPbAllocEvents, nonFreeCount_append,
    nonFreeCount_eq_zero_of_freeOnly hfree, nonFreeCount_rustAllocEvents]
  have hslots := nonFreeCount_flatMap_encoderSlots_le (encoderIntoPbVecs enc)
  omega

theorem encoderIntoPbEnv_imp_spqrBoundedEvs {enc : PolyEncoder}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + (encoderIntoPbVecs enc).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs enc,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : EncoderIntoPbEnv enc evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, henc_alloc, hfree⟩
  unfold EncoderIntoPbAllocEnv at henc_alloc
  subst henc_alloc
  have hout1 : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hout12 : SpqrBoundedEvs 2 maxReq (rustAllocEvents 384 8 ++ rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 2) (Nat.le_of_eq (Nat.max_self maxReq))
      (SpqrBoundedEvs.append hout1 hout1)
  have hsl : SpqrBoundedEvs (encoderIntoPbVecs enc).length maxReq
      ((encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents) :=
    spqrBoundedEvs_flatMap_encoderSlots (encoderIntoPbVecs enc) hslots
  have hfr : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree)
  have halloc := SpqrBoundedEvs.append hout12 hsl
  have htot := SpqrBoundedEvs.append halloc hfr
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

/-! ## 3. Arm 10 (`States.ct2Sampled`, tag `12`) Envelope, Steppers, and Main Theorems -/

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 10 (`States.ct2Sampled`, tag `12`):
    delegates solely to `<PolyEncoder>::into_pb` on `s.sending_ct2`. -/
abbrev Ct2SampledEnv {F : ShaCompress}
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  EncoderIntoPbEnv s.sending_ct2

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget
