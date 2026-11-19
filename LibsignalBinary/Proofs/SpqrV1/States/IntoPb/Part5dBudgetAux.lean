/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5d -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Shared `RustCliAllocBudget` Helpers for Arms 7 & 8

Shared allocator envelopes (`Ct1CloneAllocEnv`, `Ct1CloneAndDropEnv`, `Ct1SampledEnv`,
`EkReceivedCt1SampledEnv`), `VmPreserved` prologue/epilogue wrappers, and `<PolyEncoder>::into_pb` /
`<PolyDecoder>::into_pb` call-and-expose helpers for Arms 7 (`States.ct1Sampled`) and 8
(`States.ekReceivedCt1Sampled`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux

open CryptoVerification.SpqrV1.States.IntoPb (bv_add_add_lit' bv_sub_sub_lit' sp_sub_1520_add_1424 sp_sub_480_add_200 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168 sp_sub_96_sub_176 sp_sub_96_sub_192 sp_sub_96_sub_208 statesIntoPbJumpTableAt statesIntoPbStack)

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (
  PolyDecoder PolyEncoder States spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled EkReceivedCt1Sampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoInnerStateAt optProtoInnerStateSize sub_ok_of_addr_eq vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
  protoPolynomialDecoderAt protoPolynomialDecoderSize
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (
  ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents
)

/-! ## 1. VM-Step & Framing Helpers -/

theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

theorem vmPreserved_prepend {s s1 s2 : State}
    (h2 : VmPreserved s1 s2) (h1 : VmPreserved s s1) :
    VmPreserved s s2 :=
  h1.trans h2

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

theorem seq_vm_step {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

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

local macro "by_into_pb_vm_steps " "(" tac:tacticSeq ")" : tactic =>
  `(tactic| (
      apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
      ($tac)))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_1520_add_1424
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168 sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 2. Allocator Event Envelopes for Arms 7 & 8 -/

/-- Exact allocation envelope for cloning `ct1 : List (BitVec 8)`. -/
@[expose] def Ct1CloneAllocEnv (ct1 : List (BitVec 8)) : List AllocEvent → Prop :=
  (· = ct1CloneEvents ct1)

/-- Sequential envelope for cloning `ct1` followed by dropping the old `(cap_ct1, ptr_ct1)` buffer. -/
@[expose] def Ct1CloneAndDropEnv (ct1 : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAllocEnv ct1) FreeOnlyEvs

theorem fitsEvents_clone_of_ct1CloneAndDropEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {ct1 : List (BitVec 8)}
    (h : FitsEnv M lim st (Ct1CloneAndDropEnv ct1)) :
    FitsEvents M lim st (ct1CloneEvents ct1) :=
  FitsEnv.eq_iff.mp h.seq_left

theorem ct1CloneAndDropEnv_of_dealloc (ct1 : List (BitVec 8)) (cap_ct1 : BitVec 64) :
    Ct1CloneAndDropEnv ct1 (ct1CloneEvents ct1 ++ ct1DeallocEvents cap_ct1) :=
  SeqEnv.append rfl (freeOnlyEvs_ct1DeallocEvents cap_ct1)

/-- Full allocator event envelope for Arm 7 (`States.ct1Sampled`):
    `Ct1CloneAndDropEnv s.uc.ct1`, then `EncoderIntoPbEnv s.sending_ct1`,
    then `DecoderIntoPbEnv s.receiving_ek`. -/
@[expose] def Ct1SampledEnv {F : ShaCompress}
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAndDropEnv s.uc.ct1)
    (SeqEnv (EncoderIntoPbEnv s.sending_ct1) (DecoderIntoPbEnv s.receiving_ek))

theorem ct1SampledEnv_of_parts {F : ShaCompress}
    {s : Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {evs_cd evs_enc evs_dec : List AllocEvent}
    (hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd)
    (henc : EncoderIntoPbEnv s.sending_ct1 evs_enc)
    (hdec : DecoderIntoPbEnv s.receiving_ek evs_dec) :
    Ct1SampledEnv s (evs_cd ++ (evs_enc ++ evs_dec)) :=
  SeqEnv.append hcd (SeqEnv.append henc hdec)

/-- Full allocator event envelope for Arm 8 (`States.ekReceivedCt1Sampled`):
    `Ct1CloneAndDropEnv s.uc.ct1`, then `EncoderIntoPbEnv s.sending_ct1`. -/
@[expose] def EkReceivedCt1SampledEnv {F : ShaCompress}
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAndDropEnv s.uc.ct1) (EncoderIntoPbEnv s.sending_ct1)

theorem ekReceivedCt1SampledEnv_of_parts {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {evs_cd evs_enc : List AllocEvent}
    (hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd)
    (henc : EncoderIntoPbEnv s.sending_ct1 evs_enc) :
    EkReceivedCt1SampledEnv s (evs_cd ++ evs_enc) :=
  SeqEnv.append hcd henc

/-! ## 3. Re-Exports of `RustAlloc`-Parametric Representation Helpers -/

abbrev polyEncoderTag := @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTag
abbrev encoderStateTailAt := @CryptoVerification.SpqrV1.States.IntoPb.encoderStateTailAt
abbrev polyEncoderTailAt := @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTailAt
abbrev polyEncoderAt_eq_tag_tail :=
  @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderAt_eq_tag_tail
abbrev polyEncoderTag_eq_zero_or_one :=
  @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTag_eq_zero_or_one
abbrev chunkedCt1Sampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedCt1Sampled_expose
abbrev stA_ct1Sampled_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ct1Sampled_entails_928
abbrev ct1SampledScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ct1SampledScratchCells_entails_memRegions
abbrev outWords28_entails_ct1Sampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ct1Sampled
abbrev chunkedEkReceivedCt1Sampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedEkReceivedCt1Sampled_expose
abbrev stA_ekReceivedCt1Sampled_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ekReceivedCt1Sampled_entails_928
abbrev ekReceivedScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ekReceivedScratchCells_entails_memRegions
abbrev outWords28_entails_ekReceivedCt1Sampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ekReceivedCt1Sampled

/-! ## 4. `EncoderIntoPb` & `DecoderIntoPb` Call-and-Expose Helpers -/

/-- Envelope-parametric per-variant fixed-offset specification of `<States>::into_pb`. -/
@[expose] def statesIntoPbVariantSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, stA⟩, st) s0 =>
    ⌜s0.readReg64 .x8 = out ∧ s0.readReg64 .x0 = stA ∧
      (b &&& 0xfff#64) = 0#64 ∧ FitsEnv M lim st Env⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA stateVal ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack
  post := fun (⟨out, stA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

abbrev statesIntoPbCt1SampledSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Sampled s) (Ct1SampledEnv s)

abbrev statesIntoPbEkReceivedCt1SampledSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.ekReceivedCt1Sampled s)
    (EkReceivedCt1SampledEnv s)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
