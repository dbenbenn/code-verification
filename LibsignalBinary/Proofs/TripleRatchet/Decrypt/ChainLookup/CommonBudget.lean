/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget

open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost rootStack)

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
  (ChainKey Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost UuidParser decryptDraws protocolAddressAt sessionStateAt signalMessageAt tapeAfter
   uuidTryParse vecResultAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (tryDecryptCommonHeap tryDecryptMidMetaPlaced tryDecryptPlacedImg
   tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
  (blkPC_131 blkPl_131 decRel_afterTrFrom retEpiloguePC_placed sepWP_to_reaches_pc
   tryDecryptDummyImg tryDecryptEntry_placed tryDecryptMidMeta_placed tryDecryptStack_recombine)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpecBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStackBase)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced ErrTailStateXPlaced
   FindChainStatePlaced LoadRatchetStatePlaced
   tryDecryptFnOnPanic tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
   tryDecryptOnPanic tryDecryptRawSpecPlaced tryDecryptSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
  (sepWP_blk130_vm)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `ChainLookupFacts`: Budget Dealloc Call-Site Helpers -/

namespace ChainLookupFacts

end ChainLookupFacts

/-! ## 2. Metadata Bridges & `VmPreserved`-Strengthened Epilogue (Block `130`) -/

theorem tryDecryptDummyImg_eq_placedImg [LibsignalPlacement] :
    tryDecryptDummyImg = tryDecryptPlacedImg :=
  rfl

theorem tryDecryptMidMeta_placed_to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMeta_placed s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    tryDecryptMidMetaPlaced s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    ⟨h.2.2.2.2.2.2.1, hro⟩, h.2.2.2.2.2.2.2⟩

theorem tryDecryptMidMetaPlaced_to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMetaPlaced s0 s) :
    tryDecryptMidMeta_placed s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1.1, h.2.2.2.2.2.2.2⟩, h.2.2.2.2.2.2.1.2⟩

theorem tryDecrypt_epilogue_394_wp_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s0 s : State) (hpc : s.pc = retEpiloguePC_placed) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1504#64) (hs0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0)
      (fun sf P_f => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ (P_f ⊢ stackAt s0.sp rootStack)) := by
  unfold tryDecryptSavedRegs
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed] at hpc
  apply sepWP_blk130_vm (mid := s0.readReg64 .x30)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hvm, ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]
  · exact tryDecryptStack_recombine s0.sp s0

/-! ## 3. Budget-Threaded Block `130` Checkpoint States & Bridges -/

@[expose] def ErrTailState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailState_placed
    (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

@[expose] def ErrTailStateX_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailStateX_placed
    (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

theorem ErrTailState_placed.toX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ErrTailState_placed.toX h

@[expose] def LoadRatchetState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.LoadRatchetState_placed
    (A.atState lim st s) ctl x R s0 s

@[expose] def FindChainState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.FindChainState_placed
    (A.atState lim st s) ctl x trG tr st1 R s0 s

@[expose] def DhStepState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.DhStepState_placed
    (A.atState lim st s) ctl x trG tr st1 R s0 s

@[expose] def ConsumeMsgKeyState_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.ConsumeMsgKeyState_placed
    (A.atState lim st s) ctl x trG tr st1 ck draws R s0 s

theorem LoadRatchetStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetState_placed A lim st ctl x R s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    LoadRatchetStatePlaced (blkPl_131).base A lim st ctl x R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem LoadRatchetStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetStatePlaced (blkPl_131).base A lim st ctl x R s0 s) :
    LoadRatchetState_placed A lim st ctl x R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem FindChainStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainState_placed A lim st ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    FindChainStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem FindChainStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s) :
    FindChainState_placed A lim st ctl x trG tr st1 R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem DhStepStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : DhStepState_placed A lim st ctl x trG tr st1 R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    DhStepStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem DhStepStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : DhStepStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 R s0 s) :
    DhStepState_placed A lim st ctl x trG tr st1 R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ConsumeMsgKeyStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ConsumeMsgKeyState_placed A lim st ctl x trG tr st1 ck draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ConsumeMsgKeyStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 ck draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ConsumeMsgKeyStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ConsumeMsgKeyStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 ck draws R s0 s) :
    ConsumeMsgKeyState_placed A lim st ctl x trG tr st1 ck draws R s0 s ∧
      LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ErrTailStatePlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ErrTailStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ErrTailStatePlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

theorem ErrTailStateXPlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    ErrTailStateXPlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed_to_placed h.2.1 hro, h.2.2⟩

theorem ErrTailStateXPlaced_to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateXPlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced_to_placed h.2.1).1, h.2.2⟩,
    (tryDecryptMidMetaPlaced_to_placed h.2.1).2⟩

/-! ## 4. Whole-Function Contracts & Epilogue-to-Outcome Combinators -/

abbrev tryDecryptRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  tryDecryptRawSpecPlaced C A lim ctl uuidParse S tdEnv

@[expose] def tryDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeLoaded lsmpl (tryDecryptRawSpec C A lim ctl uuidParse S tdEnv)

abbrev tryDecryptFnRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  tryDecryptFnRawSpecPlaced C decFn A lim ctl uuidParse S tdEnv

@[expose] def tryDecryptFnPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeLoaded lsmpl (tryDecryptFnRawSpec C decFn A lim ctl uuidParse S tdEnv)

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
