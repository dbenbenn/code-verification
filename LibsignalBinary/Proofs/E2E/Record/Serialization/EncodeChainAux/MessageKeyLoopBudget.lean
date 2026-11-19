/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoop
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBodyBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import ProofLib.SepLogic.CodeLookup
import ProofLib.VCGen
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBody -- proof-setup: allow-public-import

/-!
# Budget-threaded `message_keys` loop and epilogue for `encode::<Chain, Vec<u8>>`

Budget-threaded `[LibsignalPlacement]` proofs for the `message_keys` loop (`+0x258..+0x670`) and
epilogue of `encode::<Chain, Vec<u8>>` (block `12`).
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded
  lsMemcpySym lsρ blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecBuf vecU8At arrayAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost messageKeyAt)
open CryptoVerification.E2E.Record (lenField encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encodeChainStack encChainMem protoChainAt
  encChainSubStack encChainSavedRegs sp_sub_96_aligned stackAt_encodeChainStack_split
  sepWPp_congr_pre MkLoopRegs
  zip_map_snd_eq_encChain zip_length_eq_right mk_endPtr_step
  bv_nat_beq_zero_false mk_endPtr_ne_of_pos bv_madd_104
  vecMkRest sepWPp_extract_vecBuf_mk_le vecBuf_mk_eq_open
  chainMkUnusedAt chainAt_eq_mk_cells sepWPp_extract_chain_mk_bounds
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  doReserveSpec framelessMemcpyBudgetSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  EncodeChainEnv encodeChainSpec msgKeyLenSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_of_sepWP_lscl_vm
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  encodeChainSpecWithEnv encodeChainSpecWithEnv_eq
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem mk_len_tl_lt {α : Type} (x : α) (xs : List α)
    (h : (x :: xs).length * 104 < 2 ^ 32) :
    xs.length * 104 < 2 ^ 32 := by
  simp only [List.length_cons] at h
  omega

private theorem mk_bound_head (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound
  omega

private theorem mk_bound_tail (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    (curBs ++ lenField 4 (encMessageKey gk.2)).length +
      ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound ⊢
  omega

private theorem mk_flatten_nil_len (gk : MessageKeyGhost × MessageKeyGenerator) :
    ((([gk]).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length =
      (lenField 4 (encMessageKey gk.2)).length := by
  simp

private theorem mk_flatten_cons_len (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator)) :
    (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length =
      (lenField 4 (encMessageKey gk.2)).length +
        ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length := by
  simp [List.map_cons, List.flatten_cons, List.length_append]

/-! ## Loop back-edge (`+668..+680`) -/

theorem step_encChain_mk_next_eq_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (v cur endPtr sp0 : BitVec 64) (st : M.σ)
    (heq : ((cur + 104#64) == endPtr) = true)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (lsProg_12 H) ret sm (A.pool lim st sm ∗ F) Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (1648))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm =>
        SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_mk_next_ne_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (v cur endPtr sp0 : BitVec 64) (st : M.σ)
    (hne : ((cur + 104#64) == endPtr) = false)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 668#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v (cur + 104#64) endPtr →
      SepWPp (lsProg_12 H) ret sm (A.pool lim st sm ∗ F) Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (680))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm =>
        SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩

/-! ## Inductive `message_keys` loop (`+680..+1648`) -/

theorem step_encChain_seg4_empty_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (a sp0 : BitVec 64) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 64#64) ↦₆₄ 0#64) ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 1648#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (lsProg_12 H) ret sm ((((a + 64#64) ↦₆₄ 0#64) ∗ A.pool lim st sm) ∗ F) Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (1648))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm =>
        SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
    refine sepWPp_congr_pre (by ac_rfl)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))

theorem step_encChain_seg4_init_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (v a mkPtr sp0 : BitVec 64) (n : Nat) (st : M.σ)
    (hpos : 0 < n) (hlt : n < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 600#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_12).base + 680#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v mkPtr (mkPtr + BitVec.ofNat 64 (n * 104)) →
      SepWPp (lsProg_12 H) ret sm
        ((((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗
          A.pool lim st sm) ∗ F) Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have hnz := bv_nat_beq_zero_false hpos hlt
  have hmadd := bv_madd_104 mkPtr n
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := (blkPl_12).base + bv% (680))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm =>
        SepWPp.transport_budgetPool (A := A) (lim := lim) (st := st) hvmm (by sep_focus) ?_⟩
    refine sepWPp_congr_pre (by ac_rfl)
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *]⟩)

theorem step_encChain_epilogue_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (chainEnv : EncodeChainGhost → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (capOut ptrOut : BitVec 64)
    (st0 : M.σ) (evs : List AllocEvent)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    (hevs : chainEnv x evs)
    (hpc : s.pc = (blkPl_12).base + 1648#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A.repAlloc x.v capOut ptrOut (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      A.pool lim (M.stepEvents evs st0) s ∗ stackAt (s0.sp - 96#64) encChainSubStack ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPp (lsProg_12 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeLoaded lsmpl (encodeChainSpecWithEnv M A lim chainEnv)).post
              (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  unfold encChainSavedRegs
  have hsp_align96 := sp_sub_96_aligned halign
  apply sepWPp_of_sepWP_lscl_vm hcl (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun _hcl_f hvm_f =>
        SepWPp.transport_budgetPool (A := A) (lim := lim) (st := M.stepEvents evs st0) hvm_f
          (by sep_focus) ?_⟩
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩⟩
    intro hm
    dsimp only [withLsCodeLoaded, encodeChainSpecWithEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *], hevs⟩, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨capOut, ptrOut, ?_⟩
    rw [stackAt_encodeChainStack_split s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 28#5), s0.readReg64 (Reg.gpr 27#5),
      s0.readReg64 (Reg.gpr 26#5), s0.readReg64 (Reg.gpr 25#5),
      s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
      s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
    convert hm using 1
    ac_rfl

theorem step_encChain_epilogue_spec_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (capOut ptrOut : BitVec 64)
    (st0 : M.σ) (evs : List AllocEvent)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp} {Qp : State → SepProp → Prop}
    (hevs : EncodeChainEnv x evs)
    (hpc : s.pc = (blkPl_12).base + 1648#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A.repAlloc x.v capOut ptrOut (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      A.pool lim (M.stepEvents evs st0) s ∗ stackAt (s0.sp - 96#64) encChainSubStack ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPp (lsProg_12 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeLoaded lsmpl (encodeChainSpec M A lim)).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      Qp := by
  rw [← encodeChainSpecWithEnv_eq M A lim]
  exact step_encChain_epilogue_placed A lim EncodeChainEnv H capOut ptrOut st0 evs hevs
    hpc hrun hcl hsp halign htr hP

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.MessageKeyLoopBudget
