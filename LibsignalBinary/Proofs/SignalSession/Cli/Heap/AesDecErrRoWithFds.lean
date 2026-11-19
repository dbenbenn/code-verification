/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `withLsRet` and `withFds` Lifts for `aesDecBudgetSpecErrRo` / `cliAesDecBudgetSpecErrRo`

Pool-carried `FdsGe3Closed` (`withFds A`) and `withLsRet` weakening/lifting lemmas for
`aesDecBudgetSpecErrRo` and `cliAesDecBudgetSpecErrRo`, mirroring the `aesDecBudgetSpec` lifts in
`LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Heap.AesDecErrRoWithFds

open Arm64 ProofLib SepProp ProofLib.SepLogic
open CryptoGames.CBC (AesKey Block)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.SignalSession (lsAesDecSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns cliGhostExterns_extra_some)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.AesDecErrRoBudget
  (aesDecBudgetSpecErrRo aesDecBudgetSpecErrRo_post_entails_aesDecBudgetSpec_post
   cliAesDecBudgetSpecErrRo cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero)
open LibsignalBinary.Heap.SpecBudget (aesCallPreBudget aesDecBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
  (hookOk_withFdsGe3Closed_of_fs_eq hookOk_withLsRet_withFdsGe3Closed_of_fs_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_pool_enforced withFds_pool_unenforced withFds_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (extract_withLsRet intro_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (ExtraSpecOk)

private theorem hookOk_of_pre_post {α : Type} {f : State → State} {spec1 spec2 : Spec α}
    {Q : α → State → Prop}
    (hok : HookOk f spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → Q x s0 ∧ (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, Q x s0 → (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    HookOk f spec2 := by
  intro x R s0 hrun hpre2 hsp
  obtain ⟨hq, hpre1⟩ := hpre x R s0 hpre2
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre1 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩
  · exact Or.inl ⟨hret, hcc, hpost x R s0 (f s0) hq hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private theorem hookSat_of_hookOk_lift {α : Type} {hooks : String → Option (State → State)}
    {sym : String} {spec1 spec2 : Spec α}
    (hlift : ∀ f, HookOk f spec1 → HookOk f spec2)
    (hsat : HookSat hooks sym spec1) :
    HookSat hooks sym spec2 := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hlift f hok⟩

private theorem aes_pre_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 P2 P3 P4 P5 Tail R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim st s0 ∗ Tail) ∗ R) :
    s0.mem ⊨ (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq :
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ Tail) ∗ R =
      (⌜FdsGe3Closed s0.fs⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ Tail)) ∗ R := by
    sep_ac_rfl
  rwa [hEq] at h

private theorem aes_post_enforced {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true)
    {P1 : List AllocEvent → SepProp} {P2 P3 Tail R : SepProp}
    {st : M.σ} {sf : State}
    (h : sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗
        (∃∗ evs : List AllocEvent,
          P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail)) ∗ R) :
    sf.mem ⊨ (∃∗ evs : List AllocEvent,
        P1 evs ∗ P2 ∗ P3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨hClosedF, h⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at h ⊢
  rcases h with ⟨evs, h⟩
  refine ⟨evs, ?_⟩
  rw [withFds_pool_enforced A henf]
  have hEq :
      (P1 evs ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ Tail) ∗ R =
      ⌜FdsGe3Closed sf.fs⌝ ∗ ((P1 evs ∗ P2 ∗ P3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ Tail) ∗ R) := by
    sep_ac_rfl
  rw [hEq, satisfies_pure_sepConj]
  exact ⟨hClosedF, h⟩

/-! ## `withLsRet` Postcondition Weakening from `aesDecBudgetSpecErrRo` to `aesDecBudgetSpec` -/

theorem hookOk_withLsRet_aesDecBudgetSpec_of_errRo [LibsignalPlacement]
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (hok : HookOk f (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))) :
    HookOk f (withLsRet (aesDecBudgetSpec D M A lim)) :=
  HookOk.mono hok (fun _ _ _ hp => hp)
    (fun p R s0 sf _ hq =>
      Satisfies.mono
        (sepConj_mono_left
          (aesDecBudgetSpecErrRo_post_entails_aesDecBudgetSpec_post h1 h2 p s0 sf))
        hq)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)

theorem hookOk_withLsRet_aesDecBudgetSpec_of_cliErrRo [LibsignalPlacement]
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {f : State → State}
    (hok : HookOk f (withLsRet (cliAesDecBudgetSpecErrRo D M A lim))) :
    HookOk f (withLsRet (aesDecBudgetSpec D M A lim)) :=
  hookOk_withLsRet_aesDecBudgetSpec_of_errRo
    cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero hok

theorem hookSat_withLsRet_aesDecBudgetSpec_of_errRo [LibsignalPlacement]
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    (h1 : errStr1Addr ≠ 0#64) (h2 : errStr2Addr ≠ 0#64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym
      (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))) :
    HookSat hooks sym (withLsRet (aesDecBudgetSpec D M A lim)) :=
  hookSat_of_hookOk_lift (fun _ => hookOk_withLsRet_aesDecBudgetSpec_of_errRo h1 h2) hsat

theorem hookSat_withLsRet_aesDecBudgetSpec_of_cliErrRo [LibsignalPlacement]
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hooks : String → Option (State → State)} {sym : String}
    (hsat : HookSat hooks sym (withLsRet (cliAesDecBudgetSpecErrRo D M A lim))) :
    HookSat hooks sym (withLsRet (aesDecBudgetSpec D M A lim)) :=
  hookSat_withLsRet_aesDecBudgetSpec_of_errRo
    cliAesDecErrStr1Addr_ne_zero cliAesDecErrStr2Addr_ne_zero hsat

/-! ## `withFds` Lifts for `aesDecBudgetSpecErrRo` and `cliAesDecBudgetSpecErrRo` -/

theorem hookOk_aesDecBudgetErrRo_withFds_of_enforced
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f
      (withFdsGe3Closed (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))) :
    HookOk f (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hokFd rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    dsimp only [withFdsGe3Closed, aesDecBudgetSpecErrRo, aesCallPreBudget] at hpre ⊢
    exact ⟨trivial, aes_pre_enforced henf hpre⟩
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withFdsGe3Closed, aesDecBudgetSpecErrRo, withFds_repAlloc] at hpost ⊢
    exact aes_post_enforced henf hpost

theorem hookOk_cliAesDecBudgetErrRo_withFds_of_enforced
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f (withFdsGe3Closed (cliAesDecBudgetSpecErrRo D M A lim))) :
    HookOk f (cliAesDecBudgetSpecErrRo D M (withFds A) lim) :=
  hookOk_aesDecBudgetErrRo_withFds_of_enforced henf hokFd

theorem hookOk_aesDecBudgetErrRo_withFds
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))
    (hokFd : lim.enforced = true →
      HookOk f (withFdsGe3Closed (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))) :
    HookOk f (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim) := by
  cases henf : lim.enforced
  · have hEq : aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim =
        aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim := by
      simp only [aesDecBudgetSpecErrRo, aesCallPreBudget, withFds_pool_unenforced A henf,
        withFds_repAlloc]
    exact hEq ▸ hok
  · exact hookOk_aesDecBudgetErrRo_withFds_of_enforced henf (hokFd henf)

theorem hookOk_cliAesDecBudgetErrRo_withFds
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {f : State → State}
    (hok : HookOk f (cliAesDecBudgetSpecErrRo D M A lim))
    (hokFd : lim.enforced = true →
      HookOk f (withFdsGe3Closed (cliAesDecBudgetSpecErrRo D M A lim))) :
    HookOk f (cliAesDecBudgetSpecErrRo D M (withFds A) lim) :=
  hookOk_aesDecBudgetErrRo_withFds hok hokFd

theorem hookOk_withLsRet_aesDecBudgetErrRo_withFds_of_enforced [LibsignalPlacement]
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f
      (withLsRet (withFdsGe3Closed (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)))) :
    HookOk f (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim)) := by
  refine hookOk_of_pre_post (Q := fun _ _ => True) hokFd rfl rfl rfl ?_ ?_
  · rintro ⟨x, st⟩ R s0 hpre
    obtain ⟨hlr, hpre⟩ := extract_withLsRet hpre
    refine ⟨trivial, intro_withLsRet hlr ?_⟩
    dsimp only [withFdsGe3Closed, aesDecBudgetSpecErrRo, aesCallPreBudget] at hpre ⊢
    exact aes_pre_enforced henf hpre
  · rintro ⟨x, st⟩ R s0 sf _ hpost
    dsimp only [withLsRet, withFdsGe3Closed, aesDecBudgetSpecErrRo, withFds_repAlloc] at hpost ⊢
    exact aes_post_enforced henf hpost

theorem hookOk_withLsRet_cliAesDecBudgetErrRo_withFds_of_enforced [LibsignalPlacement]
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {f : State → State}
    (hokFd : HookOk f (withLsRet (withFdsGe3Closed (cliAesDecBudgetSpecErrRo D M A lim)))) :
    HookOk f (withLsRet (cliAesDecBudgetSpecErrRo D M (withFds A) lim)) :=
  hookOk_withLsRet_aesDecBudgetErrRo_withFds_of_enforced henf hokFd

theorem hookSat_withLsRet_aesDecBudgetErrRo_withFds_of_enforced [LibsignalPlacement]
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {abs : String → Option (State → State)} {sym : String}
    (hsat : HookSat abs sym
      (withLsRet (withFdsGe3Closed (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim)))) :
    HookSat abs sym
      (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim)) :=
  hookSat_of_hookOk_lift
    (fun _ => hookOk_withLsRet_aesDecBudgetErrRo_withFds_of_enforced henf) hsat

theorem hookSat_withLsRet_cliAesDecBudgetErrRo_withFds_of_enforced [LibsignalPlacement]
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {abs : String → Option (State → State)} {sym : String}
    (hsat : HookSat abs sym
      (withLsRet (withFdsGe3Closed (cliAesDecBudgetSpecErrRo D M A lim)))) :
    HookSat abs sym (withLsRet (cliAesDecBudgetSpecErrRo D M (withFds A) lim)) :=
  hookSat_withLsRet_aesDecBudgetErrRo_withFds_of_enforced henf hsat

theorem hookSat_withLsRet_aesDecBudgetErrRo_withFds_of_extraOk [LibsignalPlacement]
    {D : AesKey → Block → Block} {errStr1Addr errStr2Addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {gh : CliGhostHooks} {baseExt : LibsignalHooks}
    (hOk : ExtraSpecOk gh)
    (hAesDec : HookSat (cliGhostExterns gh baseExt) lsAesDecSym
      (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M A lim))) :
    HookSat (cliGhostExterns gh baseExt) lsAesDecSym
      (withLsRet (aesDecBudgetSpecErrRo D errStr1Addr errStr2Addr M (withFds A) lim)) := by
  obtain ⟨gfn, hLook⟩ := Option.isSome_iff_exists.mp (hOk.lookup_isSome (sym := lsAesDecSym))
  have hExt : cliGhostExterns gh baseExt lsAesDecSym = some gfn :=
    cliGhostExterns_extra_some gh baseExt hLook
  rcases hAesDec with ⟨f, hf, hok⟩
  have hfeq : gfn = f := Option.some.inj (hExt.symm.trans hf)
  subst hfeq
  exact ⟨gfn, hExt,
    hookOk_withLsRet_aesDecBudgetErrRo_withFds_of_enforced henf
      (hookOk_withLsRet_withFdsGe3Closed_of_fs_eq (hOk.rowOk _ gfn hLook).fs_eq hok)⟩

theorem hookSat_withLsRet_cliAesDecBudgetErrRo_withFds_of_extraOk [LibsignalPlacement]
    {D : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {gh : CliGhostHooks} {baseExt : LibsignalHooks}
    (hOk : ExtraSpecOk gh)
    (hAesDec : HookSat (cliGhostExterns gh baseExt) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo D M A lim))) :
    HookSat (cliGhostExterns gh baseExt) lsAesDecSym
      (withLsRet (cliAesDecBudgetSpecErrRo D M (withFds A) lim)) :=
  hookSat_withLsRet_aesDecBudgetErrRo_withFds_of_extraOk henf hOk hAesDec

end LibsignalBinary.Proofs.SignalSession.Cli.Heap.AesDecErrRoWithFds
