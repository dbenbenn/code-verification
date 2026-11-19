/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import ProofLib.SepLogic.HeapIntro

/-!
# `sha2::sha512::compress512` Consumer `HookOk` Row Arm (`ExtraRowSpecs.Compress512RowSpec`)

Row-owned consumer-contract leaf module for `lsCompress512SymCli` (`compress512Sym`) in
`ExtraGhostSpecs.ExtraRowSpec`, narrowed with outermost Route-`R0` `withLsRet` and parameterized by
`256`-byte stack slack (`256 ≤ stk`) at fixed SHA-512 compression function
`Sha512Math.sha512CompressState`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PqxdhPrims Sha512State UnreachedPqxdhPrimitives chunks128 compress512Hook modelPrims
   readSha512State sha512StateBytesLE)
open CryptoVerification.E2E.Pqxdh.Shared
  (compressInPlaceStubSpecPlaced pqxdhHookStack sha512CompressOutBytes)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FdsHiFrame RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (perm_writeBytes_norm)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512
  (compress512StackedMasterSpec stackedMaster_simulates_cliExt
   stackedMaster_simulates_cliExt_budget stackedMaster_simulates_cliExt_keepsFs
   stackedMaster_simulates_pqxdhStubPlaced stackedMaster_simulates_pqxdhStubPlaced_budget
   stackedMaster_simulates_pqxdhStubPlaced_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Math
  (pointsToBytes_sha512StateBytesLE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookOk_withLsRet specSimulates_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

private theorem hookOk_of_simulates {α β : Type} {f : State → State}
    {s₁ : Spec α} {s₂ : Spec β} (hsim : SpecSimulates s₁ s₂) (hok : HookOk f s₁) :
    HookOk f s₂ :=
  fun y R s0 hrun hpre hsp => by
    obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
    obtain ⟨hkf, hsym, hout₁⟩ := hok x R₁ s0 hrun hpre₁ hsp
    exact ⟨hkf, hsym, hmap (f s0) hout₁⟩

private theorem hookOk_withLsRet_of_simulates [LibsignalPlacement] {α β : Type} {f : State → State}
    {master : Spec α} {consumer : Spec β}
    (hsim : SpecSimulates master consumer)
    (hh : HookOk f (withLsRet master)) :
    HookOk f (withLsRet consumer) :=
  hookOk_of_simulates (specSimulates_withLsRet hsim) hh

private theorem hookOk_withLsRet_withAlloc_of_ls [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved (withLsRet spec))) :
    HookOk f (withLsRet (withAlloc A lim spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  exact hookOk_withAlloc_of_withVmPreserved A lim hh ⟨x, st⟩ R s0 hrun
    (by dsimp only [withLsRet, withAlloc] at hpre ⊢; simpa only [sepConj_assoc] using hpre) hsp

/-- `sha2::sha512::compress512` (`lsCompress512SymCli` / `compress512Sym`) consumer `HookOk` arm
    narrowed with outermost Route-`R0` `withLsRet` at fixed `sha512CompressState` with stack slack
    `256 ≤ stk`, bundling all `CliExt.compress512Spec` and `compressInPlaceStubSpec*` variants. -/
structure Compress512RowSpec [LibsignalPlacement] (f : State → State) : Prop where
  vmPreserved : ∀ s : State, VmPreserved s (f s)
  fs_eq : ∀ s : State, (f s).fs = s.fs
  stackedMaster : ∀ stk : Nat, 256 ≤ stk →
    HookOk f (withLsRet (compress512StackedMasterSpec stk))
  stackedMaster_vm : ∀ stk : Nat, 256 ≤ stk →
    HookOk f (withLsRet (withVmPreserved (compress512StackedMasterSpec stk)))
  stackedMaster_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 256 ≤ stk →
    HookOk f (withLsRet (withAlloc A lim (compress512StackedMasterSpec stk)))
  stackedMaster_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 256 ≤ stk →
    HookOk f (withAlloc A lim (withLsRet (compress512StackedMasterSpec stk)))
  cliExt_ls : ∀ {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q))
  cliExt_keepsFs : ∀ {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
    HookOk f (withLsRet (keepsFs (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))
  cliExt_vm : ∀ {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
    HookOk f
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))
  cliExt_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
    HookOk f
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))
  cliExt_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
    HookOk f
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q)))
  pqxdhStubPlaced_ls : ∀ (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
    P0.Q.F512 = sha512CompressState →
    HookOk f
      (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))
  pqxdhStubPlaced_keepsFs : ∀ (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
    P0.Q.F512 = sha512CompressState →
    HookOk f (withLsRet (keepsFs
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))
  pqxdhStubPlaced_vm : ∀ (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
    P0.Q.F512 = sha512CompressState →
    HookOk f (withLsRet (withVmPreserved
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))
  pqxdhStubPlaced_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
    P0.Q.F512 = sha512CompressState →
    HookOk f (withLsRet (withAlloc A lim
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))
  pqxdhStubPlaced_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
    P0.Q.F512 = sha512CompressState →
    HookOk f (withAlloc A lim (withLsRet
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)))

private theorem hookOk_withLsRet_withVm_of_ls [LibsignalPlacement] {α : Type}
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withLsRet spec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    HookOk f (withLsRet (withVmPreserved spec)) := by
  have hv := hookOk_withVmPreserved hh hvm
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ (withVmPreserved (withLsRet spec)).pre x s0 ∗ R := by
    dsimp only [withVmPreserved, withLsRet] at hpre ⊢
    exact hpre
  obtain ⟨hkf, hsym, hout⟩ := hv x R s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, withLsRet] at hpost ⊢
    exact hpost
  · dsimp only [withVmPreserved, withLsRet] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [withVmPreserved, withLsRet] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [withVmPreserved, withLsRet] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Construct `Compress512RowSpec f` from the stacked master `withLsRet` contract (`256 ≤ stk`),
    `VmPreserved`, and `fs` preservation. -/
theorem Compress512RowSpec.of_ls_vm [LibsignalPlacement] {f : State → State}
    (hmaster : ∀ stk : Nat, 256 ≤ stk →
      HookOk f (withLsRet (compress512StackedMasterSpec stk)))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (hfs : ∀ s : State, (f s).fs = s.fs) :
    Compress512RowSpec f := by
  have hext : 256 ≤ extHookStack := by decide
  have hpq : 256 ≤ pqxdhHookStack := by decide
  have hcli_ls : ∀ {Q : PqxdhPrims}, Q.F512 = sha512CompressState →
      HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) :=
    fun hF => hookOk_withLsRet_of_simulates
      (stackedMaster_simulates_cliExt hF).toSpecSimulates (hmaster extHookStack hext)
  have hstubP_ls : ∀ (X : UnreachedPqxdhPrimitives) {P0 : PEParams},
      P0.Q.F512 = sha512CompressState →
      HookOk f (withLsRet
        (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)) :=
    fun X {_} hF => hookOk_withLsRet_of_simulates
      (stackedMaster_simulates_pqxdhStubPlaced X hF).toSpecSimulates (hmaster pqxdhHookStack hpq)
  exact
    { vmPreserved := hvm
      fs_eq := hfs
      stackedMaster := hmaster
      stackedMaster_vm := fun stk hlo => hookOk_withLsRet_withVm_of_ls (hmaster stk hlo) hvm
      stackedMaster_alloc := fun A lim stk hlo =>
        hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hmaster stk hlo) hvm)
      stackedMaster_alloc_ls := fun A lim stk hlo =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hmaster stk hlo) hvm)
      cliExt_ls := hcli_ls
      cliExt_keepsFs := fun hF => hookOk_withLsRet_of_simulates
        (stackedMaster_simulates_cliExt_keepsFs hF).toSpecSimulates (hmaster extHookStack hext)
      cliExt_vm := fun hF => hookOk_withLsRet_of_simulates
        (stackedMaster_simulates_cliExt_budget hF).toSpecSimulates (hmaster extHookStack hext)
      cliExt_alloc := fun {_} A lim {_} hF =>
        hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hcli_ls hF) hvm)
      cliExt_alloc_ls := fun {_} A lim {_} hF =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hcli_ls hF) hvm)
      pqxdhStubPlaced_ls := hstubP_ls
      pqxdhStubPlaced_keepsFs := fun X {_} hF => hookOk_withLsRet_of_simulates
        (stackedMaster_simulates_pqxdhStubPlaced_keepsFs X hF).toSpecSimulates
        (hmaster pqxdhHookStack hpq)
      pqxdhStubPlaced_vm := fun X {_} hF => hookOk_withLsRet_of_simulates
        (stackedMaster_simulates_pqxdhStubPlaced_budget X hF).toSpecSimulates
        (hmaster pqxdhHookStack hpq)
      pqxdhStubPlaced_alloc := fun {_} A lim X {_} hF =>
        hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hstubP_ls X hF) hvm)
      pqxdhStubPlaced_alloc_ls := fun {_} A lim X {_} hF =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hstubP_ls X hF) hvm) }

/-- Construct `Compress512RowSpec f` from an un-narrowed `HookOk f (compress512StackedMasterSpec stk)`
    (`256 ≤ stk`), `VmPreserved`, and `fs` preservation. -/
theorem Compress512RowSpec.of_vm [LibsignalPlacement] {f : State → State}
    (hmaster : ∀ stk : Nat, 256 ≤ stk → HookOk f (compress512StackedMasterSpec stk))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (hfs : ∀ s : State, (f s).fs = s.fs) :
    Compress512RowSpec f :=
  Compress512RowSpec.of_ls_vm (fun stk hlo => hookOk_withLsRet (hmaster stk hlo)) hvm hfs

private theorem next_head {A B C D : SepProp} {m : Memory}
    (h : m ⊨ A ∗ ((B ∗ C) ∗ D)) : m ⊨ B ∗ (C ∗ (D ∗ A)) := by
  rwa [sepConj_comm A ((B ∗ C) ∗ D), sepConj_assoc, sepConj_assoc] at h

private theorem sha512StateBytesLE_len (h : Sha512State) :
    (sha512StateBytesLE h).length = 64 := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem readSha512State_of_pointsToBytes {m : Memory} {a : BitVec 64} {st : Sha512State}
    {R : SepProp} (h : m ⊨ (a ↦ₛ sha512StateBytesLE st) ∗ R) :
    readSha512State m a = st := by
  have hc := h
  rw [pointsToBytes_sha512StateBytesLE a st] at hc
  rcases st with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩ <;>
    try (simp at hl)
  simp only [List.Vector.toList, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hc
  have c0 := hc; rw [sepConj_assoc] at c0
  have r0 : m.read64 a = w0 := (IsBlock.pointsTo64 a w0).read c0
  have c1 := next_head c0
  have r1 : m.read64 (a + 8#64) = w1 := (IsBlock.pointsTo64 (a + 8#64) w1).read c1
  have c2 := next_head c1
  have r2 : m.read64 (a + 16#64) = w2 := (IsBlock.pointsTo64 (a + 16#64) w2).read c2
  have c3 := next_head c2
  have r3 : m.read64 (a + 24#64) = w3 := (IsBlock.pointsTo64 (a + 24#64) w3).read c3
  have c4 := next_head c3
  have r4 : m.read64 (a + 32#64) = w4 := (IsBlock.pointsTo64 (a + 32#64) w4).read c4
  have c5 := next_head c4
  have r5 : m.read64 (a + 40#64) = w5 := (IsBlock.pointsTo64 (a + 40#64) w5).read c5
  have c6 := next_head c5
  have r6 : m.read64 (a + 48#64) = w6 := (IsBlock.pointsTo64 (a + 48#64) w6).read c6
  have c7 := c6
  rw [sepConj_comm ((a + 48#64) ↦₆₄ w6) _, sepConj_assoc] at c7
  have r7 : m.read64 (a + 56#64) = w7 := (IsBlock.pointsTo64 (a + 56#64) w7).read c7
  apply List.Vector.ext
  intro i
  simp only [readSha512State, List.Vector.get_ofFn]
  fin_cases i
  · simpa [List.Vector.get, BitVec.add_zero] using r0
  · simpa [List.Vector.get] using r1
  · simpa [List.Vector.get] using r2
  · simpa [List.Vector.get] using r3
  · simpa [List.Vector.get] using r4
  · simpa [List.Vector.get] using r5
  · simpa [List.Vector.get] using r6
  · simpa [List.Vector.get] using r7

/-- Pure fallback `compress512Hook sha512CompressState` for `lsCompress512Sym`. -/
abbrev compress512Fallback : State → State :=
  compress512Hook sha512CompressState

theorem compress512Fallback_vmPreserved (s : State) : VmPreserved s (compress512Fallback s) := by
  unfold compress512Fallback compress512Hook returnToLinkRegister
  exact ⟨⟨rfl, rfl, rfl⟩, rfl,
    fun a => congrFun (perm_writeBytes_norm _ _ _) a, fun _ _ _ => rfl⟩

private theorem compress512Fallback_master_ok (stk : Nat) :
    HookOk compress512Fallback (compress512StackedMasterSpec stk) := by
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre _hsp
  dsimp only [compress512StackedMasterSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len⟩, hmem⟩
  have hst_rd : readSha512State s0.mem stA = st := readSha512State_of_pointsToBytes hmem
  have hmem_blk :
      s0.mem ⊨ (blkA ↦ₛ bs) ∗ ((stA ↦ₛ sha512StateBytesLE st) ∗ (stackAt s0.sp stk ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (stA ↦ₛ sha512StateBytesLE st) (blkA ↦ₛ bs),
      sepConj_assoc] at hmem
  have hbs_rd : s0.mem.readBytes blkA (128 * n) = bs := by
    rw [← hbs_len]; exact ((IsBlock.pointsToBytes blkA bs).read hmem_blk).2
  let outBytes := sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)
  have hout_len : outBytes.length = 64 := sha512StateBytesLE_len _
  have hst_len : (sha512StateBytesLE st).length = 64 := sha512StateBytesLE_len st
  have hmem_reg :
      s0.mem ⊨ memRegion stA outBytes.length ∗ ((blkA ↦ₛ bs) ∗ (stackAt s0.sp stk ∗ R)) := by
    rw [hout_len]
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans (pointsToBytes_entails_memRegion stA _)
        (by rw [hst_len]; exact Entails.refl _)))
      hmem
  have hlen64 : outBytes.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  have heq : compress512Fallback s0 =
      (s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr) := by
    unfold compress512Fallback compress512Hook returnToLinkRegister
    dsimp only
    rw [hx0, hx1, hx2, hst_rd, hbs_rd]
    rfl
  rw [heq]
  refine ⟨keepsFrozen_writeBytes_of_memRegion outBytes hlen64 hmem_reg,
    rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [compress512StackedMasterSpec]
  have hm_eq :
      ((s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr)).mem =
        s0.mem.writeBytes stA outBytes := rfl
  have hp_pres : ProcessFieldsPreserved s0
      ((s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => congrFun (perm_writeBytes_norm _ _ _) a⟩
  have ha_pres : AllocCallPreserved s0
      ((s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hm_eq]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hp_pres, ha_pres⟩, satisfies_writeBytes outBytes hlen64 hmem_reg⟩

theorem compress512Fallback_rowSpec [LibsignalPlacement] :
    Compress512RowSpec compress512Fallback :=
  Compress512RowSpec.of_vm (fun stk _ => compress512Fallback_master_ok stk)
    compress512Fallback_vmPreserved (fun _ => rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
