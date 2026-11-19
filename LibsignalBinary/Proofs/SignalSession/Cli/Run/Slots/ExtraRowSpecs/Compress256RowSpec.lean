/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf -- proof-setup: allow-public-import

/-!
# `sha2::sha256::compress256` Consumer `HookOk` Row Arm (`ExtraRowSpecs.Compress256RowSpec`)

Row-owned consumer-contract leaf module for `lsCompress256Sym` in `ExtraGhostSpecs.ExtraRowSpec`,
narrowed with outermost Route-`R0` `withLsRet` and parameterized by `176`-byte stack slack
(`176 ≤ stk`) at fixed SHA-256 compression function
`CryptoVerification.LibsignalSpqrV1.sha256Compress`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.LibsignalTripleRatchet (compress256Spec withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HookOkCompress256 KeepsExec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionCompress256ROBudgetSpec)

/-- Single-block `sha2::sha256::compress256` contract (`x2 = 1#64`), matching
    `Slots.compress256SingleSpec` field-for-field (`rfl` via `hookOk_congr`). -/
@[expose] def compress256RowSingleSpec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8)) where
  pre := fun (stA, st, blkA, blk) s =>
    ⌜s.readReg64 .x0 = stA ∧ s.readReg64 .x1 = blkA ∧ s.readReg64 .x2 = 1#64 ∧
      blk.length = 64⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ blk)
  post := fun (stA, st, blkA, blk) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ shaStateBytes (F st blk)) ∗ (blkA ↦ₛ blk)

/-- `sha2::sha256::compress256` (`lsCompress256Sym`) consumer `HookOk` arm narrowed with outermost
    Route-`R0` `withLsRet` at fixed `sha256Compress` with stack slack `176 ≤ stk`:
    - `HookOkCompress256 f sha256Compress` (`withLsRet (sessionCompress256ROBudgetSpec sha256Compress 176)` +
      `KeepsExec`),
    - `withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk)` (and `withAlloc`),
    - multi-block `withLsRet (withStack (compress256Spec sha256Compress) stk)` (plain,
      `withVmPreserved`, `withAlloc`),
    - single-block `withLsRet (withStack (compress256RowSingleSpec sha256Compress) stk)` (plain,
      `withVmPreserved`, `withAlloc`). -/
structure Compress256RowSpec [LibsignalPlacement] (f : State → State) : Prop where
  exact : HookOkCompress256 f sha256Compress
  roBudget : ∀ stk : Nat, 176 ≤ stk →
    HookOk f (withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk))
  roBudget_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 176 ≤ stk →
    HookOk f (withLsRet (withAlloc A lim (sessionCompress256ROBudgetSpec sha256Compress stk)))
  multi : ∀ stk : Nat, 176 ≤ stk →
    HookOk f (withLsRet (withStack (compress256Spec sha256Compress) stk))
  multi_vm : ∀ stk : Nat, 176 ≤ stk →
    HookOk f (withLsRet (withVmPreserved (withStack (compress256Spec sha256Compress) stk)))
  multi_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 176 ≤ stk →
    HookOk f (withLsRet (withAlloc A lim (withStack (compress256Spec sha256Compress) stk)))
  single : ∀ stk : Nat, 176 ≤ stk →
    HookOk f (withLsRet (withStack (compress256RowSingleSpec sha256Compress) stk))
  single_vm : ∀ stk : Nat, 176 ≤ stk →
    HookOk f (withLsRet (withVmPreserved (withStack (compress256RowSingleSpec sha256Compress) stk)))
  single_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 176 ≤ stk →
    HookOk f (withLsRet (withAlloc A lim (withStack (compress256RowSingleSpec sha256Compress) stk)))

private theorem hookOk_withLsRet_withAlloc_of_ls [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved (withLsRet spec))) :
    HookOk f (withLsRet (withAlloc A lim spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  exact hookOk_withAlloc_of_withVmPreserved A lim hh ⟨x, st⟩ R s0 hrun
    (by dsimp only [withLsRet, withAlloc] at hpre ⊢; simpa only [sepConj_assoc] using hpre) hsp

theorem Compress256RowSpec.of_ls_vm [LibsignalPlacement] {f : State → State}
    (hkeepsExec : ∀ s : State, s.mem.RW (s.readReg64 .x0) 32 → KeepsExec s.mem (f s).mem)
    (hro : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk)))
    (hmulti : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (withLsRet (withStack (compress256Spec sha256Compress) stk)))
    (hsingle : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (withLsRet (withStack (compress256RowSingleSpec sha256Compress) stk)))
    (hvm : ∀ s : State, VmPreserved s (f s)) : Compress256RowSpec f where
  exact := ⟨hro 176 (by decide), hkeepsExec⟩
  roBudget := hro
  roBudget_alloc := fun A lim stk hlo =>
    hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hro stk hlo) hvm)
  multi := hmulti
  multi_vm := fun stk hlo => hookOk_withVmPreserved (hmulti stk hlo) hvm
  multi_alloc := fun A lim stk hlo =>
    hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hmulti stk hlo) hvm)
  single := hsingle
  single_vm := fun stk hlo => hookOk_withVmPreserved (hsingle stk hlo) hvm
  single_alloc := fun A lim stk hlo =>
    hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (hsingle stk hlo) hvm)

theorem Compress256RowSpec.of_vm [LibsignalPlacement] {f : State → State}
    (hkeepsExec : ∀ s : State, s.mem.RW (s.readReg64 .x0) 32 → KeepsExec s.mem (f s).mem)
    (hro : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (sessionCompress256ROBudgetSpec sha256Compress stk))
    (hmulti : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (withStack (compress256Spec sha256Compress) stk))
    (hsingle : ∀ stk : Nat, 176 ≤ stk →
      HookOk f (withStack (compress256RowSingleSpec sha256Compress) stk))
    (hvm : ∀ s : State, VmPreserved s (f s)) : Compress256RowSpec f :=
  Compress256RowSpec.of_ls_vm hkeepsExec
    (fun stk hlo => hookOk_withLsRet (hro stk hlo))
    (fun stk hlo => hookOk_withLsRet (hmulti stk hlo))
    (fun stk hlo => hookOk_withLsRet (hsingle stk hlo))
    hvm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec
