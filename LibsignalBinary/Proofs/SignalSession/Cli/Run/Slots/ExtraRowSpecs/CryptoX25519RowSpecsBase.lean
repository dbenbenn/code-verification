/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import ProofLib.Hoare.Model
import ProofLib.Process.PureMem

/-!
# Placement-Free X25519 Consumer `HookOk` Row Structures & Pure Fallbacks (`CryptoX25519RowSpecsBase`)

Cycle-free base leaf module for the two X25519 rows in `ExtraGhostSpecs.ExtraRowSpec`:
- `lsPubFromSecretSym` (`X25519PubFromSecretRowSpec`, stack slack `1904 ≤ stk ≤ 2 ^ 64`, fixed at
  `x25519PubFromSecretRef`);
- `lsDiffieHellmanSym` (`X25519DiffieHellmanRowSpec`, stack slack `1808 ≤ stk ≤ 2 ^ 64`, fixed at
  `x25519Ref`);
together with the pure fallback instantiations (`pubFromSecretFallback_rowSpec`,
`diffieHellmanFallback_rowSpec`), kept strictly below `ExtraGhostSpecs` / `CliHookSatPlaced` /
`Phase4GhostHooks`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet
  (derivePublicKeyBytesStackSpec diffieHellmanHook diffieHellmanHook_ok diffieHellmanSpec
   extHookStack pubFromSecretHook pubFromSecretHook_ok pubFromSecretSpec)
open CryptoVerification.SignalSession.CliExt (dhSpec pureByteFunctionSpec withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FdsHiFrame RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (x25519PubFromSecretRef x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookOk_withLsRet specSimulates_withLsRet withLsRet withLsRet_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)

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

private theorem withLsRet_withAlloc [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc A lim spec) = withAlloc A lim (withLsRet spec) := by
  cases spec
  dsimp only [withLsRet, withAlloc]
  congr 1
  funext ⟨x, st⟩ s
  simp only [sepConj_assoc]

/-! ## 1. `lsPubFromSecretSym` Consumer Row Contract (`X25519PubFromSecretRowSpec`) -/

/-- Consumer `HookOk` arm for `lsPubFromSecretSym` (`<PublicKey as From<&StaticSecret>>::from`,
    Block `18` of `x25519CliMultiLib`), narrowed with outermost Route-`R0` `withLsRet` at
    `x25519PubFromSecretRef` (`1904 ≤ stk ≤ 2 ^ 64`). -/
structure X25519PubFromSecretRowSpec [LibsignalPlacement] (f : State → State) : Prop where
  vmPreserved : ∀ s : State, VmPreserved s (f s)
  fs_eq : ∀ s : State, (f s).fs = s.fs
  withStack_ls : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))
  withStack_vm : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withVmPreserved (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)))
  withStack_keepsFs : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk))))
  withStack_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withAlloc A lim (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)))
  withStack_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withAlloc A lim (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)))
  cliExt_ls : ∀ {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))
  cliExt_vm : ∀ {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
    HookOk f (withLsRet (withVmPreserved
      (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))
  cliExt_keepsFs : ∀ {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))))
  cliExt_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
    HookOk f (withLsRet (withAlloc A lim
      (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))
  cliExt_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
    HookOk f (withAlloc A lim (withLsRet
      (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))
  pureByteFunction_ls : ∀ byVal : Bool,
    HookOk f (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal))
  pureByteFunction_vm : ∀ byVal : Bool,
    HookOk f (withLsRet (withVmPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal)))
  pureByteFunction_keepsFs : ∀ byVal : Bool,
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (pureByteFunctionSpec x25519PubFromSecretRef byVal))))
  pureByteFunction_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (byVal : Bool),
    HookOk f (withLsRet (withAlloc A lim (pureByteFunctionSpec x25519PubFromSecretRef byVal)))
  pureByteFunction_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (byVal : Bool),
    HookOk f (withAlloc A lim (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal)))
  derivePublicKeyBytesStack_ls : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))
  derivePublicKeyBytesStack_vm : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
  derivePublicKeyBytesStack_keepsFs : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))))
  derivePublicKeyBytesStack_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
  derivePublicKeyBytesStack_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))
  derivePublicKeyBytesStackBudget_ls : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))
  derivePublicKeyBytesStackBudget_vm : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))
  derivePublicKeyBytesStackBudget_keepsFs : ∀ stk : Nat, 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))))
  derivePublicKeyBytesStackBudget_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))
  derivePublicKeyBytesStackBudget_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat), 1904 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))

/-! ## 2. `lsDiffieHellmanSym` Consumer Row Contract (`X25519DiffieHellmanRowSpec`) -/

/-- Consumer `HookOk` arm for `lsDiffieHellmanSym` (`<StaticSecret>::diffie_hellman`, Block `17` of
    `x25519CliMultiLib`), narrowed with outermost Route-`R0` `withLsRet` at `x25519Ref`
    (`1808 ≤ stk ≤ 2 ^ 64`). -/
structure X25519DiffieHellmanRowSpec [LibsignalPlacement] (f : State → State) : Prop where
  vmPreserved : ∀ s : State, VmPreserved s (f s)
  fs_eq : ∀ s : State, (f s).fs = s.fs
  withStack_ls : ∀ stk : Nat, 1808 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk))
  withStack_vm : ∀ stk : Nat, 1808 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved (withStack (diffieHellmanSpec x25519Ref) stk)))
  withStack_keepsFs : ∀ stk : Nat, 1808 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved (keepsFs (withStack (diffieHellmanSpec x25519Ref) stk))))
  withStack_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 1808 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withAlloc A lim (withStack (diffieHellmanSpec x25519Ref) stk)))
  withStack_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat), 1808 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withAlloc A lim (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk)))
  cliExt_ls : ∀ {C : Crypto}, C.X = x25519Ref → HookOk f (withLsRet (dhSpec C))
  cliExt_vm : ∀ {C : Crypto}, C.X = x25519Ref → HookOk f (withLsRet (withVmPreserved (dhSpec C)))
  cliExt_keepsFs : ∀ {C : Crypto}, C.X = x25519Ref →
    HookOk f (withLsRet (withVmPreserved (keepsFs (dhSpec C))))
  cliExt_alloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto}, C.X = x25519Ref →
    HookOk f (withLsRet (withAlloc A lim (dhSpec C)))
  cliExt_alloc_ls : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto}, C.X = x25519Ref →
    HookOk f (withAlloc A lim (withLsRet (dhSpec C)))

/-! ## 3. Pure Fallback Instantiations (`pubFromSecretHook`, `diffieHellmanHook`) -/

private theorem pubFromSecretHook_vmPreserved {pubKey} (s0 : State) :
    VmPreserved s0 (pubFromSecretHook pubKey s0) := by
  unfold pubFromSecretHook
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => ?_, FdsHiFrame.of_fs_eq rfl⟩
  simp only [retHook, State.setPC, State.setMem, Memory.perm_writeBytes]

private theorem diffieHellmanHook_vmPreserved {X} (s0 : State) :
    VmPreserved s0 (diffieHellmanHook X s0) := by
  unfold diffieHellmanHook
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => ?_, FdsHiFrame.of_fs_eq rfl⟩
  simp only [retHook, State.setPC, State.setMem, Memory.perm_writeBytes]

attribute [local irreducible] x25519PubFromSecretRef x25519Ref

private theorem hookOk_keepsFs_of_fs_eq {α : Type} {fb : State → State} {spec : Spec α}
    (hok : HookOk fb spec) (hfs : ∀ s : State, (fb s).fs = s.fs)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    HookOk fb (keepsFs spec) :=
  fun x R s0 hrun hpre hsp => by
    obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [keepsFs]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfs s0, hpost⟩
    · rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
    · rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
    · rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

private theorem hookOk_withStack_of_unstacked {α : Type} {fb : State → State} {spec : Spec α}
    (hok : HookOk fb spec) (stk : Nat)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    HookOk fb (withStack spec stk) :=
  fun x R s0 hrun hpre hsp => by
    dsimp only [withStack] at hpre
    rw [sepConj_assoc] at hpre
    obtain ⟨hkf, hsym, hout⟩ := hok x (stackAt s0.sp stk ∗ R) s0 hrun hpre hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withStack]
      rwa [sepConj_assoc]
    · rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
    · rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
    · rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

private theorem pubFromSecret_sim_pureByteFunction (byVal : Bool) :
    SpecSimulates
      (withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack)
      (pureByteFunctionSpec x25519PubFromSecretRef byVal) := by
  cases byVal
  · exact fun x R _ hpre => ⟨x, R, hpre, fun _ hout => hout⟩
  · refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R _ hpre =>
      ⟨(inA, v, ret), R, hpre, fun _ _ _ hpost => ?_⟩
    dsimp only [withStack, pubFromSecretSpec, pureByteFunctionSpec,
      CryptoVerification.SignalSession.CliExt.inputAfter, reduceIte] at hpost ⊢
    have hent : (inA ↦ₛ v.toList) ⊢ memRegion inA 32 := by
      simpa using pointsToBytes_entails_memRegion inA v.toList
    exact Satisfies.mono (by
      refine sepConj_mono (sepConj_mono ?_ (Entails.refl _)) (Entails.refl _)
      refine sepConj_mono (Entails.refl _) (sepConj_mono hent (Entails.refl _))) hpost

private theorem pubFromSecret_sim_derivePublicKeyBytesStack (stk : Nat) :
    SpecSimulates
      (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)
      (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk) := by
  refine SpecSimulates.of_map fun x R _ hpre => ?_
  refine ⟨(x.secret, x.sec, x.out), R, ?_, fun _ _ _ hpost => ?_⟩
  · dsimp only [withStack, pubFromSecretSpec, derivePublicKeyBytesStackSpec] at hpre ⊢
    exact Satisfies.mono (by sep_entail) hpre
  · dsimp only [withStack, pubFromSecretSpec, derivePublicKeyBytesStackSpec] at hpost ⊢
    exact Satisfies.mono (by sep_entail) hpost

private theorem derivePublicKeyBytesStack_sim_budget (stk : Nat) :
    SpecSimulates
      (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))
      (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk) := by
  refine SpecSimulates.of_map fun x R s0 hpre => ⟨x, R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [withVmPreserved, derivePublicKeyBytesStackSpec,
    derivePublicKeyBytesStackBudgetSpec] at hpost ⊢
  have h1 : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗ (⌜sf.trace = s0.trace⌝ ∗
      ((x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (x25519PubFromSecretRef x.sec).toList) ∗
        stackAt s0.sp stk ∗ R)) :=
    Satisfies.mono (by sep_entail) hpost
  obtain ⟨hvm, h2⟩ := (satisfies_pure_sepConj _ _ _).mp h1
  obtain ⟨htr, h3⟩ := (satisfies_pure_sepConj _ _ _).mp h2
  have h4 : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      ((x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (x25519PubFromSecretRef x.sec).toList) ∗
        stackAt s0.sp stk ∗ R) :=
    (satisfies_pure_sepConj _ _ _).mpr ⟨⟨htr, hvm⟩, h3⟩
  exact Satisfies.mono (by sep_entail) h4

/-- Pure fallback `pubFromSecretHook x25519PubFromSecretRef` satisfies
    `X25519PubFromSecretRowSpec`. -/
theorem pubFromSecretFallback_rowSpec [LibsignalPlacement] :
    X25519PubFromSecretRowSpec (pubFromSecretHook x25519PubFromSecretRef) := by
  let fb := pubFromSecretHook x25519PubFromSecretRef
  have hvm : ∀ s : State, VmPreserved s (fb s) :=
    pubFromSecretHook_vmPreserved
  have hfs : ∀ s : State, (fb s).fs = s.fs := fun _ => rfl
  have hstk_raw : ∀ stk : Nat, HookOk fb (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk) :=
    fun stk => hookOk_withStack_of_unstacked (pubFromSecretHook_ok x25519PubFromSecretRef) stk
  have hls : ∀ stk : Nat,
      HookOk fb (withLsRet (withStack (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
    fun stk => hookOk_withLsRet (hstk_raw stk)
  have hcli_ls : ∀ {C : Crypto}, C.pubKey = x25519PubFromSecretRef →
      HookOk fb (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) := by
    intro C hC
    have heq : CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C =
        withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack := by
      rw [← hC]; rfl
    rw [heq]; exact hls extHookStack
  have hpbf_ls : ∀ byVal : Bool,
      HookOk fb (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal)) :=
    fun byVal => hookOk_withLsRet_of_simulates
      (pubFromSecret_sim_pureByteFunction byVal) (hls extHookStack)
  have hdpk_ls : ∀ stk : Nat,
      HookOk fb (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
    fun stk => hookOk_withLsRet_of_simulates
      (pubFromSecret_sim_derivePublicKeyBytesStack stk) (hls stk)
  have hdpk_vm : ∀ stk : Nat,
      HookOk fb
        (withLsRet (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
    fun stk => by
      rw [withLsRet_withVmPreserved]
      exact hookOk_withVmPreserved (hdpk_ls stk) hvm
  have hdpkb_ls : ∀ stk : Nat,
      HookOk fb (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)) :=
    fun stk => hookOk_withLsRet_of_simulates
      (derivePublicKeyBytesStack_sim_budget stk) (hdpk_vm stk)
  exact
    { vmPreserved := hvm
      fs_eq := hfs
      withStack_ls := fun stk _ _ => hls stk
      withStack_vm := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hls stk) hvm
      withStack_keepsFs := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]
        exact hookOk_withVmPreserved (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq (hstk_raw stk) hfs)) hvm
      withStack_alloc := fun A lim stk _ _ => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hls stk) hvm)
      withStack_alloc_ls := fun A lim stk _ _ =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hls stk) hvm)
      cliExt_ls := hcli_ls
      cliExt_vm := fun hC => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hcli_ls hC) hvm
      cliExt_keepsFs := fun {C} hC => by
        have heq : CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C =
            withStack (pubFromSecretSpec x25519PubFromSecretRef) extHookStack := by
          rw [← hC]; rfl
        rw [heq, withLsRet_withVmPreserved]
        exact hookOk_withVmPreserved
          (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq (hstk_raw extHookStack) hfs)) hvm
      cliExt_alloc := fun {_} A lim {_} hC => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hcli_ls hC) hvm)
      cliExt_alloc_ls := fun {_} A lim {_} hC =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hcli_ls hC) hvm)
      pureByteFunction_ls := hpbf_ls
      pureByteFunction_vm := fun byVal => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hpbf_ls byVal) hvm
      pureByteFunction_keepsFs := fun byVal => by
        rw [withLsRet_withVmPreserved]
        have hpbf_raw : HookOk fb (pureByteFunctionSpec x25519PubFromSecretRef byVal) :=
          fun y R s0 hrun hpre hsp => by
            obtain ⟨x, R₁, hpre₁, hmap⟩ :=
              pubFromSecret_sim_pureByteFunction byVal y R s0 hpre
            obtain ⟨hkf, hsym, hout⟩ := hstk_raw extHookStack x R₁ s0 hrun hpre₁ hsp
            exact ⟨hkf, hsym, hmap _ hout⟩
        exact hookOk_withVmPreserved (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq hpbf_raw hfs)) hvm
      pureByteFunction_alloc := fun A lim byVal => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hpbf_ls byVal) hvm)
      pureByteFunction_alloc_ls := fun A lim byVal =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hpbf_ls byVal) hvm)
      derivePublicKeyBytesStack_ls := fun stk _ _ => hdpk_ls stk
      derivePublicKeyBytesStack_vm := fun stk _ _ => hdpk_vm stk
      derivePublicKeyBytesStack_keepsFs := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]
        have hdpk_raw : HookOk fb (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk) :=
          fun y R s0 hrun hpre hsp => by
            obtain ⟨x, R₁, hpre₁, hmap⟩ :=
              pubFromSecret_sim_derivePublicKeyBytesStack stk y R s0 hpre
            obtain ⟨hkf, hsym, hout⟩ := hstk_raw stk x R₁ s0 hrun hpre₁ hsp
            exact ⟨hkf, hsym, hmap _ hout⟩
        exact hookOk_withVmPreserved (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq hdpk_raw hfs)) hvm
      derivePublicKeyBytesStack_alloc := fun A lim stk _ _ => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hdpk_ls stk) hvm)
      derivePublicKeyBytesStack_alloc_ls := fun A lim stk _ _ =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hdpk_ls stk) hvm)
      derivePublicKeyBytesStackBudget_ls := fun stk _ _ => hdpkb_ls stk
      derivePublicKeyBytesStackBudget_vm := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hdpkb_ls stk) hvm
      derivePublicKeyBytesStackBudget_keepsFs := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]
        have hdpkb_raw :
            HookOk fb (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk) :=
          fun y R s0 hrun hpre hsp => by
            have hdpk_raw : HookOk fb
                (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
              hookOk_withVmPreserved
                (fun y' R' s0' hrun' hpre' hsp' => by
                  obtain ⟨x, R₁, hpre₁, hmap⟩ :=
                    pubFromSecret_sim_derivePublicKeyBytesStack stk y' R' s0' hpre'
                  obtain ⟨hkf, hsym, hout⟩ := hstk_raw stk x R₁ s0' hrun' hpre₁ hsp'
                  exact ⟨hkf, hsym, hmap _ hout⟩) hvm
            obtain ⟨x, R₁, hpre₁, hmap⟩ :=
              derivePublicKeyBytesStack_sim_budget stk y R s0 hpre
            obtain ⟨hkf, hsym, hout⟩ := hdpk_raw x R₁ s0 hrun hpre₁ hsp
            exact ⟨hkf, hsym, hmap _ hout⟩
        exact hookOk_withVmPreserved (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq hdpkb_raw hfs)) hvm
      derivePublicKeyBytesStackBudget_alloc := fun A lim stk _ _ => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hdpkb_ls stk) hvm)
      derivePublicKeyBytesStackBudget_alloc_ls := fun A lim stk _ _ =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hdpkb_ls stk) hvm) }

/-- Pure fallback `diffieHellmanHook x25519Ref` satisfies `X25519DiffieHellmanRowSpec`. -/
theorem diffieHellmanFallback_rowSpec [LibsignalPlacement] :
    X25519DiffieHellmanRowSpec (diffieHellmanHook x25519Ref) := by
  let fb := diffieHellmanHook x25519Ref
  have hvm : ∀ s : State, VmPreserved s (fb s) :=
    diffieHellmanHook_vmPreserved
  have hfs : ∀ s : State, (fb s).fs = s.fs := fun _ => rfl
  have hstk_raw : ∀ stk : Nat, HookOk fb (withStack (diffieHellmanSpec x25519Ref) stk) :=
    fun stk => hookOk_withStack_of_unstacked (diffieHellmanHook_ok x25519Ref) stk
  have hls : ∀ stk : Nat, HookOk fb (withLsRet (withStack (diffieHellmanSpec x25519Ref) stk)) :=
    fun stk => hookOk_withLsRet (hstk_raw stk)
  have hcli_ls : ∀ {C : Crypto}, C.X = x25519Ref → HookOk fb (withLsRet (dhSpec C)) := by
    intro C hC
    have heq : dhSpec C = withStack (diffieHellmanSpec x25519Ref) extHookStack := by
      rw [← hC]; rfl
    rw [heq]; exact hls extHookStack
  exact
    { vmPreserved := hvm
      fs_eq := hfs
      withStack_ls := fun stk _ _ => hls stk
      withStack_vm := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hls stk) hvm
      withStack_keepsFs := fun stk _ _ => by
        rw [withLsRet_withVmPreserved]
        exact hookOk_withVmPreserved (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq (hstk_raw stk) hfs)) hvm
      withStack_alloc := fun A lim stk _ _ => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hls stk) hvm)
      withStack_alloc_ls := fun A lim stk _ _ =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hls stk) hvm)
      cliExt_ls := hcli_ls
      cliExt_vm := fun hC => by
        rw [withLsRet_withVmPreserved]; exact hookOk_withVmPreserved (hcli_ls hC) hvm
      cliExt_keepsFs := fun {C} hC => by
        have heq : dhSpec C = withStack (diffieHellmanSpec x25519Ref) extHookStack := by
          rw [← hC]; rfl
        rw [heq, withLsRet_withVmPreserved]
        exact hookOk_withVmPreserved
          (hookOk_withLsRet (hookOk_keepsFs_of_fs_eq (hstk_raw extHookStack) hfs)) hvm
      cliExt_alloc := fun {_} A lim {_} hC => by
        rw [withLsRet_withAlloc]
        exact hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hcli_ls hC) hvm)
      cliExt_alloc_ls := fun {_} A lim {_} hC =>
        hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (hcli_ls hC) hvm) }

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
