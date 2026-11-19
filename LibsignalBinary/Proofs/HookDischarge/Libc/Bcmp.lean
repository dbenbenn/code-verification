/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.MemcmpProof
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import

/-!
# Byte-Exact `bcmp` / `memcmp` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp`)

Byte-exact discharge of all `signal-session` CLI and E2E `bcmp` / `memcmp` call-site contracts
by routing directly through `VerifiedLibraries.Musl.Proofs.MemcmpProof`
(`memcmpROPreserving_libca_codeAt_ok`, `bcmpROPreserving_patchCalls_ok`, `bcmpROPreserving_image_ok`,
and `MemcmpStatePreserved`) over `VerifiedLibraries.Musl.bcmpWords` (`1` word `[0x17fffff6#32]`,
patched tail-call `b memcmp` via `bcmpCalls = [(0, "memcmp")]`) and
`VerifiedLibraries.Musl.memcmpLibcaWords` (`13` words = `52` B from `rustc 1.98.1`'s
`aarch64-unknown-linux-musl/lib/self-contained/libc.a` `bcmp.lo` and `memcmp.lo`):

1. **Scalar state preservation (`MemcmpStatePreserved`):**
   `MemcmpProof` establishes `sf.mem = s0.mem ∧ sf.vregs = s0.vregs ∧ ProcessFieldsPreserved s0 sf`
   directly on `memcmpLibcaWords` and the 1-word `b memcmp` stub, yielding `bcmpMemVregsROSpec`,
   `VmPreserved s0 sf`, `sf.fs = s0.fs` (`keepsFs`), and `sf.trace = s0.trace` without duplicating
   any loop or tail-call proofs here.
2. **Consumer `bcmp` specs discharged across all `(aRo, bRo : Bool)` combinations:**
   Weakening `bytesAt` / `↦ₛ` to `↦ᵣ` on entry (`satisfies_bytesAt_to_ro` /
   `Satisfies.pointsToBytes_to_ro`) and rewriting `sf.mem = s0.mem` on exit discharges
   `CliExt.bcmpSpec`, `Cli.cliBcmpSpec`, `HooksE.bcmpVregsSpec`, and `HooksE.e2eBcmpSpec`
   (together with `keepsFs`, `withVmPreserved`, and `muslStringProg` image placement).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp

open Arm64 ProofLib
open VerifiedLibraries.Musl (bcmpWords bcmpCalls memcmpLibcaWords bcmpROSpec memcmpROSpec
  RoSlice8 SliceLenPair memcmpBytes memcmpBytes_eq_zero_iff withMemcmpPreserved
  memcmpROPreservingSpec bcmpROPreservingSpec memcmpROPreserving_libca_codeAt_ok
  bcmpROPreserving_patchCalls_ok bcmpROPreserving_image_ok muslStringProg)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (BcmpCall bcmpSpec)
open CryptoVerification.SignalSession.Cli (CliBcmpCall cliBcmpSpec)
open CryptoVerification.E2E.HooksE (BcmpCall bcmpVregsSpec e2eBcmpSpec)
open LibsignalBinary.Heap (VmPreserved FdsHiFrame)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs bytesAt satisfies_bytesAt_to_ro)

/-- Strengthened read-only `memcmp`/`bcmp` specification recording `sf.mem = s0.mem` and
    `sf.vregs = s0.vregs` (both satisfied by the 13 scalar store-free words `memcmpLibcaWords`
    and 1-word `b memcmp` `bcmpWords`). -/
@[expose] def bcmpMemVregsROSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (s1, s2, n, bs1, bs2) s0 =>
    ⌜s0.readReg64 .x0 = s1 ∧ s0.readReg64 .x1 = s2 ∧ s0.readReg64 .x2 = n ∧
      n.toNat = bs1.length ∧ n.toNat = bs2.length⌝ ∗
      (s1 ↦ᵣ bs1) ∗ (s2 ↦ᵣ bs2)
  post := fun (_s1, _s2, _n, bs1, bs2) s0 sf =>
    ⌜sf.readReg32 .x0 = memcmpBytes bs1 bs2 ∧ sf.mem = s0.mem ∧ sf.vregs = s0.vregs⌝ ∗
      (_s1 ↦ᵣ bs1) ∗ (_s2 ↦ᵣ bs2)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Stack-parameterized mirror of `CliExt.bcmpSpec` and `Cli.cliBcmpSpec`. -/
@[expose] def cliBcmpStackSpec (hookStack : Nat := extHookStack) :
    Spec CryptoVerification.SignalSession.CliExt.BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗
      stackAt s.sp hookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      bytesAt x.aRo x.a x.bsA ∗ bytesAt x.bRo x.b x.bsB ∗
      stackAt s0.sp hookStack

/-- `cliBcmpStackSpec extHookStack` is definitionally (`rfl`) `CliExt.bcmpSpec`. -/
theorem cliBcmpStackSpec_extHookStack :
    cliBcmpStackSpec extHookStack = CryptoVerification.SignalSession.CliExt.bcmpSpec := rfl

/-! ## 1. Spec-Level Reductions from `VerifiedLibraries.Musl.Proofs.MemcmpProof` -/

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

private theorem setWidth32_readReg64_eq_readReg32 (s : State) :
    (s.readReg64 .x0).setWidth 32 = s.readReg32 .x0 := rfl

private theorem memcmpROPreserving_eq_bcmpROPreserving :
    memcmpROPreservingSpec = bcmpROPreservingSpec := rfl

/-- Exact `libc.a` `memcmp` bytes (`memcmpLibcaWords`, `13` scalar words) satisfy
    `bcmpMemVregsROSpec` (`sf.mem = s0.mem ∧ sf.vregs = s0.vregs`), derived directly from
    `VerifiedLibraries.Musl.memcmpROPreserving_libca_codeAt_ok`. -/
theorem memcmpLibca_memVregsRO_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcmpLibcaWords) :
    subroutine_ok prog a bcmpMemVregsROSpec := by
  refine subroutine_ok_map (memcmpROPreserving_libca_codeAt_ok prog a hc) ?_
  rintro ⟨s1, s2, n, bs1, bs2⟩ R s0 hpre
  dsimp only [bcmpMemVregsROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen1, hlen2⟩, hmem⟩
  refine ⟨(s1, s2, n, bs1, bs2), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcmpROPreservingSpec, withMemcmpPreserved, memcmpROSpec, RoSlice8, SliceLenPair,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, hlen1, hlen2, Satisfies.of_eq hmem⟩
  · dsimp only [memcmpROPreservingSpec, withMemcmpPreserved, memcmpROSpec, RoSlice8, CType.I32,
      CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [bcmpMemVregsROSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hmem_eq, hvregs, _hpf⟩, hret, _hmem_ro⟩
    rw [hmem_eq]
    exact ⟨⟨hret, rfl, hvregs⟩, by simpa only [sepConj_assoc] using hmem⟩

private theorem cliBcmpStackSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok {prog : Program}
    {entry : BitVec 64} (hookStack : Nat := extHookStack)
    (h : subroutine_ok prog entry bcmpROPreservingSpec) :
    subroutine_ok prog entry (withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))) := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  dsimp only [withVmPreserved, keepsFs, cliBcmpStackSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hmem_a : s0.mem ⊨ (x.a ↦ᵣ x.bsA) ∗ (bytesAt x.bRo x.b x.bsB ∗ (stackAt s0.sp hookStack ∗ R)) :=
    satisfies_bytesAt_to_ro (by simpa only [sepConj_assoc] using hmem)
  have hmem_ab : s0.mem ⊨ (x.b ↦ᵣ x.bsB) ∗ ((x.a ↦ᵣ x.bsA) ∗ (stackAt s0.sp hookStack ∗ R)) :=
    satisfies_bytesAt_to_ro (Satisfies.of_eq hmem_a)
  refine ⟨(x.a, x.b, s0.readReg64 .x2, x.bsA, x.bsB), stackAt s0.sp hookStack ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8, SliceLenPair,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, by omega, Satisfies.of_eq hmem_ab⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8, CType.I32,
      CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [withVmPreserved, keepsFs, cliBcmpStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, setWidth32_readReg64_eq_readReg32] at hpost ⊢
    rcases hpost with ⟨⟨hmem_eq, _hvregs, hpf⟩, hret, _hmem_ro⟩
    rw [hmem_eq]
    refine ⟨vmPreserved_of_processFieldsPreserved hpf, hpf.1, ⟨?_, hpf.2.1⟩,
      by simpa only [sepConj_assoc] using hmem⟩
    rw [hret]
    exact memcmpBytes_eq_zero_iff hlen.symm

private theorem bcmpVregsSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok {prog : Program}
    {entry : BitVec 64} (h : subroutine_ok prog entry bcmpROPreservingSpec) :
    subroutine_ok prog entry
      (withVmPreserved (keepsFs CryptoVerification.E2E.HooksE.bcmpVregsSpec)) := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  dsimp only [withVmPreserved, keepsFs, CryptoVerification.E2E.HooksE.bcmpVregsSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hmem_a : s0.mem ⊨ (x.a ↦ᵣ x.bsA) ∗ ((x.b ↦ₛ x.bsB) ∗ (stackAt s0.sp extHookStack ∗ R)) :=
    Satisfies.pointsToBytes_to_ro (by simpa only [sepConj_assoc] using hmem)
  have hmem_ab : s0.mem ⊨ (x.b ↦ᵣ x.bsB) ∗ ((x.a ↦ᵣ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) :=
    Satisfies.pointsToBytes_to_ro (Satisfies.of_eq hmem_a)
  refine ⟨(x.a, x.b, s0.readReg64 .x2, x.bsA, x.bsB), stackAt s0.sp extHookStack ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8, SliceLenPair,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, by omega, Satisfies.of_eq hmem_ab⟩
  · dsimp only [bcmpROPreservingSpec, withMemcmpPreserved, bcmpROSpec, RoSlice8, CType.I32,
      CType.scalarTy, CType.SemType.valWf] at hpost
    dsimp only [withVmPreserved, keepsFs, CryptoVerification.E2E.HooksE.bcmpVregsSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, setWidth32_readReg64_eq_readReg32] at hpost ⊢
    rcases hpost with ⟨⟨hmem_eq, hvregs, hpf⟩, hret, _hmem_ro⟩
    rw [hmem_eq]
    refine ⟨vmPreserved_of_processFieldsPreserved hpf, hpf.1, ⟨?_, hvregs, hpf.2.1⟩,
      by simpa only [sepConj_assoc] using hmem⟩
    rw [hret]
    exact memcmpBytes_eq_zero_iff hlen.symm

/-- Region-local `subroutine_ok`: exact `libc.a` `memcmp` bytes (`memcmpLibcaWords`) satisfy
    `withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))` across all `(aRo, bRo : Bool)`. -/
theorem memcmpLibca_cliBcmpStackSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords a memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))) := by
  let _ := h_no_ext
  exact cliBcmpStackSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok hookStack
    (memcmpROPreserving_eq_bcmpROPreserving ▸ memcmpROPreserving_libca_codeAt_ok prog a hc)

/-- Region-local `subroutine_ok`: exact `libc.a` `memcmp` bytes (`memcmpLibcaWords`) satisfy
    `withVmPreserved (keepsFs HooksE.bcmpVregsSpec)` (`sf.vregs = s0.vregs` preserved). -/
theorem memcmpLibca_bcmpVregsSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    (hc : prog.hasWords a memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a
      (withVmPreserved (keepsFs CryptoVerification.E2E.HooksE.bcmpVregsSpec)) := by
  let _ := h_no_ext
  exact bcmpVregsSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok
    (memcmpROPreserving_eq_bcmpROPreserving ▸ memcmpROPreserving_libca_codeAt_ok prog a hc)

/-- Region-local layout-generic real-bytes `bcmp` contract (`bcmpWords` patched to
    `resolve "memcmp"` + `memcmpLibcaWords` at `resolve "memcmp"`): satisfies
    `withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hookStack : Nat := extHookStack)
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved (keepsFs (cliBcmpStackSpec hookStack))) := by
  let _ := h_no_ext
  exact cliBcmpStackSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok hookStack
    (bcmpROPreserving_patchCalls_ok prog a resolve hrange hbcmp
      (memcmpROPreserving_libca_codeAt_ok prog (resolve "memcmp") hmemcmp))

/-- Region-local layout-generic real-bytes `bcmp` contract: satisfies
    `withVmPreserved (keepsFs HooksE.bcmpVregsSpec)` (`sf.vregs = s0.vregs` preserved). -/
theorem bcmp_bcmpVregsSpec_withVmPreserved_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a
      (withVmPreserved (keepsFs CryptoVerification.E2E.HooksE.bcmpVregsSpec)) := by
  let _ := h_no_ext
  exact bcmpVregsSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok
    (bcmpROPreserving_patchCalls_ok prog a resolve hrange hbcmp
      (memcmpROPreserving_libca_codeAt_ok prog (resolve "memcmp") hmemcmp))

/-! ## 2. Direct Real-Bytes Consumer Corollaries (`bcmpWords` + `memcmpLibcaWords`) -/

private theorem drop_keepsFs_under_vmPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry (withVmPreserved (keepsFs spec)))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_map h
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by
      dsimp only [withVmPreserved, keepsFs] at hp; rw [hpan] at hp
      exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by
      dsimp only [withVmPreserved, keepsFs] at he; rw [hex] at he
      exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by
      dsimp only [withVmPreserved, keepsFs] at ho; rw [hoom] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withVmPreserved, keepsFs] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, hpost.2.2⟩

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `withVmPreserved CliExt.bcmpSpec`. -/
theorem bcmp_cliExtBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.SignalSession.CliExt.bcmpSpec) :=
  drop_keepsFs_under_vmPreserved
    (bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok extHookStack hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `CliExt.bcmpSpec` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_cliExtBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.SignalSession.CliExt.bcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_cliExtBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `keepsFs CliExt.bcmpSpec`. -/
theorem bcmp_cliExtBcmpSpec_keepsFs_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (keepsFs CryptoVerification.SignalSession.CliExt.bcmpSpec) :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_cliBcmpStackSpec_withVmPreserved_keepsFs_ok extHookStack hrange hbcmp hmemcmp h_no_ext)

/-- `VerifiedLibraries.muslStringLib` placement corollary: `muslStringProg pl (fun _ => none)`
    satisfies `withVmPreserved CliExt.bcmpSpec` at `"bcmp"`. -/
theorem bcmp_cliExtBcmpSpec_image_ok (pl : Obj.Placement)
    (hP : VerifiedLibraries.muslStringLib.Placeable pl) :
    subroutine_ok (muslStringProg pl (fun _ => none))
      ((muslStringProg pl (fun _ => none)).fnAddr "bcmp")
      (withVmPreserved CryptoVerification.SignalSession.CliExt.bcmpSpec) :=
  drop_keepsFs_under_vmPreserved
    (cliBcmpStackSpec_vm_keepsFs_ok_of_bcmpROPreserving_ok extHookStack
      (bcmpROPreserving_image_ok pl (fun _ => none) hP))

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `withVmPreserved DirSpecs.cliBcmpSpec`. -/
theorem bcmp_dirCliBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.SignalSession.Cli.cliBcmpSpec) := by
  have h := bcmp_cliExtBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext
  refine subroutine_ok_map h
    (fun x R s0 hpre => ⟨⟨x.a, x.aRo, x.bsA, x.b, x.bRo, x.bsB⟩, R, hpre, fun _ hpost => hpost⟩)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `DirSpecs.cliBcmpSpec` across all `(aRo, bRo : Bool)`. -/
theorem bcmp_dirCliBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.SignalSession.Cli.cliBcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_dirCliBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `withVmPreserved HooksE.bcmpVregsSpec`. -/
theorem bcmp_bcmpVregsSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.E2E.HooksE.bcmpVregsSpec) :=
  drop_keepsFs_under_vmPreserved
    (bcmp_bcmpVregsSpec_withVmPreserved_keepsFs_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `HooksE.bcmpVregsSpec` (`sf.vregs = s0.vregs`). -/
theorem bcmp_bcmpVregsSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.E2E.HooksE.bcmpVregsSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_bcmpVregsSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `withVmPreserved HooksE.e2eBcmpSpec`. -/
theorem bcmp_e2eBcmpSpec_withVmPreserved_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a (withVmPreserved CryptoVerification.E2E.HooksE.e2eBcmpSpec) := by
  have h := bcmp_bcmpVregsSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext
  refine subroutine_ok_map h (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  dsimp only [withVmPreserved, CryptoVerification.E2E.HooksE.bcmpVregsSpec,
    CryptoVerification.E2E.HooksE.e2eBcmpSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1, ⟨hpost.2.1.1, hpost.2.1.2.2⟩, hpost.2.2⟩

/-- Region-local `subroutine_ok`: real `libc.a` `bcmp` + `memcmp` bytes satisfy
    `HooksE.e2eBcmpSpec`. -/
theorem bcmp_e2eBcmpSpec_ok {prog : Program} {a : BitVec 64}
    {resolve : String → BitVec 64}
    (hrange : Obj.BranchInRange (a + 0#64) (resolve "memcmp"))
    (hbcmp : prog.hasWords a (Obj.patchCalls bcmpCalls bcmpWords a resolve))
    (hmemcmp : prog.hasWords (resolve "memcmp") memcmpLibcaWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none) :
    subroutine_ok prog a CryptoVerification.E2E.HooksE.e2eBcmpSpec :=
  LibsignalBinary.Heap.SpecBudget.subroutine_ok_of_withVmPreserved
    (bcmp_e2eBcmpSpec_withVmPreserved_ok hrange hbcmp hmemcmp h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Libc.Bcmp
