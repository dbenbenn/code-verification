/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced -- proof-setup: allow-public-import
import LibsignalBinary.Heap.IfaceBudgetLemmas
import ProofLib.Hoare.Model
import ProofLib.Process.PureMem

/-!
# `<std::sys::sync::once::futex::Once>::call` Consumer `HookOk` Row Arm (`SpqrOnceCallRowSpec`)

Row-owned consumer-contract leaf module for `spqrOnceCallSym` (`lsSpqrOnceCallSym`) in
`ExtraGhostSpecs.ExtraRowSpec`, together with the `[LibsignalPlacement]`-indexed pure fallback
`spqrOnceCallFallback` satisfying `HookOk spqrOnceCallFallback spqrOnceCallGhostSpec`.

Like `LibcruxHmacRowSpec` and `AesEncRowSpec`/`AesDecRowSpec`, `spqrOnceCallGhostSpec` depends on
placement (`lsρ tokenStorageName` in `post`), so `SpqrOnceCallRowSpec` is `True` inside
placement-free `ExtraRowSpec` (`pureExtraGhosts`, `a0Ghost`, `bumpGhost`), while `CliGhostSpqrAllocHooks`
carries the placement-indexed `HookOk` and `lsρ`-uniqueness fields (`OnceCallHookOk`).
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (LsRetAddrNoProbe spqrLazyLockVtableSym spqrOnceCallGhostSpec spqrOnceCallSym spqrProbeEnvAt)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (perm_writeBytes_norm)

/-- Row-owned consumer `ExtraRowSpec` predicate for `lsSpqrOnceCallSym` (`True`; placement-indexed
    `spqrOnceCallGhostSpec` `HookOk` and `lsρ` uniqueness live in `CliGhostSpqrAllocHooks`). -/
@[expose] def SpqrOnceCallRowSpec (_f : State → State) : Prop :=
  True

theorem SpqrOnceCallRowSpec.intro (f : State → State) : SpqrOnceCallRowSpec f :=
  trivial

/-- Pure `[LibsignalPlacement]`-indexed fallback for `spqrOnceCallSym`: reads `slotPtr := *x2`,
    writes `1#8` to `STORAGE.0`, `0#32` to `TOKEN + 8`, and `0#64` to `*slotPtr`, and returns to
    `lr` preserving `fs`, `trace`, `VmPreserved`, and `AllocCallPreserved`. -/
@[expose] def spqrOnceCallFallback [LibsignalPlacement] (s : State) : State :=
  let slotPtr := s.mem.read64 (s.readReg64 .x2)
  let m1 := s.mem.writeBytes (lsρ tokenStorageName) [1#8]
  let m2 := m1.writeBytes (lsρ tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]
  let m3 := m2.writeBytes slotPtr [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
  returnToLinkRegister (s.setMem m3)

theorem spqrOnceCallFallback_fs [LibsignalPlacement] (s : State) :
    (spqrOnceCallFallback s).fs = s.fs :=
  rfl

theorem spqrOnceCallFallback_trace [LibsignalPlacement] (s : State) :
    (spqrOnceCallFallback s).trace = s.trace :=
  rfl

theorem spqrOnceCallFallback_fsT [LibsignalPlacement] :
    HookFsTraced IsFsC spqrOnceCallFallback :=
  fun _ => FsTraced.of_eq rfl rfl

theorem spqrOnceCallFallback_noAllocFailed [LibsignalPlacement] (s : State) :
    ∃ d : List TraceEvent, (spqrOnceCallFallback s).trace = s.trace ++ d ∧
      allocFailedEvent ∉ d :=
  ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩

theorem spqrOnceCallFallback_perm [LibsignalPlacement] (s : State) (a : BitVec 64) :
    (spqrOnceCallFallback s).mem.perm a = s.mem.perm a := by
  unfold spqrOnceCallFallback returnToLinkRegister
  dsimp only
  have h3 := congrFun (perm_writeBytes_norm (s.mem.writeBytes (lsρ tokenStorageName) [1#8]
    |>.writeBytes (lsρ tokenName + 8#64) [0#8, 0#8, 0#8, 0#8])
    (s.mem.read64 (s.readReg64 .x2)) [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]) a
  have h2 := congrFun (perm_writeBytes_norm (s.mem.writeBytes (lsρ tokenStorageName) [1#8])
    (lsρ tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]) a
  have h1 := congrFun (perm_writeBytes_norm s.mem (lsρ tokenStorageName) [1#8]) a
  exact h3.trans (h2.trans h1)

theorem spqrOnceCallFallback_vmPreserved [LibsignalPlacement] (s : State) :
    VmPreserved s (spqrOnceCallFallback s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, spqrOnceCallFallback_perm s, fun _ _ _ => rfl⟩

theorem spqrOnceCallFallback_acp [LibsignalPlacement] (s : State) :
    AllocCallPreserved s (spqrOnceCallFallback s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pointsToBytes_zero4 (a : BitVec 64) :
    (a ↦ₛ [0#8, 0#8, 0#8, 0#8]) = (a ↦₃₂ 0#32) := by
  rw [pointsToBytes4_eq_pointsTo32]
  rfl

private theorem pointsToBytes_zero8 (a : BitVec 64) :
    (a ↦ₛ [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]) = (a ↦₆₄ 0#64) := by
  rw [pointsToBytes8_eq_pointsTo64]
  rfl

theorem spqrOnceCallFallback_ok [LibsignalPlacement] :
    HookOk spqrOnceCallFallback spqrOnceCallGhostSpec := by
  intro ⟨dp, sp⟩ R s0 hrun hpre _hsp
  dsimp only [spqrOnceCallGhostSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hlr, _hx0, _hx1, hx2, _hx3⟩, hmem0⟩
  have hmem_dp :
      s0.mem ⊨ (dp ↦₆₄ sp) ∗
        ((lsρ tokenStorageName ↦₈ 255#8) ∗ ((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗
          spqrProbeEnvAt ∗ (sp ↦₆₄ lsρ tokenName) ∗ stackAt s0.sp 160 ∗ R) :=
    Satisfies.mono (by sep_entail) hmem0
  have hsp_rd : s0.mem.read64 dp = sp := (IsBlock.pointsTo64 dp sp).read hmem_dp
  let m1 := s0.mem.writeBytes (lsρ tokenStorageName) [1#8]
  let m2 := m1.writeBytes (lsρ tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]
  let m3 := m2.writeBytes sp [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
  have hreg1 :
      s0.mem ⊨ memRegion (lsρ tokenStorageName) ([1#8].length) ∗
        (((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗ spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗
          (sp ↦₆₄ lsρ tokenName) ∗ stackAt s0.sp 160 ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (pointsTo8_entails_memRegion (lsρ tokenStorageName) 255#8)) hmem0
  have hkf1 : Memory.KeepsFrozen s0.mem m1 :=
    keepsFrozen_writeBytes_of_memRegion [1#8] (by decide) hreg1
  have hp1 : m1.perm = s0.mem.perm := perm_writeBytes_norm _ _ _
  have hm1 :
      m1 ⊨ (lsρ tokenStorageName ↦₈ 1#8) ∗
        (((lsρ tokenName + 8#64) ↦₃₂ 3#32) ∗ spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗
          (sp ↦₆₄ lsρ tokenName) ∗ stackAt s0.sp 160 ∗ R) := by
    have hw1 := satisfies_writeBytes [1#8] (by decide) hreg1
    rwa [pointsToBytes_singleton] at hw1
  have hreg2 :
      m1 ⊨ memRegion (lsρ tokenName + 8#64) ([0#8, 0#8, 0#8, 0#8].length) ∗
        ((lsρ tokenStorageName ↦₈ 1#8) ∗ spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗
          (sp ↦₆₄ lsρ tokenName) ∗ stackAt s0.sp 160 ∗ R) := by
    refine Satisfies.mono ?_ hm1
    refine Entails.trans (by sep_entail)
      (sepConj_mono_left (pointsTo32_entails_memRegion (lsρ tokenName + 8#64) 3#32))
  have hkf2 : Memory.KeepsFrozen m1 m2 :=
    keepsFrozen_writeBytes_of_memRegion [0#8, 0#8, 0#8, 0#8] (by decide) hreg2
  have hp2 : m2.perm = m1.perm := perm_writeBytes_norm _ _ _
  have hm2 :
      m2 ⊨ ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
        ((lsρ tokenStorageName ↦₈ 1#8) ∗ spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗
          (sp ↦₆₄ lsρ tokenName) ∗ stackAt s0.sp 160 ∗ R) := by
    have hw2 := satisfies_writeBytes [0#8, 0#8, 0#8, 0#8] (by decide) hreg2
    rwa [pointsToBytes_zero4] at hw2
  have hreg3 :
      m2 ⊨ memRegion sp ([0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8].length) ∗
        ((lsρ tokenStorageName ↦₈ 1#8) ∗ ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
          spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗ stackAt s0.sp 160 ∗ R) := by
    refine Satisfies.mono ?_ hm2
    refine Entails.trans (by sep_entail)
      (sepConj_mono_left (pointsTo64_entails_memRegion sp (lsρ tokenName)))
  have hkf3 : Memory.KeepsFrozen m2 m3 :=
    keepsFrozen_writeBytes_of_memRegion [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] (by decide) hreg3
  have hp3 : m3.perm = m2.perm := perm_writeBytes_norm _ _ _
  have hm3 :
      m3 ⊨ (sp ↦₆₄ 0#64) ∗
        ((lsρ tokenStorageName ↦₈ 1#8) ∗ ((lsρ tokenName + 8#64) ↦₃₂ 0#32) ∗
          spqrProbeEnvAt ∗ (dp ↦₆₄ sp) ∗ stackAt s0.sp 160 ∗ R) := by
    have hw3 :=
      satisfies_writeBytes [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] (by decide) hreg3
    rwa [pointsToBytes_zero8] at hw3
  have hkf : Memory.KeepsFrozen s0.mem m3 := (hkf1.trans hkf2).trans hkf3
  have hfb_eq : spqrOnceCallFallback s0 = returnToLinkRegister (s0.setMem m3) := by
    unfold spqrOnceCallFallback
    dsimp only
    rw [hx2, hsp_rd]
  have hvm : VmPreserved s0 (spqrOnceCallFallback s0) := spqrOnceCallFallback_vmPreserved s0
  have hacp : AllocCallPreserved s0 (spqrOnceCallFallback s0) := spqrOnceCallFallback_acp s0
  have htr : (spqrOnceCallFallback s0).trace = s0.trace := rfl
  rw [hfb_eq] at hvm hacp htr ⊢
  refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [spqrOnceCallGhostSpec]
  have hm_eq : (returnToLinkRegister (s0.setMem m3)).mem = m3 := rfl
  rw [hm_eq]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hvm, hacp, htr⟩, Satisfies.mono (by sep_entail) hm3⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec
